import crypto from 'crypto';
import dotenv from 'dotenv';
import express, { NextFunction, Request, Response } from 'express';
import fs from 'fs';
import path from 'path';
import { createServer as createViteServer } from 'vite';
import { sanitizeBase64Image } from './server/imageSanitizer';
import {
  appendInternalAuditLog,
  AppStoreData,
  getAdminEmail,
  loadStore,
  saveStore,
  StoredConfession,
  StoredUser,
  toMessageEntries,
  UPLOADS_DIR,
} from './server/store';
import {
  DEFAULT_COOLDOWN_HOURS,
  evaluateCooldown,
  isValidDisplayName,
  isValidEmail,
  isValidPassword,
  isValidUsername,
  MAX_COMMENT_LENGTH,
  MAX_CONFESSION_LENGTH,
  MAX_MESSAGE_LENGTH,
  MIN_CONFESSION_LENGTH,
  MIN_PASSWORD_LENGTH,
  normalizeEmail,
} from './src/shared/rules';
import {
  AdminAccountView,
  AdminQueueConfession,
  AdminQueueLostFound,
  AdminReportItem,
  AuthUser,
  CONFESSION_CATEGORIES,
  ConfessionCategory,
  ConfessionTimeFilter,
  ItemMessageThread,
  LOST_FOUND_CATEGORIES,
  LostFoundCategory,
  PublicComment,
  PublicConfession,
  PublicLostFoundItem,
  REACTION_TYPES,
  ReactionType,
  REJECT_REASONS,
  RejectReason,
} from './src/shared/types';

dotenv.config();

const PORT = 3000;
const SESSION_COOKIE = 'qp_sid';
const VISITOR_COOKIE = 'qp_vid';
const SESSION_TTL_MS = 30 * 24 * 60 * 60 * 1000;
const OTP_TTL_MS = 10 * 60 * 1000;

function getCooldownHours(): number {
  const raw = Number(process.env.CONFESSION_COOLDOWN_HOURS);
  return Number.isFinite(raw) && raw > 0 ? raw : DEFAULT_COOLDOWN_HOURS;
}

function sha256Hex(value: string): string {
  return crypto.createHash('sha256').update(value, 'utf8').digest('hex');
}

function safeEqualText(a: string, b: string): boolean {
  const hashA = crypto.createHash('sha256').update(a, 'utf8').digest();
  const hashB = crypto.createHash('sha256').update(b, 'utf8').digest();
  return crypto.timingSafeEqual(hashA, hashB);
}

function hashPasscode(passcode: string): string {
  const salt = crypto.randomBytes(16).toString('hex');
  const derived = crypto.scryptSync(passcode, salt, 64).toString('hex');
  return `${salt}:${derived}`;
}

function verifyPasscodeHash(passcode: string, storedHash: string): boolean {
  const [salt, hexKey] = storedHash.split(':');
  if (!salt || !hexKey) return false;
  const derived = crypto.scryptSync(passcode, salt, 64);
  const expected = Buffer.from(hexKey, 'hex');
  if (derived.length !== expected.length) return false;
  return crypto.timingSafeEqual(derived, expected);
}

function parseCookies(req: Request): Record<string, string> {
  const header = req.headers.cookie;
  if (!header) return {};
  const result: Record<string, string> = {};
  for (const part of header.split(';')) {
    const idx = part.indexOf('=');
    if (idx === -1) continue;
    const key = part.slice(0, idx).trim();
    const val = part.slice(idx + 1).trim();
    if (key) {
      try {
        result[key] = decodeURIComponent(val);
      } catch {
        result[key] = val;
      }
    }
  }
  return result;
}

function setPartitionedCookie(res: Response, name: string, value: string, maxAgeMs: number) {
  const maxAgeSec = Math.max(0, Math.floor(maxAgeMs / 1000));
  const cookie = `${name}=${encodeURIComponent(
    value
  )}; Path=/; Max-Age=${maxAgeSec}; HttpOnly; Secure; SameSite=None; Partitioned`;
  res.append('Set-Cookie', cookie);
}

function clearPartitionedCookie(res: Response, name: string) {
  const cookie = `${name}=; Path=/; Max-Age=0; HttpOnly; Secure; SameSite=None; Partitioned`;
  res.append('Set-Cookie', cookie);
}

function toAuthUser(u: StoredUser): AuthUser {
  const needsProfileSetup = !u.name.trim() || !u.username.trim();
  return {
    id: u.id,
    email: u.email,
    name: u.name,
    username: u.username,
    role: u.role,
    needsProfileSetup,
  };
}

function getSessionUser(req: Request, store: AppStoreData): StoredUser | null {
  const authHeader = req.headers.authorization;
  let token: string | null = null;
  if (authHeader && authHeader.startsWith('Bearer ')) {
    token = authHeader.slice(7).trim();
  }
  if (!token) {
    const cookies = parseCookies(req);
    token = cookies[SESSION_COOKIE] || null;
  }
  if (!token) return null;

  const tokenHash = sha256Hex(token);
  const now = Date.now();
  const session = store.sessions.find((s) => s.tokenHash === tokenHash && s.expiresAt > now);
  if (!session) return null;

  return store.users.find((u) => u.id === session.userId) || null;
}

function getOrCreateVisitorId(req: Request, res: Response): string {
  const cookies = parseCookies(req);
  const existing = cookies[VISITOR_COOKIE];
  if (existing && /^[a-f0-9]{24,64}$/i.test(existing)) {
    return existing;
  }
  const fresh = crypto.randomBytes(16).toString('hex');
  setPartitionedCookie(res, VISITOR_COOKIE, fresh, 365 * 24 * 60 * 60 * 1000);
  return fresh;
}

function toPublicConfession(
  c: StoredConfession,
  store: AppStoreData,
  actorKey: string | null
): PublicConfession {
  const bannedUserIds = new Set(store.users.filter((u) => u.banned).map((u) => u.id));
  const commentCount = store.comments.filter(
    (cm) =>
      cm.confessionId === c.id &&
      !cm.hiddenByModeration &&
      !bannedUserIds.has(cm.userId)
  ).length;

  const viewerReactions: ReactionType[] = [];
  if (actorKey) {
    for (const rType of REACTION_TYPES) {
      if ((c.reactionActors[rType] || []).includes(actorKey)) {
        viewerReactions.push(rType);
      }
    }
  }

  // Strictly omit userId and any author metadata
  return {
    id: c.id,
    text: c.text,
    category: c.category,
    createdAt: c.createdAt,
    reactions: {
      heart: c.reactions.heart || 0,
      laugh: c.reactions.laugh || 0,
      wow: c.reactions.wow || 0,
    },
    viewerReactions,
    commentCount,
  };
}

function verifyMutationOriginOrHeader(req: Request, res: Response, next: NextFunction) {
  if (!['POST', 'PUT', 'PATCH', 'DELETE'].includes(req.method)) {
    return next();
  }
  const hasCustomHeader = req.headers['x-requested-with'] === 'XMLHttpRequest';
  const hasBearer = Boolean(req.headers.authorization?.startsWith('Bearer '));
  if (hasCustomHeader || hasBearer) {
    return next();
  }
  const origin = req.headers.origin;
  const host = (req.headers['x-forwarded-host'] as string) || req.headers.host;
  if (origin && host) {
    try {
      const originHost = new URL(origin).host;
      if (originHost === host) {
        return next();
      }
    } catch {
      // Invalid origin header
    }
  }
  return res.status(403).json({ error: 'Cross-site request blocked.' });
}

async function startServer() {
  const app = express();
  app.set('trust proxy', 1);
  app.use(express.json({ limit: '4mb' }));
  app.use('/api', verifyMutationOriginOrHeader);

  // Serve sanitized uploaded images with strict path confinement
  app.get('/api/uploads/:filename', (req, res) => {
    const filename = String(req.params.filename || '');
    if (!/^[a-f0-9-]+\.(jpg|png|webp)$/i.test(filename)) {
      return res.status(400).json({ error: 'Invalid file name.' });
    }
    const resolved = path.resolve(UPLOADS_DIR, filename);
    if (!resolved.startsWith(UPLOADS_DIR + path.sep) || !fs.existsSync(resolved)) {
      return res.status(404).json({ error: 'Image not found.' });
    }
    return res.sendFile(resolved);
  });

  // Upload and automatically strip all EXIF/XMP/IPTC/comment metadata
  app.post('/api/uploads', (req, res) => {
    const store = loadStore();
    const user = getSessionUser(req, store);
    if (!user || !user.username) {
      return res.status(401).json({ error: 'Sign in and complete your profile to upload photos.' });
    }

    try {
      const { dataUrl } = req.body as { dataUrl?: string };
      const sanitized = sanitizeBase64Image(dataUrl || '');
      const filename = `${crypto.randomUUID()}.${sanitized.ext}`;
      const destPath = path.resolve(UPLOADS_DIR, filename);
      if (!destPath.startsWith(UPLOADS_DIR + path.sep)) {
        return res.status(400).json({ error: 'Invalid upload destination.' });
      }
      fs.writeFileSync(destPath, sanitized.buffer);
      return res.status(201).json({ photoUrl: `/api/uploads/${filename}` });
    } catch (err) {
      return res.status(400).json({
        error: err instanceof Error ? err.message : 'Unable to process image.',
      });
    }
  });

  // Session check
  app.get('/api/auth/session', (req, res) => {
    const store = loadStore();
    const user = getSessionUser(req, store);
    const cooldownHours = getCooldownHours();
    const cooldown = evaluateCooldown(user?.lastConfessionAt, cooldownHours);
    return res.json({
      user: user ? toAuthUser(user) : null,
      cooldown,
      cooldownHours,
    });
  });

  // Built-in unlimited & free OTP generator for Sign Up & Password Reset
  app.post('/api/auth/request-code', (req, res) => {
    const body = (req.body || {}) as { email?: string; purpose?: 'signup' | 'reset' };
    const rawEmail = String(body.email || '');
    if (!isValidEmail(rawEmail)) {
      return res.status(400).json({ error: 'Please enter a valid email address.' });
    }
    const email = normalizeEmail(rawEmail);
    const purpose = body.purpose === 'reset' ? 'reset' : 'signup';
    const store = loadStore();
    const adminEmail = getAdminEmail();

    if (email === adminEmail) {
      const envPasscode = (process.env.ADMIN_PASSCODE || '').trim();
      const adminNeedsClaim = !envPasscode && !store.adminPasscodeHash;
      return res.json({
        email,
        delivery: 'email',
        isAdminAccount: true,
        adminNeedsClaim,
      });
    }

    const existingUser = store.users.find((u) => u.email === email);
    if (
      purpose === 'signup' &&
      existingUser &&
      existingUser.name &&
      existingUser.username &&
      existingUser.passwordHash
    ) {
      return res.status(409).json({
        error: 'An account with this email already exists. Please sign in with your email and password.',
      });
    }
    if (purpose === 'reset' && !existingUser) {
      return res.status(404).json({
        error: 'No account found with that email. Please sign up first.',
      });
    }

    const otp = String(crypto.randomInt(100000, 1000000));
    const magicToken = crypto.randomBytes(24).toString('hex');
    const now = Date.now();

    // Clean expired or previous challenges for this email (unlimited fresh OTP requests)
    store.otpChallenges = store.otpChallenges.filter(
      (c) => c.email !== email && c.expiresAt > now
    );
    store.otpChallenges.push({
      email,
      otpHash: sha256Hex(otp),
      magicTokenHash: sha256Hex(magicToken),
      attempts: 0,
      expiresAt: now + OTP_TTL_MS,
    });
    saveStore(store);

    return res.json({
      email,
      delivery: 'preview',
      previewOtp: otp,
      previewMagicToken: magicToken,
      isAdminAccount: false,
    });
  });

  // Email + Password Sign In (also handles admin passcode / first-run claim)
  app.post('/api/auth/login', (req, res) => {
    const body = (req.body || {}) as {
      email?: string;
      password?: string;
      claimPasscode?: string;
    };

    const email = normalizeEmail(String(body.email || ''));
    if (!isValidEmail(email)) {
      return res.status(400).json({ error: 'Please enter a valid email address.' });
    }

    const store = loadStore();
    const now = Date.now();
    const adminEmail = getAdminEmail();
    let user: StoredUser | undefined;

    if (email === adminEmail) {
      const envPasscode = (process.env.ADMIN_PASSCODE || '').trim();
      if (envPasscode) {
        const candidate = String(body.password || '');
        if (!candidate || !safeEqualText(candidate, envPasscode)) {
          return res.status(401).json({ error: 'Invalid email or password.' });
        }
      } else if (store.adminPasscodeHash) {
        const candidate = String(body.password || '');
        if (!candidate || !verifyPasscodeHash(candidate, store.adminPasscodeHash)) {
          return res.status(401).json({ error: 'Invalid email or password.' });
        }
      } else {
        const claim = String(body.claimPasscode || '');
        if (!claim) {
          return res.status(403).json({
            error:
              'First-time admin setup: choose a moderator passcode (min 6 characters) to unlock admin access.',
            adminNeedsClaim: true,
          });
        }
        if (claim.length < 6) {
          return res
            .status(400)
            .json({ error: 'Moderator passcode must be at least 6 characters.' });
        }
        store.adminPasscodeHash = hashPasscode(claim);
      }

      user = store.users.find((u) => u.email === adminEmail);
      if (!user) {
        user = {
          id: `usr_admin_${crypto.randomBytes(4).toString('hex')}`,
          email: adminEmail,
          name: 'Campus Admin',
          username: 'campus_mod',
          role: 'admin',
          banned: false,
          createdAt: now,
          lastConfessionAt: null,
        };
        store.users.unshift(user);
      } else {
        user.role = 'admin';
      }
    } else {
      const candidate = String(body.password || '');
      user = store.users.find((u) => u.email === email);
      if (!user) {
        return res.status(401).json({ error: 'Invalid email or password.' });
      }
      if (!user.passwordHash) {
        return res.status(403).json({
          error: 'No password set for this account yet. Use "Forgot / Set password via OTP" below.',
        });
      }
      if (!candidate || !verifyPasscodeHash(candidate, user.passwordHash)) {
        return res.status(401).json({ error: 'Invalid email or password.' });
      }
    }

    const rawSessionToken = crypto.randomBytes(32).toString('hex');
    store.sessions = store.sessions.filter((s) => s.expiresAt > now);
    store.sessions.push({
      tokenHash: sha256Hex(rawSessionToken),
      userId: user.id,
      createdAt: now,
      expiresAt: now + SESSION_TTL_MS,
    });
    saveStore(store);

    setPartitionedCookie(res, SESSION_COOKIE, rawSessionToken, SESSION_TTL_MS);
    return res.json({
      user: toAuthUser(user),
      sessionToken: rawSessionToken,
    });
  });

  // Verify OTP / Magic Link or Admin Passcode / First-Run Claim
  app.post('/api/auth/verify', (req, res) => {
    const body = (req.body || {}) as {
      email?: string;
      code?: string;
      magicToken?: string;
      adminPasscode?: string;
      claimPasscode?: string;
    };

    const email = normalizeEmail(String(body.email || ''));
    if (!isValidEmail(email)) {
      return res.status(400).json({ error: 'Valid email is required.' });
    }

    const store = loadStore();
    const now = Date.now();
    const adminEmail = getAdminEmail();
    let user: StoredUser | undefined;

    if (email === adminEmail) {
      const envPasscode = (process.env.ADMIN_PASSCODE || '').trim();
      if (envPasscode) {
        const candidate = String(body.adminPasscode || '');
        if (!candidate || !safeEqualText(candidate, envPasscode)) {
          return res.status(401).json({ error: 'Invalid moderator passcode.' });
        }
      } else if (store.adminPasscodeHash) {
        const candidate = String(body.adminPasscode || '');
        if (!candidate || !verifyPasscodeHash(candidate, store.adminPasscodeHash)) {
          return res.status(401).json({ error: 'Invalid moderator passcode.' });
        }
      } else {
        const claim = String(body.claimPasscode || '');
        if (claim.length < 6) {
          return res
            .status(400)
            .json({ error: 'Moderator passcode must be at least 6 characters.' });
        }
        store.adminPasscodeHash = hashPasscode(claim);
      }

      user = store.users.find((u) => u.email === adminEmail);
      if (!user) {
        user = {
          id: `usr_admin_${crypto.randomBytes(4).toString('hex')}`,
          email: adminEmail,
          name: 'Campus Admin',
          username: 'campus_mod',
          role: 'admin',
          banned: false,
          createdAt: now,
          lastConfessionAt: null,
        };
        store.users.unshift(user);
      } else {
        user.role = 'admin';
      }
    } else {
      const challenge = store.otpChallenges.find(
        (c) => c.email === email && c.expiresAt > now
      );
      if (!challenge) {
        return res
          .status(401)
          .json({ error: 'Verification code expired. Please request a new one.' });
      }
      if (challenge.attempts >= 5) {
        return res
          .status(429)
          .json({ error: 'Too many invalid attempts. Request a new code.' });
      }

      const code = String(body.code || '').trim();
      const magicToken = String(body.magicToken || '').trim();
      const codeMatches = code && safeEqualText(sha256Hex(code), challenge.otpHash);
      const magicMatches =
        magicToken && safeEqualText(sha256Hex(magicToken), challenge.magicTokenHash);

      if (!codeMatches && !magicMatches) {
        challenge.attempts += 1;
        saveStore(store);
        return res.status(401).json({ error: 'Invalid verification code.' });
      }

      store.otpChallenges = store.otpChallenges.filter((c) => c.email !== email);
      user = store.users.find((u) => u.email === email);
      if (!user) {
        user = {
          id: `usr_${crypto.randomBytes(6).toString('hex')}`,
          email,
          name: '',
          username: '',
          role: 'student',
          banned: false,
          createdAt: now,
          lastConfessionAt: null,
        };
        store.users.push(user);
      }
    }

    // Create session
    const rawSessionToken = crypto.randomBytes(32).toString('hex');
    store.sessions = store.sessions.filter((s) => s.expiresAt > now);
    store.sessions.push({
      tokenHash: sha256Hex(rawSessionToken),
      userId: user.id,
      createdAt: now,
      expiresAt: now + SESSION_TTL_MS,
    });
    saveStore(store);

    setPartitionedCookie(res, SESSION_COOKIE, rawSessionToken, SESSION_TTL_MS);
    return res.json({
      user: toAuthUser(user),
      sessionToken: rawSessionToken,
    });
  });

  // Profile & password setup after email OTP verification
  app.post('/api/auth/profile', (req, res) => {
    const store = loadStore();
    const user = getSessionUser(req, store);
    if (!user) {
      return res.status(401).json({ error: 'Please verify your email first.' });
    }

    const body = (req.body || {}) as { name?: string; username?: string; password?: string };
    const name = String(body.name || '').trim();
    const username = String(body.username || '').trim();
    const password = typeof body.password === 'string' ? body.password : '';

    if (!isValidDisplayName(name)) {
      return res.status(400).json({ error: 'Name must be between 2 and 40 characters.' });
    }
    if (!isValidUsername(username)) {
      return res.status(400).json({
        error: 'Username must be 3–20 characters using letters, numbers, or underscores.',
      });
    }

    if (user.role !== 'admin' && (!user.passwordHash || password.length > 0)) {
      if (!isValidPassword(password)) {
        return res.status(400).json({
          error: `Password must be at least ${MIN_PASSWORD_LENGTH} characters.`,
        });
      }
      user.passwordHash = hashPasscode(password);
    }

    const taken = store.users.some(
      (u) => u.id !== user.id && u.username.toLowerCase() === username.toLowerCase()
    );
    if (taken) {
      return res.status(409).json({ error: 'That username is already taken.' });
    }

    user.name = name;
    user.username = username;
    saveStore(store);

    return res.json({ user: toAuthUser(user) });
  });

  // Set or reset password after OTP verification
  app.post('/api/auth/reset-password', (req, res) => {
    const store = loadStore();
    const user = getSessionUser(req, store);
    if (!user) {
      return res.status(401).json({ error: 'Please verify your email with OTP first.' });
    }
    if (user.role === 'admin') {
      return res.status(403).json({ error: 'Admin passcode cannot be changed here.' });
    }

    const password = String((req.body as { password?: string })?.password || '');
    if (!isValidPassword(password)) {
      return res.status(400).json({
        error: `Password must be at least ${MIN_PASSWORD_LENGTH} characters.`,
      });
    }

    user.passwordHash = hashPasscode(password);
    saveStore(store);
    return res.json({ user: toAuthUser(user) });
  });

  app.post('/api/auth/logout', (req, res) => {
    const store = loadStore();
    const authHeader = req.headers.authorization;
    const cookies = parseCookies(req);
    const token =
      (authHeader?.startsWith('Bearer ') ? authHeader.slice(7).trim() : null) ||
      cookies[SESSION_COOKIE];

    if (token) {
      const hash = sha256Hex(token);
      store.sessions = store.sessions.filter((s) => s.tokenHash !== hash);
      saveStore(store);
    }
    clearPartitionedCookie(res, SESSION_COOKIE);
    return res.json({ ok: true });
  });

  // Public Confessions Feed (no login required, strictly zero author details)
  app.get('/api/confessions', (req, res) => {
    const store = loadStore();
    const user = getSessionUser(req, store);
    const cookies = parseCookies(req);
    const vid = cookies[VISITOR_COOKIE] || null;
    const actorKey = user ? `u:${user.id}` : vid ? `v:${vid}` : null;

    const category = String(req.query.category || 'all');
    const timeframe = String(req.query.timeframe || 'all') as ConfessionTimeFilter;
    const offset = Math.max(0, Number(req.query.offset) || 0);
    const limit = Math.min(30, Math.max(1, Number(req.query.limit) || 6));

    const bannedIds = new Set(store.users.filter((u) => u.banned).map((u) => u.id));
    const now = Date.now();
    const oneDayMs = 24 * 60 * 60 * 1000;
    const oneWeekMs = 7 * oneDayMs;

    let list = store.confessions.filter(
      (c) => c.status === 'approved' && !bannedIds.has(c.userId)
    );

    if (category !== 'all') {
      list = list.filter((c) => c.category === category);
    }
    if (timeframe === 'today') {
      list = list.filter((c) => now - c.createdAt <= oneDayMs);
    } else if (timeframe === 'this week') {
      list = list.filter((c) => now - c.createdAt <= oneWeekMs);
    }

    if (timeframe === 'most reacted') {
      list.sort((a, b) => {
        const totalA =
          (a.reactions.heart || 0) + (a.reactions.laugh || 0) + (a.reactions.wow || 0);
        const totalB =
          (b.reactions.heart || 0) + (b.reactions.laugh || 0) + (b.reactions.wow || 0);
        return totalB - totalA || b.createdAt - a.createdAt;
      });
    } else {
      list.sort((a, b) => b.createdAt - a.createdAt);
    }

    const slice = list.slice(offset, offset + limit);
    const nextOffset = offset + slice.length;
    const hasMore = nextOffset < list.length;

    return res.json({
      items: slice.map((c) => toPublicConfession(c, store, actorKey)),
      nextOffset,
      hasMore,
    });
  });

  // Submit Confession (logged-in user, text-only, cooldown rate-limited)
  app.post('/api/confessions', (req, res) => {
    const store = loadStore();
    const user = getSessionUser(req, store);
    if (!user || !user.username) {
      return res.status(401).json({ error: 'Sign in and complete your profile to confess.' });
    }

    const cooldownHours = getCooldownHours();
    const cooldown = evaluateCooldown(user.lastConfessionAt, cooldownHours);
    if (!cooldown.allowed) {
      return res.status(429).json({
        error: 'Rate limit active. Please wait before submitting another confession.',
      });
    }

    const body = (req.body || {}) as { text?: string; category?: string | null };
    const text = String(body.text || '').trim();
    if (text.length < MIN_CONFESSION_LENGTH || text.length > MAX_CONFESSION_LENGTH) {
      return res.status(400).json({
        error: `Confession must be between ${MIN_CONFESSION_LENGTH} and ${MAX_CONFESSION_LENGTH} characters.`,
      });
    }

    let category: ConfessionCategory | null = null;
    if (body.category && CONFESSION_CATEGORIES.includes(body.category as ConfessionCategory)) {
      category = body.category as ConfessionCategory;
    }

    const now = Date.now();
    const confession: StoredConfession = {
      id: `conf_${crypto.randomBytes(6).toString('hex')}`,
      userId: user.id,
      text,
      category,
      status: 'pending',
      createdAt: now,
      reactions: { heart: 0, laugh: 0, wow: 0 },
      reactionActors: { heart: [], laugh: [], wow: [] },
    };

    store.confessions.unshift(confession);
    user.lastConfessionAt = now;
    saveStore(store);

    appendInternalAuditLog({
      targetType: 'confession',
      targetId: confession.id,
      userId: user.id,
      action: 'submitted',
    });

    const nextCooldown = evaluateCooldown(user.lastConfessionAt, cooldownHours, now);
    return res.status(201).json({
      item: {
        id: confession.id,
        text: confession.text,
        category: confession.category,
        status: confession.status,
        rejectReason: null,
        createdAt: confession.createdAt,
      },
      cooldown: nextCooldown,
    });
  });

  // React to Confession (anonymous visitor or registered user)
  app.post('/api/confessions/:id/react', (req, res) => {
    const store = loadStore();
    const user = getSessionUser(req, store);
    const vid = getOrCreateVisitorId(req, res);
    const actorKey = user ? `u:${user.id}` : `v:${vid}`;

    const reaction = String((req.body as { reaction?: string })?.reaction || '') as ReactionType;
    if (!REACTION_TYPES.includes(reaction)) {
      return res.status(400).json({ error: 'Invalid reaction type.' });
    }

    const confession = store.confessions.find(
      (c) => c.id === req.params.id && c.status === 'approved'
    );
    if (!confession) {
      return res.status(404).json({ error: 'Confession not found.' });
    }

    const actors = confession.reactionActors[reaction] || [];
    const idx = actors.indexOf(actorKey);
    if (idx === -1) {
      actors.push(actorKey);
      confession.reactions[reaction] = (confession.reactions[reaction] || 0) + 1;
    } else {
      actors.splice(idx, 1);
      confession.reactions[reaction] = Math.max(0, (confession.reactions[reaction] || 0) - 1);
    }
    confession.reactionActors[reaction] = actors;
    saveStore(store);

    return res.json({ confession: toPublicConfession(confession, store, actorKey) });
  });

  // Confession Comments (public read, login required to post, shows public username only)
  app.get('/api/confessions/:id/comments', (req, res) => {
    const store = loadStore();
    const confession = store.confessions.find(
      (c) => c.id === req.params.id && c.status === 'approved'
    );
    if (!confession) {
      return res.status(404).json({ error: 'Confession not found.' });
    }

    const bannedIds = new Set(store.users.filter((u) => u.banned).map((u) => u.id));
    const comments: PublicComment[] = store.comments
      .filter(
        (cm) =>
          cm.confessionId === confession.id &&
          !cm.hiddenByModeration &&
          !bannedIds.has(cm.userId)
      )
      .sort((a, b) => a.createdAt - b.createdAt)
      .map((cm) => ({
        id: cm.id,
        confessionId: cm.confessionId,
        username: cm.usernameSnapshot,
        text: cm.text,
        createdAt: cm.createdAt,
      }));

    return res.json({ comments });
  });

  app.post('/api/confessions/:id/comments', (req, res) => {
    const store = loadStore();
    const user = getSessionUser(req, store);
    if (!user || !user.username) {
      return res.status(401).json({ error: 'Sign in and complete your profile to comment.' });
    }

    const confession = store.confessions.find(
      (c) => c.id === req.params.id && c.status === 'approved'
    );
    if (!confession) {
      return res.status(404).json({ error: 'Confession not found.' });
    }

    const text = String((req.body as { text?: string })?.text || '').trim();
    if (text.length < 2 || text.length > MAX_COMMENT_LENGTH) {
      return res.status(400).json({
        error: `Comment must be between 2 and ${MAX_COMMENT_LENGTH} characters.`,
      });
    }

    const comment = {
      id: `cmt_${crypto.randomBytes(6).toString('hex')}`,
      confessionId: confession.id,
      userId: user.id,
      usernameSnapshot: user.username,
      text,
      createdAt: Date.now(),
      // Silently hide comments from banned accounts without alerting the user
      hiddenByModeration: user.banned,
    };

    store.comments.push(comment);
    saveStore(store);

    appendInternalAuditLog({
      targetType: 'comment',
      targetId: comment.id,
      userId: user.id,
      action: 'commented',
    });

    return res.status(201).json({
      comment: {
        id: comment.id,
        confessionId: comment.confessionId,
        username: comment.usernameSnapshot,
        text: comment.text,
        createdAt: comment.createdAt,
      },
    });
  });

  // Public Lost & Found Board (browsable without login, no email/phone/name exposed)
  app.get('/api/lost-found', (req, res) => {
    const store = loadStore();
    const viewer = getSessionUser(req, store);
    const bannedIds = new Set(store.users.filter((u) => u.banned).map((u) => u.id));

    const typeFilter = String(req.query.type || 'all');
    const categoryFilter = String(req.query.category || 'all');
    const q = String(req.query.q || '').trim().toLowerCase();

    let items = store.lostFoundItems.filter(
      (item) => item.status === 'approved' && !bannedIds.has(item.userId)
    );

    if (typeFilter === 'lost' || typeFilter === 'found') {
      items = items.filter((item) => item.type === typeFilter);
    }
    if (categoryFilter !== 'all') {
      items = items.filter((item) => item.category === categoryFilter);
    }
    if (q) {
      items = items.filter(
        (item) =>
          item.title.toLowerCase().includes(q) ||
          item.description.toLowerCase().includes(q) ||
          item.location.toLowerCase().includes(q)
      );
    }

    items.sort((a, b) => b.createdAt - a.createdAt);

    const publicItems: PublicLostFoundItem[] = items.map((item) => ({
      id: item.id,
      title: item.title,
      description: item.description,
      photoUrl: item.photoUrl,
      type: item.type,
      location: item.location,
      category: item.category,
      createdAt: item.createdAt,
      isOwn: Boolean(viewer && viewer.id === item.userId),
    }));

    return res.json({ items: publicItems });
  });

  // Submit Lost & Found Item
  app.post('/api/lost-found', (req, res) => {
    const store = loadStore();
    const user = getSessionUser(req, store);
    if (!user || !user.username) {
      return res.status(401).json({ error: 'Sign in and complete your profile to post an item.' });
    }

    const body = (req.body || {}) as {
      title?: string;
      description?: string;
      type?: string;
      location?: string;
      category?: string;
      photoUrl?: string;
    };

    const title = String(body.title || '').trim();
    const description = String(body.description || '').trim();
    const type: 'lost' | 'found' | null =
      body.type === 'found' ? 'found' : body.type === 'lost' ? 'lost' : null;
    const location = String(body.location || '').trim();
    const category = LOST_FOUND_CATEGORIES.includes(body.category as LostFoundCategory)
      ? (body.category as LostFoundCategory)
      : 'Other';

    if (title.length < 3 || title.length > 80) {
      return res.status(400).json({ error: 'Item title must be 3–80 characters.' });
    }
    if (description.length < 8 || description.length > 500) {
      return res.status(400).json({ error: 'Description must be 8–500 characters.' });
    }
    if (!type) {
      return res.status(400).json({ error: 'Type must be lost or found.' });
    }
    if (location.length < 2 || location.length > 80) {
      return res.status(400).json({ error: 'Location must be 2–80 characters.' });
    }

    let safePhotoUrl: string | undefined;
    if (body.photoUrl) {
      const candidate = String(body.photoUrl).trim();
      if (!/^\/api\/uploads\/[a-f0-9-]+\.(jpg|png|webp)$/i.test(candidate)) {
        return res.status(400).json({ error: 'Invalid photo reference.' });
      }
      safePhotoUrl = candidate;
    }

    const item = {
      id: `lf_${crypto.randomBytes(6).toString('hex')}`,
      userId: user.id,
      title,
      description,
      photoUrl: safePhotoUrl,
      type,
      location,
      category,
      status: 'pending' as const,
      createdAt: Date.now(),
    };

    store.lostFoundItems.unshift(item);
    saveStore(store);

    appendInternalAuditLog({
      targetType: 'lost_found',
      targetId: item.id,
      userId: user.id,
      action: 'submitted',
    });

    return res.status(201).json({
      item: {
        id: item.id,
        title: item.title,
        description: item.description,
        photoUrl: item.photoUrl,
        type: item.type,
        location: item.location,
        category: item.category,
        status: item.status,
        rejectReason: null,
        createdAt: item.createdAt,
      },
    });
  });

  // In-app Lost & Found Messaging (never exposes email/phone/real name)
  app.post('/api/lost-found/:id/messages', (req, res) => {
    const store = loadStore();
    const user = getSessionUser(req, store);
    if (!user || !user.username) {
      return res.status(401).json({ error: 'Sign in and complete your profile to message.' });
    }

    const item = store.lostFoundItems.find(
      (i) => i.id === req.params.id && i.status === 'approved'
    );
    if (!item) {
      return res.status(404).json({ error: 'Lost & Found item not found.' });
    }

    const body = (req.body || {}) as { threadId?: string; text?: string };
    const text = String(body.text || '').trim();
    if (text.length < 2 || text.length > MAX_MESSAGE_LENGTH) {
      return res.status(400).json({
        error: `Message must be between 2 and ${MAX_MESSAGE_LENGTH} characters.`,
      });
    }

    let thread = body.threadId
      ? store.messageThreads.find((t) => t.id === body.threadId)
      : store.messageThreads.find(
          (t) => t.itemId === item.id && t.initiatorUserId === user.id
        );

    if (thread) {
      if (thread.initiatorUserId !== user.id && thread.ownerUserId !== user.id) {
        return res.status(403).json({ error: 'Not authorized for this conversation.' });
      }
    } else {
      if (item.userId === user.id) {
        return res.status(400).json({ error: 'You cannot start a thread on your own item.' });
      }
      thread = {
        id: `thr_${crypto.randomBytes(6).toString('hex')}`,
        itemId: item.id,
        initiatorUserId: user.id,
        ownerUserId: item.userId,
        createdAt: Date.now(),
      };
      store.messageThreads.push(thread);
    }

    const message = {
      id: `msg_${crypto.randomBytes(6).toString('hex')}`,
      threadId: thread.id,
      senderUserId: user.id,
      senderUsername: user.username,
      text,
      createdAt: Date.now(),
    };

    store.itemMessages.push(message);
    saveStore(store);

    const threadMessages = store.itemMessages
      .filter((m) => m.threadId === thread!.id)
      .sort((a, b) => a.createdAt - b.createdAt);

    const otherUserId =
      thread.initiatorUserId === user.id ? thread.ownerUserId : thread.initiatorUserId;
    const otherUser = store.users.find((u) => u.id === otherUserId);

    const formatted: ItemMessageThread = {
      id: thread.id,
      itemId: item.id,
      itemTitle: item.title,
      itemType: item.type,
      counterpartyLabel: otherUser?.username ? `@${otherUser.username}` : 'Campus user',
      messages: toMessageEntries(threadMessages, user.id),
    };

    return res.status(201).json({ thread: formatted });
  });

  // User Activity Endpoints
  app.get('/api/my/confessions', (req, res) => {
    const store = loadStore();
    const user = getSessionUser(req, store);
    if (!user) return res.status(401).json({ error: 'Unauthorized.' });

    const items = store.confessions
      .filter((c) => c.userId === user.id)
      .sort((a, b) => b.createdAt - a.createdAt)
      .map((c) => ({
        id: c.id,
        text: c.text,
        category: c.category,
        status: c.status,
        rejectReason: c.rejectReason || null,
        createdAt: c.createdAt,
      }));
    return res.json({ items });
  });

  app.get('/api/my/lost-found', (req, res) => {
    const store = loadStore();
    const user = getSessionUser(req, store);
    if (!user) return res.status(401).json({ error: 'Unauthorized.' });

    const items = store.lostFoundItems
      .filter((i) => i.userId === user.id)
      .sort((a, b) => b.createdAt - a.createdAt)
      .map((i) => ({
        id: i.id,
        title: i.title,
        description: i.description,
        photoUrl: i.photoUrl,
        type: i.type,
        location: i.location,
        category: i.category,
        status: i.status,
        rejectReason: i.rejectReason || null,
        createdAt: i.createdAt,
      }));
    return res.json({ items });
  });

  app.get('/api/my/messages', (req, res) => {
    const store = loadStore();
    const user = getSessionUser(req, store);
    if (!user) return res.status(401).json({ error: 'Unauthorized.' });

    const myThreads = store.messageThreads
      .filter((t) => t.initiatorUserId === user.id || t.ownerUserId === user.id)
      .map((t) => {
        const item = store.lostFoundItems.find((i) => i.id === t.itemId);
        const otherUserId = t.initiatorUserId === user.id ? t.ownerUserId : t.initiatorUserId;
        const otherUser = store.users.find((u) => u.id === otherUserId);
        const msgs = store.itemMessages
          .filter((m) => m.threadId === t.id)
          .sort((a, b) => a.createdAt - b.createdAt);

        return {
          id: t.id,
          itemId: t.itemId,
          itemTitle: item?.title || 'Lost & Found item',
          itemType: item?.type || 'lost',
          counterpartyLabel: otherUser?.username ? `@${otherUser.username}` : 'Campus user',
          messages: toMessageEntries(msgs, user.id),
        } satisfies ItemMessageThread;
      });

    return res.json({ threads: myThreads });
  });

  // Public Reports Submission
  app.post('/api/reports', (req, res) => {
    const store = loadStore();
    const user = getSessionUser(req, store);
    const vid = getOrCreateVisitorId(req, res);

    const body = (req.body || {}) as {
      targetType?: string;
      targetId?: string;
      reason?: string;
      details?: string;
    };

    const targetType =
      body.targetType === 'confession' || body.targetType === 'lost_found'
        ? body.targetType
        : null;
    const targetId = String(body.targetId || '').trim();
    const reason = String(body.reason || '').trim().slice(0, 100);
    const details = String(body.details || '').trim().slice(0, 300);

    if (!targetType || !targetId || !reason) {
      return res.status(400).json({ error: 'Target and reason are required.' });
    }

    const exists =
      targetType === 'confession'
        ? store.confessions.some((c) => c.id === targetId)
        : store.lostFoundItems.some((i) => i.id === targetId);
    if (!exists) {
      return res.status(404).json({ error: 'Reported post not found.' });
    }

    store.reports.unshift({
      id: `rep_${crypto.randomBytes(6).toString('hex')}`,
      targetType,
      targetId,
      reporterKey: user ? `u:${user.id}` : `v:${vid}`,
      reason,
      details: details || undefined,
      status: 'open',
      createdAt: Date.now(),
    });
    saveStore(store);

    return res.status(201).json({ ok: true });
  });

  // Admin Middleware
  function requireAdmin(req: Request, res: Response): { store: AppStoreData; admin: StoredUser } | null {
    const store = loadStore();
    const user = getSessionUser(req, store);
    if (!user || user.role !== 'admin') {
      res.status(403).json({ error: 'Admin access required.' });
      return null;
    }
    return { store, admin: user };
  }

  app.get('/api/admin/queues', (req, res) => {
    const ctx = requireAdmin(req, res);
    if (!ctx) return;
    const { store } = ctx;

    const bannedIds = new Set(store.users.filter((u) => u.banned).map((u) => u.id));

    const confessionsQueue: AdminQueueConfession[] = store.confessions
      .filter((c) => c.status === 'pending')
      .sort((a, b) => a.createdAt - b.createdAt)
      .map((c) => ({
        id: c.id,
        text: c.text,
        category: c.category,
        createdAt: c.createdAt,
        authorBanned: bannedIds.has(c.userId),
      }));

    const lostFoundQueue: AdminQueueLostFound[] = store.lostFoundItems
      .filter((i) => i.status === 'pending')
      .sort((a, b) => a.createdAt - b.createdAt)
      .map((i) => ({
        id: i.id,
        title: i.title,
        description: i.description,
        photoUrl: i.photoUrl,
        type: i.type,
        location: i.location,
        category: i.category,
        createdAt: i.createdAt,
        authorBanned: bannedIds.has(i.userId),
      }));

    return res.json({ confessionsQueue, lostFoundQueue });
  });

  app.get('/api/admin/reports', (req, res) => {
    const ctx = requireAdmin(req, res);
    if (!ctx) return;
    const { store } = ctx;

    const reports: AdminReportItem[] = store.reports
      .slice()
      .sort((a, b) => b.createdAt - a.createdAt)
      .map((r) => {
        let targetSnippet = '[Removed content]';
        if (r.targetType === 'confession') {
          const c = store.confessions.find((item) => item.id === r.targetId);
          if (c) targetSnippet = c.text.slice(0, 140);
        } else {
          const lf = store.lostFoundItems.find((item) => item.id === r.targetId);
          if (lf) targetSnippet = `${lf.title} — ${lf.description.slice(0, 90)}`;
        }
        return {
          id: r.id,
          targetType: r.targetType,
          targetId: r.targetId,
          targetSnippet,
          reason: r.reason,
          details: r.details,
          status: r.status,
          createdAt: r.createdAt,
        };
      });

    return res.json({ reports });
  });

  app.get('/api/admin/accounts', (req, res) => {
    const ctx = requireAdmin(req, res);
    if (!ctx) return;
    const { store } = ctx;

    const accounts: AdminAccountView[] = store.users
      .filter((u) => u.role !== 'admin')
      .sort((a, b) => b.createdAt - a.createdAt)
      .map((u) => ({
        id: u.id,
        username: u.username,
        banned: u.banned,
        createdAt: u.createdAt,
        confessionCount: store.confessions.filter((c) => c.userId === u.id).length,
        lostFoundCount: store.lostFoundItems.filter((i) => i.userId === u.id).length,
      }));

    return res.json({ accounts });
  });

  app.post('/api/admin/confessions/:id/moderate', (req, res) => {
    const ctx = requireAdmin(req, res);
    if (!ctx) return;
    const { store, admin } = ctx;

    const confession = store.confessions.find((c) => c.id === req.params.id);
    if (!confession) return res.status(404).json({ error: 'Confession not found.' });

    const body = (req.body || {}) as { action?: string; rejectReason?: RejectReason };
    if (body.action === 'approve') {
      const author = store.users.find((u) => u.id === confession.userId);
      if (author?.banned) {
        return res
          .status(400)
          .json({ error: 'Cannot approve submission from a silently banned account.' });
      }
      confession.status = 'approved';
      confession.rejectReason = null;
    } else if (body.action === 'reject') {
      const validReason = REJECT_REASONS.some((r) => r.value === body.rejectReason)
        ? body.rejectReason
        : 'inappropriate';
      confession.status = 'rejected';
      confession.rejectReason = validReason;
    } else {
      return res.status(400).json({ error: 'Invalid moderation action.' });
    }

    saveStore(store);
    appendInternalAuditLog({
      targetType: 'moderation',
      targetId: confession.id,
      userId: admin.id,
      action: `confession_${body.action}`,
    });

    return res.json({ ok: true });
  });

  app.post('/api/admin/lost-found/:id/moderate', (req, res) => {
    const ctx = requireAdmin(req, res);
    if (!ctx) return;
    const { store, admin } = ctx;

    const item = store.lostFoundItems.find((i) => i.id === req.params.id);
    if (!item) return res.status(404).json({ error: 'Item not found.' });

    const body = (req.body || {}) as { action?: string; rejectReason?: RejectReason };
    if (body.action === 'approve') {
      const author = store.users.find((u) => u.id === item.userId);
      if (author?.banned) {
        return res
          .status(400)
          .json({ error: 'Cannot approve submission from a silently banned account.' });
      }
      item.status = 'approved';
      item.rejectReason = null;
    } else if (body.action === 'reject') {
      const validReason = REJECT_REASONS.some((r) => r.value === body.rejectReason)
        ? body.rejectReason
        : 'inappropriate';
      item.status = 'rejected';
      item.rejectReason = validReason;
    } else {
      return res.status(400).json({ error: 'Invalid moderation action.' });
    }

    saveStore(store);
    appendInternalAuditLog({
      targetType: 'moderation',
      targetId: item.id,
      userId: admin.id,
      action: `lost_found_${body.action}`,
    });

    return res.json({ ok: true });
  });

  app.post('/api/admin/confessions/:id/ban-author', (req, res) => {
    const ctx = requireAdmin(req, res);
    if (!ctx) return;
    const { store, admin } = ctx;

    const confession = store.confessions.find((c) => c.id === req.params.id);
    if (!confession) return res.status(404).json({ error: 'Confession not found.' });

    const author = store.users.find((u) => u.id === confession.userId);
    if (author && author.role !== 'admin') {
      author.banned = true;
    }
    confession.status = 'rejected';
    confession.rejectReason = 'inappropriate';
    saveStore(store);

    appendInternalAuditLog({
      targetType: 'moderation',
      targetId: confession.id,
      userId: admin.id,
      action: `silent_ban_user:${confession.userId}`,
    });

    return res.json({ ok: true });
  });

  app.post('/api/admin/lost-found/:id/ban-author', (req, res) => {
    const ctx = requireAdmin(req, res);
    if (!ctx) return;
    const { store, admin } = ctx;

    const item = store.lostFoundItems.find((i) => i.id === req.params.id);
    if (!item) return res.status(404).json({ error: 'Item not found.' });

    const author = store.users.find((u) => u.id === item.userId);
    if (author && author.role !== 'admin') {
      author.banned = true;
    }
    item.status = 'rejected';
    item.rejectReason = 'inappropriate';
    saveStore(store);

    appendInternalAuditLog({
      targetType: 'moderation',
      targetId: item.id,
      userId: admin.id,
      action: `silent_ban_user:${item.userId}`,
    });

    return res.json({ ok: true });
  });

  app.post('/api/admin/reports/:id/resolve', (req, res) => {
    const ctx = requireAdmin(req, res);
    if (!ctx) return;
    const { store, admin } = ctx;

    const report = store.reports.find((r) => r.id === req.params.id);
    if (!report) return res.status(404).json({ error: 'Report not found.' });

    const action = (req.body as { action?: string })?.action;
    if (action !== 'dismiss' && action !== 'remove_post' && action !== 'ban_author') {
      return res.status(400).json({ error: 'Invalid report resolution action.' });
    }

    if (action === 'remove_post' || action === 'ban_author') {
      if (report.targetType === 'confession') {
        const c = store.confessions.find((item) => item.id === report.targetId);
        if (c) {
          c.status = 'rejected';
          c.rejectReason = 'inappropriate';
          if (action === 'ban_author') {
            const author = store.users.find((u) => u.id === c.userId);
            if (author && author.role !== 'admin') author.banned = true;
          }
        }
      } else {
        const lf = store.lostFoundItems.find((item) => item.id === report.targetId);
        if (lf) {
          lf.status = 'rejected';
          lf.rejectReason = 'inappropriate';
          if (action === 'ban_author') {
            const author = store.users.find((u) => u.id === lf.userId);
            if (author && author.role !== 'admin') author.banned = true;
          }
        }
      }
    }

    report.status = 'resolved';
    saveStore(store);

    appendInternalAuditLog({
      targetType: 'moderation',
      targetId: report.id,
      userId: admin.id,
      action: `report_${action}`,
    });

    return res.json({ ok: true });
  });

  app.post('/api/admin/accounts/:id/ban', (req, res) => {
    const ctx = requireAdmin(req, res);
    if (!ctx) return;
    const { store, admin } = ctx;

    const target = store.users.find((u) => u.id === req.params.id && u.role !== 'admin');
    if (!target) return res.status(404).json({ error: 'Account not found.' });

    const banned = Boolean((req.body as { banned?: boolean })?.banned);
    target.banned = banned;
    saveStore(store);

    appendInternalAuditLog({
      targetType: 'moderation',
      targetId: target.id,
      userId: admin.id,
      action: banned ? 'silent_ban' : 'unban',
    });

    return res.json({ ok: true });
  });

  // Vite dev middleware or static dist in production
  if (process.env.NODE_ENV !== 'production') {
    const vite = await createViteServer({
      server: { middlewareMode: true },
      appType: 'spa',
    });
    app.use(vite.middlewares);
  } else {
    const distPath = path.resolve(process.cwd(), 'dist');
    app.use(express.static(distPath));
    app.get('*', (_req, res) => {
      res.sendFile(path.resolve(distPath, 'index.html'));
    });
  }

  app.listen(PORT, '0.0.0.0', () => {
    console.log(`Sigma Community server listening on http://0.0.0.0:${PORT}`);
  });
}

startServer().catch((err) => {
  console.error('Failed to start server:', err);
  process.exit(1);
});
