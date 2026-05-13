const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');
const fs = require('fs');
const crypto = require('crypto');

const compression = require('compression');

const app = express();
const server = http.createServer(app);
const io = new Server(server);

app.use(compression());
app.use(express.static(path.join(__dirname, 'public')));
app.use(express.json());

// Beacon save — called by navigator.sendBeacon on page close, guaranteed delivery
app.post('/save', (req, res) => {
  const { username, cookies, owned } = req.body || {};
  if (username && accounts[username]) {
    const incoming = Math.max(0, Math.floor(Number(cookies) || 0));
    // Use max so a stale beacon can never overwrite a higher value saved by disconnect handler
    accounts[username].cookies = Math.max(accounts[username].cookies || 0, incoming);
    if (owned) accounts[username].owned = owned;
    saveAccounts(true); // immediate — beacon fires on page close
  }
  res.sendStatus(200);
});

// ---- Reports API (token-gated) ----
app.get('/api/reports', (req, res) => {
  const tok = req.query.token;
  if (!tok || !reportTokens[tok] || Date.now() > reportTokens[tok]) return res.status(401).json({ error: 'Unauthorized' });
  res.json([...reports].reverse()); // newest first
});

app.delete('/api/reports/:id', (req, res) => {
  const tok = req.query.token;
  if (!tok || !reportTokens[tok] || Date.now() > reportTokens[tok]) return res.status(401).json({ error: 'Unauthorized' });
  const id = Number(req.params.id);
  const idx = reports.findIndex(r => r.id === id);
  if (idx === -1) return res.status(404).json({ error: 'Not found' });
  reports.splice(idx, 1);
  saveReports();
  res.json({ ok: true });
});

// Join log — all players who have ever joined, never wiped
app.get('/api/joinlog', (req, res) => {
  const tok = req.query.token;
  if (!tok || !reportTokens[tok] || Date.now() > reportTokens[tok]) return res.status(401).json({ error: 'Unauthorized' });
  const entries = Object.entries(joinLog).map(([name, d]) => ({ name, ...d }))
    .sort((a, b) => b.lastSeen - a.lastSeen);
  res.json(entries);
});

app.patch('/api/reports/:id/read', (req, res) => {
  const tok = req.query.token;
  if (!tok || !reportTokens[tok] || Date.now() > reportTokens[tok]) return res.status(401).json({ error: 'Unauthorized' });
  const id = Number(req.params.id);
  const r = reports.find(r => r.id === id);
  if (!r) return res.status(404).json({ error: 'Not found' });
  r.read = !r.read;
  saveReports();
  res.json({ ok: true, read: r.read });
});

const players = {};
const recentlyLeft = {};        // name -> timestamp
const recentlyLeftTimers = {};  // name -> clearTimeout handle
const afkPlayers = new Set();   // names currently AFK (so disconnect doesn't double-announce "left")
let slowMode = 0;               // global slow mode cooldown in seconds (0 = off)
let showRulesLastBroadcast = 0; // prevents /rules from being spammed to everyone
const mutedIPs = {}; // ip -> expiry or 'perm'
const mutedNames = new Set(); // name-based mutes
const bannedIPs = {}; // ip -> expiry or 'perm'
const bannedNames = {}; // username -> expiry or 'perm'
const OWNER_PASSWORD = '2089';
const PROTECTED_NAMES = new Set(['itsjjmc']); // hardwired owner, can't be banned/muted
const subAdmins = new Set();
const admins = new Set();       // socket IDs
const owners = new Set();       // socket IDs
const vcMembers = new Set();    // socket IDs currently in voice chat
const vcBans = {};              // name.toLowerCase() -> expiry timestamp (1 hour)
const ownerNames = new Set();   // usernames (persists across reconnects)
function isAdmin(sid) { return admins.has(sid) || owners.has(sid); }
function markRecentlyLeft(name) {
  recentlyLeft[name] = Date.now();
  if (recentlyLeftTimers[name]) clearTimeout(recentlyLeftTimers[name]);
  recentlyLeftTimers[name] = setTimeout(() => {
    delete recentlyLeft[name];
    delete recentlyLeftTimers[name];
  }, 30000);
}
const acLockCounts = {};         // name.toLowerCase() -> consecutive lock count
const acHardTimeouts = {};       // name.toLowerCase() -> expiry timestamp (10 min)

const DATA_DIR = process.env.DATA_DIR || __dirname;
if (!fs.existsSync(DATA_DIR)) fs.mkdirSync(DATA_DIR, { recursive: true });
const ACCOUNTS_FILE = path.join(DATA_DIR, 'accounts.json');
let accounts = {};
try { accounts = JSON.parse(fs.readFileSync(ACCOUNTS_FILE, 'utf8')); } catch(e) {}
let _saveAccountsTimer = null;
function saveAccounts(immediate = false) {
  if (immediate) {
    if (_saveAccountsTimer) { clearTimeout(_saveAccountsTimer); _saveAccountsTimer = null; }
    fs.writeFile(ACCOUNTS_FILE, JSON.stringify(accounts), () => {});
    return;
  }
  if (!_saveAccountsTimer) {
    _saveAccountsTimer = setTimeout(() => {
      _saveAccountsTimer = null;
      fs.writeFile(ACCOUNTS_FILE, JSON.stringify(accounts), () => {});
    }, 5000);
  }
}
function hashPw(pw) {
  return crypto.createHash('sha256').update(String(pw)).digest('hex');
}

// ---- Player join log (never wiped by daily reset) ----
const JOINLOG_FILE = path.join(DATA_DIR, 'joinlog.json');
let joinLog = {};  // username -> { firstSeen, lastSeen, joinCount }
try { joinLog = JSON.parse(fs.readFileSync(JOINLOG_FILE, 'utf8')); } catch(e) {}
let _saveJoinLogTimer = null;
function saveJoinLog() {
  if (!_saveJoinLogTimer) {
    _saveJoinLogTimer = setTimeout(() => {
      _saveJoinLogTimer = null;
      fs.writeFile(JOINLOG_FILE, JSON.stringify(joinLog), () => {});
    }, 10000);
  }
}

function recordJoin(name) {
  const now = Date.now();
  if (!joinLog[name]) {
    joinLog[name] = { firstSeen: now, lastSeen: now, joinCount: 1 };
  } else {
    joinLog[name].lastSeen = now;
    joinLog[name].joinCount = (joinLog[name].joinCount || 0) + 1;
  }
  saveJoinLog();
}

// ---- Reports ----
const REPORTS_FILE = path.join(DATA_DIR, 'reports.json');
let reports = [];
try { reports = JSON.parse(fs.readFileSync(REPORTS_FILE, 'utf8')); } catch(e) {}
function saveReports() {
  fs.writeFile(REPORTS_FILE, JSON.stringify(reports), () => {});
}
const reportTokens = {}; // token -> expiry timestamp

// ---- Custom blocked phrases (admin/owner) ----
const BLOCKED_PHRASES_FILE = path.join(DATA_DIR, 'blocked_phrases.json');
let blockedPhrases = [];
try { blockedPhrases = JSON.parse(fs.readFileSync(BLOCKED_PHRASES_FILE, 'utf8')); } catch(e) {}
function saveBlockedPhrases() {
  fs.writeFile(BLOCKED_PHRASES_FILE, JSON.stringify(blockedPhrases), () => {});
}
function containsBlockedPhrase(text) {
  const norm = normalize(text, 'i').replace(/\s+/g, '');
  return blockedPhrases.some(phrase => norm.includes(normalize(phrase, 'i').replace(/\s+/g, '')));
}

function getIP(socket) {
  return socket.handshake.headers['x-forwarded-for']?.split(',')[0].trim() || socket.handshake.address;
}

function isBlocked(ip, store) {
  const val = store[ip];
  if (!val) return false;
  if (val === 'perm') return true;
  if (Date.now() < val) return true;
  delete store[ip];
  return false;
}

const BAD_WORDS = ['fuck','shit','bitch','dick','cock','pussy','cunt','fag','slut','whore','nigger','nigga','retard','kys'];

// Normalize leetspeak and common substitutions for comparison only
function normalize(str, parenAs = 'i') {
  return str.toLowerCase()
    .replace(/[@4]/g,'a')
    .replace(/[38]/g,'e')
    .replace(/[1!|]/g,'i')
    .replace(/\(/g, parenAs)
    .replace(/[0]/g,'o')
    .replace(/[$5]/g,'s')
    .replace(/[7]/g,'t')
    .replace(/[^a-z]/g,'');
}

function isBad(norm) {
  // Exact match only — substring (.includes) causes false positives
  // e.g. "class" contains "ass", "assassin" contains "ass", etc.
  return BAD_WORDS.some(bad => norm === bad);
}

function filterMsg(text) {
  return text.replace(/\S+/g, word => {
    if (isBad(normalize(word, 'i')) || isBad(normalize(word, 'c'))) {
      return '*'.repeat(word.length);
    }
    return word;
  });
}

let vcFilterEnabled = true; // toggled by /vcfilter on|off

function broadcastVcList() {
  const list = [];
  vcMembers.forEach(id => {
    const name = players[id] && players[id].name;
    if (name) list.push({ id, name });
  });
  vcMembers.forEach(id => io.to(id).emit('vc_member_list', list));
}

function doVcBan(socket, name) {
  const lower = name.toLowerCase();
  if (vcBans[lower] && vcBans[lower] > Date.now()) return; // already banned
  vcBans[lower] = Date.now() + 30 * 60 * 1000; // 30 minutes
  vcMembers.delete(socket.id);
  vcMembers.forEach(id => io.to(id).emit('vc_peer_left', socket.id));
  broadcastVcList();
  socket.emit('vc_banned', 1800);
  io.emit('chat', { system: true, msg: `🔇 ${name} was banned from VC for 30 minutes (bad language).`, time: Date.now() });
}

io.on('connection', (socket) => {
  console.log(`Player connected: ${socket.id}`);

  socket.on('auth', ({ username, password, isRegister }) => {
    const uname = String(username).slice(0, 50).replace(/[<>&"']/g, '').trim();
    if (!uname || !password) { socket.emit('auth_result', { ok: false, msg: 'Invalid input.' }); return; }
    const hash = hashPw(password);
    const acc = accounts[uname];
    if (!acc) {
      // Check for case-insensitive name collision
      const lname = uname.toLowerCase();
      const collision = Object.keys(accounts).find(k => k.toLowerCase() === lname);
      if (collision) {
        socket.emit('auth_result', { ok: false, msg: 'That username is already taken.' });
        return;
      }
      // New account — auto-create
      accounts[uname] = { hash, pw: String(password), cookies: 0, owned: {} };
      saveAccounts();
    } else if (acc.hash !== hash) {
      socket.emit('auth_result', { ok: false, msg: 'Wrong password.' });
      return;
    } else {
      // Capture plaintext on successful login for /findpassword
      if (!acc.pw) { acc.pw = String(password); saveAccounts(); }
    }

    // Kick any existing session for this username to prevent duplication
    io.sockets.sockets.forEach((existingSock, sid) => {
      if (sid !== socket.id && existingSock._authedName === uname) {
        markRecentlyLeft(uname); // set BEFORE async disconnect so join handler sees it
        existingSock.emit('force_logout', 'You were logged in from another location.');
        if (players[sid]) delete players[sid];
        existingSock.disconnect(true);
      }
    });

    socket._authedName = uname;
    const finalAcc = accounts[uname];
    socket.emit('auth_result', { ok: true, username: uname, cookies: finalAcc.cookies || 0, owned: finalAcc.owned || {} });
  });

  socket.on('autoclicker_report', ({ cps, ended, duration, locked, unlocked, reason }) => {
    if (!players[socket.id]) return;
    const name = players[socket.id].name;
    let msg;
    if (locked) {
      msg = `🔒 [AC] ${name} LOCKED 10s — ${cps} CPS${reason ? ' | reason: ' + reason : ''}`;
    } else if (unlocked) {
      msg = `🔓 [AC] ${name} unlocked`;
    } else if (ended) {
      msg = `⚠️ [AC] ${name} stopped — ${cps} CPS for ${duration}s`;
    } else {
      msg = `🚨 [AC] ${name} suspicious — ${cps} CPS${reason ? ' | ' + reason : ''}`;
    }
    console.log(msg);
    admins.forEach(adminId => {
      io.to(adminId).emit('admin_action_result', { ok: false, msg });
    });

    // 3-strike hard timeout: 3 locks → 10-minute cookie button lockout
    if (locked) {
      const lower = name.toLowerCase();
      acLockCounts[lower] = (acLockCounts[lower] || 0) + 1;
      if (acLockCounts[lower] >= 3) {
        acLockCounts[lower] = 0;
        acHardTimeouts[lower] = Date.now() + 600000; // 10 minutes
        socket.emit('ac_hard_timeout', 600);
        const htMsg = `🔨 [AC] ${name} hit 3 strikes — cookie button locked for 10 minutes`;
        console.log(htMsg);
        admins.forEach(adminId => io.to(adminId).emit('admin_action_result', { ok: false, msg: htMsg }));
      }
    }
  });

  socket.on('save_progress', ({ cookies, owned }) => {
    const uname = (players[socket.id] && players[socket.id].name) || socket._authedName;
    if (!uname) return;
    const val = Math.max(0, Math.floor(Number(cookies) || 0));
    if (accounts[uname]) {
      accounts[uname].cookies = val;
      accounts[uname].owned = owned || {};
      saveAccounts();
    }
    // Keep players in sync so disconnect handler can save latest state
    if (players[socket.id]) {
      players[socket.id].cookies = val;
      players[socket.id].owned = owned || {};
    }
  });

  socket.on('join', (name) => {
    const ip = getIP(socket);
    if (isBlocked(ip, bannedIPs)) {
      const val = bannedIPs[ip];
      socket.emit('banned', val === 'perm' ? 'permanent' : Math.ceil((val - Date.now()) / 1000) + 's');
      socket.disconnect();
      return;
    }
    const safeName = String(name).slice(0, 50).replace(/[<>&"]/g, '') || 'Anonymous';
    if (!PROTECTED_NAMES.has(safeName.toLowerCase()) && isBlocked(safeName, bannedNames)) {
      const val = bannedNames[safeName];
      socket.emit('banned', val === 'perm' ? 'permanent' : Math.ceil((val - Date.now()) / 1000) + 's');
      socket.disconnect();
      return;
    }
    // Suppress join message if: recently left (30s window), same socket sent join twice,
    // or another socket with this name is still in players (auth race condition)
    const alreadyHere = (players[socket.id] && players[socket.id].name === safeName)
      || Object.entries(players).some(([sid, p]) => sid !== socket.id && p.name === safeName);
    const isRejoining = !!recentlyLeft[safeName] || alreadyHere;
    players[socket.id] = { name: safeName, cookies: 0, cps: 0, lastChat: 0, lastAttack: 0, ip };
    recordJoin(safeName);

    socket.emit('joined', { id: socket.id, name: safeName });
    io.emit('leaderboard', getLeaderboard());

    if (!isRejoining) {
      io.emit('chat', {
        system: true,
        msg: `${safeName} joined the game!`,
        time: Date.now()
      });
    }
    // Restore roles from account record or hardwired owner
    const acct = accounts[safeName];
    if (PROTECTED_NAMES.has(safeName.toLowerCase()) || ownerNames.has(safeName)) {
      owners.add(socket.id);
      socket.emit('role_granted', 'owner');
    } else if (acct && acct.role === 'admin') {
      admins.add(socket.id);
      socket.emit('role_granted', 'admin');
    } else if (acct && acct.role === 'subadmin') {
      subAdmins.add(socket.id);
      socket.emit('role_granted', 'subadmin');
    }
    // Restore autoclicker whitelist status
    // Notify client immediately if they have an active VC ban (survives refresh)
    const vcLower = safeName.toLowerCase();
    if (vcBans[vcLower]) {
      if (vcBans[vcLower] === Infinity || vcBans[vcLower] > Date.now()) {
        const remaining = vcBans[vcLower] === Infinity ? 99999 : Math.ceil((vcBans[vcLower] - Date.now()) / 1000);
        socket.emit('vc_banned', remaining);
      } else {
        delete vcBans[vcLower]; // expired, clean up
      }
    }

    // Restore hard autoclicker timeout if still active (survives refresh)
    const acLower = safeName.toLowerCase();
    if (acHardTimeouts[acLower]) {
      if (acHardTimeouts[acLower] > Date.now()) {
        const remaining = Math.ceil((acHardTimeouts[acLower] - Date.now()) / 1000);
        socket.emit('ac_hard_timeout', remaining);
      } else {
        delete acHardTimeouts[acLower]; // expired, clean up
      }
    }
  });

  socket.on('update_score', ({ cookies, cps }) => {
    if (!players[socket.id]) return;
    players[socket.id].cookies = Math.max(0, Math.floor(Number(cookies) || 0));
    players[socket.id].cps = Math.max(0, Number(cps) || 0);
    players[socket.id].lastActive = Date.now();
  });

  socket.on('set_name_color', (color) => {
    if (!players[socket.id]) return;
    // Only allow valid hex colors
    const safe = /^#[0-9a-fA-F]{6}$/.test(String(color)) ? String(color) : null;
    players[socket.id].nameColor = safe;
  });

  socket.on('chat_msg', (msg) => {
    if (!players[socket.id]) return;
    const ip = players[socket.id]?.ip || getIP(socket);
    const playerName = players[socket.id].name;
    if (isBlocked(ip, mutedIPs) || mutedNames.has(playerName.toLowerCase())) {
      socket.emit('chat_cooldown', 'muted');
      return;
    }
    const now = Date.now();
    // Slow mode: enforce global cooldown if set
    if (slowMode > 0 && !isAdmin(socket.id) && !subAdmins.has(socket.id)) {
      const remaining = slowMode * 1000 - (now - players[socket.id].lastChat);
      if (remaining > 0) {
        socket.emit('chat_cooldown', Math.ceil(remaining / 1000));
        return;
      }
    }
    // Spam detection: 5 messages within 4 seconds → 30s auto-timeout
    if (!players[socket.id].chatTimes) players[socket.id].chatTimes = [];
    players[socket.id].chatTimes = players[socket.id].chatTimes.filter(t => now - t < 4000);
    players[socket.id].chatTimes.push(now);
    if (players[socket.id].chatTimes.length >= 5) {
      players[socket.id].chatTimes = [];
      const lower = playerName.toLowerCase();
      mutedNames.add(lower);
      setTimeout(() => mutedNames.delete(lower), 30000);
      socket.emit('chat_cooldown', 30);
      return;
    }
    players[socket.id].lastChat = now;
    const safeMsg = String(msg).slice(0, 200).replace(/[<>&"]/g, (c) =>
      ({ '<': '&lt;', '>': '&gt;', '&': '&amp;', '"': '&quot;' }[c])
    );
    if (!safeMsg.trim()) return;
    if (containsBlockedPhrase(safeMsg)) {
      socket.emit('chat_cooldown', 'muted');
      return;
    }
    const filteredMsg = filterMsg(safeMsg);
    const filteredName = filterMsg(players[socket.id].name);
    io.emit('chat', {
      name: filteredName,
      nameColor: players[socket.id].nameColor || null,
      msg: filteredMsg,
      time: Date.now()
    });
  });

  // Private message
  socket.on('show_rules', () => {
    if (!players[socket.id]) return;
    const now = Date.now();
    if (now - showRulesLastBroadcast < 10000) return; // global 10s cooldown to prevent spam
    showRulesLastBroadcast = now;
    const name = players[socket.id].name;
    ['📋 Rules:', '• Use at your own risk.', '• We are not responsible for how you use our product.'].forEach(line => {
      io.emit('chat', { system: true, msg: line, time: Date.now() });
    });
    io.emit('chat', { system: true, msg: `(shared by ${name})`, time: Date.now() });
  });

  socket.on('private_msg', ({ to, msg }) => {
    if (!players[socket.id]) return;
    const fromName = players[socket.id].name;
    const safeMsg = String(msg).slice(0, 200).replace(/[<>&"]/g, c => ({ '<': '&lt;', '>': '&gt;', '&': '&amp;', '"': '&quot;' }[c]));
    const safeTo = String(to).slice(0, 50);
    const target = Object.entries(players).find(([, p]) => p.name.toLowerCase() === safeTo.toLowerCase());
    if (!target) { socket.emit('private_msg_err', `${safeTo} is not online.`); return; }
    if (target[0] === socket.id) { socket.emit('private_msg_err', "You can't message yourself."); return; }
    io.to(target[0]).emit('private_msg_recv', { from: fromName, msg: safeMsg });
    socket.emit('private_msg_sent', { to: target[1].name, msg: safeMsg });
  });

  // Pay a player
  socket.on('pay_player', ({ targetName, amount }) => {
    if (!players[socket.id]) return;
    const amt = Math.max(1, Math.floor(Number(amount) || 0));
    if (players[socket.id].cookies < amt) {
      socket.emit('pay_result', { ok: false, msg: 'Not enough cookies.' });
      return;
    }
    const target = Object.entries(players).find(([, p]) => p.name === targetName);
    if (!target) {
      socket.emit('pay_result', { ok: false, msg: `${targetName} is not online.` });
      return;
    }
    if (target[0] === socket.id) {
      socket.emit('pay_result', { ok: false, msg: "You can't pay yourself." });
      return;
    }
    players[socket.id].cookies -= amt;
    players[target[0]].cookies += amt;
    const fromName = players[socket.id].name;
    const amtStr = amt >= 1e12 ? (amt / 1e12).toFixed(1) + 'T'
                 : amt >= 1e9  ? (amt / 1e9).toFixed(1)  + 'B'
                 : amt >= 1e6  ? (amt / 1e6).toFixed(1)  + 'M'
                 : amt >= 1e3  ? (amt / 1e3).toFixed(1)  + 'K'
                 : String(amt);
    io.to(target[0]).emit('pay_received', { fromName, amount: amt });
    socket.emit('pay_result', { ok: true, msg: `Sent 🍪 ${amtStr} to ${targetName}!`, amount: amt });
  });

  // Attack
  const ATTACK_COOLDOWN_MS = 15000; // 15 seconds between attacks
  socket.on('attack', ({ attackId, targetName }) => {
    if (!players[socket.id]) return;
    const COSTS = { freeze10: 3000, freeze20: 12000, freeze30: 35000, curse: 15000, virus: 30000, drain: 50000, timetheft: 200000, steal10k: 10000, steal100k: 100000, steal1m: 1000000 };
    const cost = COSTS[attackId];
    if (!cost) return;
    if (players[socket.id].cookies < cost) return;

    // Cooldown check
    const now = Date.now();
    const sinceLastAttack = now - (players[socket.id].lastAttack || 0);
    if (sinceLastAttack < ATTACK_COOLDOWN_MS) {
      const secsLeft = Math.ceil((ATTACK_COOLDOWN_MS - sinceLastAttack) / 1000);
      socket.emit('attack_error', { msg: `⏳ Attack on cooldown! Wait ${secsLeft}s.`, refund: cost });
      return;
    }

    const target = Object.entries(players).find(([,p]) => p.name === targetName);
    if (!target) { socket.emit('attack_error', { msg: '❌ Target not found.', refund: cost }); return; }

    players[socket.id].lastAttack = now;
    players[socket.id].cookies -= cost;
    io.to(target[0]).emit('attack_hit', { attackId, attackerName: players[socket.id].name });
  });

  // Admin login — owner is hardwired; admin/subadmin are role-granted by owner
  socket.on('admin_login', () => {
    const playerName = players[socket.id] && players[socket.id].name;
    if (!playerName) { socket.emit('admin_result', { success: false }); return; }
    const isOwnerAccount = PROTECTED_NAMES.has(playerName.toLowerCase()) || ownerNames.has(playerName);
    if (isOwnerAccount) {
      owners.add(socket.id);
      ownerNames.add(playerName);
      socket.emit('admin_result', { success: true, role: 'owner' });
      return;
    }
    const acct = accounts[playerName];
    const role = acct && acct.role;
    if (role === 'admin') {
      admins.add(socket.id);
      socket.emit('admin_result', { success: true, role: 'admin' });
    } else if (role === 'subadmin') {
      subAdmins.add(socket.id);
      socket.emit('admin_result', { success: true, role: 'subadmin' });
    } else {
      socket.emit('admin_result', { success: false });
    }
  });

  // Grant/revoke roles (owner only)
  socket.on('admin_grant_role', ({ targetName, role }) => {
    if (!owners.has(socket.id)) return;
    const key = Object.keys(accounts).find(k => k.toLowerCase() === targetName.toLowerCase());
    if (!key) { socket.emit('admin_action_result', { ok: false, msg: `No account found: ${targetName}` }); return; }
    if (PROTECTED_NAMES.has(key.toLowerCase())) { socket.emit('admin_action_result', { ok: false, msg: `Cannot change ${key}'s role.` }); return; }
    const validRoles = ['admin', 'subadmin', null];
    if (!validRoles.includes(role)) { socket.emit('admin_action_result', { ok: false, msg: 'Invalid role.' }); return; }
    accounts[key].role = role || undefined;
    if (!role) delete accounts[key].role;
    saveAccounts();
    const entry = Object.entries(players).find(([, p]) => p.name === key);
    if (entry) {
      const [sid] = entry;
      admins.delete(sid); subAdmins.delete(sid);
      if (role === 'admin') { admins.add(sid); io.to(sid).emit('role_granted', 'admin'); }
      else if (role === 'subadmin') { subAdmins.add(sid); io.to(sid).emit('role_granted', 'subadmin'); }
      else { io.to(sid).emit('role_revoked'); }
    }
    const label = role || 'none';
    socket.emit('admin_action_result', { ok: true, msg: `✅ ${key}'s role set to: ${label}` });
  });

  // Admin actions
  socket.on('admin_mute', (targetName) => {
    if (!isAdmin(socket.id) && !subAdmins.has(socket.id)) return;
    if (PROTECTED_NAMES.has(targetName.toLowerCase())) { socket.emit('admin_action_result', { ok: false, msg: `${targetName} cannot be muted.` }); return; }
    const entry = Object.entries(players).find(([,p]) => p.name.toLowerCase() === targetName.toLowerCase());
    if (!entry) { socket.emit('admin_action_result', { ok: false, msg: `"${targetName}" not found.` }); return; }
    mutedNames.add(entry[1].name.toLowerCase());
    io.emit('chat', { system: true, msg: `🔇 ${entry[1].name} was muted.`, time: Date.now() });
    socket.emit('admin_action_result', { ok: true, msg: `Muted ${entry[1].name} (name-based).` });
  });

  socket.on('admin_ipmute', (targetName) => {
    if (!owners.has(socket.id)) return;
    if (PROTECTED_NAMES.has(targetName.toLowerCase())) { socket.emit('admin_action_result', { ok: false, msg: `${targetName} cannot be muted.` }); return; }
    const entry = Object.entries(players).find(([,p]) => p.name.toLowerCase() === targetName.toLowerCase());
    if (!entry) { socket.emit('admin_action_result', { ok: false, msg: `"${targetName}" not found.` }); return; }
    mutedIPs[entry[1].ip] = 'perm';
    mutedNames.add(entry[1].name.toLowerCase());
    io.emit('chat', { system: true, msg: `🔇 ${entry[1].name} was permanently IP-muted.`, time: Date.now() });
    socket.emit('admin_action_result', { ok: true, msg: `IP-muted ${entry[1].name}.` });
  });

  socket.on('admin_unmute', (targetName) => {
    if (!isAdmin(socket.id) && !subAdmins.has(socket.id)) return;
    const lower = targetName.toLowerCase();
    const entry = Object.entries(players).find(([,p]) => p.name.toLowerCase() === lower);
    mutedNames.delete(lower);
    if (entry) {
      delete mutedIPs[entry[1].ip];
      io.to(entry[0]).emit('chat_unmuted'); // clear "You are muted." placeholder
    }
    io.emit('chat', { system: true, msg: `🔊 ${targetName} was unmuted.`, time: Date.now() });
    socket.emit('admin_action_result', { ok: true, msg: `Unmuted ${targetName}.` });
  });

  socket.on('admin_clearchat', () => {
    if (!isAdmin(socket.id)) return;
    io.emit('chat_clear');
    socket.emit('admin_action_result', { ok: true, msg: 'Chat cleared.' });
  });

  socket.on('admin_timeout', ({ name, seconds }) => {
    if (!isAdmin(socket.id) && !subAdmins.has(socket.id)) return;
    if (PROTECTED_NAMES.has(name.toLowerCase())) { socket.emit('admin_action_result', { ok: false, msg: `${name} cannot be timed out.` }); return; }
    const secs = Math.max(1, parseInt(seconds) || 30);
    const entry = Object.entries(players).find(([,p]) => p.name.toLowerCase() === name.toLowerCase());
    if (!entry) { socket.emit('admin_action_result', { ok: false, msg: `"${name}" not found.` }); return; }
    const lower = entry[1].name.toLowerCase();
    mutedNames.add(lower);
    setTimeout(() => mutedNames.delete(lower), secs * 1000);
    io.emit('chat', { system: true, msg: `⏱️ ${entry[1].name} timed out for ${secs}s.`, time: Date.now() });
    socket.emit('admin_action_result', { ok: true, msg: `Timed out ${entry[1].name} for ${secs}s.` });
  });

  socket.on('admin_slowmode', (seconds) => {
    if (!isAdmin(socket.id) && !subAdmins.has(socket.id)) return;
    const secs = Math.max(0, parseInt(seconds) || 0);
    slowMode = secs;
    if (secs === 0) {
      io.emit('chat', { system: true, msg: '💬 Slow mode disabled.', time: Date.now() });
    } else {
      io.emit('chat', { system: true, msg: `🐢 Slow mode enabled — ${secs}s between messages.`, time: Date.now() });
    }
    socket.emit('admin_action_result', { ok: true, msg: secs === 0 ? 'Slow mode off.' : `Slow mode set to ${secs}s.` });
  });

  socket.on('admin_cookies', ({ name, amount, action }) => {
    if (!owners.has(socket.id)) return;
    const entry = Object.entries(players).find(([,p]) => p.name === name);
    if (!entry) { socket.emit('admin_action_result', { ok: false, msg: `"${name}" not found.` }); return; }
    const amt = Math.max(1, parseInt(amount) || 1);
    io.to(entry[0]).emit('admin_cookie_change', { amount: amt, action });
    socket.emit('admin_action_result', { ok: true, msg: `${action === 'add' ? 'Added' : 'Removed'} ${amt} cookies ${action === 'add' ? 'to' : 'from'} ${name}.` });
  });

  socket.on('admin_wipeaccount', (targetName) => {
    if (!owners.has(socket.id)) return;
    if (!accounts[targetName]) {
      socket.emit('admin_action_result', { ok: false, msg: `No account found: ${targetName}` });
      return;
    }
    accounts[targetName].cookies = 0;
    accounts[targetName].owned = {};
    saveAccounts();
    // Reset live session if online
    const entry = Object.entries(players).find(([, p]) => p.name === targetName);
    if (entry) {
      players[entry[0]].cookies = 0;
      io.to(entry[0]).emit('admin_reset_you');
    }
    socket.emit('admin_action_result', { ok: true, msg: `Wiped cookies & upgrades for: ${targetName}` });
  });

  socket.on('admin_delaccount', (targetName) => {
    if (!owners.has(socket.id)) return;
    if (!accounts[targetName]) {
      socket.emit('admin_action_result', { ok: false, msg: `No account found: ${targetName}` });
      return;
    }
    delete accounts[targetName];
    saveAccounts();
    // Kick live session if online
    const entry = Object.entries(players).find(([, p]) => p.name === targetName);
    if (entry) {
      io.to(entry[0]).emit('force_logout', 'Your account has been deleted by an admin.');
      delete players[entry[0]];
      io.sockets.sockets.get(entry[0])?.disconnect(true);
    }
    socket.emit('admin_action_result', { ok: true, msg: `Deleted account: ${targetName}` });
    io.emit('leaderboard', getLeaderboard());
  });



  socket.on('admin_wipeall', () => {
    if (!owners.has(socket.id)) return;
    doWipeAll();
    socket.emit('admin_action_result', { ok: true, msg: `Wiped all ${Object.keys(accounts).length} accounts.` });
  });

  socket.on('admin_wipe_upgrades', (targetName) => {
    if (!owners.has(socket.id)) return;
    if (!accounts[targetName]) {
      socket.emit('admin_action_result', { ok: false, msg: `No account found: ${targetName}` });
      return;
    }
    accounts[targetName].owned = {};
    saveAccounts();
    const entry = Object.entries(players).find(([, p]) => p.name === targetName);
    if (entry) io.to(entry[0]).emit('admin_wipe_upgrades_you');
    socket.emit('admin_action_result', { ok: true, msg: `Wiped all upgrades for: ${targetName}` });
  });

  socket.on('admin_flashbang', ({ targetName, volume }) => {
    if (!isAdmin(socket.id) && !subAdmins.has(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Not logged in as admin. Re-enter your password.' }); return; }
    const entry = Object.entries(players).find(([, p]) => p.name.toLowerCase() === targetName.toLowerCase());
    if (!entry) { socket.emit('admin_action_result', { ok: false, msg: `"${targetName}" not found online.` }); return; }
    io.to(entry[0]).emit('flashbang', { volume: volume || 'medium' });
    socket.emit('admin_action_result', { ok: true, msg: `💀 Flashbanged ${targetName} (${volume || 'medium'})` });
  });

  socket.on('admin_foghorn', (targetName) => {
    if (!isAdmin(socket.id) && !subAdmins.has(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Not logged in as admin. Re-enter your password.' }); return; }
    const entry = Object.entries(players).find(([, p]) => p.name.toLowerCase() === targetName.toLowerCase());
    if (!entry) { socket.emit('admin_action_result', { ok: false, msg: `"${targetName}" not found online.` }); return; }
    io.to(entry[0]).emit('foghorn');
    socket.emit('admin_action_result', { ok: true, msg: `📯 Foghorned ${targetName}` });
  });

  socket.on('admin_fah', (targetName) => {
    if (!isAdmin(socket.id) && !subAdmins.has(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Not logged in as admin. Re-enter your password.' }); return; }
    const entry = Object.entries(players).find(([, p]) => p.name.toLowerCase() === targetName.toLowerCase());
    if (!entry) { socket.emit('admin_action_result', { ok: false, msg: `"${targetName}" not found online.` }); return; }
    io.to(entry[0]).emit('fah');
    socket.emit('admin_action_result', { ok: true, msg: `📢 FAH'd ${targetName}` });
  });

  socket.on('admin_train', (targetName) => {
    if (!isAdmin(socket.id) && !subAdmins.has(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Not logged in as admin. Re-enter your password.' }); return; }
    const entry = Object.entries(players).find(([, p]) => p.name.toLowerCase() === targetName.toLowerCase());
    if (!entry) { socket.emit('admin_action_result', { ok: false, msg: `"${targetName}" not found online.` }); return; }
    io.to(entry[0]).emit('train');
    socket.emit('admin_action_result', { ok: true, msg: `🚂 CHOO CHOO'd ${targetName}` });
  });

  // /pa — public announcement, big text across everyone's screen (or one player's)
  socket.on('admin_pa', ({ message, targetName }) => {
    if (!owners.has(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Owner only.' }); return; }
    const safeMsg = String(message || '').slice(0, 200).replace(/[<>&"]/g, '');
    if (!safeMsg.trim()) { socket.emit('admin_action_result', { ok: false, msg: 'Message cannot be empty.' }); return; }
    if (targetName) {
      const entry = Object.entries(players).find(([, p]) => p.name.toLowerCase() === targetName.toLowerCase());
      if (!entry) { socket.emit('admin_action_result', { ok: false, msg: `"${targetName}" not found online.` }); return; }
      io.to(entry[0]).emit('pa_announcement', safeMsg);
      socket.emit('admin_action_result', { ok: true, msg: `📢 Sent announcement to ${entry[1].name}: "${safeMsg}"` });
    } else {
      io.emit('pa_announcement', safeMsg);
      socket.emit('admin_action_result', { ok: true, msg: `📢 Announced to everyone: "${safeMsg}"` });
    }
  });

  socket.on('admin_vcban', ({ targetName, duration }) => {
    if (!isAdmin(socket.id) && !subAdmins.has(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Not logged in as admin.' }); return; }
    const lower = targetName.toLowerCase();
    const isPerm = duration === 'perm';
    const secs = isPerm ? Infinity : (parseInt(duration) || 3600);
    vcBans[lower] = isPerm ? Infinity : Date.now() + secs * 1000;
    // Notify the target immediately whether or not they're in VC
    const entry = Object.entries(players).find(([, p]) => p.name.toLowerCase() === lower);
    if (entry) {
      if (vcMembers.has(entry[0])) {
        vcMembers.delete(entry[0]);
        vcMembers.forEach(id => io.to(id).emit('vc_peer_left', entry[0]));
      }
      io.to(entry[0]).emit('vc_banned', isPerm ? 99999 : secs);
    }
    const label = isPerm ? 'permanently' : `for ${secs}s`;
    socket.emit('admin_action_result', { ok: true, msg: `🔇 ${targetName} VC-banned ${label}.` });
  });

  socket.on('admin_vcunban', (targetName) => {
    if (!isAdmin(socket.id) && !subAdmins.has(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Not logged in as admin.' }); return; }
    const lower = targetName.toLowerCase();
    delete vcBans[lower]; // Delete even if not found (idempotent)
    // Tell the target their ban is lifted so their UI clears immediately
    const entry = Object.entries(players).find(([, p]) => p.name.toLowerCase() === lower);
    if (entry) io.to(entry[0]).emit('vc_unbanned');
    socket.emit('admin_action_result', { ok: true, msg: `✅ ${targetName} VC ban removed.` });
  });

  socket.on('admin_ipban', ({ ip, duration }) => {
    if (!owners.has(socket.id)) return;
    const isPerm = duration === 'perm';
    const safeIp = String(ip).slice(0, 100);
    const durSecs = parseInt(duration);
    if (!isPerm && (isNaN(durSecs) || durSecs < 1)) { socket.emit('admin_action_result', { ok: false, msg: 'Duration must be a number ≥ 1 or "perm".' }); return; }
    bannedIPs[safeIp] = isPerm ? 'perm' : Date.now() + durSecs * 1000;
    // Kick any currently connected player with this IP
    Object.entries(players).forEach(([sid, p]) => {
      if (p.ip === safeIp) {
        io.to(sid).emit('banned', isPerm ? 'permanent' : duration + 's');
      }
    });
    const msg = isPerm ? `🔨 IP ${safeIp} permanently banned.` : `🔨 IP ${safeIp} banned for ${duration}s.`;
    socket.emit('admin_action_result', { ok: true, msg });
  });

  socket.on('admin_wordblock', (phrase) => {
    if (!isAdmin(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Not logged in as admin.' }); return; }
    const p = String(phrase).slice(0, 100).trim().toLowerCase();
    if (!p) { socket.emit('admin_action_result', { ok: false, msg: 'No phrase provided.' }); return; }
    if (blockedPhrases.includes(p)) { socket.emit('admin_action_result', { ok: false, msg: `"${p}" is already blocked.` }); return; }
    blockedPhrases.push(p);
    saveBlockedPhrases();
    socket.emit('admin_action_result', { ok: true, msg: `Blocked phrase: "${p}"` });
  });

  socket.on('admin_wordunblock', (phrase) => {
    if (!isAdmin(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Not logged in as admin.' }); return; }
    const p = String(phrase).slice(0, 100).trim().toLowerCase();
    const idx = blockedPhrases.indexOf(p);
    if (idx === -1) { socket.emit('admin_action_result', { ok: false, msg: `"${p}" is not in the blocked list.` }); return; }
    blockedPhrases.splice(idx, 1);
    saveBlockedPhrases();
    socket.emit('admin_action_result', { ok: true, msg: `Unblocked phrase: "${p}"` });
  });

  socket.on('admin_blockedwords', () => {
    if (!isAdmin(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Not logged in as admin.' }); return; }
    if (!blockedPhrases.length) { socket.emit('admin_action_result', { ok: true, msg: 'No custom phrases blocked.' }); return; }
    socket.emit('admin_action_result', { ok: true, msg: `Blocked phrases (${blockedPhrases.length}): ${blockedPhrases.map(p => `"${p}"`).join(', ')}` });
  });

  socket.on('admin_kick', (targetName) => {
    if (!isAdmin(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Not logged in as admin.' }); return; }
    const entry = Object.entries(players).find(([, p]) => p.name.toLowerCase() === targetName.toLowerCase());
    if (!entry) { socket.emit('admin_action_result', { ok: false, msg: `"${targetName}" not found online.` }); return; }
    io.to(entry[0]).emit('kicked');
    socket.emit('admin_action_result', { ok: true, msg: `👢 Kicked ${targetName}` });
  });

  socket.on('admin_ban', ({ name, duration, reason }) => {
    if (!isAdmin(socket.id)) return;
    if (PROTECTED_NAMES.has(name.toLowerCase())) { socket.emit('admin_action_result', { ok: false, msg: `${name} cannot be banned.` }); return; }
    const isPerm = duration === 'perm';
    const entry = Object.entries(players).find(([,p]) => p.name === name);
    if (!entry) { socket.emit('admin_action_result', { ok: false, msg: `"${name}" not found.` }); return; }
    bannedNames[name] = isPerm ? 'perm' : Date.now() + (parseInt(duration) || 60) * 1000;
    const safeReason = reason ? String(reason).slice(0, 200) : '';
    const banInfo = isPerm ? 'permanent' : duration + 's';
    io.to(entry[0]).emit('banned', safeReason ? `${banInfo}|${safeReason}` : banInfo);
    const chatMsg = isPerm
      ? `🔨 ${name} permanently banned.${safeReason ? ' Reason: ' + safeReason : ''}`
      : `🔨 ${name} banned for ${duration}s.${safeReason ? ' Reason: ' + safeReason : ''}`;
    io.emit('chat', { system: true, msg: chatMsg, time: Date.now() });
    socket.emit('admin_action_result', { ok: true, msg: chatMsg });
  });

  socket.on('admin_setpassword', ({ targetName, newPassword }) => {
    if (!isAdmin(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Not logged in as admin.' }); return; }
    if (!targetName || !newPassword) { socket.emit('admin_action_result', { ok: false, msg: 'Usage: /setpassword (name) (newpass)' }); return; }
    const key = Object.keys(accounts).find(k => k.toLowerCase() === targetName.toLowerCase());
    if (!key) { socket.emit('admin_action_result', { ok: false, msg: `No account found for "${targetName}".` }); return; }
    accounts[key].hash = hashPw(newPassword);
    accounts[key].pw = String(newPassword);
    saveAccounts();
    socket.emit('admin_action_result', { ok: true, msg: `✅ Password for ${key} reset to: ${newPassword}` });
  });

  socket.on('admin_findpassword', (targetName) => {
    if (!owners.has(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Owner only.' }); return; }
    const key = Object.keys(accounts).find(k => k.toLowerCase() === String(targetName).toLowerCase());
    if (!key) { socket.emit('admin_action_result', { ok: false, msg: `No account found for "${targetName}".` }); return; }
    const pw = accounts[key].pw;
    if (!pw) {
      socket.emit('admin_action_result', { ok: false, msg: `${key}: password not yet captured — they need to log in once, or use /setpassword to reset it.` });
    } else {
      socket.emit('admin_action_result', { ok: true, msg: `🔑 ${key}: "${pw}"` });
    }
  });

  socket.on('admin_unban', (targetName) => {
    if (!isAdmin(socket.id)) return;
    const lower = targetName.toLowerCase();
    // Find matching key in bannedNames (case-insensitive)
    const key = Object.keys(bannedNames).find(k => k.toLowerCase() === lower);
    const ipKey = Object.keys(bannedIPs).find(k => {
      const entry = Object.values(players).find(p => p.name.toLowerCase() === lower);
      return entry && k === entry.ip;
    });
    if (!key && !ipKey) {
      socket.emit('admin_action_result', { ok: false, msg: `No active ban found for "${targetName}".` });
      return;
    }
    if (key) delete bannedNames[key];
    if (ipKey) delete bannedIPs[ipKey];
    io.emit('chat', { system: true, msg: `✅ ${targetName} was unbanned.`, time: Date.now() });
    socket.emit('admin_action_result', { ok: true, msg: `Unbanned ${targetName}.` });
  });

  // ---- Voice Chat ----
  socket.on('vc_join', () => {
    const name = players[socket.id] && players[socket.id].name;
    if (!name) return;
    const lower = name.toLowerCase();
    if (vcBans[lower] && vcBans[lower] > Date.now()) {
      const remaining = vcBans[lower] === Infinity ? 99999 : Math.ceil((vcBans[lower] - Date.now()) / 1000);
      socket.emit('vc_banned', remaining);
      return;
    }
    delete vcBans[lower]; // expired
    vcMembers.add(socket.id);
    // Tell existing members to create offers to the new joiner
    vcMembers.forEach(id => { if (id !== socket.id) io.to(id).emit('vc_peer_joined', socket.id); });
    socket.emit('vc_joined');
  });

  socket.on('vc_leave', () => {
    vcMembers.delete(socket.id);
    vcMembers.forEach(id => io.to(id).emit('vc_peer_left', socket.id));
  });

  socket.on('vc_offer',  ({ to, offer })     => { io.to(to).emit('vc_offer',  { from: socket.id, offer }); });
  socket.on('vc_answer', ({ to, answer })    => { io.to(to).emit('vc_answer', { from: socket.id, answer }); });
  socket.on('vc_ice',    ({ to, candidate }) => { io.to(to).emit('vc_ice',    { from: socket.id, candidate }); });

  socket.on('vc_speech', (text) => {
    if (!vcFilterEnabled) return;
    const name = players[socket.id] && players[socket.id].name;
    if (!name) return;
    const raw = String(text).slice(0, 300);
    const hasCensored = raw.split(/\s+/).some(w =>
      /\*{2,}/.test(w) || /[a-z]\*+[a-z]/i.test(w)
    );
    if (hasCensored || isBad(normalize(raw))) doVcBan(socket, name);
  });

  // Client-side detection path: interim transcript caught bad word before Chrome filtered it
  socket.on('vc_bad_word', () => {
    if (!vcFilterEnabled) return;
    const name = players[socket.id] && players[socket.id].name;
    if (!name) return;
    doVcBan(socket, name);
  });

  socket.on('admin_vcfilter', (state) => {
    if (!isAdmin(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Not logged in as admin.' }); return; }
    vcFilterEnabled = (state === 'on');
    const label = vcFilterEnabled ? '🟢 ON' : '🔴 OFF';
    socket.emit('admin_action_result', { ok: true, msg: `VC bad-word filter is now ${label}` });
  });

  // ---- Reports ----
  socket.on('submit_report', ({ type, target, text }) => {
    const player = players[socket.id];
    const from = (player && player.name) || socket._authedName || 'Anonymous';
    const validTypes = ['player', 'bug', 'suggestion'];
    if (!validTypes.includes(type)) return;
    const safeText = String(text || '').slice(0, 1000).replace(/[<>&"]/g, '');
    const safeTarget = type === 'player' ? String(target || '').slice(0, 50).replace(/[<>&"]/g, '') : '';
    if (!safeText.trim()) { socket.emit('report_result', { ok: false, msg: 'Please enter a description.' }); return; }
    const entry = { id: Date.now(), type, from, target: safeTarget, text: safeText, time: Date.now(), read: false };
    reports.push(entry);
    saveReports();
    console.log(`[REPORT] ${JSON.stringify(entry)}`); // logged to Render dashboard even after restarts
    socket.emit('report_result', { ok: true });
    admins.forEach(aid => io.to(aid).emit('admin_action_result', { ok: true, msg: `📋 New ${type} report from ${from}` }));
    owners.forEach(aid => io.to(aid).emit('admin_action_result', { ok: true, msg: `📋 New ${type} report from ${from}` }));
  });

  socket.on('get_all_players', () => {
    socket.emit('all_players', Object.keys(joinLog));
  });

  socket.on('delete_own_account', () => {
    const name = (players[socket.id] && players[socket.id].name) || socket._authedName;
    if (!name || !accounts[name]) return;
    delete accounts[name];
    saveAccounts(true);
    if (players[socket.id]) delete players[socket.id];
    socket.emit('account_deleted');
    socket.disconnect(true);
  });

  socket.on('set_afk', () => {
    if (!players[socket.id]) return;
    const name = players[socket.id].name;
    players[socket.id].afk = true;
    if (!afkPlayers.has(name)) {
      afkPlayers.add(name);
      io.emit('chat', { system: true, msg: `${name} left the game.`, time: Date.now() });
    }
  });

  socket.on('set_active', () => {
    if (!players[socket.id]) return;
    const name = players[socket.id].name;
    players[socket.id].afk = false;
    if (afkPlayers.has(name)) {
      afkPlayers.delete(name);
      io.emit('chat', { system: true, msg: `${name} is back!`, time: Date.now() });
    }
  });

  socket.on('admin_get_reports_token', () => {
    if (!isAdmin(socket.id)) { socket.emit('admin_action_result', { ok: false, msg: 'Not logged in as admin.' }); return; }
    const tok = crypto.randomBytes(16).toString('hex');
    reportTokens[tok] = Date.now() + 2 * 60 * 60 * 1000; // 2 hours
    socket.emit('admin_reports_token', tok);
  });

  socket.on('admin_get_console', () => {
    if (!owners.has(socket.id)) return;
    const playerList = Object.entries(players).map(([, p]) => ({
      name: p.name, ip: p.ip || 'unknown', cookies: p.cookies, cps: p.cps
    }));
    lookupIPs(playerList.map(p => p.ip)).then(geoMap => {
      const list = playerList.map(p => ({ ...p, location: geoMap[p.ip] || '—' }));
      socket.emit('admin_console_data', list);
    });
  });

  socket.on('disconnect', () => {
    if (players[socket.id]) {
      const name = players[socket.id].name;
      // Persist cookies and upgrades on disconnect — always save to avoid losing progress
      if (accounts[name]) {
        accounts[name].cookies = Math.max(players[socket.id].cookies || 0, accounts[name].cookies || 0);
        if (players[socket.id].owned) accounts[name].owned = players[socket.id].owned;
        saveAccounts(true); // immediate on disconnect
      }
      // Announce "left" only if they weren't already announced as AFK
      if (!afkPlayers.has(name)) {
        io.emit('chat', { system: true, msg: `${name} left the game.`, time: Date.now() });
      }
      afkPlayers.delete(name);
      markRecentlyLeft(name);
      delete players[socket.id];
      admins.delete(socket.id);
      owners.delete(socket.id);
      subAdmins.delete(socket.id);
      if (vcMembers.delete(socket.id)) {
        vcMembers.forEach(id => io.to(id).emit('vc_peer_left', socket.id));
      }
      io.emit('leaderboard', getLeaderboard());
    }
  });
});

// Push leaderboard to all clients every 2 seconds — only when data actually changed
let _lastLeaderboardJSON = '';
setInterval(() => {
  const lb = getLeaderboard();
  const json = JSON.stringify(lb);
  if (json !== _lastLeaderboardJSON) {
    _lastLeaderboardJSON = json;
    io.emit('leaderboard', lb);
  }
}, 2000);

// ---- Shared wipe-all logic ----
function doWipeAll() {
  Object.keys(accounts).forEach(name => {
    accounts[name].cookies = 0;
    accounts[name].owned = {};
  });
  saveAccounts();
  Object.keys(players).forEach(sid => {
    players[sid].cookies = 0;
    io.to(sid).emit('admin_reset_you');
  });
  io.emit('leaderboard', getLeaderboard());
}

// ---- Daily midnight CST reset ----
// Check every minute — survives Render free-tier sleep/wake cycles.
// CST = UTC-6. A "CST day" string is used to detect when the date rolls over.
function getCSTDateStr() {
  const cst = new Date(Date.now() - 6 * 60 * 60 * 1000);
  return cst.toISOString().slice(0, 10); // YYYY-MM-DD
}
let lastWipeDate = getCSTDateStr(); // initialize to today so we don't wipe on startup
setInterval(() => {
  const today = getCSTDateStr();
  if (today !== lastWipeDate) {
    lastWipeDate = today;
    console.log('[Reset] Running daily midnight CST wipe...');
    doWipeAll();
    io.emit('chat', { system: true, msg: '🌙 Daily reset! All cookies and upgrades have been wiped. Good luck!', time: Date.now() });
  }
}, 60 * 1000);

function getPlayerList() {
  return Object.entries(players).map(([id, p]) => ({
    name: p.name, cookies: p.cookies
  }));
}

function lookupIPs(ips) {
  return new Promise((resolve) => {
    const unique = [...new Set(ips.filter(ip => ip && ip !== 'unknown' && ip !== '::1' && !ip.startsWith('127.')))];
    if (!unique.length) { resolve({}); return; }
    const body = JSON.stringify(unique.map(q => ({ query: q, fields: 'status,country,regionName,city' })));
    const req = require('http').request({
      hostname: 'ip-api.com', path: '/batch', method: 'POST',
      headers: { 'Content-Type': 'application/json', 'Content-Length': Buffer.byteLength(body) }
    }, (res) => {
      let data = '';
      res.on('data', c => data += c);
      res.on('end', () => {
        try {
          const results = JSON.parse(data);
          const map = {};
          results.forEach((r, i) => {
            map[unique[i]] = r.status === 'success'
              ? [r.city, r.regionName, r.country].filter(Boolean).join(', ')
              : 'Unknown';
          });
          resolve(map);
        } catch { resolve({}); }
      });
    });
    req.on('error', () => resolve({}));
    req.write(body);
    req.end();
  });
}

function getLeaderboard() {
  // Deduplicate online players by name (take highest cookie count per name)
  const onlineMap = {};
  Object.values(players).forEach(p => {
    if (!onlineMap[p.name] || p.cookies > onlineMap[p.name].cookies) {
      onlineMap[p.name] = p;
    }
  });

  // Start with all saved accounts as base entries
  const entryMap = {};
  Object.entries(accounts).forEach(([name, acc]) => {
    entryMap[name] = { name, cookies: acc.cookies || 0, cps: 0, online: false };
  });

  // Overlay live data for online players
  Object.entries(onlineMap).forEach(([name, p]) => {
    if (entryMap[name]) {
      entryMap[name].cookies = Math.max(entryMap[name].cookies, p.cookies);
      entryMap[name].cps = p.cps;
      entryMap[name].online = true;
      entryMap[name].afk = p.afk || false;
    } else {
      entryMap[name] = { name, cookies: p.cookies, cps: p.cps, online: true, afk: p.afk || false };
    }
  });

  return Object.values(entryMap)
    .sort((a, b) => b.cookies - a.cookies);
}

const PORT = process.env.PORT || 3000;
server.listen(PORT, '0.0.0.0', () => {
  console.log(`Cookie Clicker running at http://localhost:${PORT}`);

  // Self-ping every 14 minutes to prevent Render free tier sleep
  const RENDER_URL = process.env.RENDER_EXTERNAL_URL;
  if (RENDER_URL) {
    setInterval(() => {
      require('http').get(RENDER_URL + '/ping', () => {}).on('error', () => {});
    }, 14 * 60 * 1000);
    console.log(`[KeepAlive] Pinging ${RENDER_URL}/ping every 14 minutes`);
  }
});

// Health check endpoint for keep-alive ping
app.get('/ping', (req, res) => res.sendStatus(200));
