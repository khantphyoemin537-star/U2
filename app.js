// ===========================================================
// Card Market — Mini App frontend. No framework/build step —
// plain JS, since this is a small, single-purpose page served
// directly by the backend in server.py.
// ===========================================================

const tg = window.Telegram?.WebApp;
const INIT_DATA = tg?.initData || "";
const GLOW_TIERS = new Set(['SUPREME', 'CATAPHRACT', 'CROSSVERSE', 'DIVINE']); // holographic treatment

// ---------- Telegram chrome ----------
if (tg) {
  tg.ready();
  tg.expand();
  // Sync our CSS tokens to whatever theme Telegram's client is actually in, so this never
  // looks like a foreign page dropped into the app — only overriding what the client
  // actually provides; our own dark palette stays as the fallback for anything it doesn't.
  const applyTheme = () => {
    const p = tg.themeParams || {};
    const root = document.documentElement.style;
    if (p.bg_color) root.setProperty('--bg', p.bg_color);
    if (p.secondary_bg_color) root.setProperty('--bg-elevated', p.secondary_bg_color);
    if (p.text_color) root.setProperty('--text', p.text_color);
    if (p.hint_color) root.setProperty('--text-dim', p.hint_color);
  };
  applyTheme();
  tg.onEvent('themeChanged', applyTheme);
}

function haptic(style = 'light') {
  try { tg?.HapticFeedback?.impactOccurred(style); } catch (_) {}
}
function notifyHaptic(type = 'success') {
  try { tg?.HapticFeedback?.notificationOccurred(type); } catch (_) {}
}

// ---------- API ----------
async function api(path, { method = 'GET', body } = {}) {
  const res = await fetch(path, {
    method,
    headers: {
      'Content-Type': 'application/json',
      'X-Telegram-Init-Data': INIT_DATA,
    },
    body: body ? JSON.stringify(body) : undefined,
  });
  let data = {};
  try { data = await res.json(); } catch (_) {}
  if (!res.ok) throw new Error(data.detail || `Request failed (${res.status})`);
  return data;
}

// ---------- toast ----------
let toastTimer = null;
function toast(msg) {
  let el = document.getElementById('toast');
  if (!el) {
    el = document.createElement('div');
    el.id = 'toast';
    el.className = 'toast';
    document.body.appendChild(el);
  }
  el.textContent = msg;
  el.classList.add('show');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => el.classList.remove('show'), 2200);
}

// ---------- rarity display ----------
const RARITY_LABEL = {
  SUPREME: 'Supreme', CATAPHRACT: 'Cataphract', CROSSVERSE: 'Crossverse', DIVINE: 'Divine',
  MYSTICAL: 'Mystical', LEGENDARY: 'Legendary', RARE: 'Rare', UNCOMMON: 'Uncommon', COMMON: 'Common',
};

function fmtSeconds(s) {
  if (s == null) return '';
  const h = Math.floor(s / 3600), m = Math.floor((s % 3600) / 60);
  if (h > 0) return `${h}h ${m}m left`;
  if (m > 0) return `${m}m left`;
  return `${s}s left`;
}

const EMPTY_ICON = `<svg width="52" height="52" viewBox="0 0 52 52" fill="none" xmlns="http://www.w3.org/2000/svg">
  <rect x="8" y="14" width="30" height="30" rx="5" transform="rotate(-6 8 14)" stroke="currentColor" stroke-width="1.6"/>
  <rect x="14" y="9" width="30" height="30" rx="5" transform="rotate(6 14 9)" stroke="currentColor" stroke-width="1.6" fill="none"/>
</svg>`;

function renderEmpty(container, text) {
  container.innerHTML = `<div class="empty-state">${EMPTY_ICON}<p class="empty-note">${text}</p></div>`;
}

// ---------- skeleton ----------
function renderSkeleton(grid, count = 6) {
  grid.innerHTML = '';
  for (let i = 0; i < count; i++) {
    const el = document.createElement('div');
    el.className = 'card-tile skel';
    el.style.animationDelay = '0s'; // skeletons appear instantly, no stagger
    el.innerHTML = `
      <div class="card-tile-img-wrap"></div>
      <div class="card-tile-body">
        <div class="skel-line w60"></div>
        <div class="skel-line w40"></div>
      </div>`;
    grid.appendChild(el);
  }
}

// ---------- card tile ----------
function cardTile({ char_id, name, category, rarity_tier, quantity, priceText, priceKind, secondsLeft, extraNote, index, onClick }) {
  const el = document.createElement('div');
  el.className = 'card-tile' + (GLOW_TIERS.has(rarity_tier) ? ' glow' : '');
  el.style.animationDelay = `${Math.min(index, 10) * 0.035}s`;

  let countdownHtml = '';
  if (secondsLeft != null) {
    const urgent = secondsLeft < 3600;
    const pct = Math.max(2, Math.min(100, Math.round((secondsLeft / 86400) * 100)));
    countdownHtml = `
      <div class="countdown-row">
        <div class="countdown-track"><div class="countdown-fill ${urgent ? 'urgent' : ''}" style="width:${pct}%"></div></div>
        <span class="countdown-text ${urgent ? 'urgent' : ''}">${fmtSeconds(secondsLeft)}</span>
      </div>`;
  } else if (extraNote) {
    countdownHtml = `<div class="countdown-row"><span class="countdown-text">${extraNote}</span></div>`;
  }

  el.innerHTML = `
    <div class="card-tile-img-wrap">
      <div class="rarity-bar rarity-${rarity_tier || 'COMMON'}"></div>
      <img src="/api/character-image/${encodeURIComponent(char_id)}" loading="lazy">
      ${quantity ? `<span class="qty-badge">×${quantity}</span>` : ''}
    </div>
    <div class="card-tile-body">
      <div class="card-tile-name">${name || '?'}</div>
      <div class="card-tile-meta">${category || ''}${category ? ' · ' : ''}${RARITY_LABEL[rarity_tier] || rarity_tier || ''}</div>
      ${priceText ? `
        <div class="card-tile-price">
          <span class="price-amount">${priceText}</span>
          <span class="price-tag ${priceKind === 'auction' ? 'auction' : ''}">${priceKind === 'auction' ? 'Bid' : 'Buy'}</span>
        </div>` : ''}
      ${countdownHtml}
    </div>
  `;
  const img = el.querySelector('img');
  img.addEventListener('load', () => img.classList.add('loaded'));
  img.addEventListener('error', () => { img.style.opacity = 0.15; });
  el.addEventListener('click', onClick);
  return el;
}

// ---------- balance ----------
let lastBalance = null;
async function refreshBalance() {
  try {
    const me = await api('/api/me');
    const amountEl = document.getElementById('balance-amount');
    amountEl.textContent = me.ccm_balance.toLocaleString();
    if (lastBalance != null && me.ccm_balance !== lastBalance) {
      const pill = document.querySelector('.balance-pill');
      pill.classList.add('bump');
      setTimeout(() => pill.classList.remove('bump'), 260);
    }
    lastBalance = me.ccm_balance;
    return me;
  } catch (e) { toast(e.message); }
}

// ---------- views ----------
const views = ['market', 'cards', 'listings', 'bids'];

function switchView(name) {
  views.forEach(v => {
    document.getElementById(`view-${v}`).hidden = v !== name;
  });
  document.querySelectorAll('.tab').forEach(t => t.classList.toggle('active', t.dataset.view === name));
  haptic();
  loadView(name);
}

document.querySelectorAll('.tab').forEach(t => t.addEventListener('click', () => switchView(t.dataset.view)));

async function loadView(name) {
  if (name === 'market') return loadMarket();
  if (name === 'cards') return loadMyCards();
  if (name === 'listings') return loadMyListings();
  if (name === 'bids') return loadMyBids();
}

async function loadMarket() {
  const grid = document.getElementById('market-grid');
  renderSkeleton(grid);
  let data;
  try { data = await api('/api/market'); } catch (e) { return toast(e.message); }
  if (!data.listings.length) return renderEmpty(grid, 'Nothing listed right now — check back soon.');
  grid.innerHTML = '';
  data.listings.forEach((l, i) => {
    const isAuction = l.type === 'auction';
    grid.appendChild(cardTile({
      char_id: l.char_id, name: l.name, category: l.category, rarity_tier: l.rarity_tier,
      priceText: `${(isAuction ? l.current_bid : l.price).toLocaleString()} ccm`,
      priceKind: l.type,
      secondsLeft: isAuction ? l.seconds_left : null,
      extraNote: isAuction ? (l.bid_count ? `${l.bid_count} bid${l.bid_count > 1 ? 's' : ''}` : 'No bids yet') : null,
      index: i,
      onClick: () => openMarketSheet(l),
    }));
  });
}

async function loadMyCards() {
  const grid = document.getElementById('cards-grid');
  renderSkeleton(grid);
  let data;
  try { data = await api('/api/my-cards'); } catch (e) { return toast(e.message); }
  if (!data.cards.length) return renderEmpty(grid, 'No spare cards to sell yet — go catch some.');
  grid.innerHTML = '';
  data.cards.forEach((c, i) => {
    grid.appendChild(cardTile({
      char_id: c.char_id, name: c.name, category: c.category, rarity_tier: c.rarity_tier,
      quantity: c.quantity, index: i,
      onClick: () => openMyCardSheet(c),
    }));
  });
}

async function loadMyListings() {
  const grid = document.getElementById('listings-grid');
  renderSkeleton(grid);
  let data;
  try { data = await api('/api/my-listings'); } catch (e) { return toast(e.message); }
  if (!data.listings.length) return renderEmpty(grid, "You don't have anything listed.");
  grid.innerHTML = '';
  data.listings.forEach((l, i) => {
    const isAuction = l.type === 'auction';
    const secondsLeft = l.expires_at ? Math.max(0, Math.round(l.expires_at - Date.now() / 1000)) : null;
    grid.appendChild(cardTile({
      char_id: l.char_id, name: l.char_id, category: '', rarity_tier: null,
      priceText: `${(isAuction ? l.current_bid : l.price).toLocaleString()} ccm`,
      priceKind: l.type,
      secondsLeft: isAuction ? secondsLeft : null,
      extraNote: isAuction ? null : 'Listed',
      index: i,
      onClick: () => openMyListingSheet(l),
    }));
  });
}

async function loadMyBids() {
  const grid = document.getElementById('bids-grid');
  renderSkeleton(grid);
  let data;
  try { data = await api('/api/my-bids'); } catch (e) { return toast(e.message); }
  if (!data.listings.length) return renderEmpty(grid, "You're not leading any auctions.");
  grid.innerHTML = '';
  data.listings.forEach((l, i) => {
    const secondsLeft = l.expires_at ? Math.max(0, Math.round(l.expires_at - Date.now() / 1000)) : null;
    grid.appendChild(cardTile({
      char_id: l.char_id, name: l.char_id, category: '', rarity_tier: null,
      priceText: `${l.current_bid.toLocaleString()} ccm`, priceKind: 'auction',
      secondsLeft, extraNote: 'Leading', index: i,
      onClick: () => openMarketSheet({ ...l, listing_id: l._id }),
    }));
  });
}

// ---------- action sheet ----------
const backdrop = document.getElementById('sheet-backdrop');
const sheet = document.getElementById('sheet');

function closeSheet() { backdrop.hidden = true; sheet.innerHTML = ''; }
backdrop.addEventListener('click', (e) => { if (e.target === backdrop) closeSheet(); });

function openSheet(html) {
  sheet.innerHTML = html;
  backdrop.hidden = false;
  haptic();
}

function heroBlock(char_id, name, meta) {
  return `
    <div class="sheet-hero">
      <div class="sheet-hero-img"><img src="/api/character-image/${encodeURIComponent(char_id)}"></div>
      <div class="sheet-hero-info"><h2>${name}</h2><div class="meta">${meta}</div></div>
    </div>`;
}

// Buy / Bid on a market listing
function openMarketSheet(l) {
  const isAuction = l.type === 'auction';
  const minBid = l.current_bid + (l.bid_count ? 1 : 0);
  openSheet(`
    ${heroBlock(l.char_id, l.name || l.char_id, `${l.category || ''} · ${RARITY_LABEL[l.rarity_tier] || ''}`)}
    ${isAuction ? `
      <div class="field-label">Current bid</div>
      <div class="card-tile-price"><span class="price-amount">${l.current_bid.toLocaleString()} ccm</span></div>
      <div class="field-label">Your bid (ccm)</div>
      <input class="field-input" id="bid-amount" type="number" inputmode="numeric" min="${minBid}" placeholder="${minBid.toLocaleString()} or more">
      <button class="btn btn-primary" id="sheet-action">Place bid</button>
    ` : `
      <div class="field-label">Price</div>
      <div class="card-tile-price"><span class="price-amount">${l.price.toLocaleString()} ccm</span></div>
      <button class="btn btn-primary" id="sheet-action">Buy now</button>
    `}
    <button class="btn btn-ghost" id="sheet-cancel">Close</button>
  `);
  document.getElementById('sheet-cancel').onclick = closeSheet;
  document.getElementById('sheet-action').onclick = async () => {
    try {
      if (isAuction) {
        const amount = parseInt(document.getElementById('bid-amount').value, 10);
        if (!amount || amount < minBid) return toast(`Bid at least ${minBid.toLocaleString()} ccm`);
        await api('/api/market/bid', { method: 'POST', body: { listing_id: l.listing_id, amount } });
        toast('Bid placed!');
      } else {
        await api('/api/market/buy', { method: 'POST', body: { listing_id: l.listing_id } });
        toast('Bought!');
      }
      notifyHaptic('success');
      closeSheet();
      refreshBalance();
      loadMarket();
    } catch (e) { notifyHaptic('error'); toast(e.message); }
  };
}

// Sell / Auction / Scrap one of your own cards
function openMyCardSheet(c) {
  let mode = 'sell';
  const render = () => `
    ${heroBlock(c.char_id, c.name, `${c.category} · ${RARITY_LABEL[c.rarity_tier] || ''} · ${c.quantity} spare${c.quantity > 1 ? 's' : ''}`)}
    <div class="segmented">
      <button data-m="sell" class="${mode === 'sell' ? 'active' : ''}">Sell</button>
      <button data-m="auction" class="${mode === 'auction' ? 'active' : ''}">Auction</button>
      ${c.scrappable ? `<button data-m="scrap" class="${mode === 'scrap' ? 'active' : ''}">Scrap</button>` : ''}
    </div>
    ${mode !== 'scrap' ? `
      <div class="field-label">${mode === 'auction' ? 'Starting bid (ccm)' : 'Price (ccm)'}</div>
      <input class="field-input" id="list-price" type="number" inputmode="numeric" min="1" placeholder="e.g. 500">
      ${mode === 'auction' ? '<div class="field-label">Runs for 24 hours — highest bid wins.</div>' : ''}
      <button class="btn btn-primary" id="sheet-action">${mode === 'auction' ? 'Start auction' : 'List for sale'}</button>
    ` : `
      <div class="field-label">Burns one copy for ¼ of its usual value — Divine and rarer can't be scrapped, only sold or auctioned.</div>
      <button class="btn btn-danger" id="sheet-action">Scrap one copy</button>
    `}
    <button class="btn btn-ghost" id="sheet-cancel">Close</button>
  `;
  openSheet(render());
  const wire = () => {
    document.querySelectorAll('.segmented button').forEach(b => b.onclick = () => { mode = b.dataset.m; openSheet(render()); wire(); });
    document.getElementById('sheet-cancel').onclick = closeSheet;
    document.getElementById('sheet-action').onclick = async () => {
      try {
        if (mode === 'scrap') {
          const res = await api('/api/market/scrap', { method: 'POST', body: { char_id: c.char_id } });
          toast(res.ccm_earned > 0 ? `Scrapped for ${res.ccm_earned.toLocaleString()} ccm` : 'Scrapped (not priced yet — 0 ccm)');
        } else {
          const price = parseInt(document.getElementById('list-price').value, 10);
          if (!price || price < 1) return toast('Enter a price first.');
          await api('/api/market/list', { method: 'POST', body: { char_id: c.char_id, type: mode === 'auction' ? 'auction' : 'buy_now', price } });
          toast(mode === 'auction' ? 'Auction started!' : 'Listed for sale!');
        }
        notifyHaptic('success');
        closeSheet();
        refreshBalance();
        loadMyCards();
      } catch (e) { notifyHaptic('error'); toast(e.message); }
    };
  };
  wire();
}

// Cancel your own listing
function openMyListingSheet(l) {
  const isAuction = l.type === 'auction';
  const hasBid = !!l.current_bidder_id;
  openSheet(`
    ${heroBlock(l.char_id, l.char_id, isAuction ? `Auction · current bid ${l.current_bid.toLocaleString()} ccm` : `Listed · ${l.price.toLocaleString()} ccm`)}
    ${isAuction && hasBid ? `<div class="field-label">Can't cancel — this auction already has a bid. It'll settle automatically when the 24h ends.</div>` : `
      <button class="btn btn-danger" id="sheet-action">Cancel listing</button>
    `}
    <button class="btn btn-ghost" id="sheet-cancel">Close</button>
  `);
  document.getElementById('sheet-cancel').onclick = closeSheet;
  const actionBtn = document.getElementById('sheet-action');
  if (actionBtn) actionBtn.onclick = async () => {
    try {
      await api('/api/market/cancel', { method: 'POST', body: { listing_id: l._id } });
      toast('Listing cancelled.');
      notifyHaptic('success');
      closeSheet();
      loadMyListings();
    } catch (e) { notifyHaptic('error'); toast(e.message); }
  };
}

// ---------- boot ----------
(async function init() {
  await refreshBalance();
  await loadMarket();
  // Keep countdowns and listing states fresh without the user having to pull-to-refresh —
  // a live auction floor that visibly goes stale reads as broken.
  setInterval(() => {
    const active = views.find(v => !document.getElementById(`view-${v}`).hidden);
    loadView(active);
    refreshBalance();
  }, 20000);
})();
