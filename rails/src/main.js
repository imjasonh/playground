import initWasm, { WasmEngine } from "../vendor/rails_engine/rails_server.js";
import { BoardRenderer } from "./renderer.js";
import { RoomClient } from "./net.js";
import {
  isSoundEnabled,
  playBuildClick,
  playDeliverChime,
  playTurnChime,
  playVictoryFanfare,
  setSoundEnabled,
} from "./sound.js";

const COLORS = ["#e11d48", "#2563eb", "#16a34a", "#d97706", "#9333ea", "#0891b2"];

const els = {
  canvas: document.getElementById("board-canvas"),
  tooltip: document.getElementById("map-tooltip"),
  toast: document.getElementById("toast"),
  modeBadge: document.getElementById("mode-badge"),
  roomBadge: document.getElementById("room-badge"),
  turnDot: document.getElementById("turn-dot"),
  turnText: document.getElementById("turn-text"),
  btnUndo: document.getElementById("btn-undo"),
  btnPitch: document.getElementById("btn-pitch"),
  btnPrimary: document.getElementById("btn-primary-action"),
  btnDirectory: document.getElementById("btn-directory"),
  btnSound: document.getElementById("btn-sound"),
  btnMenu: document.getElementById("btn-menu"),
  btnZoomIn: document.getElementById("btn-zoom-in"),
  btnZoomOut: document.getElementById("btn-zoom-out"),
  btnZoomFit: document.getElementById("btn-zoom-fit"),
  scoreboard: document.getElementById("scoreboard"),
  victoryTarget: document.getElementById("victory-target"),
  eventsSection: document.getElementById("events-section"),
  activeEvents: document.getElementById("active-events"),
  trainPanel: document.getElementById("train-panel"),
  moveCounter: document.getElementById("move-counter"),
  cardsTitle: document.getElementById("cards-title"),
  deckCounter: document.getElementById("deck-counter"),
  cardsList: document.getElementById("cards-list"),
  turnLog: document.getElementById("turn-log"),
  lobbyModal: document.getElementById("lobby-modal"),
  tabLocal: document.getElementById("tab-local"),
  tabOnline: document.getElementById("tab-online"),
  panelLocal: document.getElementById("panel-local"),
  panelOnline: document.getElementById("panel-online"),
  localMode: document.getElementById("local-mode"),
  localEvents: document.getElementById("local-events"),
  localSeats: document.getElementById("local-seats"),
  btnAddHuman: document.getElementById("btn-add-human"),
  btnAddBot: document.getElementById("btn-add-bot"),
  btnStartLocal: document.getElementById("btn-start-local"),
  onlineName: document.getElementById("online-name"),
  onlineRoom: document.getElementById("online-room"),
  onlineServer: document.getElementById("online-server"),
  onlineConnectActions: document.getElementById("online-connect-actions"),
  btnOnlineConnect: document.getElementById("btn-online-connect"),
  onlineLobbyView: document.getElementById("online-lobby-view"),
  onlineRoomCode: document.getElementById("online-room-code"),
  onlineMode: document.getElementById("online-mode"),
  onlineEvents: document.getElementById("online-events"),
  onlineSeats: document.getElementById("online-seats"),
  btnOnlineAddBot: document.getElementById("btn-online-add-bot"),
  btnCopyInvite: document.getElementById("btn-copy-invite"),
  btnOnlineStart: document.getElementById("btn-online-start"),
  directoryModal: document.getElementById("directory-modal"),
  directoryGrid: document.getElementById("directory-grid"),
  btnCloseDirectory: document.getElementById("btn-close-directory"),
  victoryModal: document.getElementById("victory-modal"),
  victoryTitle: document.getElementById("victory-title"),
  victorySubtitle: document.getElementById("victory-subtitle"),
  victoryStandings: document.getElementById("victory-standings"),
  btnVictoryInspect: document.getElementById("btn-victory-inspect"),
  btnVictoryNew: document.getElementById("btn-victory-new"),
};

const app = {
  engine: null,
  mapData: null,
  renderer: null,
  sessionType: "local", // "local" | "online"
  roomClient: null,
  mySlot: null, // null in local hotseat (control any non-bot) or spectator online
  state: null,
  majorProgress: [],
  reachableSet: new Set(),
  hoveredMp: null,
  localPreview: null,
  remoteDraft: null,
  highlight: null, // { commodity, destCityId }
  trimSelected: new Set(),
  aiTimer: null,
  toastTimer: null,
  localSeatDraft: [
    { name: "You", color: COLORS[0], is_bot: false },
    { name: "RailBot 1", color: COLORS[1], is_bot: true },
    { name: "RailBot 2", color: COLORS[2], is_bot: true },
  ],
};

function showToast(msg, isError = false) {
  els.toast.textContent = msg;
  els.toast.classList.toggle("error", isError);
  els.toast.classList.remove("hidden");
  clearTimeout(app.toastTimer);
  app.toastTimer = setTimeout(() => els.toast.classList.add("hidden"), 2800);
}

function canControlCurrentPlayer() {
  if (!app.state || app.state.phase === "finished") return false;
  const cur = app.state.players[app.state.current_player];
  if (!cur || cur.is_bot) return false;
  if (app.sessionType === "online") {
    return app.mySlot === cur.id;
  }
  return true;
}

function activeViewPlayerId() {
  if (!app.state) return 0;
  if (app.sessionType === "online" && app.mySlot !== null) {
    return app.mySlot;
  }
  return app.state.current_player;
}

function draw() {
  if (!app.renderer) return;
  app.renderer.render({
    state: app.state,
    reachableSet: canControlCurrentPlayer() && app.state?.phase === "operate" ? app.reachableSet : null,
    hoveredMp: app.hoveredMp,
    localPreview: app.localPreview,
    remoteDraft: app.remoteDraft,
    highlight: app.highlight,
  });
}

function updateGameState(newState, { playSounds = true } = {}) {
  const prevTurnPlayer = app.state?.current_player;
  const prevDeliveries = app.state?.players.reduce((s, p) => s + p.deliveries_completed, 0) ?? 0;
  const prevWinner = app.state?.winner;

  app.state = newState;
  app.localPreview = null;
  app.remoteDraft = null;
  app.trimSelected.clear();

  if (app.sessionType === "online") {
    app.engine.set_remote_state(JSON.stringify(newState));
  }

  try {
    app.majorProgress = JSON.parse(app.engine.major_city_progress_json());
  } catch {
    app.majorProgress = newState.players.map(() => []);
  }

  if (newState.phase === "operate" && newState.players[newState.current_player]?.train_pos != null) {
    try {
      const list = JSON.parse(app.engine.reachable_mileposts_json(newState.current_player));
      app.reachableSet = new Set(list);
    } catch {
      app.reachableSet = new Set();
    }
  } else {
    app.reachableSet = new Set();
  }

  if (playSounds) {
    const newDeliveries = newState.players.reduce((s, p) => s + p.deliveries_completed, 0);
    if (newState.winner != null && prevWinner == null) {
      playVictoryFanfare();
    } else if (newDeliveries > prevDeliveries) {
      playDeliverChime();
    } else if (prevTurnPlayer !== undefined && prevTurnPlayer !== newState.current_player && canControlCurrentPlayer()) {
      playTurnChime();
    }
  }

  renderHud();
  draw();

  if (newState.winner != null && prevWinner == null) {
    showVictoryModal();
  }

  scheduleLocalAiIfNeeded();
}

function scheduleLocalAiIfNeeded() {
  clearTimeout(app.aiTimer);
  if (app.sessionType !== "local" || !app.state || app.state.phase === "finished") return;
  const cur = app.state.players[app.state.current_player];
  if (cur?.is_bot) {
    app.aiTimer = setTimeout(() => {
      try {
        const nextJson = app.engine.step_local_ai();
        updateGameState(JSON.parse(nextJson));
      } catch (err) {
        showToast(`RailBot error: ${err}`, true);
      }
    }, 320);
  }
}

function sendAction(action) {
  if (!canControlCurrentPlayer()) return;
  const pid = app.state.current_player;
  if (app.sessionType === "online") {
    app.roomClient.send({ type: "game_action", action });
  } else {
    try {
      const nextJson = app.engine.apply_local_action(pid, JSON.stringify(action));
      if (action.type === "build_track") playBuildClick();
      updateGameState(JSON.parse(nextJson));
    } catch (err) {
      showToast(String(err), true);
    }
  }
}

function renderHud() {
  const s = app.state;
  if (!s) return;

  const cur = s.players[s.current_player];
  const mine = canControlCurrentPlayer();
  const modeLabel = s.config.mode === "fast" ? "Fast" : "Standard";
  els.modeBadge.textContent = `${modeLabel}${s.config.events_enabled ? " + Events" : ""}`;
  els.victoryTarget.textContent = `Win: ${s.config.victory_major_cities} Majors + $${s.config.victory_cash}M`;

  // Top turn banner
  els.turnDot.style.background = cur.color;
  const phaseText = (() => {
    if (s.phase === "finished") return `${s.players[s.winner]?.name ?? "Someone"} Wins!`;
    if (s.phase === "initial_build") {
      const rem = 20 - s.turn_tracker.build_spent;
      return `Initial Build ${s.initial_round}/${s.config.mode === "fast" ? 3 : 2} — $${rem}M left`;
    }
    if (s.phase === "trim_hand") return `Trim Hand (discard ${cur.hand.length - 3} to keep 3)`;
    if (s.phase === "operate") {
      if (cur.train_pos == null) return "Place Locomotive at any City";
      const maxSpd = trainSpeed(cur.train_tier, s.config.mode);
      return `Operate (${s.turn_tracker.moves_used}/${maxSpd} moves)`;
    }
    if (s.phase === "build") {
      const rem = 20 - s.turn_tracker.build_spent;
      return `Build Track / Upgrade ($${rem}M left)`;
    }
    return s.phase;
  })();
  els.turnText.textContent = `Turn ${s.turn_number} · ${cur.name}: ${phaseText}`;

  // Action buttons
  els.btnUndo.disabled = !mine || !s.turn_tracker.can_undo;
  els.btnPitch.style.display = mine && s.phase === "operate" && !s.turn_tracker.has_acted_this_turn ? "" : "none";

  if (s.phase === "operate") {
    els.btnPrimary.textContent = "Finish Moving → Build";
    els.btnPrimary.disabled = !mine;
    els.btnPrimary.className = "primary";
  } else if (s.phase === "trim_hand") {
    const need = cur.hand.length - 3;
    els.btnPrimary.textContent = `Discard ${app.trimSelected.size}/${need} & Keep 3`;
    els.btnPrimary.disabled = !mine || app.trimSelected.size !== need;
    els.btnPrimary.className = "success";
  } else if (s.phase === "finished") {
    els.btnPrimary.textContent = "Game Over";
    els.btnPrimary.disabled = true;
  } else {
    els.btnPrimary.textContent = "End Turn";
    els.btnPrimary.disabled = !mine;
    els.btnPrimary.className = "success";
  }

  // Scoreboard
  els.scoreboard.innerHTML = "";
  s.players.forEach((p, idx) => {
    const majors = app.majorProgress[idx]?.length ?? 0;
    const row = document.createElement("div");
    row.className = `player-row${p.id === s.current_player ? " active" : ""}`;
    row.innerHTML = `
      <div class="player-info">
        <span class="color-dot" style="background:${p.color}"></span>
        <span class="player-name" title="${escapeHtml(p.name)}">${escapeHtml(p.name)}${p.is_bot ? " 🤖" : ""}</span>
      </div>
      <div class="player-stats">
        <span title="Train">${shortTier(p.train_tier)}</span>
        <span class="stat-majors" title="Connected Major Cities">⬡${majors}/${s.config.victory_major_cities}</span>
        <span class="stat-cash">$${p.cash}M${p.debt ? ` (-$${p.debt}M)` : ""}</span>
      </div>
    `;
    els.scoreboard.appendChild(row);
  });

  // Active Events
  if (s.active_events.length > 0) {
    els.eventsSection.style.display = "";
    els.activeEvents.innerHTML = s.active_events
      .map((ev) => `<div class="event-banner"><strong>⚠ ${escapeHtml(ev.title)}</strong>${escapeHtml(ev.description)}</div>`)
      .join("");
  } else {
    els.eventsSection.style.display = "none";
  }

  // Locomotive & Cargo panel (for viewed player)
  const vp = s.players[activeViewPlayerId()];
  const isVpTurn = mine && vp.id === s.current_player;
  const maxSpd = trainSpeed(vp.train_tier, s.config.mode);
  const cap = trainCapacity(vp.train_tier);
  els.moveCounter.textContent = `${tierLabel(vp.train_tier)} · ${maxSpd} mp/turn`;

  const curCity = vp.train_pos != null ? app.renderer.cityById.get(app.renderer.mpById.get(vp.train_pos)?.city_id) : null;
  let trainHtml = `
    <div class="train-header">
      <span><b style="color:${vp.color}">●</b> ${escapeHtml(vp.name)}</span>
      <span style="color:var(--muted);font-size:12px">${curCity ? `At ${escapeHtml(curCity.name)}` : vp.train_pos != null ? `Milepost #${vp.train_pos}` : "Not placed"}</span>
    </div>
    <div class="cargo-slots">
  `;
  for (let i = 0; i < cap; i++) {
    const commId = vp.cargo[i];
    if (commId) {
      const c = app.renderer.commById.get(commId);
      const canDrop = isVpTurn && s.phase === "operate" && curCity;
      trainHtml += `<button class="cargo-chip" data-drop-slot="${i}" ${canDrop ? "" : "disabled"} style="border-color:${c?.color ?? "#94a3b8"}" title="Click to drop at city">
        <span class="comm-pill" style="background:${c?.color ?? "#475569"}">${c?.short ?? commId}</span> ${escapeHtml(c?.name ?? commId)}${canDrop ? " ×" : ""}
      </button>`;
    } else {
      trainHtml += `<span class="cargo-chip empty">Empty Hold</span>`;
    }
  }
  trainHtml += `</div>`;

  // Pickup buttons when at a producing city
  if (isVpTurn && s.phase === "operate" && curCity && curCity.commodities.length > 0) {
    trainHtml += `<div style="font-size:11px;color:var(--muted);margin-bottom:4px">Pick up at ${escapeHtml(curCity.name)}:</div><div class="city-goods">`;
    for (const cid of curCity.commodities) {
      const c = app.renderer.commById.get(cid);
      const left = s.chip_supply[cid] ?? 0;
      const disabled = vp.cargo.length >= cap || left <= 0;
      trainHtml += `<button class="small" data-pickup="${cid}" ${disabled ? "disabled" : ""}>+ ${escapeHtml(c?.name ?? cid)} (${left})</button>`;
    }
    trainHtml += `</div>`;
  }

  // Heating Fuel Shortage bonus delivery button
  if (isVpTurn && s.phase === "operate" && curCity) {
    for (const ev of s.active_events) {
      if (ev.effect.type === "heating_fuel_shortage" && ev.effect.target_cities.includes(curCity.id)) {
        const slot = vp.cargo.findIndex((c) => c === ev.effect.commodity || c === "coal");
        if (slot >= 0) {
          trainHtml += `<div class="upgrade-row"><button class="success small" data-deliver-event="${ev.card_id}" data-slot="${slot}">🔥 Fulfill ${escapeHtml(ev.title)} (+$${ev.effect.bonus}M)</button></div>`;
        }
      }
    }
  }

  // Upgrade Train buttons during Build phase
  if (isVpTurn && s.phase === "build" && s.turn_tracker.build_spent === 0 && !s.turn_tracker.upgraded_this_turn) {
    const upgrades = nextUpgrades(vp.train_tier);
    if (upgrades.length > 0) {
      trainHtml += `<div class="upgrade-row">`;
      for (const u of upgrades) {
        trainHtml += `<button class="small primary" data-upgrade="${u}" ${vp.cash < 20 ? "disabled" : ""}>⬆ ${tierLabel(u)} ($20M)</button>`;
      }
      trainHtml += `</div>`;
    }
  }

  // Emergency borrow option if cash < $10M and debt == 0
  if (isVpTurn && (s.phase === "build" || s.phase === "operate") && vp.cash < 10 && vp.debt === 0) {
    trainHtml += `<div class="upgrade-row"><button class="small warn" data-borrow="15">🏦 Emergency Loan +$15M (repay $30M)</button></div>`;
  }

  els.trainPanel.innerHTML = trainHtml;

  // Bind dynamic train panel buttons
  els.trainPanel.querySelectorAll("[data-pickup]").forEach((btn) => {
    btn.addEventListener("click", () => sendAction({ type: "pickup_load", commodity: btn.dataset.pickup }));
  });
  els.trainPanel.querySelectorAll("[data-drop-slot]").forEach((btn) => {
    btn.addEventListener("click", () => sendAction({ type: "drop_load", slot: Number(btn.dataset.dropSlot) }));
  });
  els.trainPanel.querySelectorAll("[data-upgrade]").forEach((btn) => {
    btn.addEventListener("click", () => sendAction({ type: "upgrade_train", target_tier: btn.dataset.upgrade }));
  });
  els.trainPanel.querySelectorAll("[data-borrow]").forEach((btn) => {
    btn.addEventListener("click", () => sendAction({ type: "borrow", amount: Number(btn.dataset.borrow) }));
  });
  els.trainPanel.querySelectorAll("[data-deliver-event]").forEach((btn) => {
    btn.addEventListener("click", () =>
      sendAction({
        type: "deliver_event_bonus",
        slot: Number(btn.dataset.slot),
        event_card_id: Number(btn.dataset.deliverEvent),
      })
    );
  });

  // Demand Cards
  els.deckCounter.textContent = `Deck: ${s.draw_pile_count}`;
  els.cardsTitle.textContent =
    s.phase === "trim_hand" && isVpTurn
      ? `Click ${vp.hand.length - 3} card(s) to discard`
      : `${vp.name}'s Demand Cards (hover to locate)`;

  els.cardsList.innerHTML = "";
  vp.hand.forEach((card, ci) => {
    if (card.kind !== "demand") return;
    const cardEl = document.createElement("div");
    cardEl.className = `demand-card${app.trimSelected.has(ci) ? " trim-selected" : ""}`;
    if (s.phase === "trim_hand" && isVpTurn) {
      cardEl.style.cursor = "pointer";
      cardEl.addEventListener("click", () => {
        if (app.trimSelected.has(ci)) app.trimSelected.delete(ci);
        else if (app.trimSelected.size < vp.hand.length - 3) app.trimSelected.add(ci);
        renderHud();
      });
    }

    let html = `<div class="demand-card-header"><span>Contract #${card.id}</span><span>Payoff</span></div>`;
    card.demands.forEach((d, di) => {
      const comm = app.renderer.commById.get(d.commodity);
      const destCity = app.renderer.cityById.get(d.city_id);
      const matchingSlot =
        isVpTurn && s.phase === "operate" && curCity && curCity.id === d.city_id
          ? vp.cargo.findIndex((c) => c === d.commodity)
          : -1;
      const deliverable = matchingSlot >= 0;

      html += `
        <div class="demand-row${deliverable ? " deliverable" : ""}" data-ci="${ci}" data-di="${di}" data-comm="${d.commodity}" data-dest="${d.city_id}" data-slot="${matchingSlot}">
          <div class="demand-left">
            <span class="comm-pill" style="background:${comm?.color ?? "#475569"}">${comm?.short ?? d.commodity}</span>
            <span><b>${escapeHtml(comm?.name ?? d.commodity)}</b> → ${escapeHtml(destCity?.name ?? d.city_id)}</span>
          </div>
          <span class="demand-payout">${deliverable ? `✓ Deliver $${d.payout}M` : `$${d.payout}M`}</span>
        </div>
      `;
    });
    cardEl.innerHTML = html;

    cardEl.querySelectorAll(".demand-row").forEach((row) => {
      row.addEventListener("mouseenter", () => {
        app.highlight = { commodity: row.dataset.comm, destCityId: row.dataset.dest };
        draw();
      });
      row.addEventListener("mouseleave", () => {
        app.highlight = null;
        draw();
      });
      row.addEventListener("click", (ev) => {
        const slot = Number(row.dataset.slot);
        if (slot >= 0) {
          ev.stopPropagation();
          sendAction({
            type: "deliver_load",
            slot,
            card_index: Number(row.dataset.ci),
            demand_index: Number(row.dataset.di),
          });
        }
      });
    });

    els.cardsList.appendChild(cardEl);
  });

  // Turn Log (newest first)
  els.turnLog.innerHTML = [...s.log]
    .reverse()
    .slice(0, 30)
    .map((entry) => `<div class="log-item"><b>T${entry.turn}</b> ${escapeHtml(entry.text)}</div>`)
    .join("");
}

function showVictoryModal() {
  const s = app.state;
  if (!s || s.winner == null) return;
  const w = s.players[s.winner];
  els.victoryTitle.textContent = `🏆 ${w.name} Wins!`;
  els.victorySubtitle.textContent = `Connected ${app.majorProgress[w.id]?.length ?? 5} Major Cities with $${w.cash}M in ${s.turn_number} turns.`;
  const sorted = [...s.players].sort((a, b) => b.cash - a.cash);
  els.victoryStandings.innerHTML = sorted
    .map(
      (p, i) => `
      <div class="seat-item">
        <b>#${i + 1}</b>
        <span class="color-dot" style="background:${p.color}"></span>
        <span style="flex:1"><b>${escapeHtml(p.name)}</b> (${tierLabel(p.train_tier)})</span>
        <span>⬡${app.majorProgress[p.id]?.length ?? 0} Majors</span>
        <span class="stat-cash">$${p.cash}M</span>
        <span style="color:var(--muted)">${p.deliveries_completed} del.</span>
      </div>`
    )
    .join("");
  els.victoryModal.classList.remove("hidden");
}

// --- Canvas Interaction (Pan / Zoom / Hover Preview / Click Action) ---
function setupCanvasInteraction() {
  let dragging = false;
  let moved = false;
  let lastX = 0;
  let lastY = 0;

  els.canvas.addEventListener("mousedown", (e) => {
    if (e.button !== 0) return;
    dragging = true;
    moved = false;
    lastX = e.clientX;
    lastY = e.clientY;
    els.canvas.classList.add("dragging");
  });

  window.addEventListener("mouseup", () => {
    dragging = false;
    els.canvas.classList.remove("dragging");
  });

  els.canvas.addEventListener("mousemove", (e) => {
    const rect = els.canvas.getBoundingClientRect();
    const sx = e.clientX - rect.left;
    const sy = e.clientY - rect.top;

    if (dragging) {
      const dx = e.clientX - lastX;
      const dy = e.clientY - lastY;
      if (Math.hypot(dx, dy) > 3) moved = true;
      lastX = e.clientX;
      lastY = e.clientY;
      app.renderer.panBy(dx, dy);
      draw();
      return;
    }

    const mp = app.renderer.hitTestMilepost(sx, sy);
    if (mp?.id === app.hoveredMp?.id) {
      positionTooltip(sx, sy);
      return;
    }
    app.hoveredMp = mp;
    app.localPreview = null;

    if (!mp) {
      els.tooltip.classList.add("hidden");
      els.canvas.classList.remove("pointing");
      if (app.sessionType === "online" && canControlCurrentPlayer()) {
        app.roomClient?.sendDraft([], []);
      }
      draw();
      return;
    }

    els.canvas.classList.add("pointing");
    const city = mp.city_id ? app.renderer.cityById.get(mp.city_id) : null;
    let tip = city
      ? `<b>${escapeHtml(city.name)}</b> (${city.size} city)<br/>Produces: ${city.commodities.map((c) => app.renderer.commById.get(c)?.name ?? c).join(", ")}`
      : `<b>Milepost #${mp.id}</b> (${mp.terrain})`;

    if (canControlCurrentPlayer() && app.state) {
      const pid = app.state.current_player;
      if (app.state.phase === "initial_build" || app.state.phase === "build") {
        try {
          const prev = JSON.parse(app.engine.preview_build(pid, mp.id));
          app.localPreview = prev;
          if (prev.edges.length > 0) {
            tip += `<br/><span style="color:${prev.affordable ? "#4ade80" : "#f87171"}">Build ${prev.edges.length} seg: <b>$${prev.total_cost}M</b>${prev.error ? ` (${escapeHtml(prev.error)})` : ""}</span>`;
          } else if (prev.error) {
            tip += `<br/><span style="color:var(--muted)">${escapeHtml(prev.error)}</span>`;
          }
          if (app.sessionType === "online") {
            app.roomClient?.sendDraft(prev.affordable ? prev.edges : [], []);
          }
        } catch {
          // ignore
        }
      } else if (app.state.phase === "operate") {
        const cur = app.state.players[pid];
        if (cur.train_pos == null) {
          tip += city
            ? `<br/><span style="color:#4ade80">Click to place locomotive at ${escapeHtml(city.name)}</span>`
            : `<br/><span style="color:#f87171">Click a city to place your locomotive</span>`;
        } else {
          try {
            const prev = JSON.parse(app.engine.preview_move(pid, mp.id));
            if (prev.reachable && prev.hops > 0) {
              app.localPreview = { path: prev.path, affordable: true };
              tip += `<br/><span style="color:#38bdf8">Move <b>${prev.hops}</b> milepost(s)${prev.additional_fee ? ` (+$${prev.additional_fee}M trackage)` : ""}</span>`;
              if (app.sessionType === "online") {
                app.roomClient?.sendDraft([], prev.path);
              }
            }
          } catch {
            // ignore
          }
        }
      }
    }

    els.tooltip.innerHTML = tip;
    els.tooltip.classList.remove("hidden");
    positionTooltip(sx, sy);
    draw();
  });

  els.canvas.addEventListener("click", (e) => {
    if (moved || !canControlCurrentPlayer() || !app.state) return;
    const rect = els.canvas.getBoundingClientRect();
    const mp = app.renderer.hitTestMilepost(e.clientX - rect.left, e.clientY - rect.top);
    if (!mp) return;

    const pid = app.state.current_player;
    const phase = app.state.phase;

    if (phase === "initial_build" || phase === "build") {
      try {
        const prev = JSON.parse(app.engine.preview_build(pid, mp.id));
        if (prev.edges.length > 0 && prev.affordable) {
          sendAction({ type: "build_track", edges: prev.edges });
        } else if (prev.error) {
          showToast(prev.error, true);
        }
      } catch (err) {
        showToast(String(err), true);
      }
    } else if (phase === "operate") {
      const cur = app.state.players[pid];
      if (cur.train_pos == null) {
        if (mp.city_id) {
          sendAction({ type: "place_train", milepost: mp.id });
        } else {
          showToast("Click any city to place your locomotive", true);
        }
      } else {
        try {
          const prev = JSON.parse(app.engine.preview_move(pid, mp.id));
          if (prev.reachable && prev.path.length >= 2) {
            sendAction({ type: "move_train", path: prev.path });
          } else if (prev.error) {
            showToast(prev.error, true);
          }
        } catch (err) {
          showToast(String(err), true);
        }
      }
    }
  });

  els.canvas.addEventListener(
    "wheel",
    (e) => {
      e.preventDefault();
      const rect = els.canvas.getBoundingClientRect();
      const factor = e.deltaY < 0 ? 1.12 : 0.89;
      app.renderer.zoomAt(e.clientX - rect.left, e.clientY - rect.top, factor);
      draw();
    },
    { passive: false }
  );

  window.addEventListener("resize", () => {
    app.renderer?.resize();
    draw();
  });
}

function positionTooltip(sx, sy) {
  els.tooltip.style.left = `${Math.min(sx + 16, els.canvas.clientWidth - 265)}px`;
  els.tooltip.style.top = `${Math.max(12, sy - 14)}px`;
}

// --- Lobby & Modals ---
function renderLocalSeats() {
  els.localSeats.innerHTML = "";
  app.localSeatDraft.forEach((seat, idx) => {
    const row = document.createElement("div");
    row.className = "seat-item";
    row.innerHTML = `
      <span class="color-dot" style="background:${seat.color}"></span>
      <input type="text" value="${escapeHtml(seat.name)}" maxlength="20" />
      <span class="badge">${seat.is_bot ? "RailBot" : "Human"}</span>
      <button class="small" ${app.localSeatDraft.length <= 2 ? "disabled" : ""}>×</button>
    `;
    row.querySelector("input").addEventListener("input", (e) => {
      seat.name = e.target.value;
    });
    row.querySelector("button").addEventListener("click", () => {
      app.localSeatDraft.splice(idx, 1);
      renderLocalSeats();
    });
    els.localSeats.appendChild(row);
  });
}

function renderOnlineLobby(lobby) {
  els.onlineRoomCode.textContent = lobby.code;
  els.onlineMode.value = lobby.config.mode;
  els.onlineEvents.value = lobby.config.events_enabled ? "on" : "off";
  els.onlineSeats.innerHTML = lobby.seats
    .map(
      (s) => `
      <div class="seat-item">
        <span class="color-dot" style="background:${s.color}"></span>
        <span style="flex:1"><b>${escapeHtml(s.name)}</b> ${s.slot === app.mySlot ? "(You)" : ""}</span>
        <span class="badge">${s.is_bot ? "RailBot" : s.connected ? "Online" : "Offline"}</span>
        ${s.is_bot ? `<button class="small" data-rm-bot="${s.slot}">×</button>` : ""}
      </div>`
    )
    .join("");
  els.onlineSeats.querySelectorAll("[data-rm-bot]").forEach((btn) => {
    btn.addEventListener("click", () => {
      app.roomClient?.send({ type: "remove_bot", slot: Number(btn.dataset.rmBot) });
    });
  });
  els.roomBadge.textContent = `ROOM ${lobby.code} 📋`;
  els.roomBadge.style.display = "";
}

function buildDirectory() {
  els.directoryGrid.innerHTML = "";
  for (const c of app.mapData.commodities) {
    const srcs = (app.renderer.sourcesByComm.get(c.id) || []).map((x) => x.name).join(", ");
    const left = app.state?.chip_supply?.[c.id] ?? c.chips;
    const div = document.createElement("div");
    div.className = "dir-item";
    div.style.cursor = "pointer";
    div.innerHTML = `
      <div style="display:flex;justify-content:space-between;margin-bottom:3px">
        <span><span class="comm-pill" style="background:${c.color}">${c.short}</span> <b>${escapeHtml(c.name)}</b></span>
        <span style="color:var(--muted)">${left}/${c.chips} chips</span>
      </div>
      <div style="color:var(--muted);font-size:11px">${escapeHtml(srcs)}</div>
    `;
    div.addEventListener("click", () => {
      app.highlight = { commodity: c.id, destCityId: null };
      els.directoryModal.classList.add("hidden");
      showToast(`Highlighted ${c.name} sources on map`);
      draw();
    });
    els.directoryGrid.appendChild(div);
  }
}

function setupControls() {
  els.tabLocal.addEventListener("click", () => {
    els.tabLocal.classList.add("active");
    els.tabOnline.classList.remove("active");
    els.panelLocal.style.display = "";
    els.panelOnline.style.display = "none";
  });
  els.tabOnline.addEventListener("click", () => {
    els.tabOnline.classList.add("active");
    els.tabLocal.classList.remove("active");
    els.panelOnline.style.display = "";
    els.panelLocal.style.display = "none";
  });

  els.btnAddHuman.addEventListener("click", () => {
    if (app.localSeatDraft.length >= 6) return;
    const i = app.localSeatDraft.length;
    app.localSeatDraft.push({ name: `Player ${i + 1}`, color: COLORS[i % COLORS.length], is_bot: false });
    renderLocalSeats();
  });
  els.btnAddBot.addEventListener("click", () => {
    if (app.localSeatDraft.length >= 6) return;
    const i = app.localSeatDraft.length;
    app.localSeatDraft.push({ name: `RailBot ${i}`, color: COLORS[i % COLORS.length], is_bot: true });
    renderLocalSeats();
  });

  els.btnStartLocal.addEventListener("click", () => {
    app.roomClient?.close();
    app.sessionType = "local";
    app.mySlot = null;
    els.roomBadge.style.display = "none";
    const opts = {
      mode: els.localMode.value,
      events_enabled: els.localEvents.value === "on",
      players: app.localSeatDraft.map((s) => ({
        name: s.name.trim() || "Conductor",
        color: s.color,
        is_bot: s.is_bot,
      })),
      seed: Math.floor(Math.random() * 1e9) + 1,
    };
    try {
      const json = app.engine.start_local_game(JSON.stringify(opts));
      els.lobbyModal.classList.add("hidden");
      updateGameState(JSON.parse(json), { playSounds: false });
      playTurnChime();
    } catch (err) {
      showToast(String(err), true);
    }
  });

  els.btnOnlineConnect.addEventListener("click", async () => {
    const serverUrl = els.onlineServer.value.trim();
    const name = els.onlineName.value.trim() || "Conductor";
    let code = els.onlineRoom.value.trim().toUpperCase();

    app.roomClient?.close();
    app.roomClient = new RoomClient(serverUrl, {
      onWelcome: (msg) => {
        app.sessionType = "online";
        app.mySlot = msg.slot ?? null;
        els.onlineConnectActions.style.display = "none";
        els.onlineLobbyView.style.display = "";
        renderOnlineLobby(msg.lobby);
        const nextUrl = new URL(window.location.href);
        nextUrl.searchParams.set("room", msg.code);
        window.history.replaceState({}, "", nextUrl);
        if (msg.state) {
          els.lobbyModal.classList.add("hidden");
          updateGameState(msg.state, { playSounds: false });
        }
      },
      onLobby: (lobby) => {
        renderOnlineLobby(lobby);
      },
      onState: (state) => {
        els.lobbyModal.classList.add("hidden");
        updateGameState(state);
      },
      onDraft: (draft) => {
        app.remoteDraft = draft;
        draw();
      },
      onError: (message) => showToast(message, true),
      onDisconnect: () => showToast("Disconnected — reconnecting…", true),
    });

    try {
      if (!code) {
        code = await app.roomClient.createRoom();
        els.onlineRoom.value = code;
      }
      app.roomClient.connect(code, name);
    } catch (err) {
      showToast(err.message, true);
    }
  });

  const pushOnlineConfig = () => {
    app.roomClient?.send({
      type: "update_config",
      config: {
        map_id: "na_classic",
        mode: els.onlineMode.value,
        events_enabled: els.onlineEvents.value === "on",
        victory_cash: 250,
        victory_major_cities: 5,
      },
    });
  };
  els.onlineMode.addEventListener("change", pushOnlineConfig);
  els.onlineEvents.addEventListener("change", pushOnlineConfig);
  els.btnOnlineAddBot.addEventListener("click", () => app.roomClient?.send({ type: "add_bot" }));
  els.btnOnlineStart.addEventListener("click", () => app.roomClient?.send({ type: "start_game" }));

  const copyInvite = () => {
    navigator.clipboard?.writeText(window.location.href).then(
      () => showToast("Copied room invite link for Google Meet!"),
      () => showToast(window.location.href)
    );
  };
  els.btnCopyInvite.addEventListener("click", copyInvite);
  els.roomBadge.addEventListener("click", copyInvite);

  // Topbar controls
  els.btnUndo.addEventListener("click", () => sendAction({ type: "undo" }));
  els.btnPitch.addEventListener("click", () => sendAction({ type: "pitch_hand" }));
  els.btnPrimary.addEventListener("click", () => {
    if (!app.state) return;
    if (app.state.phase === "operate") {
      sendAction({ type: "end_operate_phase" });
    } else if (app.state.phase === "trim_hand") {
      sendAction({ type: "discard_initial_cards", indices: [...app.trimSelected] });
    } else {
      sendAction({ type: "end_turn" });
    }
  });

  els.btnDirectory.addEventListener("click", () => {
    buildDirectory();
    els.directoryModal.classList.remove("hidden");
  });
  els.btnCloseDirectory.addEventListener("click", () => els.directoryModal.classList.add("hidden"));
  els.btnMenu.addEventListener("click", () => els.lobbyModal.classList.remove("hidden"));
  els.btnVictoryInspect.addEventListener("click", () => els.victoryModal.classList.add("hidden"));
  els.btnVictoryNew.addEventListener("click", () => {
    els.victoryModal.classList.add("hidden");
    els.lobbyModal.classList.remove("hidden");
  });

  els.btnSound.addEventListener("click", () => {
    setSoundEnabled(!isSoundEnabled());
    els.btnSound.textContent = isSoundEnabled() ? "🔊" : "🔇";
  });

  els.btnZoomIn.addEventListener("click", () => {
    app.renderer.zoomAt(els.canvas.clientWidth / 2, els.canvas.clientHeight / 2, 1.2);
    draw();
  });
  els.btnZoomOut.addEventListener("click", () => {
    app.renderer.zoomAt(els.canvas.clientWidth / 2, els.canvas.clientHeight / 2, 0.83);
    draw();
  });
  els.btnZoomFit.addEventListener("click", () => {
    app.renderer.fitToViewport();
    draw();
  });

  window.addEventListener("keydown", (e) => {
    if (e.target.tagName === "INPUT" || e.target.tagName === "SELECT") return;
    if ((e.key === "z" || e.key === "Z") && !els.btnUndo.disabled) {
      els.btnUndo.click();
    } else if (e.key === "Enter" && !els.btnPrimary.disabled) {
      els.btnPrimary.click();
    }
  });
}

function trainSpeed(tier, mode) {
  const fast = mode === "fast";
  if (tier === "fast_freight" || tier === "superfreight") return fast ? 16 : 12;
  return fast ? 12 : 9;
}

function trainCapacity(tier) {
  return tier === "heavy_freight" || tier === "superfreight" ? 3 : 2;
}

function tierLabel(tier) {
  return (
    {
      freight: "Freight",
      fast_freight: "Fast Freight",
      heavy_freight: "Heavy Freight",
      superfreight: "Superfreight",
    }[tier] || tier
  );
}

function shortTier(tier) {
  return { freight: "FRT", fast_freight: "FAST", heavy_freight: "HVY", superfreight: "SUP" }[tier] || tier;
}

function nextUpgrades(tier) {
  if (tier === "freight") return ["fast_freight", "heavy_freight"];
  if (tier === "fast_freight" || tier === "heavy_freight") return ["superfreight"];
  return [];
}

function escapeHtml(str) {
  return String(str)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;");
}

async function boot() {
  await initWasm();
  app.engine = new WasmEngine();
  app.mapData = JSON.parse(app.engine.get_map_json());
  app.renderer = new BoardRenderer(els.canvas, app.mapData);

  renderLocalSeats();
  setupCanvasInteraction();
  setupControls();
  draw();

  // Auto-select Online tab if ?room=CODE is present in URL (Google Meet invite link!)
  const params = new URLSearchParams(window.location.search);
  const room = params.get("room");
  if (room) {
    els.onlineRoom.value = room.toUpperCase();
    els.tabOnline.click();
  }

  // Expose debug handle for automated Playwright screenshots & inspection.
  app.syncState = (s) => updateGameState(s, { playSounds: false });
  app.redraw = draw;
  window.__railsApp = app;
}

boot().catch((err) => {
  console.error(err);
  showToast(`Failed to load Wasm engine: ${err.message}`, true);
});
