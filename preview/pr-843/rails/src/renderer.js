// Interactive pan/zoom Canvas 2D renderer for the North America crayon rails board.

export class BoardRenderer {
  constructor(canvas, mapData) {
    this.canvas = canvas;
    this.ctx = canvas.getContext("2d");
    this.map = mapData;
    this.mpById = new Map(mapData.mileposts.map((m) => [m.id, m]));
    this.cityById = new Map(mapData.cities.map((c) => [c.id, c]));
    this.commById = new Map(mapData.commodities.map((c) => [c.id, c]));
    this.sourcesByComm = new Map();
    for (const c of mapData.cities) {
      for (const comm of c.commodities) {
        if (!this.sourcesByComm.has(comm)) this.sourcesByComm.set(comm, []);
        this.sourcesByComm.get(comm).push(c);
      }
    }

    // Camera state: world coords -> screen px = (wx * scale + offsetX)
    this.scale = 28;
    this.offsetX = 20;
    this.offsetY = 20;
    this.dpr = window.devicePixelRatio || 1;
    this.fitToViewport();
  }

  resize() {
    const rect = this.canvas.parentElement.getBoundingClientRect();
    this.dpr = window.devicePixelRatio || 1;
    this.canvas.width = Math.max(1, Math.floor(rect.width * this.dpr));
    this.canvas.height = Math.max(1, Math.floor(rect.height * this.dpr));
    this.canvas.style.width = `${rect.width}px`;
    this.canvas.style.height = `${rect.height}px`;
  }

  fitToViewport() {
    this.resize();
    const w = this.canvas.width / this.dpr;
    const h = this.canvas.height / this.dpr;
    const pad = 28;
    const sx = (w - pad * 2) / this.map.geography.width;
    const sy = (h - pad * 2) / this.map.geography.height;
    this.scale = Math.max(12, Math.min(sx, sy));
    this.offsetX = (w - this.map.geography.width * this.scale) / 2;
    this.offsetY = (h - this.map.geography.height * this.scale) / 2;
  }

  zoomAt(screenX, screenY, factor) {
    const oldScale = this.scale;
    const newScale = Math.max(14, Math.min(95, oldScale * factor));
    const wx = (screenX - this.offsetX) / oldScale;
    const wy = (screenY - this.offsetY) / oldScale;
    this.scale = newScale;
    this.offsetX = screenX - wx * newScale;
    this.offsetY = screenY - wy * newScale;
  }

  panBy(dx, dy) {
    this.offsetX += dx;
    this.offsetY += dy;
  }

  worldToScreen(wx, wy) {
    return [wx * this.scale + this.offsetX, wy * this.scale + this.offsetY];
  }

  screenToWorld(sx, sy) {
    return [(sx - this.offsetX) / this.scale, (sy - this.offsetY) / this.scale];
  }

  hitTestMilepost(sx, sy) {
    const [wx, wy] = this.screenToWorld(sx, sy);
    let best = null;
    let bestD2 = 0.52 * 0.52;
    for (const mp of this.map.mileposts) {
      const dx = mp.x - wx;
      const dy = mp.y - wy;
      const d2 = dx * dx + dy * dy;
      if (d2 < bestD2) {
        bestD2 = d2;
        best = mp;
      }
    }
    return best;
  }

  render(view) {
    const ctx = this.ctx;
    const w = this.canvas.width / this.dpr;
    const h = this.canvas.height / this.dpr;
    ctx.save();
    ctx.scale(this.dpr, this.dpr);

    // 1. Ocean background
    const grad = ctx.createLinearGradient(0, 0, 0, h);
    grad.addColorStop(0, "#152d46");
    grad.addColorStop(1, "#1e3f5e");
    ctx.fillStyle = grad;
    ctx.fillRect(0, 0, w, h);

    ctx.save();
    ctx.translate(this.offsetX, this.offsetY);
    ctx.scale(this.scale, this.scale);

    // 2. Landmass parchment + coastline stroke
    for (const poly of this.map.geography.land_polygons) {
      this.tracePoly(ctx, poly);
      ctx.fillStyle = "#f2ead4";
      ctx.fill();
      ctx.lineWidth = 0.14;
      ctx.strokeStyle = "#8a7b5b";
      ctx.stroke();
    }

    // 3. Great Lakes cutouts
    for (const poly of this.map.geography.lake_polygons) {
      this.tracePoly(ctx, poly);
      ctx.fillStyle = "#29557a";
      ctx.fill();
      ctx.lineWidth = 0.08;
      ctx.strokeStyle = "#7699b8";
      ctx.stroke();
    }

    // 4. US-Canada Border
    ctx.save();
    ctx.setLineDash([0.3, 0.22]);
    ctx.lineWidth = 0.08;
    ctx.strokeStyle = "rgba(100, 116, 139, 0.55)";
    for (const b of this.map.geography.borders) {
      this.traceLine(ctx, b.points);
      ctx.stroke();
    }
    ctx.restore();

    // 5. Rivers
    ctx.lineCap = "round";
    ctx.lineJoin = "round";
    for (const r of this.map.geography.rivers) {
      this.traceLine(ctx, r.points);
      ctx.lineWidth = 0.2;
      ctx.strokeStyle = "#4895c8";
      ctx.stroke();
    }

    // 6. Subtle lattice guides for river/inlet crossings
    for (const e of this.map.edges) {
      if (e.kind === "inlet") {
        const a = this.mpById.get(e.a);
        const b = this.mpById.get(e.b);
        ctx.beginPath();
        ctx.moveTo(a.x, a.y);
        ctx.lineTo(b.x, b.y);
        ctx.lineWidth = 0.09;
        ctx.strokeStyle = "rgba(2, 132, 199, 0.35)";
        ctx.stroke();
      }
    }

    // 7. Major City Red Hubs (filled translucent crimson polygon around hub mileposts)
    for (const city of this.map.cities) {
      if (city.size !== "major") continue;
      const center = this.mpById.get(city.center_mp);
      ctx.beginPath();
      ctx.arc(center.x, center.y, 1.18, 0, Math.PI * 2);
      ctx.fillStyle = "rgba(220, 38, 38, 0.19)";
      ctx.fill();
      ctx.lineWidth = 0.09;
      ctx.strokeStyle = "rgba(220, 38, 38, 0.72)";
      ctx.stroke();
    }

    // 8. Active Event Hazard Overlays (Storm / Flood / Strike)
    if (view.state?.active_events?.length) {
      for (const ev of view.state.active_events) {
        const eff = ev.effect;
        if (eff.type === "storm" || eff.type === "flood") {
          const c = this.cityById.get(eff.city_id);
          if (c) {
            const mp = this.mpById.get(c.center_mp);
            ctx.beginPath();
            ctx.arc(mp.x, mp.y, eff.radius * 0.92, 0, Math.PI * 2);
            ctx.fillStyle = eff.type === "flood"
              ? "rgba(56, 189, 248, 0.2)"
              : "rgba(239, 68, 68, 0.18)";
            ctx.fill();
            ctx.lineWidth = 0.08;
            ctx.strokeStyle = eff.type === "flood" ? "#38bdf8" : "#ef4444";
            ctx.stroke();
          }
        } else if (eff.type === "strike") {
          for (const cid of eff.cities) {
            const c = this.cityById.get(cid);
            if (!c) continue;
            const mp = this.mpById.get(c.center_mp);
            ctx.beginPath();
            ctx.arc(mp.x, mp.y, eff.radius * 0.92, 0, Math.PI * 2);
            ctx.fillStyle = "rgba(245, 158, 11, 0.2)";
            ctx.fill();
            ctx.lineWidth = 0.08;
            ctx.strokeStyle = "#f59e0b";
            ctx.stroke();
          }
        }
      }
    }

    // 9. Reachable milepost highlight (during Operate phase)
    if (view.reachableSet && view.reachableSet.size > 0) {
      for (const id of view.reachableSet) {
        const mp = this.mpById.get(id);
        if (!mp) continue;
        ctx.beginPath();
        ctx.arc(mp.x, mp.y, 0.26, 0, Math.PI * 2);
        ctx.fillStyle = "rgba(56, 189, 248, 0.32)";
        ctx.fill();
      }
    }

    // 10. Built Crayon Tracks (with parallel lane offsetting when multiple players share an edge)
    if (view.state?.tracks?.length) {
      const byEdge = new Map();
      for (const t of view.state.tracks) {
        const k = t.a < t.b ? `${t.a}-${t.b}` : `${t.b}-${t.a}`;
        if (!byEdge.has(k)) byEdge.set(k, []);
        byEdge.get(k).push(t);
      }

      for (const list of byEdge.values()) {
        const count = list.length;
        list.forEach((seg, idx) => {
          const a = this.mpById.get(seg.a);
          const b = this.mpById.get(seg.b);
          const dx = b.x - a.x;
          const dy = b.y - a.y;
          const len = Math.hypot(dx, dy) || 1;
          const nx = -dy / len;
          const ny = dx / len;
          const shift = (idx - (count - 1) / 2) * 0.14;
          const player = view.state.players[seg.owner];
          const color = player ? player.color : "#333";

          // Subtle dark casing so crayon colors pop on parchment
          ctx.beginPath();
          ctx.moveTo(a.x + nx * shift, a.y + ny * shift);
          ctx.lineTo(b.x + nx * shift, b.y + ny * shift);
          ctx.lineWidth = 0.22;
          ctx.strokeStyle = "rgba(15, 23, 42, 0.45)";
          ctx.stroke();

          ctx.beginPath();
          ctx.moveTo(a.x + nx * shift, a.y + ny * shift);
          ctx.lineTo(b.x + nx * shift, b.y + ny * shift);
          ctx.lineWidth = 0.15;
          ctx.strokeStyle = color;
          ctx.stroke();
        });
      }
    }

    // 11. Remote Player Live Draft Preview (Google Meet collaboration!)
    if (view.remoteDraft && view.state) {
      const p = view.state.players[view.remoteDraft.player_id];
      const col = p ? p.color : "#38bdf8";
      this.drawDraftOverlay(ctx, view.remoteDraft.build_edges, view.remoteDraft.move_path, col, true);
    }

    // 12. Local Player Hovered Build/Move Preview
    if (view.localPreview && view.state) {
      const p = view.state.players[view.state.current_player];
      const col = view.localPreview.affordable === false ? "#ef4444" : (p ? p.color : "#0284c7");
      this.drawDraftOverlay(ctx, view.localPreview.edges, view.localPreview.path, col, false);
    }

    // 13. Mileposts & Terrain Symbols
    for (const mp of this.map.mileposts) {
      if (mp.terrain === "clear") {
        ctx.beginPath();
        ctx.arc(mp.x, mp.y, 0.085, 0, Math.PI * 2);
        ctx.fillStyle = "#5c5346";
        ctx.fill();
      } else if (mp.terrain === "mountain" || mp.terrain === "alpine") {
        // Crisp mountain triangle
        ctx.beginPath();
        ctx.moveTo(mp.x, mp.y - 0.2);
        ctx.lineTo(mp.x + 0.19, mp.y + 0.14);
        ctx.lineTo(mp.x - 0.19, mp.y + 0.14);
        ctx.closePath();
        ctx.fillStyle = "#785a3a";
        ctx.fill();
      } else if (mp.terrain === "major_city") {
        ctx.beginPath();
        ctx.arc(mp.x, mp.y, 0.14, 0, Math.PI * 2);
        ctx.fillStyle = "#dc2626";
        ctx.fill();
        ctx.lineWidth = 0.05;
        ctx.strokeStyle = "#fff";
        ctx.stroke();
      } else if (mp.terrain === "medium_city") {
        ctx.beginPath();
        ctx.rect(mp.x - 0.17, mp.y - 0.17, 0.34, 0.34);
        ctx.fillStyle = "#1e293b";
        ctx.fill();
        ctx.lineWidth = 0.06;
        ctx.strokeStyle = "#fef08a";
        ctx.stroke();
      } else if (mp.terrain === "small_city") {
        ctx.beginPath();
        ctx.arc(mp.x, mp.y, 0.17, 0, Math.PI * 2);
        ctx.fillStyle = "#334155";
        ctx.fill();
        ctx.lineWidth = 0.05;
        ctx.strokeStyle = "#f8fafc";
        ctx.stroke();
      }
    }

    // 14. Demand Card / Commodity Highlights (Destination Bullseye + Source Badges)
    if (view.highlight) {
      if (view.highlight.destCityId) {
        const dc = this.cityById.get(view.highlight.destCityId);
        if (dc) {
          const mp = this.mpById.get(dc.center_mp);
          ctx.beginPath();
          ctx.arc(mp.x, mp.y, 0.72, 0, Math.PI * 2);
          ctx.lineWidth = 0.14;
          ctx.strokeStyle = "#facc15";
          ctx.stroke();
          ctx.beginPath();
          ctx.arc(mp.x, mp.y, 0.45, 0, Math.PI * 2);
          ctx.lineWidth = 0.08;
          ctx.strokeStyle = "#16a34a";
          ctx.stroke();
        }
      }
      if (view.highlight.commodity) {
        const comm = this.commById.get(view.highlight.commodity);
        const srcs = this.sourcesByComm.get(view.highlight.commodity) || [];
        for (const sc of srcs) {
          const mp = this.mpById.get(sc.center_mp);
          ctx.beginPath();
          ctx.arc(mp.x, mp.y, 0.56, 0, Math.PI * 2);
          ctx.fillStyle = "rgba(56, 189, 248, 0.28)";
          ctx.fill();
          ctx.lineWidth = 0.11;
          ctx.strokeStyle = comm ? comm.color : "#38bdf8";
          ctx.stroke();
        }
      }
    }

    // 15. City Labels (crisp dark halo for instant readability)
    ctx.textAlign = "center";
    ctx.textBaseline = "bottom";
    for (const city of this.map.cities) {
      const mp = this.mpById.get(city.center_mp);
      const isMajor = city.size === "major";
      ctx.font = `${isMajor ? "800" : "700"} ${isMajor ? 0.52 : 0.38}px Inter, sans-serif`;
      const lx = mp.x + (city.id === "detroit" ? -0.35 : city.id === "cleveland" ? 0.35 : 0);
      const ly = mp.y - (isMajor ? 0.3 : 0.24) + (city.id === "cleveland" ? 0.62 : 0);
      ctx.lineWidth = 0.14;
      ctx.strokeStyle = "rgba(242, 234, 212, 0.92)";
      ctx.strokeText(city.name, lx, ly);
      ctx.fillStyle = isMajor ? "#991b1b" : "#0f172a";
      ctx.fillText(city.name, lx, ly);
    }

    // 16. Hovered Milepost Ring
    if (view.hoveredMp) {
      ctx.beginPath();
      ctx.arc(view.hoveredMp.x, view.hoveredMp.y, 0.32, 0, Math.PI * 2);
      ctx.lineWidth = 0.09;
      ctx.strokeStyle = "#0284c7";
      ctx.stroke();
    }

    // 17. Locomotive Tokens
    if (view.state?.players) {
      const byPos = new Map();
      for (const p of view.state.players) {
        if (p.train_pos == null) continue;
        if (!byPos.has(p.train_pos)) byPos.set(p.train_pos, []);
        byPos.get(p.train_pos).push(p);
      }
      for (const [mpId, list] of byPos.entries()) {
        const mp = this.mpById.get(mpId);
        if (!mp) continue;
        list.forEach((p, idx) => {
          const ox = (idx - (list.length - 1) / 2) * 0.42;
          const tx = mp.x + ox;
          const ty = mp.y + 0.05;
          const isCur = p.id === view.state.current_player;

          if (isCur) {
            ctx.beginPath();
            ctx.arc(tx, ty, 0.46, 0, Math.PI * 2);
            ctx.fillStyle = "rgba(250, 204, 21, 0.35)";
            ctx.fill();
          }

          // Rounded locomotive body
          ctx.beginPath();
          ctx.arc(tx, ty, 0.32, 0, Math.PI * 2);
          ctx.fillStyle = p.color;
          ctx.fill();
          ctx.lineWidth = 0.09;
          ctx.strokeStyle = "#ffffff";
          ctx.stroke();

          // Cargo pips inside token
          for (let c = 0; c < p.cargo.length; c++) {
            const px = tx + (c - (p.cargo.length - 1) / 2) * 0.16;
            ctx.beginPath();
            ctx.arc(px, ty, 0.065, 0, Math.PI * 2);
            ctx.fillStyle = "#fef08a";
            ctx.fill();
          }
        });
      }
    }

    ctx.restore();
    ctx.restore();
  }

  drawDraftOverlay(ctx, edges, path, color, isRemote) {
    ctx.save();
    ctx.setLineDash([0.24, 0.16]);
    ctx.lineWidth = isRemote ? 0.16 : 0.2;
    ctx.strokeStyle = color;
    ctx.globalAlpha = isRemote ? 0.65 : 0.92;

    if (edges && edges.length) {
      for (const [aId, bId] of edges) {
        const a = this.mpById.get(aId);
        const b = this.mpById.get(bId);
        if (!a || !b) continue;
        ctx.beginPath();
        ctx.moveTo(a.x, a.y);
        ctx.lineTo(b.x, b.y);
        ctx.stroke();
      }
    }
    if (path && path.length >= 2) {
      ctx.beginPath();
      const first = this.mpById.get(path[0]);
      ctx.moveTo(first.x, first.y);
      for (let i = 1; i < path.length; i++) {
        const pt = this.mpById.get(path[i]);
        ctx.lineTo(pt.x, pt.y);
      }
      ctx.stroke();
    }
    ctx.restore();
  }

  tracePoly(ctx, pts) {
    ctx.beginPath();
    pts.forEach(([x, y], i) => {
      if (i === 0) ctx.moveTo(x, y);
      else ctx.lineTo(x, y);
    });
    ctx.closePath();
  }

  traceLine(ctx, pts) {
    ctx.beginPath();
    pts.forEach(([x, y], i) => {
      if (i === 0) ctx.moveTo(x, y);
      else ctx.lineTo(x, y);
    });
  }
}
