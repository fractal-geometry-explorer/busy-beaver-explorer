(() => {
  const tip = document.getElementById("rk-tip"), fab = document.getElementById("rules-fab");
  const panel = document.getElementById("rules-panel"), closeBtn = document.getElementById("rp-close");
  let pinned = null;
  const cells = r => panel.querySelectorAll('td[data-r="' + r + '"]');
  function mark(r) {
    panel.querySelectorAll("td.on").forEach(td => td.classList.remove("on"));
    document.querySelectorAll(".rk.on").forEach(el => el.classList.remove("on"));
    if (r) cells(r).forEach(td => td.classList.add("on"));
  }
  function place(el) {
    const b = el.getBoundingClientRect(), t = tip.getBoundingClientRect();
    let x = b.left + b.width / 2 - t.width / 2;
    x = Math.max(8, Math.min(x, window.innerWidth - t.width - 8));
    let y = b.top - t.height - 8;
    if (y < 8) y = b.bottom + 8;
    tip.style.left = x + "px"; tip.style.top = y + "px";
  }
  function show(el) {
    const d = DEF[el.dataset.r]; if (!d) return;
    tip.innerHTML = '<span class="tip-r">' + el.dataset.r + '</span><span class="tip-t">' + d.text + '</span><span class="tip-c">' +
      d.chips.map(c => '<span class="chip ' + c[0] + '"><span class="sw ' + c[0] + '"></span>' + c[1] + '</span>').join("") + '</span>';
    tip.hidden = false; place(el); mark(el.dataset.r); el.classList.add("on");
  }
  function hide() { tip.hidden = true; pinned = null; mark(null); }
  document.addEventListener("pointerover", e => {
    if (e.pointerType === "touch" || pinned) return;
    const el = e.target.closest(".rk"); if (el) show(el);
  });
  document.addEventListener("pointerout", e => {
    if (e.pointerType === "touch" || pinned) return;
    const el = e.target.closest(".rk"); if (el && !el.contains(e.relatedTarget)) hide();
  });
  document.addEventListener("click", e => {
    const el = e.target.closest(".rk");
    if (el) { if (pinned === el) { hide(); } else { pinned = el; show(el); } return; }
    if (pinned && !e.target.closest("#rk-tip")) hide();
  });
  window.addEventListener("scroll", () => { if (!tip.hidden) { if (pinned) place(pinned); else hide(); } }, { passive: true });
  window.addEventListener("resize", () => { if (!tip.hidden) hide(); });
  function setOpen(open) {
    panel.hidden = !open; fab.setAttribute("aria-expanded", String(open)); fab.classList.toggle("open", open);
    try { localStorage.setItem("rulesPanelOpen", open ? "1" : "0"); } catch (err) {}
  }
  fab.addEventListener("click", () => setOpen(panel.hidden));
  closeBtn.addEventListener("click", () => { setOpen(false); fab.focus(); });
  document.addEventListener("keydown", e => { if (e.key === "Escape") { hide(); if (!panel.hidden) setOpen(false); } });
  try { if (localStorage.getItem("rulesPanelOpen") === "1") setOpen(true); } catch (err) {}
})();
