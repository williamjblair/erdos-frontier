# Erdős Problem 639 — drafting inputs

- upstream state: **proved (Lean)**  
- machine verdict: **None** (source None)  
- formal_proof link allowed: **False** (unconditional + signed vsa_ required)

## Problem text (VERBATIM SOURCE — cite, do not rephrase)

```latex
<!DOCTYPE html>
<html>

<head>
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<meta charset="UTF-8">

<title>639 | Erdős Problems</title>
<meta property="og:title" content="639 | Erdős Problems">
<link rel="icon" href="/static/favicon.ico">
<link rel="stylesheet" href="/static/style.css?v=733265cf">

<script>
document.addEventListener('click', (e) => {
  // Toggle reply form
  const toggle = e.target.closest('.reply-toggle');
  if (toggle) {
    const id = toggle.getAttribute('data-target');
    const form = document.getElementById(id);
    if (form) form.classList.toggle('hidden');
  }
  // Reply with quote
  const quoteBtn = e.target.closest('.reply-quote');
  if (quoteBtn) {
    const id = quoteBtn.getAttribute('data-target');
    const form = document.getElementById(id);
    if (!form) return;
    const ta = form.querySelector('textarea');
    const raw = quoteBtn.getAttribute('data-raw') || '';
    const quoted = raw.split('\n').map(l => '> ' + l).join('\n') + '\n\n';
    ta.value = quoted;
    form.classList.remove('hidden');
    ta.focus();
    const len = ta.value.length;
    ta.setSelectionRange(len, len);
  }
});
</script>

<!-- This creates the reference in the bibliography box. -->

<script>
function addNewBox(key, problem_id, shouldScroll = false) {
  const local_id = 'bib-container' + String(problem_id);
  const container = document.getElementById(local_id);
  if (!container) return;

  container.innerHTML = "";

  fetch(`/bibs/${encodeURIComponent(key)}`)
    .then(res => {
      if (!res.ok) throw new Error(`HTTP ${res.status}`);
      return res.text();
    })
    .then(html => {
      container.innerHTML = html;

      if (shouldScroll) {
        requestAnimationFrame(() => {
          container.scrollIntoView({
            behavior: "smooth",
            block: "start"
          });
        });
      }
    })
    .catch(err => {
      console.error("Failed to load bib:", err);
      container.textContent = "Unable to load reference.";

      if (shouldScroll) {
        container.scrollIntoView({
          behavior: "smooth",
          block: "start"
        });
      }
    });
}
</script>

<script>
const filledSVG = `
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="black" class="fav-icon">
  <path fill-rule="evenodd" d="M10.788 3.21c.448-1.077 1.976-1.077 2.424 0l2.082 5.006 5.404.434c1.164.093 1.636 1.545.749 2.305l-4.117 3.527 1.257 5.273c.271 1.136-.964 2.033-1.96 1.425L12 18.354 7.373 21.18c-.996.608-2.231-.29-1.96-1.425l1.257-5.273-4.117-3.527c-.887-.76-.415-2.212.749-2.305l5.404-.434 2.082-5.005Z" clip-rule="evenodd" />
</svg>
                `;
const outlineSVG = `
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" stroke="black" fill="white" class="fav-icon">
  <path stroke-linecap="round" stroke-linejoin="round" d="M11.48 3.499a.562.562 0 0 1 1.04 0l2.125 5.111a.563.563 0 0 0 .475.345l5.518.442c.499.04.701.663.321.988l-4.204 3.602a.563.563 0 0 0-.182.557l1.285 5.385a.562.562 0 0 1-.84.610l-4.725-2.885a.562.562 0 0 0-.586 0L6.982 20.54a.562.562 0 0 1-.840-.610l1.285-5.386a.563.563 0 0 0-.182-.557L3.041 10.385a.562.562 0 0 1 .321-.988l5.518-.442a.563.563 0 0 0 .475-.345L11.48 3.5Z" />
</svg>
                `;

document.addEventListener("click", async (e) => {
  const btn = e.target.closest(".fav-btn");
  if (!btn) return;

  e.preventDefault();
  const problemId = btn.dataset.problemId;

  try {
    const res = await fetch(`/forum/toggle_favourite/${problemId}`, { method: "POST" });
    const data = await res.json();

    btn.dataset.favourited = data.favourited ? "true" : "false";
    btn.innerHTML = data.favourited ? filledSVG : outlineSVG;
  } catch (err) {
    console.error("Toggle failed:", err);
  }
});
</script>

    
<script>
function addImageBox(X, problem_id, shouldScroll = true) {
  const local_id = 'image-container' + String(problem_id);
  const container = document.getElementById(local_id);
  if (!container) return;

  container.innerHTML = "";

  const newBox = document.createElement("div");

  const img = document.createElement("img");
  img.src = `/static/${encodeURIComponent(X)}.png`;
  img.className = "responsive-image";
  img.alt = String(X);

  newBox.appendChild(img);
  container.appendChild(newBox);

  if (shouldScroll) {
    requestAnimationFrame(() => {
      container.scrollIntoView({
        behavior: "smooth",
        block: "start"
      });
    });
  }
}
</script>


<script>
document.addEventListener('DOMContentLoaded', function() {
  const form = document.getElementById('searchForm');
  if (!form) return;
  form.addEventListener('submit', function (e) {
    const input = form.querySelector('.searchTerm');
    if (!input) return;
    const value = input.value.trim();
    if (!value) return;
    const path = '/search/' + encodeURIComponent(value);
    const inDual = window.location.pathname.startsWith("/dual");
    if (inDual) {
      e.preventDefault(); 
      const selected = document.querySelector('input[name="targetPanel"]:checked');
      const panel = selected ? selected.value : "left";
      const iframe = document.getElementById(`iframe-${panel}`);
      if (iframe) {
        const url = path.includes("?") ? path + "&embed=1" : path + "?embed=1";
        iframe.src = url;
        const box = document.querySelector(`#panel-${panel} input`);
        if (box) box.value = path;
      } else {
        window.location.href = path;
      }
    } else {
      form.action = path;
      form.method = "GET";
    }
  });
});
</script>

<script>
document.addEventListener('DOMContentLoaded', function() {
  if (window.location.pathname.startsWith("/dual")) return;

  var form = document.getElementById('idsearchForm');
  if (!form) return;

  form.onsubmit = function() {
    var input = document.querySelector('.idsearchTerm').value.trim();
    var searchUrl;

    if (/^\d+$/.test(input)) {
        searchUrl = '/' + encodeURIComponent(input);
    } else if (/^((\d+|end)(-(\d+|end))?\s*)+(open|solved|yes|no)?$/.test(input.toLowerCase())) {
        let parts = input.split(/\s+/).filter(Boolean);
        searchUrl = '/range/' + parts.map(encodeURIComponent).join('/');
    } else {
        alert("Enter either a single integer or a space-separated list of numbers/ranges...");
        return false;
    }
    window.location.href = searchUrl;
    return false;
  };
});
</script>

<script>
  window.CURRENT_USERNAME = "";
</script>


<script>
document.addEventListener("click", async (ev) => {
  const btn = ev.target.closest(".reaction-btn");
  if (!btn) return;
  const you = window.CURRENT_USERNAME || "";
  const bar = btn.closest(".reaction-bar");
  const postId = bar?.dataset.postId;
  const rtype = btn.dataset.type;
  const reactUrl = bar?.dataset.reactUrl; 
  if (!postId || !rtype || !reactUrl) return;

  try {
    const res = await fetch(reactUrl, {
      method: "POST",
      credentials: "same-origin",
      headers: {"Content-Type": "application/json"},
      body: JSON.stringify({type: rtype})
    });
    const data = await res.json();
    if (!data.ok) {
      alert(data.error || "Could not update reaction.");
      return;
    }
    const summary = data.summary;
    
    bar.querySelectorAll(".reaction-btn").forEach(b => {
      const t = b.dataset.type;
      const countSpan = bar.querySelector(`.reaction-count[data-type="${t}"]`);
      if (countSpan && summary[t]) {
        countSpan.textContent = summary[t].count;
    const desc = b.dataset.desc || "";
    const usersTitle = summary[t].users_title || "No one yet.";
    b.title = `${desc}\n\n${usersTitle}`;
      }
        const iReacted = you && (summary[t].users_title || "").includes(you);
  b.classList.toggle("active", !!iReacted);
  b.setAttribute("aria-pressed", iReacted ? "true" : "false");
    });
  } catch (e) {
    console.error(e);
    alert("Only registered users with 5+ posts can react.");
  }
});
</script>

<script>
document.addEventListener("DOMContentLoaded", function () {
  document.body.addEventListener("click", function (e) {
    const link = e.target.closest(".problem-reaction-link");
    if (!link) return;

    e.preventDefault();

    const row = link.closest(".problem-reaction-row");
    if (!row) return;

    const form = row.querySelector(".problem-reaction-form");
    if (!form) return;

    const formData = new FormData(form);

    fetch(form.action, {
      method: "POST",
      body: formData,
      headers: {
        "X-Requested-With": "XMLHttpRequest"
      }
    })
      .then(resp => resp.json())
      .then(data => {
        if (!data.ok) {
          console.error(data.error || "Problem reaction update failed");
          return;
        }

        const summary = data.summary;

        // Update users text for each reaction type
        for (const [type, info] of Object.entries(summary)) {
          const r = document.querySelector(
            `.problem-reaction-row[data-reaction-type="${type}"]`
          );
          if (!r) continue;

          const usersCell = r.querySelector(".problem-reaction-users");
          if (usersCell) {
            usersCell.textContent = info.users_title || "None yet";
          }
        }
        link.classList.toggle("active");
        if (link.classList.contains("active")) {
          link.textContent = "(no)";
        } else {
          link.textContent = "(yes)";
        }
      })
      .catch(err => {
        console.error("Problem reaction AJAX error", err);
      });
  });
});
</script>






</head>

<body>

<div class="topnav">

  <div class="left">
    <div class="logo">
      <a class="dual-aware" href="/"><img src="/static/EPLogo.png" alt="Logo" height="50"></a>
    </div>
    <div class="links dual-aware desktop-nav">
      <a href="/forum">Forum</a>
      <a href="/dm">Inbox</a> 
      <a href="/favourites">Favourites</a>
      <a href="/tags">Tags</a> 
      <div class="dropdown">
        <a href="javascript:void(0)" class="dropbtn">More</a>
        <div class="dropdown-content">
          <a href="/faq">FAQ</a>
          <a href="/prizes">Prizes</a>
          <a href="/lists">Problem Lists</a>
          <a href="/definitions">Definitions</a>
          <a href="/links">Links</a>
        </div>
      </div> 
    </div>
    <div class="mobile-nav">
    
        <a class="forumlink" href="/forum">Forum</a>
    <div class="dropdown">
      <button class="dropbtn" id="mobileMenuButton">Menu</button>
      <div class="dropdown-content">
        <a href="/dm">Inbox</a> 
        <a href="/favourites">Favourites</a>
        <a href="/tags">Tags</a>  
        <a href="/faq">FAQ</a>
        <a href="/prizes">Prizes</a>
        <a href="/lists">Problem Lists</a>
        <a href="/definitions">Definitions</a>
        <a href="/links">Links</a>
      </div>
     </div>
    </div>
  </div>

  <div class = "middle">
    <div class="button-container" style="max-width: 50%;">
      <form id="idsearchForm">
        <input required type="text" name="query" class="idsearchTerm" placeholder="# (or range #-#)" title="Enter either a single integer or a space-separated list of numbers/ranges, optionally ending with 'open' or 'solved'.">
        <button type="submit" class="searchButton">Go</button>
      </form>
    </div>
    <div class="button-container" style="max-width: 50%;">
      <form id="searchForm">
        <input required type="text" name="query" class="searchTerm" placeholder="Search" title="Search all problems.">
        <button type="submit" class="searchButton">Go</button>
      </form>
    </div>
  </div>

  <div class="right">
    <a href="#" id="dualViewLink" class="split_all">Dual View</a>
    <a href="/random_solved" class="split_solved dual-aware">Random Solved</a>
    <a href="/random_open" class="split_open dual-aware">Random Open</a>
  </div>

</div>

<div id="notifications-slot"></div>

<script>
(function () {
  const params = new URLSearchParams(window.location.search);
  if (params.get("embed")) return;

  fetch("/forum/notifications/fragment", {cache: "no-store"})
    .then(r => r.text())
    .then(html => {
      document.getElementById("notifications-slot").innerHTML = html;
    })
    .catch(() => {});
})();
</script>


<div class="container">
  <div class="problem-box">
    <div class="problem-text">  
      <div id="content" style="white-space: pre-line;">
      Is it true that if the edges of $K_n$ are 2-coloured then there are at most $n^2/4$ many edges which do not occur in a monochromatic triangle?
      </div>
    </div>
  <div class="problem-additional-text" style="white-space: pre-line;"> 
  
  Solved by Erd\H{o}s, Rousseau, and Schelp for large $n$, but unpublished. Alon has observed that this also follows from a result of Pyber \cite{Py86}, which states that (for large enough $n$) at most $\lfloor n^2/4\rfloor+2$ monochromatic cliques cover all edges of a $2$-coloured $K_n$. <br><br>This problem was solved completely by Keevash and Sudakov \cite{KeSu04}, who proved that the correct threshold is $\lfloor n^2/4\rfloor$ for all $n\geq 7$, is $\binom{n}{2}$ for $n\leq 5$, and is $10$ for $n=6$.
  
  </div>
  
  <div class="problem-additional-text" style="white-space: pre-line;"> 
  <h3>References</h3>
  
  [KeSu04] Keevash, Peter and Sudakov, Benny, <i>On the number of edges not covered by monochromatic copies of<br>a fixed graph</i>. J. Combin. Theory Ser. B (2004), 41--53.
  
  [Py86] Pyber, L., <i>Clique covering of graphs</i>. Combinatorica (1986), 393--398.
  
  </div>
                                        
  <div class="problem-additional-text" style="text-align:center; padding: 10px;">
  <a href="/639">Back to the problem</a>
  </div>

</div>                

    





<!-- Previewing forum posts -->
<!-- Previewing forum posts -->
<script>
document.addEventListener("DOMContentLoaded", function () {
  function escapeHtml(str) {
    return String(str).replace(/[&<>"']/g, m => ({
      "&": "&amp;",
      "<": "&lt;",
      ">": "&gt;",
      '"': "&quot;",
      "'": "&#39;"
    })[m]);
  }

  function normalizeHref(href) {
    href = href.trim();
    if (!/^https?:\/\//i.test(href) && !href.startsWith("/")) {
      href = "https://" + href;
    }

    return href;
  }

  let mathJaxQueue = Promise.resolve();

  function clearMathJax(element) {
    if (window.MathJax && MathJax.typesetClear) {
      MathJax.typesetClear([element]);
    }
  }

  function typesetMath(element) {
    if (!window.MathJax) return;

    if (MathJax.typesetPromise) {
      mathJaxQueue = mathJaxQueue
        .then(() => {
          if (MathJax.startup && MathJax.startup.promise) {
            return MathJax.startup.promise;
          }
        })
        .then(() => MathJax.typesetPromise([element]))
        .catch(err => {
          console.error("MathJax typeset failed:", err);
        });

      return;
    }

    if (MathJax.Hub) {
      MathJax.Hub.Queue(["Typeset", MathJax.Hub, element]);
    }
  }

  function renderPreview(textarea, preview, label) {
    let raw = textarea.value;
    const anchors = [];
    let idx = 0;

    raw = raw.replace(
      /<a\s+href=("(?:[^"]*)"|'(?:[^']*)')\s*>([\s\S]*?)<\/a>/gi,
      (match, qHref, labelText) => {
        const href = qHref.slice(1, -1);
        const token = `__A_TAG_${idx++}__`;

        anchors.push({
          token,
          href: normalizeHref(href),
          label: labelText
        });

        return token;
      }
    );

    let safe = escapeHtml(raw);

    anchors.forEach(a => {
      const html = `<a href="${escapeHtml(a.href)}">${escapeHtml(a.label)}</a>`;
      safe = safe.replace(a.token, html);
    });

    safe = safe.replace(/\{PROBLEM=(.+?)\}/g, (_, p1) =>
      `<a href="/${escapeHtml(p1)}">[${escapeHtml(p1)}]</a>`
    );

    safe = safe.replace(/\n/g, "<br>");
    clearMathJax(preview);

    if (!safe.trim()) {
      preview.innerHTML = "";
      preview.classList.add("hidden");
      label.classList.add("hidden");
      return;
    }

    preview.innerHTML = safe;
    preview.classList.remove("hidden");
    label.classList.remove("hidden");

    typesetMath(preview);
  }

  document.querySelectorAll("form textarea").forEach(textarea => {
    const form = textarea.closest("form");
    const preview = form && form.querySelector(".post-preview");
    const label = form && form.querySelector(".preview-label");

    if (preview && label) {
      textarea.addEventListener("input", () => renderPreview(textarea, preview, label));
      renderPreview(textarea, preview, label);
    }
  });
});
</script>

<!-- To handle the search bar -->
<script>
document.addEventListener('DOMContentLoaded', function () {
    function setFilterLink(linkId, newFilter) {
        const link = document.getElementById(linkId);
        if (!link) return;
        const pathParts = window.location.pathname.split("/");
        // Expect: /<section>/<entry> or /<section>/<entry>/<filter>
        if (pathParts.length >= 3) {
            const section = pathParts[1];
            const entry = pathParts[2];
            // Construct base: /tags/additive, /sources_bib/BL09, etc.
            const baseUrl = "/" + section + "/" + entry;
            link.href = baseUrl + "/" + newFilter;
        }
    }
    setFilterLink("solvedLink", "solved");
    setFilterLink("openLink", "open");
    setFilterLink("yesLink", "yes");
    setFilterLink("noLink", "no");
});
</script>

<!-- Handle the dual view link -->
<script>
document.addEventListener("DOMContentLoaded", function () {
  const dualLink = document.getElementById("dualViewLink");
  if (!dualLink) return;

  const isInDualView = window.location.pathname.startsWith("/dual");
  dualLink.textContent = isInDualView ? "Exit Dual View" : "Dual View";
  dualLink.addEventListener("click", function (e) {
    e.preventDefault();

    if (isInDualView) {
      try {
        const leftIframe = document.getElementById("iframe-left");
        const src = leftIframe?.src || "/";
        let clean = src.replace(window.location.origin, "");
        clean = clean.replace(/[?&]embed=1/, "");

        window.location.href = clean;
      } catch (err) {
        window.location.href = "/";
      }
    } else {
      const currentPath = window.location.pathname + window.location.search;
      const rightPanelDefault = "/";
      const hash = `#left:${encodeURIComponent(currentPath)}&right:${encodeURIComponent(rightPanelDefault)}`;
      window.location.href = `/dual${hash}`;
    }
  });
});
</script>

<!-- Redirect links and searches when in dual view mode -->
<script>
document.addEventListener("DOMContentLoaded", function () {
  if (!window.location.pathname.startsWith("/dual")) return;

  function getTargetPanel() {
    const selected = document.querySelector('input[name="targetPanel"]:checked');
    return selected ? selected.value : "left";
  }

  function loadInPanel(panel, path) {
    if (!path) return;
    const iframe = document.getElementById(`iframe-${panel}`);
    if (!iframe) return;
    const url = path.includes("?") ? path + "&embed=1" : path + "?embed=1";
    iframe.src = url;
    const inputBox = document.querySelector(`#panel-${panel} input`);
    if (inputBox) inputBox.value = path;
    console.log(`Loaded "${url}" into panel "${panel}"`);
  }
  
  document.querySelectorAll(".dual-aware a[href^='/'], a.dual-aware[href^='/']").forEach(link => {
    link.addEventListener("click", function (e) {
      e.preventDefault();
      const path = this.getAttribute("href");
      loadInPanel(getTargetPanel(), path);
    });
  });

  const idForm = document.getElementById("idsearchForm");
  if (idForm) {
    idForm.addEventListener("submit", function (e) {
      e.preventDefault();
      const input = idForm.querySelector(".idsearchTerm").value.trim();
      if (!input) return;

      let path = null;

      if (/^\d+$/.test(input)) {
        path = "/go_to/" + encodeURIComponent(input);
      } else if (/^((\d+|end)(-(\d+|end))?\s*)+(open|solved|yes|no)?$/i.test(input)) {
        const parts = input.split(/\s+/).filter(Boolean);
        path = "/range/" + parts.map(encodeURIComponent).join("/");
      } else {
        alert("Invalid input format.");
        return;
      }

      loadInPanel(getTargetPanel(), path);
    });
  }

  const searchForm = document.getElementById("searchForm");
  if (searchForm) {
    searchForm.addEventListener("submit", function (e) {
      e.preventDefault();
      const input = searchForm.querySelector(".searchTerm").value.trim();
      if (!input) return;

      const path = "/search/" + encodeURIComponent(input);
      loadInPanel(getTargetPanel(), path);
    });
  }
});
</script>

<!-- Different menu on mobile -->

<script>
document.addEventListener("DOMContentLoaded", function () {
  const button = document.getElementById("mobileMenuButton");
  const dropdown = document.getElementById("mobileDropdown");

  if (button && dropdown) {
    button.addEventListener("click", function () {
      dropdown.classList.toggle("show");
    });

    document.addEventListener("click", function (e) {
      if (!button.contains(e.target) && !dropdown.contains(e.target)) {
        dropdown.classList.remove("show");
      }
    });
  }
});
</script>

<!-- For expanding threads -->

<script>
document.addEventListener('click', (e) => {
  const link = e.target.closest('#toggle-posts');
  if (!link) return;
  e.preventDefault(); 

  const box = document.getElementById('more-posts');
  const isHidden = box.classList.toggle('hidden');
  const expanded = !isHidden;

  link.setAttribute('aria-expanded', expanded ? 'true' : 'false');
  box.setAttribute('aria-hidden', expanded ? 'false' : 'true');

  link.textContent = expanded
    ? 'Show only the top five comments'
    : `Show ${link.dataset.remaining} more comments`;
});
</script>


<script>
document.addEventListener('click', (e) => {
  const link = e.target.closest('.toggle-replies');
  if (!link) return;
  e.preventDefault();

  const pid = link.dataset.postId;
  const box = document.getElementById(`more-replies-${pid}`);
  if (!box) return;

  const isHidden = box.classList.toggle('hidden');
  const expanded = !isHidden;

  link.setAttribute('aria-expanded', expanded ? 'true' : 'false');
  box.setAttribute('aria-hidden', expanded ? 'false' : 'true');

  link.textContent = expanded
    ? 'Hide replies'
    : `Show ${link.dataset.remaining} more replies`;
});
</script>


<script>
document.addEventListener("click", async function (event) {
    const button = event.target.closest(".problem-status-option");
    if (!button) return;

    const widget = button.closest(".problem-status-widget");
    if (!widget) return;

    if (widget.dataset.canEdit !== "1") return;

    const status = button.dataset.status;
    const url = widget.dataset.setUrl;

    widget.classList.add("is-saving");

    const buttons = widget.querySelectorAll(".problem-status-option");
    buttons.forEach(btn => btn.disabled = true);

    try {
        const response = await fetch(url, {
            method: "POST",
            credentials: "same-origin",
            headers: {
                "Content-Type": "application/json",
                "X-Requested-With": "fetch"
            },
            body: JSON.stringify({ status: status })
        });

        const data = await response.json().catch(() => ({}));

        if (!response.ok || !data.ok) {
            throw new Error(data.error || "Could not update problem status.");
        }

        widget.dataset.currentStatus = data.status;

        buttons.forEach(btn => {
            const active = btn.dataset.status === data.status;
            btn.classList.toggle("is-active", active);
            btn.setAttribute("aria-checked", active ? "true" : "false");
        });

        const label = widget.querySelector(".js-problem-status-label");
        const description = widget.querySelector(".js-problem-status-description");

        if (label) label.textContent = data.label || button.dataset.label;
        if (description) description.textContent = data.description || button.dataset.description;
          widget.style.setProperty("--status-progress", button.dataset.progress);

    } catch (err) {
        alert(err.message || "Could not update problem status.");
    } finally {
        widget.classList.remove("is-saving");

        if (widget.dataset.canEdit === "1") {
            buttons.forEach(btn => btn.disabled = false);
        }
    }
});
</script>
  
<script defer src="https://static.cloudflareinsights.com/beacon.min.js/v4513226cdae34746b4dedf0b4dfa099e1781791509496" integrity="sha512-ZE9pZaUXND66v380QUtch/5sE9tPFh2zg45pR2PB0CVkCtOREv2AJKkSidISWkysEuQ0EH8faUU5du78bx87UQ==" data-cf-beacon='{"version":"2024.11.0","token":"b8844510a8d24cfb9a8920cc04221446","r":1,"server_timing":{"name":{"cfCacheStatus":true,"cfEdge":true,"cfExtPri":true,"cfL4":true,"cfOrigin":true,"cfSpeedBrain":true},"location_startswith":null}}' crossorigin="anonymous"></script>
</body>
</html>
```

## Hosted theorem — plby (https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos639.lean)

```lean
/-- The definition of an edge (represented by its endpoints)
**n**ot being **i**n a **m**onochromatic **t**riangle. `NIMT x x` is always `False`. -/
def NIMT (x y : V) : Prop :=
  x ≠ y ∧ ¬∃ z, x ≠ z ∧ y ≠ z ∧ C s(x, y) = C s(x, z) ∧ C s(x, y) = C s(y, z)

namespace NIMT

lemma symm (hxy : NIMT C x y) : NIMT C y x := by
  grind [NIMT]

lemma irrefl : ¬NIMT C x x := by
  simp [NIMT]

lemma resolve (hxy : NIMT C x y) (hxz : x ≠ z) (hyz : y ≠ z) (hc : C s(x, y) = C s(x, z)) :
    C s(x, y) ≠ C s(y, z) ∧ C s(x, z) ≠ C s(y, z) := by
  rw [← hc, and_self]
  contrapose! hxy
  simp_rw [NIMT, not_and_or, not_not]
  tauto

end NIMT

variable (C) in
/-- A triangle of `NIMT` edges and the object intensely studied in Keevash and Sudakov's proof. -/
structure AFrame where
  /-- The A-frame's vertices – `x` is considered the head -/
  (x y z : V)
  /-- `xy` is `NIMT` -/
  nxy : NIMT C x y
  /-- `xz` is `NIMT` -/
  nxz : NIMT C x z
  /-- `yz` is `NIMT` -/
  nyz : NIMT C y z
  /-- `xz` is coloured differently from `yz` -/
  cxy : C s(x, z) ≠ C s(y, z)
  /-- `xy` is coloured differently from `yz` -/
  cxz : C s(x, y) ≠ C s(y, z)

-- An edge is "blue" with respect to an A-frame if its colour matches that of `yz`
-- and "red" if its colour matches that of `xy` and `xz`.

namespace AFrame

variable (A : AFrame C)

lemma cyz : C s(A.x, A.y) = C s(A.x, A.z) := by
  grind [A.cxy, A.cxz]

/-- All edges from `x` to outside the A-frame are blue. -/
lemma blue_xw (hw : w ∉ [A.x, A.y, A.z]) : C s(A.x, w) = C s(A.y, A.z) := by
  have h := A.nyz
  contrapose! h
  obtain ⟨hwx, hwy, hwz⟩ : A.x ≠ w ∧ A.y ≠ w ∧ A.z ≠ w := by grind
  have r₁ := A.nxy.resolve hwx hwy (by grind [A.cxz])
  have r₂ := A.nxz.resolve hwx hwz (by grind [A.cxy])
  grind [NIMT]

variable (nxw : NIMT C A.x w ∧ A.y ≠ w ∧ A.z ≠ w)

include nxw

/-- Suppose `xw` is a fourth `NIMT` edge.
Then for all fifth vertices `v`, `xv` is blue and `wv` is red. -/
lemma blue_xv_red_wv (hv : v ∉ [w, A.x, A.y, A.z]) :
    C s(A.x, v) = C s(A.x, w) ∧ C s(w, v) ≠ C s(A.x, w) := by
  obtain hw : w ∉ [A.x, A.y, A.z] := by grind [NIMT]
  have bxw := A.blue_xw hw
  rw [List.mem_cons, not_or, ← Ne.eq_def] at hv
  have bxv := A.blue_xw hv.2
  grind [nxw.1.resolve (show A.x ≠ v by grind) hv.1.symm (by grind)]

/-- Suppose `xw` is a fourth `NIMT` edge.
Then for all edges `uv` not incident to `wxyz`, `uv` is not `NIMT`. -/
lemma not_NIMT_uv (hu : u
```

## Hosted theorem — jayyhk (https://github.com/Jayyhk/erdos-lean/blob/main/problems/639/Erdos639.lean)

```lean
/-- The definition of an edge (represented by its endpoints)
**n**ot being **i**n a **m**onochromatic **t**riangle. `NIMT x x` is always `False`. -/
def NIMT (x y : V) : Prop :=
  x ≠ y ∧ ¬∃ z, x ≠ z ∧ y ≠ z ∧ C s(x, y) = C s(x, z) ∧ C s(x, y) = C s(y, z)

namespace NIMT

lemma symm (hxy : NIMT C x y) : NIMT C y x := by
  grind [NIMT]

lemma irrefl : ¬NIMT C x x := by
  simp [NIMT]

lemma resolve (hxy : NIMT C x y) (hxz : x ≠ z) (hyz : y ≠ z) (hc : C s(x, y) = C s(x, z)) :
    C s(x, y) ≠ C s(y, z) ∧ C s(x, z) ≠ C s(y, z) := by
  rw [← hc, and_self]
  contrapose! hxy
  simp_rw [NIMT, not_and_or, not_not]
  tauto

end NIMT

variable (C) in
/-- A triangle of `NIMT` edges and the object intensely studied in Keevash and Sudakov's proof. -/
structure AFrame where
  /-- The A-frame's vertices – `x` is considered the head -/
  (x y z : V)
  /-- `xy` is `NIMT` -/
  nxy : NIMT C x y
  /-- `xz` is `NIMT` -/
  nxz : NIMT C x z
  /-- `yz` is `NIMT` -/
  nyz : NIMT C y z
  /-- `xz` is coloured differently from `yz` -/
  cxy : C s(x, z) ≠ C s(y, z)
  /-- `xy` is coloured differently from `yz` -/
  cxz : C s(x, y) ≠ C s(y, z)

-- An edge is "blue" with respect to an A-frame if its colour matches that of `yz`
-- and "red" if its colour matches that of `xy` and `xz`.

namespace AFrame

variable (A : AFrame C)

lemma cyz : C s(A.x, A.y) = C s(A.x, A.z) := by
  grind [A.cxy, A.cxz]

/-- All edges from `x` to outside the A-frame are blue. -/
lemma blue_xw (hw : w ∉ [A.x, A.y, A.z]) : C s(A.x, w) = C s(A.y, A.z) := by
  have h := A.nyz
  contrapose! h
  obtain ⟨hwx, hwy, hwz⟩ : A.x ≠ w ∧ A.y ≠ w ∧ A.z ≠ w := by grind
  have r₁ := A.nxy.resolve hwx hwy (by grind [A.cxz])
  have r₂ := A.nxz.resolve hwx hwz (by grind [A.cxy])
  grind [NIMT]

variable (nxw : NIMT C A.x w ∧ A.y ≠ w ∧ A.z ≠ w)

include nxw

/-- Suppose `xw` is a fourth `NIMT` edge.
Then for all fifth vertices `v`, `xv` is blue and `wv` is red. -/
lemma blue_xv_red_wv (hv : v ∉ [w, A.x, A.y, A.z]) :
    C s(A.x, v) = C s(A.x, w) ∧ C s(w, v) ≠ C s(A.x, w) := by
  obtain hw : w ∉ [A.x, A.y, A.z] := by grind [NIMT]
  have bxw := A.blue_xw hw
  rw [List.mem_cons, not_or, ← Ne.eq_def] at hv
  have bxv := A.blue_xw hv.2
  grind [nxw.1.resolve (show A.x ≠ v by grind) hv.1.symm (by grind)]

/-- Suppose `xw` is a fourth `NIMT` edge.
Then for all edges `uv` not incident to `wxyz`, `uv` is not `NIMT`. -/
lemma not_NIMT_uv (hu : u
```

```lean
/-- **Erdős Problem 639** (Erdős–Rousseau–Schelp, completed by Keevash–Sudakov).
For any 2-colouring of the edges of `K_n` with `n ≥ 10`, the number of edges that
do not occur in a monochromatic triangle is at most `n²/4`. Matches Erdős's
literal phrasing in [Er97d]: "at most n²/4 for large n" — the "large n" hypothesis
is witnessed by `n ≥ 10`. -/
theorem erdos_639 {V : Type*} [Fintype V] [DecidableEq V] {C : Sym2 V → Fin 2}
    (hn : 10 ≤ Fintype.card V) :
    #(SimpleGraph.nimt C).edgeFinset ≤ (Fintype.card V) ^ 2 / 4
```

## Drafting rules
- Derive the statement from the problem text; the hosted theorems are a shape prior. Record EVERY divergence between your statement and each hosted theorem in draft.json divergence_notes.
- Category must match upstream state; verbatim docstring; erdos_<n> naming; one @[category], AMS tags; sorry body.
