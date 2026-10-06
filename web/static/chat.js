// Chat with the Knowledgebase (experimental): a chat that runs entirely in this
// page, opened from the button beside the dependency graph.
// The reader's own API key goes straight from the browser to the provider they
// pick -- AFTD has no server -- and the knowledgebase is searched here, in two
// tools the model calls: search_knowledgebase and get_entry. Web search is the
// provider's own tool. build.py writes the files the tools read
// (chat/kb-index.json, chat/kb-detail.json).
//
// The same file loads in Node (module.exports), so the provider code can be
// run against the real APIs without a browser.

(function () {
'use strict';

// ------------------------------------------------------------ the knowledgebase
const STOP = new Set(('a an and are as at be by can do does for from has have how i in is it its ' +
  'me of on or that the their there this to was what when where which who why with any about ' +
  'into than then them these those our we you your').split(' '));

// Words as the search compares them: camelCase, Lean's `_` and `.` split, lower
// case, and a crude plural strip so "chores" finds "chore".
function words(text) {
  const raw = String(text || '').replace(/([a-z0-9])([A-Z])/g, '$1 $2').toLowerCase()
    .match(/[0-9a-z\u00c0-\u024f\u0370-\u03ff\u0400-\u04ff]+/g) || [];
  const out = [];
  for (let w of raw) {
    if (STOP.has(w)) continue;
    if (w.length > 4 && w.endsWith('s') && !w.endsWith('ss')) w = w.slice(0, -1);
    out.push(w);
  }
  return out;
}

const clip = (s, n) => {
  s = String(s || '');
  return s.length > n ? s.slice(0, n - 1).trimEnd() + '…' : s;
};

// Fields an entry is searched by, and how much a match in each counts.
const FIELDS = [['name', 3], ['title', 3], ['informal', 1.5], ['topic', 1], ['domain', 0.5],
  ['citation', 1], ['source', 1], ['source_title', 1], ['statement', 0.7], ['known', 0.5],
  ['status', 0.5], ['provenance', 0.5]];

class Knowledgebase {
  // `index` is chat/kb-index.json; `loadDetail` fetches chat/kb-detail.json the
  // first time the model reads an entry in full; `base` is the site's root URL.
  constructor(index, loadDetail, base) {
    this.index = index;
    this.entries = index.entries;
    this.loadDetail = loadDetail;
    this.base = base;
    this.detail = null;
    this.byName = new Map(this.entries.map(e => [e.name.toLowerCase(), e]));
    this.docs = this.entries.map(e => {
      const tf = new Map();
      let len = 0;
      for (const [f, w] of FIELDS) for (const t of words(e[f])) { tf.set(t, (tf.get(t) || 0) + w); len += w; }
      return {tf, len};
    });
    this.avg = this.docs.reduce((a, d) => a + d.len, 0) / Math.max(1, this.docs.length);
    this.df = new Map();
    for (const d of this.docs) for (const t of d.tf.keys()) this.df.set(t, (this.df.get(t) || 0) + 1);
  }

  url(e) { return new URL(e.url, this.base).href; }

  static fits(e, type) {
    switch (type) {
      case 'theorem': return e.type === 'declaration' && e.status === 'verified in Lean';
      case 'definition': return e.type === 'declaration' && e.status === 'definition';
      case 'not_yet_proved': return e.type === 'declaration' && e.status.startsWith('stated');
      case 'open_problem': return e.type !== 'declaration';
      default: return true;
    }
  }

  // BM25 over the weighted fields, with a bonus for a Lean name typed exactly.
  search(query, type = 'any', limit = 8) {
    const q = [...new Set(words(query))];
    const exact = String(query || '').trim().replace(/`/g, '').toLowerCase();
    const N = this.docs.length, k1 = 1.2, b = 0.75;
    const scored = [];
    this.entries.forEach((e, i) => {
      if (!Knowledgebase.fits(e, type)) return;
      const d = this.docs[i];
      let s = 0;
      for (const t of q) {
        const f = d.tf.get(t);
        if (!f) continue;
        const df = this.df.get(t);
        s += Math.log(1 + (N - df + 0.5) / (df + 0.5)) * f * (k1 + 1) / (f + k1 * (1 - b + b * d.len / this.avg));
      }
      const name = e.name.toLowerCase();
      if (name === exact) s += 100;
      else if (exact.length > 3 && name.includes(exact.replace(/\s+/g, '_'))) s += 8;
      if (s > 0) scored.push([s, e]);
    });
    scored.sort((x, y) => y[0] - x[0]);
    return scored.slice(0, Math.max(1, Math.min(20, limit | 0 || 8))).map(([, e]) => this.brief(e));
  }

  brief(e) {
    if (e.type === 'declaration') {
      return {name: e.name, kind: e.kind, status: e.status, topic: e.topic,
        says: clip(e.informal, 360), provenance: e.provenance || undefined, url: this.url(e)};
    }
    return {ref: e.name, type: e.type, title: e.title, status: e.status, topic: e.topic,
      statement: clip(e.statement, 360), url: this.url(e)};
  }

  async get(name) {
    const key = String(name || '').trim().replace(/^`|`$/g, '').toLowerCase();
    const e = this.byName.get(key) || this.byName.get(key.replace(/^op(\d+)$/, 'op-$1'));
    if (!e) {
      // A misspelt name: what the search finds, else names sharing its start.
      let closest = this.search(name, 'any', 5).map(h => h.name || h.ref);
      if (!closest.length && key.length >= 4) {
        closest = this.entries.map(x => x.name).filter(n => n.toLowerCase().startsWith(key.slice(0, 5))).slice(0, 8);
      }
      return {error: `No entry is named ${name}.`, closest};
    }
    if (e.type !== 'declaration') {
      const {url, ...rest} = e;
      return {...rest, lean: (e.lean || []).map(l => {
        const d = this.byName.get(l.name.toLowerCase());
        return {...l, status: d ? d.status : 'not on the site', url: d ? this.url(d) : undefined};
      }), url: this.url(e)};
    }
    if (!this.detail) this.detail = await this.loadDetail();
    const x = this.detail[e.name] || {};
    const out = {...e, url: this.url(e)};
    delete out.type;
    if (x.reading) out.reading = x.reading;
    if (x.explanation) out.explanation = x.explanation;
    if (x.source) out.lean_source = clip(x.source, 8000);
    if (x.source_url) out.lean_file = x.source_url;
    if (x.axioms) out.axioms = x.axioms;
    if (x.deps && x.deps.length) out.depends_on = x.deps.slice(0, 40);
    if (x.used_by && x.used_by.length) out.used_by = x.used_by.slice(0, 40);
    return out;
  }

  async run(tool, args) {
    try {
      if (tool === 'search_knowledgebase') {
        const hits = this.search(args.query, args.type, args.limit);
        return hits.length ? {results: hits} : {results: [], note: 'Nothing matched; try other words.'};
      }
      if (tool === 'get_entry') return await this.get(args.name);
      return {error: `There is no tool called ${tool}.`};
    } catch (err) {
      return {error: String(err && err.message || err)};
    }
  }
}

const TOOLS = [
  {
    name: 'search_knowledgebase',
    description: 'Search the AFTD knowledgebase: Lean 4 declarations (theorems verified in ' +
      'Lean, definitions, and statements that type-check but are not yet proved), open ' +
      'problems from the literature, and reviewed community problems. Returns the best ' +
      'matches, each with a one-line summary, its status and a link. Use the words a paper ' +
      'would use, or a Lean name; if the results miss, search again with other words.',
    parameters: {
      type: 'object',
      properties: {
        query: {type: 'string', description: 'Words, or a Lean name.'},
        type: {type: 'string', enum: ['any', 'theorem', 'definition', 'not_yet_proved', 'open_problem'],
          description: 'Only one kind of entry. Default: any.'},
        limit: {type: 'integer', description: 'How many results, 1 to 20. Default: 8.'},
      },
      required: ['query'],
    },
  },
  {
    name: 'get_entry',
    description: 'Read one knowledgebase entry in full, by Lean name (for example ' +
      'condorcet_winner_unique) or problem reference (for example OP-7 or #12): the Lean ' +
      'statement and proof, what it depends on and what uses it, its citation, and for a ' +
      'problem what is known and which Lean declarations bear on it.',
    parameters: {
      type: 'object',
      properties: {name: {type: 'string', description: 'A Lean name, or a reference such as OP-7.'}},
      required: ['name'],
    },
  },
];

function systemPrompt(kb, web, today) {
  const t = kb.index.totals || {};
  const domains = (kb.index.domains || [])
    .map(d => `- ${d.title}: ${d.topics.join('; ')}`).join('\n');
  return `You are the research assistant of AFTD (Auto-Formalizing Theoretical Domains), a public knowledgebase of results from the theoretical sciences stated and proved in Lean 4 against Mathlib, at ${kb.base}. You talk with researchers. Today is ${today}; the snapshot you can search was taken ${String(kb.index.generated || '').slice(0, 10)} and holds ${t.declarations} declarations (${t.theorems} theorems, ${t.definitions} definitions) in ${t.topics} topics, plus open problems from the literature.

Domains and topics:
${domains}

How to answer:
- For anything about what AFTD contains, call search_knowledgebase first, then get_entry for the entries you rely on. Never say an entry exists, or what it states, unless a tool returned it. If several searches find nothing, say the knowledgebase does not cover it.
- Keep statuses exact. Only an entry whose status is "verified in Lean" is proved. "Stated in Lean, not yet proved" means the statement type-checks and nothing more. For open problems use the status given ("Settled in Lean", "Stated in Lean, Not Yet Proved", ...).
- Provenance: "formalization" is a published result proved again in Lean (the result is the cited authors'); "original" was stated and proved here; "erratum" means Lean shows a published claim false or incomplete.
- Link each entry you mention, as a Markdown link to its url, with Lean names in backticks, e.g. [\`condorcet_winner_unique\`](url).
- ${web ? 'Use web search for what the knowledgebase does not hold: papers, recent results, definitions, context. Cite web sources with links, and keep it clear which claims come from the web and which from the knowledgebase.' : 'Web search is off: answer from the knowledgebase and say when a question needs sources outside it.'}
- Write mathematics in LaTeX between $...$ (inline) or $$...$$ (display). Quote Lean code in fenced code blocks.
- Be direct and concise; researchers are reading.`;
}

// ------------------------------------------------------------------- providers
const MAX_ROUNDS = 10;

async function post(url, headers, body, signal) {
  const r = await fetch(url, {
    method: 'POST',
    headers: {'content-type': 'application/json', ...headers},
    body: JSON.stringify(body),
    signal,
  });
  const text = await r.text();
  let data = null;
  try { data = JSON.parse(text); } catch (_) {}
  if (!r.ok) {
    const e = data && (data.error || data);
    const err = new Error((e && (e.message || e.type)) || text.slice(0, 300) || r.statusText);
    err.status = r.status;
    throw err;
  }
  return data;
}

// Each provider keeps the conversation in its own format (`history`, appended
// to and never edited) and can rebuild one from the plain transcript when the
// reader switches provider. `c` carries: key, model, web, system, question,
// history, signal, tool(name, args), step({kind, text}).
const PROVIDERS = {
  gemini: {
    label: 'Google Gemini',
    model: 'gemini-3.8-flash',
    keyUrl: 'https://aistudio.google.com/apikey',
    fromTranscript: turns => turns.map(t => ({role: t.role === 'user' ? 'user' : 'model', parts: [{text: t.text}]})),
    async run(c) {
      const url = 'https://generativelanguage.googleapis.com/v1beta/models/' +
        encodeURIComponent(c.model) + ':generateContent';
      const tools = [{functionDeclarations: TOOLS}];
      if (c.web) tools.push({googleSearch: {}});
      c.history.push({role: 'user', parts: [{text: c.question}]});
      const out = {text: '', sources: [], usage: {input: 0, output: 0}};
      for (let round = 0; round < MAX_ROUNDS; round++) {
        const body = {systemInstruction: {parts: [{text: c.system}]}, contents: c.history, tools};
        // Lets Google Search and our functions share a turn.
        if (c.web) body.toolConfig = {includeServerSideToolInvocations: true};
        const data = await post(url, {'x-goog-api-key': c.key}, body, c.signal);
        const u = data.usageMetadata || {};
        out.usage.input += u.promptTokenCount || 0;
        out.usage.output += (u.candidatesTokenCount || 0) + (u.thoughtsTokenCount || 0);
        const cand = (data.candidates || [])[0];
        if (!cand) {
          const why = data.promptFeedback && data.promptFeedback.blockReason;
          throw new Error(why ? `Gemini blocked the question (${why}).` : 'Gemini returned no answer.');
        }
        const content = {role: 'model', parts: (cand.content && cand.content.parts) || []};
        c.history.push(content);
        for (const ch of (cand.groundingMetadata && cand.groundingMetadata.groundingChunks) || []) {
          if (ch.web && ch.web.uri) out.sources.push({url: ch.web.uri, title: ch.web.title || ch.web.uri});
        }
        for (const p of content.parts) {
          if (p.toolCall && /SEARCH/.test(p.toolCall.toolType || '')) {
            c.step({kind: 'web', text: ((p.toolCall.args || {}).queries || []).join(' · ')});
          }
        }
        const calls = content.parts.filter(p => p.functionCall);
        if (!calls.length) {
          out.text = content.parts.filter(p => p.text && !p.thought).map(p => p.text).join('');
          if (!out.text && cand.finishReason && cand.finishReason !== 'STOP') {
            out.text = `_The model stopped without an answer (${cand.finishReason})._`;
          }
          return out;
        }
        const parts = [];
        for (const p of calls) {
          const {name, args, id} = p.functionCall;
          c.step({kind: name, text: describe(name, args || {})});
          const result = await c.tool(name, args || {});
          parts.push({functionResponse: {name, ...(id ? {id} : {}), response: {result}}});
        }
        c.history.push({role: 'user', parts});
      }
      out.text = '_Stopped after too many tool calls; ask again more narrowly._';
      return out;
    },
  },

  anthropic: {
    label: 'Anthropic Claude',
    model: 'claude-opus-5-5',
    keyUrl: 'https://console.anthropic.com/settings/keys',
    fromTranscript: turns => turns.map(t => ({role: t.role, content: t.text})),
    async run(c) {
      const tools = TOOLS.map(t => ({name: t.name, description: t.description, input_schema: t.parameters}));
      if (c.web) {
        // The dynamic-filtering web search needs a recent model; older ones get the basic one.
        const recent = /claude-(opus-(4-[6-9]|5)|sonnet-(4-6|5)|fable)/.test(c.model);
        tools.push({type: recent ? 'web_search_20260209' : 'web_search_20250305', name: 'web_search', max_uses: 5});
      }
      // Server-side fallback when a safety classifier declines, on the models that have it.
      let fallbacks = /claude-(fable-5-1|opus-5|sonnet-5-5)/.test(c.model);
      c.history.push({role: 'user', content: c.question});
      const out = {text: '', sources: [], usage: {input: 0, output: 0}};
      for (let round = 0; round < MAX_ROUNDS; round++) {
        const headers = {
          'x-api-key': c.key,
          'anthropic-version': '2023-06-01',
          'anthropic-dangerous-direct-browser-access': 'true',
        };
        const body = {model: c.model, max_tokens: 16000, system: c.system, messages: c.history,
          tools, cache_control: {type: 'ephemeral'}};
        if (fallbacks) {
          headers['anthropic-beta'] = 'server-side-fallback-2026-07-01';
          body.fallbacks = 'default';
        }
        let data;
        try {
          data = await post('https://api.anthropic.com/v1/messages', headers, body, c.signal);
        } catch (err) {
          if (fallbacks && err.status === 400 && /fallback|beta/i.test(err.message)) {
            fallbacks = false;
            round--;
            continue;
          }
          throw err;
        }
        const u = data.usage || {};
        out.usage.input += (u.input_tokens || 0) + (u.cache_read_input_tokens || 0) + (u.cache_creation_input_tokens || 0);
        out.usage.output += u.output_tokens || 0;
        const content = data.content || [];
        c.history.push({role: 'assistant', content});
        for (const b of content) {
          if (b.type === 'server_tool_use' && b.name === 'web_search') {
            c.step({kind: 'web', text: (b.input || {}).query || ''});
          }
          for (const ci of (b.type === 'text' && b.citations) || []) {
            if (ci.url) out.sources.push({url: ci.url, title: ci.title || ci.url});
          }
        }
        if (data.stop_reason === 'pause_turn') continue;  // the server resumes its own loop
        if (data.stop_reason === 'tool_use') {
          const results = [];
          for (const b of content.filter(b => b.type === 'tool_use')) {
            c.step({kind: b.name, text: describe(b.name, b.input || {})});
            const r = await c.tool(b.name, b.input || {});
            results.push({type: 'tool_result', tool_use_id: b.id, content: JSON.stringify(r),
              ...(r && r.error ? {is_error: true} : {})});
          }
          c.history.push({role: 'user', content: results});
          continue;
        }
        out.text = content.filter(b => b.type === 'text').map(b => b.text).join('');
        if (data.stop_reason === 'refusal') out.text += '\n\n_The model declined to answer this._';
        if (data.stop_reason === 'max_tokens') out.text += '\n\n_The answer was cut off at the length limit._';
        return out;
      }
      out.text = '_Stopped after too many tool calls; ask again more narrowly._';
      return out;
    },
  },

  openai: {
    label: 'OpenAI',
    model: 'gpt-5.5',
    keyUrl: 'https://platform.openai.com/api-keys',
    fromTranscript: turns => turns.map(t => ({role: t.role, content: t.text})),
    async run(c) {
      const tools = TOOLS.map(t => ({type: 'function', name: t.name, description: t.description,
        parameters: t.parameters}));
      if (c.web) tools.push({type: 'web_search'});
      c.history.push({role: 'user', content: c.question});
      const out = {text: '', sources: [], usage: {input: 0, output: 0}};
      for (let round = 0; round < MAX_ROUNDS; round++) {
        // Nothing is stored at OpenAI: reasoning comes back encrypted and is
        // sent again with the rest of the conversation.
        const body = {model: c.model, instructions: c.system, input: c.history, tools,
          store: false, include: ['reasoning.encrypted_content']};
        const data = await post('https://api.openai.com/v1/responses',
          {authorization: 'Bearer ' + c.key}, body, c.signal);
        const u = data.usage || {};
        out.usage.input += u.input_tokens || 0;
        out.usage.output += u.output_tokens || 0;
        const items = data.output || [];
        c.history.push(...items);
        let text = '';
        for (const it of items) {
          if (it.type === 'web_search_call') {
            const a = it.action || {};
            c.step({kind: 'web', text: a.query || (a.queries || []).join(' · ') || a.url || ''});
          }
          if (it.type === 'message') {
            for (const part of it.content || []) {
              if (part.type !== 'output_text') continue;
              text += part.text;
              for (const a of part.annotations || []) {
                if (a.type === 'url_citation' && a.url) out.sources.push({url: a.url, title: a.title || a.url});
              }
            }
          }
        }
        const calls = items.filter(it => it.type === 'function_call');
        if (!calls.length) {
          out.text = text;
          if (data.status === 'incomplete') out.text += '\n\n_The answer was cut off._';
          return out;
        }
        for (const call of calls) {
          let args = {};
          try { args = JSON.parse(call.arguments || '{}'); } catch (_) {}
          c.step({kind: call.name, text: describe(call.name, args)});
          const r = await c.tool(call.name, args);
          c.history.push({type: 'function_call_output', call_id: call.call_id, output: JSON.stringify(r)});
        }
      }
      out.text = '_Stopped after too many tool calls; ask again more narrowly._';
      return out;
    },
  },
};

function describe(tool, args) {
  if (tool === 'search_knowledgebase') return String(args.query || '');
  if (tool === 'get_entry') return String(args.name || '');
  return '';
}

// One question, asked with whatever the conversation already holds. On failure
// the provider's history is put back as it was, so the next question starts
// from a consistent conversation.
async function ask(c) {
  const p = PROVIDERS[c.provider];
  const mark = c.history.length;
  try {
    const out = await p.run({...c, tool: (name, args) => c.kb.run(name, args)});
    const seen = new Set();
    out.sources = out.sources.filter(s => !seen.has(s.url) && seen.add(s.url));
    return out;
  } catch (err) {
    c.history.length = mark;
    throw err;
  }
}

const Core = {words, Knowledgebase, TOOLS, PROVIDERS, systemPrompt, ask};
if (typeof module !== 'undefined' && module.exports) module.exports = Core;
if (typeof document === 'undefined') return;

// --------------------------------------------------------------------- the page
const root = document.getElementById('chat');
if (!root) return;
const $ = id => document.getElementById(id);
const el = {
  set: $('chat-set'), sum: $('chat-set-sum'), provider: $('chat-provider'), model: $('chat-model'),
  key: $('chat-key'), web: $('chat-web'), remember: $('chat-remember'), keylink: $('chat-keylink'),
  log: $('chat-log'), empty: $('chat-empty'), form: $('chat-form'), q: $('chat-q'),
  send: $('chat-send'), fresh: $('chat-new'), usage: $('chat-usage'),
};
const base = new URL('../', location.href).href;

// Storage can be missing or refuse (private windows, blocked site data): the
// page works without it, it just forgets.
const store = {
  get(area, k) { try { return window[area].getItem('aftd-chat:' + k); } catch (_) { return null; } },
  set(area, k, v) { try { v == null ? window[area].removeItem('aftd-chat:' + k) : window[area].setItem('aftd-chat:' + k, v); } catch (_) {} },
};
let settings = {};
try { settings = JSON.parse(store.get('localStorage', 'settings') || '{}') || {}; } catch (_) {}
settings.models = settings.models || {};

function keyFor(p) {
  return store.get('sessionStorage', 'key:' + p) || store.get('localStorage', 'key:' + p) || '';
}
function saveKey() {
  const p = el.provider.value, k = el.key.value.trim();
  store.set('sessionStorage', 'key:' + p, k || null);
  store.set('localStorage', 'key:' + p, el.remember.checked && k ? k : null);
}
function saveSettings() {
  settings.provider = el.provider.value;
  settings.models[el.provider.value] = el.model.value.trim();
  settings.web = el.web.checked;
  settings.remember = el.remember.checked;
  store.set('localStorage', 'settings', JSON.stringify(settings));
}
function showProvider() {
  const p = el.provider.value;
  el.model.value = settings.models[p] || PROVIDERS[p].model;
  el.model.placeholder = PROVIDERS[p].model;
  el.key.value = keyFor(p);
  el.keylink.href = PROVIDERS[p].keyUrl;
  el.keylink.textContent = `Get a ${PROVIDERS[p].label} key`;
  summary();
}
function summary() {
  const k = el.key.value.trim();
  el.sum.textContent = `${PROVIDERS[el.provider.value].label} · ${el.model.value.trim() || PROVIDERS[el.provider.value].model}` +
    (el.web.checked ? ' · web' : '') + (k ? ' · key set' : ' · no key yet');
}

el.provider.value = PROVIDERS[settings.provider] ? settings.provider : 'gemini';
el.web.checked = settings.web !== false;
el.remember.checked = !!settings.remember;
showProvider();
if (el.key.value) el.set.open = false;
el.provider.addEventListener('change', () => { showProvider(); saveSettings(); });
el.model.addEventListener('change', () => { saveSettings(); summary(); });
el.web.addEventListener('change', () => { saveSettings(); summary(); });
el.key.addEventListener('input', () => { saveKey(); summary(); });
el.remember.addEventListener('change', () => { saveKey(); saveSettings(); });

// The knowledgebase files load once, on the first question.
let kbPromise = null;
function loadKb() {
  if (!kbPromise) {
    const get = u => fetch(u).then(r => { if (!r.ok) throw new Error(`Could not load ${u} (${r.status})`); return r.json(); });
    kbPromise = get(root.dataset.index)
      .then(index => new Knowledgebase(index, () => get(root.dataset.detail), base))
      .catch(err => { kbPromise = null; throw err; });
  }
  return kbPromise;
}

// The conversation: what the reader sees (`turns`, kept for a reload) and the
// provider's own record of it (`native`), rebuilt from the turns when the
// provider or model changes.
let turns = [];
try { turns = JSON.parse(store.get('localStorage', 'turns') || '[]') || []; } catch (_) {}
let native = null;
let busy = null;
let spent = {input: 0, output: 0};

// ------------------------------------------------------------------ rendering
const esc = s => String(s).replace(/[&<>"']/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'}[c]));

function safeUrl(u) {
  try {
    const url = new URL(u, base);
    return /^https?:$/.test(url.protocol) ? url.href : null;
  } catch (_) { return null; }
}

// A small Markdown renderer for the model's answers. Everything is escaped
// first; math is set aside so KaTeX gets it untouched, and code so nothing
// inside it is formatted.
function markdown(src, kb) {
  const keep = [];
  const hold = html => `\u0000${keep.push(html) - 1}\u0000`;
  let s = String(src || '').replace(/\r\n?/g, '\n');
  s = s.replace(/```[^\n]*\n([\s\S]*?)(?:```|$)/g, (_, code) => hold(`<pre class="chat-code"><code>${esc(code.replace(/\n$/, ''))}</code></pre>`));
  s = s.replace(/\$\$[\s\S]+?\$\$|\\\[[\s\S]+?\\\]|\\\([\s\S]+?\\\)|\$[^$\n]+?\$/g, m => hold(esc(m)));
  // A Lean name in backticks links to its page, unless it is already the
  // label of a Markdown link.
  s = s.replace(/(\[?)`([^`\n]+)`(\]\()?/g, (_, open, code, close) => {
    const e = !(open && close) && kb && kb.byName.get(code.toLowerCase());
    return open + hold(e && e.type === 'declaration'
      ? `<a class="decl" href="${esc(kb.url(e))}"><code>${esc(code)}</code></a>` : `<code>${esc(code)}</code>`) + (close || '');
  });
  s = esc(s);
  const inline = t => t
    .replace(/\[([^\]\n]+)\]\(([^)\s]+)\)/g, (m, label, u) => {
      const url = safeUrl(u.replace(/&amp;/g, '&'));
      if (!url) return label;
      const ext = !url.startsWith(base);
      return hold(`<a href="${esc(url)}"${ext ? ' target="_blank" rel="noopener noreferrer"' : ''}>`) + label + '</a>';
    })
    .replace(/\*\*([^*\n]+)\*\*/g, '<strong>$1</strong>')
    .replace(/(^|[\s(])\*([^*\s][^*\n]*?)\*(?=[\s).,;:!?]|$)/g, '$1<em>$2</em>')
    .replace(/(^|[\s(])_([^_\s][^_\n]*?)_(?=[\s).,;:!?]|$)/g, '$1<em>$2</em>');
  const out = [];
  let list = null;
  const close = () => { if (list) { out.push(`</${list}>`); list = null; } };
  let para = [];
  const flush = () => { if (para.length) { out.push(`<p>${inline(para.join(' '))}</p>`); para = []; } };
  for (const line of s.split('\n')) {
    let m;
    if (!line.trim()) { flush(); close(); continue; }
    if (/^\u0000\d+\u0000$/.test(line.trim()) && keep[+line.trim().slice(1, -1)].startsWith('<pre')) {
      flush(); close(); out.push(line.trim()); continue;
    }
    if ((m = line.match(/^(#{1,4})\s+(.*)$/))) {
      flush(); close();
      const h = Math.min(4, m[1].length + 2);
      out.push(`<h${h}>${inline(m[2])}</h${h}>`); continue;
    }
    if ((m = line.match(/^\s*([-*+]|\d+[.)])\s+(.*)$/))) {
      flush();
      const kind = /\d/.test(m[1]) ? 'ol' : 'ul';
      if (list !== kind) { close(); out.push(`<${kind}>`); list = kind; }
      out.push(`<li>${inline(m[2])}</li>`); continue;
    }
    if (/^\s*(---|\*\*\*)\s*$/.test(line)) { flush(); close(); out.push('<hr>'); continue; }
    if ((m = line.match(/^&gt;\s?(.*)$/))) { flush(); close(); out.push(`<blockquote>${inline(m[1])}</blockquote>`); continue; }
    if (list && /^\s{2,}\S/.test(line)) { out[out.length - 1] = out[out.length - 1].replace(/<\/li>$/, ' ' + inline(line.trim()) + '</li>'); continue; }
    close();
    para.push(line.trim());
  }
  flush(); close();
  let html = out.join('\n');
  for (let i = 0; i < 3 && html.includes('\u0000'); i++) html = html.replace(/\u0000(\d+)\u0000/g, (_, n) => keep[+n]);
  return html;
}

function typeset(node) {
  if (window.renderMathInElement) {
    try {
      window.renderMathInElement(node, {
        delimiters: [{left: '$$', right: '$$', display: true}, {left: '\\[', right: '\\]', display: true},
          {left: '$', right: '$', display: false}, {left: '\\(', right: '\\)', display: false}],
        ignoredTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code'],
        throwOnError: false,
      });
    } catch (_) {}
  }
}

const STEP_WORDS = {
  search_knowledgebase: 'Searched the knowledgebase for',
  get_entry: 'Read',
  web: 'Searched the web for',
};

function stepsHtml(steps) {
  if (!steps || !steps.length) return '';
  return `<ul class="chat-steps">${steps.map(s =>
    `<li data-kind="${esc(s.kind)}">${esc(STEP_WORDS[s.kind] || s.kind)} ${s.kind === 'get_entry' ? `<code>${esc(s.text)}</code>` : (s.text ? `“${esc(s.text)}”` : '')}</li>`).join('')}</ul>`;
}

function sourcesHtml(sources) {
  if (!sources || !sources.length) return '';
  const items = sources.map(s => {
    const url = safeUrl(s.url);
    return url ? `<li><a href="${esc(url)}" target="_blank" rel="noopener noreferrer">${esc(clip(s.title, 90))}</a></li>` : '';
  }).join('');
  return `<details class="chat-sources"><summary>Web sources (${sources.length})</summary><ol>${items}</ol></details>`;
}

function turnNode(t, kb) {
  const div = document.createElement('div');
  div.className = 'chat-turn ' + (t.role === 'user' ? 'me' : 'ai');
  if (t.role === 'user') {
    div.innerHTML = `<div class="chat-bubble">${esc(t.text).replace(/\n/g, '<br>')}</div>`;
    typeset(div);
  } else {
    div.innerHTML = stepsHtml(t.steps) +
      `<div class="chat-answer prose">${t.error ? `<p class="chat-err">${esc(t.text)}</p>` : markdown(t.text, kb)}</div>` +
      sourcesHtml(t.sources) +
      (t.error ? '' : `<div class="chat-meta"><button type="button" class="linkish" data-copy>Copy</button>` +
        (t.model ? `<span class="small">${esc(t.model)}</span>` : '') + '</div>');
    const copy = div.querySelector('[data-copy]');
    if (copy) copy.addEventListener('click', () => {
      const done = () => { copy.textContent = 'Copied'; setTimeout(() => { copy.textContent = 'Copy'; }, 1500); };
      if (navigator.clipboard) navigator.clipboard.writeText(t.text).then(done, () => {});
    });
    typeset(div.querySelector('.chat-answer'));
  }
  return div;
}

function renderAll(kb) {
  el.log.querySelectorAll('.chat-turn').forEach(n => n.remove());
  el.empty.hidden = turns.length > 0;
  for (const t of turns) el.log.appendChild(turnNode(t, kb));
}

function saveTurns() {
  // Keep the last 40 turns: enough to pick up where one left off.
  store.set('localStorage', 'turns', JSON.stringify(turns.slice(-40)));
}

function setBusy(on) {
  el.send.textContent = on ? 'Stop' : 'Ask';
  el.send.classList.toggle('stop', on);
  el.q.disabled = false;
}

// -------------------------------------------------------------------- asking
async function submit(question) {
  question = question.trim();
  if (!question) return;
  const provider = el.provider.value;
  const key = el.key.value.trim();
  const model = el.model.value.trim() || PROVIDERS[provider].model;
  if (!key) {
    el.set.open = true;
    el.key.focus();
    el.key.classList.add('want');
    setTimeout(() => el.key.classList.remove('want'), 1600);
    return;
  }
  el.q.value = '';
  el.empty.hidden = true;
  const user = {role: 'user', text: question};
  turns.push(user);
  el.log.appendChild(turnNode(user));
  const pending = document.createElement('div');
  pending.className = 'chat-turn ai pending';
  pending.innerHTML = '<ul class="chat-steps"></ul><p class="chat-wait small">Thinking…</p>';
  el.log.appendChild(pending);
  pending.scrollIntoView({block: 'nearest', behavior: 'smooth'});
  const steps = [];
  const ctrl = new AbortController();
  busy = ctrl;
  setBusy(true);
  let kb = null;
  try {
    kb = await loadKb();
    const fingerprint = provider + '|' + model;
    if (!native || native.fingerprint !== fingerprint) {
      // Earlier turns go in as plain text: tool calls and thinking belong to
      // the provider that made them.
      native = {fingerprint, history: PROVIDERS[provider].fromTranscript(
        turns.slice(0, -1).filter(t => !t.error).map(t => ({role: t.role, text: t.text})))};
    }
    const today = new Date().toISOString().slice(0, 10);
    const out = await ask({
      provider, key, model, kb,
      web: el.web.checked,
      system: systemPrompt(kb, el.web.checked, today),
      question,
      history: native.history,
      signal: ctrl.signal,
      step(s) {
        steps.push(s);
        pending.querySelector('.chat-steps').outerHTML = stepsHtml(steps) || '<ul class="chat-steps"></ul>';
      },
    });
    spent.input += out.usage.input;
    spent.output += out.usage.output;
    el.usage.textContent = `${spent.input.toLocaleString()} tokens in, ${spent.output.toLocaleString()} out this session`;
    const t = {role: 'assistant', text: out.text || '_No answer._', sources: out.sources, steps, model};
    turns.push(t);
    pending.replaceWith(turnNode(t, kb));
  } catch (err) {
    // The question stays on screen with the error; it is not sent again.
    native = null;
    let msg = String(err && err.message || err);
    if (err && err.name === 'AbortError') msg = 'Stopped.';
    else if (err && (err.status === 401 || err.status === 403)) msg = `The provider refused the key (${err.status}): ${msg}`;
    else if (err && err.status === 404) msg = `The provider does not know this model (${model}): ${msg}`;
    else if (err && err.status === 429) msg = `Rate limited or out of credit (429): ${msg}`;
    else if (err instanceof TypeError) msg = `Could not reach the provider: ${msg}`;
    const t = {role: 'assistant', text: msg, steps, error: true};
    turns.push(t);
    pending.replaceWith(turnNode(t, kb));
  } finally {
    busy = null;
    setBusy(false);
    saveTurns();
    el.q.focus();
  }
}

el.form.addEventListener('submit', ev => {
  ev.preventDefault();
  if (busy) { busy.abort(); return; }
  submit(el.q.value);
});
el.q.addEventListener('keydown', ev => {
  if (ev.key === 'Enter' && !ev.shiftKey && !ev.isComposing) {
    ev.preventDefault();
    if (!busy) submit(el.q.value);
  }
});
el.log.addEventListener('click', ev => {
  const chip = ev.target.closest('.chip');
  if (chip && !busy) submit(chip.textContent);
});
el.fresh.addEventListener('click', () => {
  if (busy) busy.abort();
  turns = [];
  native = null;
  saveTurns();
  renderAll(null);
  el.q.focus();
});

// A conversation left from an earlier visit is shown again, with its links.
if (turns.length) {
  renderAll(null);
  loadKb().then(renderAll, () => {});
}
})();
