// ==UserScript==
// @name         Bling -> Sisfrete | Cotacao de pedidos
// @namespace    local.bling.sisfrete.cotacao
// @version      1.9.1
// @description  v1.9.1: confirmacao robusta de CD e Canal de Vendas apos atualizacao do formulario.
// @match        https://bling.com.br/*
// @match        https://www.bling.com.br/*
// @match        https://cliente.sisfrete.com.br/*
// @homepageURL  https://github.com/kenuyyy/Bling-Sisfrete-Cota-o-
// @updateURL    https://raw.githubusercontent.com/kenuyyy/Bling-Sisfrete-Cota-o-/main/cotacao-sisfrete.user.js
// @downloadURL  https://raw.githubusercontent.com/kenuyyy/Bling-Sisfrete-Cota-o-/main/cotacao-sisfrete.user.js
// @noframes
// @run-at       document-idle
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_openInTab
// @grant        GM_listValues
// @grant        GM_deleteValue
// @grant        GM_addValueChangeListener
// @grant        GM_setClipboard
// @grant        GM_xmlhttpRequest
// @connect      raw.githubusercontent.com
// ==/UserScript==

(() => {
  'use strict';

  /*
   * VERSAO 1.9 — F8 no Bling captura, reutiliza a guia da Sisfrete, navega ao
   * formulario e preenche/cota conforme configuracao. Atualizacoes GitHub ativas.
   * Instalar a partir do arquivo cotacao-sisfrete.user.js do repositorio publico.
   * F8 e acoes manuais sao mantidos; a cotacao nao contrata frete.
   * Resolve controles pela estrutura DOM, sem depender de colunas no zoom.
   * Nao grava, salva nem altera o pedido do Bling.
   * Nao seleciona transportadora ou contrata frete. Apenas solicita cotacao.
   * Nao adivinha informacoes ausentes: bloqueia a cotacao e fornece diagnostico.
   * Os dados ficam no armazenamento local da extensao Tampermonkey.
   */
  const VERSION = '2.0.0';
  const VERSION_URL = 'https://raw.githubusercontent.com/kenuyyy/Bling-Sisfrete-Cota-o-/main/cotacao-sisfrete.user.js';
  const VERSION_CACHE = 'bs_version_cache_v20';
  const ERROR_HISTORY = 'bs_error_history_v20';
  const QUOTE_GUARD = 'bs_cotacao_guard_v20';
  function submitOnce(account,order) {
    // Reservar imediatamente antes do unico clique em Cotar.
    const key=QUOTE_GUARD+'_'+encodeURIComponent(account)+'_'+encodeURIComponent(order);
    const previous=GM_getValue(key,null);
    if(previous && Number.isFinite(previous.at) && Date.now()-previous.at<3*60000) {
      throw new Error('Esta cotacao ja foi solicitada nos ultimos 3 minutos. Confira o resultado antes de solicitar novamente.');
    }
    GM_setValue(key,{at:Date.now(),account,order,version:VERSION});
  }
  const KEY = 'bling_para_sisfrete_cotacao_v1';
  const HOTKEY_KEY = 'bling_para_sisfrete_atalhos_v1';
  const DEST_KEY = 'bling_para_sisfrete_destinos_por_conta_v1';
  const TAB_LIVE_PREFIX = 'bling_para_sisfrete_live_tab_v1_';
  const TAB_REQ_PREFIX = 'bling_para_sisfrete_reuse_req_v1_';
  const TAB_ACK_PREFIX = 'bling_para_sisfrete_reuse_ack_v1_';
  const OPEN_REQ_PREFIX = 'bling_para_sisfrete_abertura_v19_';
  const OPEN_HASH_PREFIX = '#bs-cotacao-';
  const TAB_TTL_MS = 180000; // abas em segundo plano podem ter timers reduzidos pelo navegador
  const RESUME_KEY = 'bs_cotacao_resume_v16'; // sessionStorage: somente apos F8 nesta aba
  const COMPARE_KEY = 'bs_cotacao_compare_v16'; // sessionStorage: leitura, nunca contrata frete
  const COMPARE_MAX_AGE_MS = 15 * 60 * 1000;
  const SIS_TAB_ID = `${Date.now()}_${Math.random().toString(36).slice(2)}`;
  let sisTabLastFocused = Date.now();
  const CD_LONG = 'BABUS COMERCIO VAREJISTA DE MOVEIS E OBJETOS DE DECORACAO LTDA';
  const DEFAULT_SETTINGS = Object.freeze({ hotkey: 'F8', openAfterCapture: true, sisAction: 'quote', panelHidden: false });
  const URL_SISFRETE = 'https://cliente.sisfrete.com.br/cotacao/nova-cotacao/form';
  const IS_BLING = /(^|\.)bling\.com\.br$/.test(location.hostname);
  const IS_SIS = location.hostname === 'cliente.sisfrete.com.br';
  const IS_SIS_QUOTE = () => location.pathname.startsWith('/cotacao/nova-cotacao/form');
  const sleep = ms => new Promise(r => setTimeout(r, ms));
  const norm = v => String(v ?? '').normalize('NFD').replace(/[\u0300-\u036f]/g, '')
    .replace(/\s+/g, ' ').replace(/\s*\*\s*/g, '').replace(/\s*:\s*$/g, '')
    .trim().toLowerCase();
  const position = el => el.getBoundingClientRect();
  const centerX = r => (r.left + r.right) / 2;
  const centerY = r => (r.top + r.bottom) / 2;
  const overlaps = (x, y, d = 14) => Math.abs(x - y) <= d;
  const msgPrefix = '[Bling > Sisfrete]';
  const log = (...v) => console.log(msgPrefix, ...v);
  let panel, launcher, statusEl, previewEl, actionGrid;
  let busy = false;
  let lastError = '';
  let recordingHotkey = false;
  let recordButton = null;
  let hotkeySummary = null;
  let destinationSummary = null;
  let destinationSubtitle = null;
  let resultSection = null;
  let resultList = null;
  let resultMeta = null;
  let comparisonObserver = null;
  let comparisonTimer = null;
  let comparisonBusy = false;
  let lastComparison = [];
  let stageName='pronto', actionName='', noticeVersion=null, newestVersion='';
  function stage(value) { stageName=value; log('Etapa',value); }
  function cmpVersions(x,y) {
    const a=String(x).split('.').map(Number), b=String(y).split('.').map(Number);
    if([...a,...b].some(n=>!Number.isInteger(n)||n<0))return 0;
    for(let i=0;i<Math.max(a.length,b.length);i++) {
      if((a[i]||0)!==(b[i]||0))return (a[i]||0)>(b[i]||0)?1:-1;
    }
    return 0;
  }
  function failures() {
    try {const a=GM_getValue(ERROR_HISTORY,[]);return Array.isArray(a)?a:[];}
    catch(_) {return [];}
  }
  function saveFailure(err) {
    try {
      const data=getData();
      const event={time:new Date().toISOString(),version:VERSION,action:actionName||'acao',
        stage:stageName,site:IS_BLING?'bling':'sisfrete',route:location.pathname,
        order:data?.order||null,account:IS_SIS?sisAccountKey():null,
        message:String(err?.message||err).slice(0,500)};
      GM_setValue(ERROR_HISTORY,[...failures(),event].slice(-15));
    } catch(e) {console.warn(msgPrefix,'Nao consegui registrar erro',e);}
  }
  function refreshVersionNotice() {
    if(!noticeVersion)return;
    const found=newestVersion && cmpVersions(newestVersion,VERSION)>0;
    noticeVersion.hidden=!found;
    noticeVersion.textContent=found ?
      'Atualizacao '+newestVersion+' disponivel. Verifique atualizacoes no Tampermonkey.' : '';
  }
  function checkNewVersion(force=false) {
    if(typeof GM_xmlhttpRequest!=='function')return;
    const cache=GM_getValue(VERSION_CACHE,{})||{};
    if(!force && Number.isFinite(cache.at) && Date.now()-cache.at<6*3600000) {
      newestVersion=String(cache.version||'');refreshVersionNotice();return;
    }
    try {
      GM_xmlhttpRequest({method:'GET',url:VERSION_URL,timeout:10000,
        headers:{'Cache-Control':'no-cache'},
        onload:r=>{
          if(r.status!==200)return;
          const match=String(r.responseText||'').match(/^\s*\/\/\s*@version\s+(\d+\.\d+(?:\.\d+)?)/m);
          if(!match)return;
          newestVersion=match[1];
          GM_setValue(VERSION_CACHE,{at:Date.now(),version:newestVersion});
          refreshVersionNotice();
        }, ontimeout:()=>console.warn(msgPrefix,'Verificacao de versao expirou'),
        onerror:()=>console.warn(msgPrefix,'Nao foi possivel verificar versao')
      });
    } catch(e) {console.warn(msgPrefix,'Nao foi possivel iniciar verificacao de versao',e);}
  }


  function visible(el) {
    if (!el || el.closest('#bs-quote-panel')) return false;
    const rect = position(el);
    if (!rect.width || !rect.height) return false;
    const css = getComputedStyle(el);
    return css.display !== 'none' && css.visibility !== 'hidden';
  }
  function controls() {
    return [...document.querySelectorAll('input, select, textarea')].filter(el => {
      return visible(el) && el.type !== 'hidden' && position(el).width >= 30;
    });
  }

  // O Range aponta para o texto real da etiqueta, sem depender de IDs dinamicos.
  function textMatches(wanted, opts = {}) {
    const result = [];
    const target = norm(wanted);
    const walker = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT);
    let node;
    while ((node = walker.nextNode())) {
      const actual = norm(node.nodeValue);
      if (actual !== target && !(opts.prefix && actual.startsWith(target))) continue;
      const parent = node.parentElement;
      if (!parent || !visible(parent)) continue;
      const range = document.createRange();
      range.selectNodeContents(node);
      const r = range.getBoundingClientRect();
      if (!r.width || !r.height) continue;
      if (opts.after != null && r.top <= opts.after) continue;
      if (opts.before != null && r.top >= opts.before) continue;
      result.push({ node: parent, rect: r, actual });
    }
    return result.sort((a, b) => a.rect.top - b.rect.top);
  }
  function textOne(wanted, opts) {
    return textMatches(wanted, opts)[0] || null;
  }
  // Ordem estrutural do DOM nao muda com zoom, largura da janela ou quebra de linhas.
  function beforeInDom(a, b) {
    return !!(a && b && (a.compareDocumentPosition(b) & Node.DOCUMENT_POSITION_FOLLOWING));
  }
  function nonPanelControls(root) {
    return [...root.querySelectorAll('input,select,textarea')]
      .filter(el => visible(el) && el.type !== 'hidden' && !el.closest('#bs-quote-panel'));
  }
  function structuralField(anchor) {
    if (!anchor) return null;
    const node = anchor.node;
    const label = node.closest('label[for]');
    if (label) {
      const target = document.getElementById(label.getAttribute('for'));
      if (target && target.matches('input,select,textarea') && visible(target)) return target;
    }
    // Comecar no proprio bloco rotulado; nao pegar campos de blocos vizinhos.
    for (let parent = node, depth = 0; parent && depth < 6; parent = parent.parentElement, depth++) {
      if (parent === document.body || parent.matches('#bs-quote-panel')) break;
      const fields = nonPanelControls(parent);
      if (fields.length === 1) return fields[0];
      if (fields.length > 1) break;
    }
    // Correspondencia acessivel: labels/aria nao dependem do layout.
    const rawName = (node.textContent || '').trim();
    const matches = controls().filter(el =>
      [el.getAttribute('aria-label'), el.getAttribute('placeholder'), el.getAttribute('title')]
        .some(value => norm(value) === norm(rawName)));
    return matches.length === 1 ? matches[0] : null;
  }
  function fieldByName(name, options = {}) {
    const matches = textMatches(name, options);
    for (const anchor of matches) {
      const f = structuralField(anchor);
      if (f) return f;
    }
    // No Sisfrete nao usar coordenadas como alternativa: em zoom podem apontar
    // para um campo DIFERENTE e produzir cotacoes erradas.
    if (IS_SIS) return null;
    for (const anchor of matches) {
      const r = anchor.rect;
      const possible = controls().map(input => {
        const a = position(input);
        const dx = Math.abs(a.left - r.left), dy = a.top - r.bottom;
        return { input, dx, dy };
      }).filter(x => x.dx <= (options.maxX ?? 110) && x.dy >= -10 && x.dy <= (options.maxY ?? 80))
        .sort((a, b) => a.dx + a.dy * 2 - (b.dx + b.dy * 2));
      if (possible.length) return possible[0].input;
    }
    return null;
  }
  function requireField(name, options) {
    const el = fieldByName(name, options);
    if (!el) throw new Error(`Nao identifiquei o campo "${name}" com seguranca na estrutura do formulario. Use Diagnostico (zoom/layout).`);
    return el;
  }
  function inputText(el) { return String(el?.value ?? '').trim(); }
  function digits(s) { return String(s ?? '').replace(/\D/g, ''); }
  function moneyCents(raw) {
    let s = String(raw ?? '').replace(/[^0-9,.\-]/g, '');
    if (!s) return NaN;
    if (s.includes(',')) s = s.replace(/\./g, '').replace(',', '.');
    else if ((s.match(/\./g) || []).length > 1) {
      const parts = s.split('.'); s = parts.slice(0, -1).join('') + '.' + parts.at(-1);
    }
    const v = Number(s);
    return Number.isFinite(v) ? Math.round(v * 100) : NaN;
  }
  function decimal(raw) {
    let s = String(raw ?? '').trim();
    if (!s) return NaN;
    if (s.includes(',')) s = s.replace(/\./g, '').replace(',', '.');
    const n = Number(s);
    return Number.isFinite(n) ? n : NaN;
  }
  function quantity(raw) {
    let s = String(raw ?? '').trim();
    if (s.includes(',')) s = s.replace(/\./g, '').replace(',', '.');
    const n = Number(s);
    return Number.isInteger(n) && n > 0 ? n : NaN;
  }
  function brMoney(cents) { return (cents / 100).toLocaleString('pt-BR', { minimumFractionDigits: 2, maximumFractionDigits: 2 }); }
  function setNativeValue(input, raw) {
    if (!input || input.disabled || input.readOnly) throw new Error('Campo bloqueado ou somente leitura: ' + (input?.placeholder || input?.name || '?'));
    const value = String(raw);
    input.focus();
    const adjusted = input.type === 'number' && typeof raw === 'string' && raw.includes(',')
      ? raw.replace(/\./g, '').replace(',', '.') : value;
    if (input.tagName === 'SELECT') {
      input.value = adjusted;
    } else {
      const proto = input.tagName === 'TEXTAREA' ? HTMLTextAreaElement.prototype : HTMLInputElement.prototype;
      const setter = Object.getOwnPropertyDescriptor(proto, 'value')?.set;
      if (setter) setter.call(input, adjusted);
      else input.value = adjusted;
    }
    input.dispatchEvent(new InputEvent('input', { bubbles: true, data: adjusted, inputType: 'insertText' }));
    input.dispatchEvent(new Event('change', { bubbles: true }));
    input.blur();
  }
  function userClick(el) {
    if (!el) throw new Error('Elemento para clique nao encontrado.');
    el.dispatchEvent(new MouseEvent('mousedown', { bubbles: true, cancelable: true }));
    el.dispatchEvent(new MouseEvent('mouseup', { bubbles: true, cancelable: true }));
    el.click();
  }
  async function waitFor(fn, timeout = 4000, label = 'elemento') {
    const end = Date.now() + timeout;
    while (Date.now() < end) {
      const result = fn();
      if (result) return result;
      await sleep(130);
    }
    throw new Error(`Tempo esgotado esperando ${label}.`);
  }
  // ------------------- GUIAS ABERTAS E PREENCHIMENTO REMOTO -------------------
  // A extensao nao consegue enumerar ou ativar qualquer guia do navegador.
  // Uma guia Sisfrete com ESTA macro ativa registra sua presenca, recebe
  // o pedido e pode navegar e preencher sem criar uma segunda guia.
  function pingSisfreteTab() {
    if (!IS_SIS) return;
    try {
      GM_setValue(TAB_LIVE_PREFIX + SIS_TAB_ID, {
        at: Date.now(), focusAt: sisTabLastFocused,
        visible: document.visibilityState === 'visible', path: location.pathname
      });
    } catch (e) { console.warn(msgPrefix, 'Nao foi possivel registrar a guia Sisfrete', e); }
  }
  function stopSisfreteTab() {
    if (!IS_SIS) return;
    try {
      GM_deleteValue(TAB_LIVE_PREFIX + SIS_TAB_ID);
      GM_deleteValue(TAB_REQ_PREFIX + SIS_TAB_ID);
      // Preservar ACK ate a origem o ler, mesmo durante navegacao.
    } catch (_) { /* registros expirados sao ignorados */ }
  }
  function buildResume(order, quote, account, newTab = false) {
    return { order, quote: !!quote, account: account || null,
      newTab: !!newTab, at: Date.now() };
  }
  function validateRemoteRequest(request) {
    const data = getData();
    if (!request?.order || !data || data.order !== request.order ||
        (request.capturedAt && data.capturedAt !== request.capturedAt)) {
      throw new Error('Pedido salvo mudou desde o F8. Recapture no Bling antes de preencher.');
    }
    if (!IS_SIS || busy) throw new Error('Guia Sisfrete ocupada; aguarde a operacao atual terminar.');
    const account = sisAccountKey();
    if (!account) throw new Error('Nao foi possivel confirmar a conta aberta na Sisfrete.');
    if (IS_SIS_QUOTE()) {
      const orderInput = fieldByName('Numero do Pedido');
      const existing = inputText(orderInput);
      if (existing && existing !== request.order) {
        throw new Error('A guia Sisfrete ja contem o pedido ' + existing +
          '. Abra um formulario vazio antes de cotar outro pedido.');
      }
    }
    return account;
  }
  function listenForReuseRequest() {
    if (!IS_SIS) return;
    pingSisfreteTab();
    GM_addValueChangeListener(TAB_REQ_PREFIX + SIS_TAB_ID, (_key, _old, request) => {
      if (!request?.nonce || Date.now() - Number(request.time) > 15000) return;
      let ack = { nonce: request.nonce, at: Date.now(), accepted: false };
      try {
        if (request.autoFill) {
          const account = validateRemoteRequest(request);
          // Guardar na SESSION desta mesma guia antes de mudar de rota.
          sessionStorage.setItem(RESUME_KEY,
            JSON.stringify(buildResume(request.order, request.quote, account)));
          ack.autoFillAcknowledged = true;
        }
        ack.accepted = true;
        GM_setValue(TAB_ACK_PREFIX + SIS_TAB_ID, ack);
        try { window.focus(); } catch (_) { /* foco pode ser bloqueado pelo navegador */ }
        if (!IS_SIS_QUOTE()) {
          markStatus('Reutilizando esta guia: abrindo Nova Cotacao.');
          location.assign(URL_SISFRETE);
          return;
        }
        if (request.autoFill) {
          markStatus('Pedido ' + request.order + ' recebido do Bling. Preenchendo a cotacao...');
          // A rota ja esta aberta; nao aguardar outro F8.
          resumeOnQuotePage();
        } else {
          markStatus('Esta guia da Sisfrete ja esta no formulario de cotacao.');
        }
      } catch (e) {
        ack = { ...ack, accepted: false, reason: String(e?.message || e) };
        GM_setValue(TAB_ACK_PREFIX + SIS_TAB_ID, ack);
        markStatus('BLOQUEADO: ' + ack.reason, true);
      }
    });
    setInterval(pingSisfreteTab, 10000);
    window.addEventListener('focus', () => { sisTabLastFocused = Date.now(); pingSisfreteTab(); });
    document.addEventListener('visibilitychange', () => {
      if (document.visibilityState === 'visible') sisTabLastFocused = Date.now();
      pingSisfreteTab();
    });
    window.addEventListener('pageshow', pingSisfreteTab);
    window.addEventListener('pagehide', stopSisfreteTab);
  }
  function activeSisfreteTabs() {
    const now = Date.now();
    let entries = [];
    try {
      entries = GM_listValues().filter(name => name.startsWith(TAB_LIVE_PREFIX))
        .map(name => ({ id: name.slice(TAB_LIVE_PREFIX.length), ...GM_getValue(name, {}) }))
        .filter(tab => tab.id && Number.isFinite(tab.at) && now - tab.at >= 0 && now - tab.at < TAB_TTL_MS);
    } catch (e) { console.warn(msgPrefix, 'Falha procurando guias Sisfrete', e); }
    return entries.sort((a, b) => (b.focusAt || 0) - (a.focusAt || 0) || b.at - a.at);
  }
  async function openOrReuseSisfrete({ autoFill = false, data = null, quote = false } = {}) {
    if (!IS_BLING) return;
    if (autoFill && (!data?.order || data.order !== getData()?.order))
      throw new Error('Capture um pedido valido no Bling antes de abrir a Sisfrete.');
    const tabs = activeSisfreteTabs();
    for (const tab of tabs.slice(0, 8)) {
      const nonce = `${Date.now()}_${Math.random().toString(36).slice(2)}`;
      try {
        GM_setValue(TAB_REQ_PREFIX + tab.id, {
          nonce, time: Date.now(), autoFill, quote: !!quote,
          order: data?.order || null, capturedAt: data?.capturedAt || null
        });
        const ack = await waitFor(() => {
          const value = GM_getValue(TAB_ACK_PREFIX + tab.id, {});
          return value?.nonce === nonce ? value : null;
        }, 4200, 'resposta da guia Sisfrete existente').catch(() => null);
        if (ack) {
          if (ack.accepted === undefined) {
            markStatus('Guia Sisfrete encontrada com uma versao antiga da macro. Atualize essa guia com F5 para permitir o F8 automatico.', true);
            return;
          }
          if (!ack.accepted) {
            markStatus('Guia Sisfrete encontrada, mas a operacao foi bloqueada: ' + (ack.reason || 'motivo desconhecido'), true);
            return;
          }
          if (autoFill && !ack.autoFillAcknowledged) {
            markStatus('Reutilizei a guia, mas ela ainda usa uma versao antiga da macro. Atualize a pagina Sisfrete com F5.', true);
            return;
          }
          markStatus(autoFill
            ? `Pedido ${data.order} enviado para a guia Sisfrete aberta. A navegacao e o preenchimento continuam nela.`
            : 'Guia Sisfrete reutilizada; abrindo o formulario sem duplicar a guia.');
          return;
        }
      } catch (e) { console.warn(msgPrefix, 'Falha ao solicitar reutilizacao', e); }
    }
    // Somente quando nenhuma guia com a macro ATIVA respondeu. O hash inclui
    // apenas um identificador temporario; os dados continuam no Tampermonkey.
    let url = URL_SISFRETE;
    let requestKey = null;
    if (autoFill) {
      const nonce = `${Date.now()}_${Math.random().toString(36).slice(2)}`;
      requestKey = OPEN_REQ_PREFIX + nonce;
      GM_setValue(requestKey, {
        nonce, order: data.order, capturedAt: data.capturedAt,
        quote: !!quote, at: Date.now()
      });
      url += OPEN_HASH_PREFIX + nonce;
    }
    try {
      GM_openInTab(url, { active: true, insert: true });
      markStatus(autoFill
        ? `Abrindo Sisfrete para preencher pedido ${data.order} automaticamente.`
        : 'Nenhuma guia Sisfrete respondeu; uma nova guia foi aberta.');
    } catch (e) {
      if (requestKey) GM_deleteValue(requestKey);
      throw new Error('Nao foi possivel abrir Sisfrete. Verifique o bloqueio de novas guias e as permissoes Tampermonkey.');
    }
  }
  function consumeNewTabRequest() {
    if (!IS_SIS || !IS_SIS_QUOTE()) return;
    const m = location.hash.match(/^#bs-cotacao-([a-zA-Z0-9_]+)$/);
    if (!m) return;
    // Remover o hash temporario da barra de enderecos, sem recarregar a pagina.
    try { history.replaceState(history.state, '', location.pathname + location.search); } catch (_) { /* opcional */ }
    const key = OPEN_REQ_PREFIX + m[1];
    const req = GM_getValue(key, null);
    GM_deleteValue(key); // token de uso unico
    if (!req || req.nonce !== m[1] || Date.now() - Number(req.at) > 60000 ||
        req.order !== getData()?.order || req.capturedAt !== getData()?.capturedAt) {
      markStatus('Abertura automatica expirada ou pedido mudou. Pressione F8 novamente.', true);
      return;
    }
    sessionStorage.setItem(RESUME_KEY, JSON.stringify(buildResume(req.order, req.quote, null, true)));
  }

  function markStatus(s, error = false) {
    if (statusEl) { statusEl.textContent = s; statusEl.style.color = error ? '#b91c1c' : '#184f38'; }
    log(s);
  }
  function getData() {
    try { return GM_getValue(KEY, null); }
    catch (e) { throw new Error('Nao foi possivel ler o armazenamento Tampermonkey.'); }
  }
  function showData() {
    const data = getData();
    if (!previewEl) return;
    previewEl.hidden = false;
    previewEl.textContent = data ? JSON.stringify({
      pedido: data.order, cep: data.cep, cidade: data.city || null, valorTotalVenda: brMoney(data.totalCents),
      freteBlingTransportador: Number.isSafeInteger(data.blingFreightCents) ? brMoney(data.blingFreightCents) : 'nao identificado',
      itens: data.items, capturadoEm: data.capturedAt
    }, null, 2) : 'Ainda nao existe um pedido capturado.';
  }

  // ------------------- LEITURA DO PEDIDO DO BLING -------------------
  function orderHeading() {
    const all = [...document.querySelectorAll('h1,h2,h3,h4,[role="heading"]')];
    const fromHead = all.map(e => e.textContent || '').join('\n').match(/pedido\s+de\s+venda\s*[-–:]\s*(\d+)/i);
    return fromHead?.[1] || (document.body.innerText || '').match(/pedido\s+de\s+venda\s*[-–:]\s*(\d+)/i)?.[1] || '';
  }
  function afterSection(sectionText, untilText) {
    const from = textOne(sectionText);
    const to = untilText ? textMatches(untilText).find(a => !from || a.rect.top > from.rect.top) : null;
    return { after: from?.rect.top ?? null, before: to?.rect.top ?? null };
  }
  function blingItems() {
    const bounds = afterSection('Itens do pedido de venda', 'Totais');
    if (bounds.after == null || bounds.before == null) throw new Error('Nao consegui delimitar a tabela de itens do Bling.');
    const hdr = ['Codigo', 'Un', 'Quantidade', 'Preco lista', 'Preco total'].map(name => ({
      name, a: textOne(name, { after: bounds.after - 1, before: bounds.before })
    }));
    const code = hdr[0].a, unitCol = hdr[1].a, qty = hdr[2].a, listCol = hdr[3].a, totalCol = hdr[4].a;
    if (!code || !unitCol || !qty || !listCol) throw new Error('Nao encontrei as colunas Codigo/Quantidade do Bling.');
    const rows = controls().filter(input => {
      const r = position(input);
      const x = centerX(r), y = centerY(r);
      return y > Math.max(code.rect.bottom, qty.rect.bottom) + 4 && y < bounds.before - 6 &&
        x >= code.rect.left - 15 && x < unitCol.rect.left - 8;
    }).sort((a, b) => position(a).top - position(b).top);
    const out = [];
    for (const el of rows) {
      const sku = inputText(el);
      if (!sku) continue;
      const y = centerY(position(el));
      const qField = controls().find(c => {
        const r = position(c); const x = centerX(r);
        return overlaps(centerY(r), y, 18) && x >= qty.rect.left - 18 && x < listCol.rect.left - 8;
      });
      const qtyValue = quantity(qField?.value);
      if (!Number.isFinite(qtyValue)) throw new Error('Quantidade invalida no item ' + sku + '.');
      const priceFields = controls().filter(c => {
        const r = position(c);
        return overlaps(centerY(r), y, 18) && totalCol && centerX(r) >= totalCol.rect.left - 20;
      }).sort((a, b) => position(a).left - position(b).left);
      let lineCents = moneyCents(priceFields[0]?.value);
      if (!Number.isFinite(lineCents) || lineCents < 0) lineCents = 0;
      out.push({ sku, qty: qtyValue, lineCents });
    }
    if (!out.length) throw new Error('Nenhum SKU foi encontrado na tabela de itens do Bling.');
    return out;
  }
  function getBlingValue(label, opts) {
    const anchor = textMatches(label, opts)[0];
    const field = fieldByName(label, opts);
    return inputText(field);
  }
  function captureBling() {
    if (!IS_BLING || !/vendas\.php/i.test(location.pathname)) throw new Error('Abra um pedido de venda na pagina do Bling.');
    const order = orderHeading();
    if (!/^\d{1,12}$/.test(order)) throw new Error('Nao encontrei o numero do pedido de venda no titulo.');
    const totalRaw = getBlingValue('Total da venda');
    const totalCents = moneyCents(totalRaw);
    if (!Number.isFinite(totalCents) || totalCents <= 0) throw new Error('Nao consegui ler o TOTAL DA VENDA do Bling.');
    const address = afterSection('Endereco de entrega', 'Dados adicionais');
    if (address.after == null) throw new Error('Nao encontrei a secao Endereco de entrega.');
    const cepRaw = getBlingValue('CEP', address);
    const cep = digits(cepRaw);
    if (!/^\d{8}$/.test(cep)) throw new Error('CEP de entrega ausente ou invalido (precisa de 8 digitos).');
    const items = blingItems();
    const city = getBlingValue('Cidade', address).trim();
    let blingFreightCents=null;
    try {
      // Frete na secao Transportador; nao confundir com Custo Frete do Marketplace.
      const freightArea=afterSection('Transportador','Objetos de postagem');
      if(freightArea.after!=null && textMatches('Frete',freightArea).length===1) {
        const result=moneyCents(getBlingValue('Frete',freightArea));
        if(Number.isSafeInteger(result) && result>=0) blingFreightCents=result;
      }
    } catch(e) {console.warn(msgPrefix,'Frete Bling nao identificado',e);}
    const data = { order, cep, city, totalCents, items, blingFreightCents, source: location.href, capturedAt: new Date().toISOString() };
    GM_setValue(KEY, data);
    markStatus(`Pedido ${order}: ${items.length} SKU(s), CEP ${cep}, venda R$ ${brMoney(totalCents)}. Capturado.`);
    showData();
    return data;
  }

  // ------------------- PREENCHIMENTO DA SISFRETE -------------------
  // Os seletores da Sisfrete podem apresentar o valor apenas como texto,
  // mantendo input.value vazio. Alem disso, os IDs desses campos mudam.
  // Sempre usamos a etiqueta + posicao visual do PROPRIO campo, nunca
  // o seletor "CDs" do cabecalho ou o texto solto do menu de opcoes.
  function selectContext(label) {
    const anchor = textOne(label);
    if (!anchor) return null;
    const widgets = '.el-select, .el-select-v2, .ant-select, .v-select, .multiselect, .select2-container, [role="combobox"]';
    const f = structuralField(anchor);
    let root = f?.closest(widgets) || null;
    // A etiqueta e o select costumam estar no mesmo bloco (Element UI / Vue),
    // que continua sendo o mesmo elemento mesmo quando as colunas quebram.
    if (!root) {
      for (let ancestor = anchor.node, depth = 0; ancestor && depth < 7; ancestor = ancestor.parentElement, depth++) {
        if (ancestor === document.body) break;
        const candidates = [...ancestor.querySelectorAll(widgets)].filter(visible)
          .filter(el => ![...ancestor.querySelectorAll(widgets)].some(other => other !== el && other.contains(el)));
        if (candidates.length === 1) { root = candidates[0]; break; }
        if (candidates.length > 1) break;
      }
    }
    // Controle nativo/associado: nao exige componente com classe fixa.
    if (!root && f) root = f.parentElement || f;
    if (!root) return null;
    const input = (root.matches('input,select') ? root : root.querySelector('input,select')) || f;
    const trigger = root.querySelector('.el-select__wrapper, .el-select-v2__wrapper, .ant-select-selector, .select2-selection, [role="combobox"]') ||
      (root.matches('[role="combobox"]') ? root : root);
    return { anchor, root, input, trigger };
  }
  function isControlDisabled(ctx) {
    const el = ctx?.input;
    return !!(el?.disabled || ctx?.root?.getAttribute('aria-disabled') === 'true' ||
      ctx?.trigger?.getAttribute('aria-disabled') === 'true' ||
      ctx?.root?.classList.contains('is-disabled') ||
      ctx?.trigger?.classList.contains('is-disabled') ||
      ctx?.root?.classList.contains('el-select--disabled') ||
      !!ctx?.root?.querySelector('[role="combobox"][aria-disabled="true"], .el-select__wrapper.is-disabled, .el-select__wrapper[aria-disabled="true"]'));
  }
  // A selecao pode estar no wrapper irmao, nao dentro de input.value.
  // Confirmar exclusivamente o proprio grupo rotulado, sem ler outro CD ou menu aberto.
  function matchSelectedValue(raw, expected) {
    const got=norm(raw), want=norm(expected);
    if (!got || !want) return false;
    if (got===want) return true;
    const clipped=got.match(/^(.{12,}?)(?:\\.\\.\\.|…)$/);
    return !!(clipped && want.startsWith(clipped[1].trim()));
  }
  function valueInControl(ctx, expected) {
    if (!ctx?.root || !ctx.anchor) return false;
    const { root,input,anchor }=ctx;
    const values=[
      input?.value,input?.getAttribute('value'),input?.getAttribute('title'),
      input?.getAttribute('aria-valuetext'),root.getAttribute('title')
    ];
    if(input?.tagName==='SELECT') values.push(input.selectedOptions?.[0]?.textContent);
    const chosen='.el-select__selected-item, .el-select__selection-item, .el-select__placeholder, .el-select__selected-label, .ant-select-selection-item, .select2-selection__rendered, [class*="selected-item"], [class*="single-value"]';
    root.querySelectorAll(chosen).forEach(el=>{
      if (visible(el) && !el.closest('[role="listbox"],[role="option"],.el-select-dropdown,.el-popper')) {
        values.push(el.textContent,el.getAttribute('title'),el.getAttribute('aria-label'));
      }
    });
    root.querySelectorAll('input,[role="combobox"]').forEach(el=>{
      if(visible(el)) values.push(el.value,el.getAttribute('title'),el.getAttribute('aria-valuetext'));
    });
    // Em algumas contas o DOM mostra a opcao ao lado do root do select.
    // Subir apenas ao primeiro ancestral que CONTEM a etiqueta E um unico input.
    let parent=root;
    for(let depth=0;parent && depth<6;parent=parent.parentElement,depth++){
      if(parent===document.body || parent.closest('#bs-quote-panel'))break;
      if(!parent.contains(anchor.node))continue;
      if(parent.querySelectorAll('input,select,textarea').length!==1)break;
      if(parent.querySelector('[role="listbox"],[role="option"],.el-select-dropdown__item'))break;
      const label=norm(anchor.node.textContent);
      const text=norm(parent.innerText||parent.textContent||'');
      if(text.startsWith(label)) values.push(text.slice(label.length).trim());
      break;
    }
    return values.some(v=>matchSelectedValue(v,expected));
  }
  function exactOption(value, selectedRoot) {
    const wanted = norm(value);
    // Priorizar opcoes de lista, evitando clicar no valor JA exibido no campo.
    const selectors = '[role="option"], .el-select-dropdown__item, .ant-select-item-option, .vs__dropdown-option, .dropdown-item, .select2-results__option, .multiselect__option';
    const listItems = [...document.querySelectorAll(selectors)].filter(el =>
      visible(el) && !selectedRoot?.contains(el) && norm(el.textContent) === wanted &&
      el.getAttribute('aria-disabled') !== 'true' &&
      position(el).top < innerHeight && position(el).bottom > 0 &&
      position(el).left < innerWidth && position(el).right > 0
    );
    if (listItems.length) return listItems.sort((a, b) => a.querySelectorAll('*').length - b.querySelectorAll('*').length)[0];
    // Fallback para frameworks em que a opcao e somente um texto clicavel.
    return textMatches(value).map(x => x.node).filter(el => {
      const r = position(el);
      return !selectedRoot?.contains(el) && r.top < innerHeight && r.bottom > 0 &&
        r.left < innerWidth && r.right > 0 &&
        !!el.closest('[role="listbox"], .el-select-dropdown, .el-popper, .dropdown-menu, [class*="dropdown"], [class*="options"]');
    })[0] || null;
  }
  async function selectionStaysVisible(label, value, milliseconds = 900) {
    const until = Date.now() + milliseconds;
    while (Date.now() < until) {
      if (!valueInControl(selectContext(label), value)) return false;
      await sleep(160);
    }
    return true;
  }
  async function chooseByLabel(label, value) {
    for (let attempt = 1; attempt <= 3; attempt++) {
      let ctx = await waitFor(() => selectContext(label), 5000, `${label}: controle`);
      await waitFor(() => {
        ctx = selectContext(label);
        return ctx && !isControlDisabled(ctx) && ctx;
      }, 9000, `${label} desbloquear`);
      if (!valueInControl(ctx, value)) {
        userClick(ctx.trigger);
        const option = await waitFor(() => exactOption(value, ctx.root), 7000, `opcao ${value}`);
        userClick(option);
      }
      try {
        await waitFor(() => valueInControl(selectContext(label), value), 4500, `${label} = ${value}`);
        if (await selectionStaysVisible(label, value, 900)) {
          markStatus(`${label}: ${value} selecionado e confirmado.`);
          return;
        }
      } catch (e) {
        if (attempt === 3) throw e;
      }
      if (attempt < 3) {
        markStatus(`${label}: selecao reiniciada pelo formulario; tentando novamente...`);
        await sleep(550);
      }
    }
    throw new Error(`Nao foi possivel manter ${label} = ${value} selecionado. Cotacao bloqueada.`);
  }
  async function lookupCep(cep, city = '') {
    const el = requireField('CEP de Destino', { maxX: 95 });
    if (digits(el.value) && digits(el.value) !== cep) {
      throw new Error('Ja ha outro CEP no formulario. Abra uma Nova Cotacao vazia para evitar manter uma cidade antiga.');
    }
    setNativeValue(el, cep);
    // Procurar a lupa no MESMO componente do CEP, sem medir pixels.
    let lookups = [];
    for (let parent = el.parentElement, depth = 0; parent && depth < 5; parent = parent.parentElement, depth++) {
      if (parent === document.body) break;
      const candidates = [...parent.querySelectorAll('button, [role="button"], .input-group-append, .el-input-group__append')]
        .filter(visible).filter(node => !node.closest('#bs-quote-panel'));
      if (candidates.length === 1) { lookups = candidates; break; }
      if (candidates.length > 1) break; // ambiguo: nao clicar outra funcao
    }
    if (lookups[0]) userClick(lookups[0]);
    else {
      el.dispatchEvent(new KeyboardEvent('keydown', { key: 'Enter', code: 'Enter', bubbles: true }));
      el.dispatchEvent(new KeyboardEvent('keyup', { key: 'Enter', code: 'Enter', bubbles: true }));
    }
    // Repetir no maximo uma busca de CEP, sem executar a cotacao.
    for(let attempt=0;attempt<2;attempt++){
      try{
        await waitFor(()=>{
          const dst=fieldByName('Destino',{maxX:110});
          return dst && inputText(dst).length>=2;
        }, attempt===0?6500:4500,'cidade de destino pelo CEP');
        break;
      }catch(e){
        if(attempt===1)throw e;
        if(digits(el.value)!==cep)throw new Error('CEP mudou durante a busca. Cotacao bloqueada.');
        markStatus('Busca de CEP demorou: repetindo apenas a consulta...');
        if(lookups[0])userClick(lookups[0]);
        else{
          el.dispatchEvent(new KeyboardEvent('keydown',{key:'Enter',code:'Enter',bubbles:true}));
          el.dispatchEvent(new KeyboardEvent('keyup',{key:'Enter',code:'Enter',bubbles:true}));
        }
      }
    }
    if (digits(el.value) !== cep) throw new Error('O CEP da Sisfrete nao coincide com o CEP de entrega do Bling.');
    const foundCity = inputText(fieldByName('Destino', { maxX: 110 }));
    if (city && !norm(foundCity).includes(norm(city))) {
      throw new Error(`Cidade da Sisfrete (${foundCity}) diferente da cidade do Bling (${city}). Nao cotarei com destino divergente.`);
    }
    markStatus('CEP e cidade conferidos.');
  }
  // A captura dos itens da Sisfrete usa a ordem do DOM e os placeholders,
  // nao as coordenadas de colunas. Funciona em zoom e janelas estreitas.
  function sisfreteRows() {
    const products = textOne('Produtos');
    const quote = textOne('Cotar Frete');
    if (!products || !quote || !beforeInDom(products.node, quote.node))
      throw new Error('Nao localizei a regiao de Produtos da Sisfrete na ordem do formulario.');
    const fields = controls().filter(el => beforeInDom(products.node, el) && beforeInDom(el, quote.node));
    const placeholder = el => norm([el?.getAttribute('placeholder'), el?.getAttribute('aria-label')].filter(Boolean).join(' '));
    const skuInputs = fields.filter(el => /^sku(\s|\(|$)/.test(placeholder(el)));
    if (!skuInputs.length) throw new Error('Nao encontrei SKU na estrutura do formulario. Use Diagnostico: informe o zoom utilizado.');
    const result = [];
    for (let i = 0; i < skuInputs.length; i++) {
      const from = fields.indexOf(skuInputs[i]);
      const end = i + 1 < skuInputs.length ? fields.indexOf(skuInputs[i + 1]) : fields.length;
      const group = fields.slice(from, end);
      // Se os campos foram movidos de coluna, os placeholders continuam iguais.
      const find = (...names) => {
        const matches = group.filter(el => names.some(name => placeholder(el) === norm(name)));
        return matches.length === 1 ? matches[0] : null;
      };
      const sku = skuInputs[i];
      const length = find('Comprimento (m)', 'Comprimento');
      const width = find('Largura (m)', 'Largura');
      const height = find('Altura (m)', 'Altura');
      const weight = find('Peso (kg)', 'Peso');
      const unit = find('Valor Unitario (R$)', 'Valor Unitario');
      const total = find('Valor Total (R$)', 'Valor Total');
      let qty = find('Quantidade');
      if (!qty && length) {
        // Campo de quantidade pode nao ter placeholder (valor padrao 1).
        // So inferir se existe exatamente um controle entre a caixa e o comprimento.
        const ix = group.indexOf(length);
        if (ix === 3 && group.length >= 9) qty = group[2];
      }
      // Exigir identificacao POSITIVA dos campos criticos; nao cotar por aproximacao.
      if (!qty || !unit || !total || !length || !width || !height || !weight)
        throw new Error(`Linha de produto ${i+1}: o layout mudou e nao foi possivel identificar todos os campos por nome. Cotacao bloqueada (use Diagnostico).`);
      result.push({ sku, qty, length, width, height, weight, unit, total });
    }
    return result;
  }
  async function addSisfreteRow() {
    const products = textOne('Produtos');
    const quote = textOne('Cotar Frete');
    const buttons = [...document.querySelectorAll('button,[role="button"]')]
      .filter(el => visible(el) && !el.closest('#bs-quote-panel') &&
        beforeInDom(products?.node, el) && beforeInDom(el, quote?.node));
    const plus = buttons.filter(el => {
      const label = norm([el.textContent, el.getAttribute('title'), el.getAttribute('aria-label')].filter(Boolean).join(' '));
      return /^\+$/u.test(label) || /adicionar|add(?!ress)|plus/.test(label) ||
        /(?:icon-|lucide-|data-icon="|class="[^"]*)(?:plus|add)/i.test(el.innerHTML);
    });
    if (plus.length !== 1) throw new Error('Nao identifiquei um botao + unico para adicionar produto. Cotacao bloqueada (zoom/layout).');
    const previousCount = sisfreteRows().length;
    userClick(plus[0]);
    await waitFor(() => sisfreteRows().length > previousCount, 3500, 'nova linha de produto');
  }
  // Sisfrete usa valor UNITARIO com 2 casas; a soma exata deve fechar
  // com o TOTAL DA VENDA do Bling, mesmo quando tem varios SKUs.
  // Precos de Bling sao usados APENAS como pesos para a distribuicao; nao
  // representam necessariamente o valor unitario final com frete/descontos.
  function gcd(a, b) { while (b) [a, b] = [b, a % b]; return a; }
  function distributeTotal(data) {
    const lines = data.items;
    const total = data.totalCents;
    if (!lines.length || !Number.isSafeInteger(total) || total <= 0) throw new Error('Total da venda invalido.');
    if (lines.some(x => !Number.isSafeInteger(x.qty) || x.qty < 1 || x.qty > 999999)) {
      throw new Error('Quantidade de pelo menos um produto nao e um inteiro positivo valido.');
    }
    const g = lines.reduce((acc, x) => gcd(acc, x.qty), 0);
    if (total % g !== 0) throw new Error('Nao e possivel dividir o total da venda com exatidao em precos unitarios de 2 casas: as quantidades nao permitem fechar os centavos. Cotacao bloqueada.');
    const weights = lines.map(x => Number(x.lineCents));
    if (weights.some(v => !Number.isSafeInteger(v) || v <= 0)) {
      if (lines.length > 1) throw new Error('Nao consegui ler o preco total de cada item do Bling: distribuicao proporcional bloqueada.');
      weights[0] = total;
    }
    const wsum = weights.reduce((a, b) => a + b, 0);
    const exact = lines.map((x, i) => (total * weights[i] / wsum) / x.qty);
    const base = exact.map(x => Math.max(0, Math.round(x)));
    const sum = () => base.reduce((acc, unit, i) => acc + unit * lines[i].qty, 0);
    if (sum() === total) return base;

    // Ajustes pequenos e inteiros por SKU; nenhuma diferenca pode ser escondida.
    // A busca dinamica minimiza o desvio da proporcao quando o arredondamento
    // de quantidades diferentes cria residuos em centavos.
    const delta = total - sum();
    const maxSteps = Math.max(15, Math.min(50, Math.abs(delta) + 15));
    const maxQty = Math.max(...lines.map(x => x.qty));
    let states = new Map([[0, { cost: 0, changes: [] }]]);
    for (let i = 0; i < lines.length; i++) {
      const next = new Map();
      const q = lines[i].qty;
      const size = Math.min(maxSteps, Math.max(5, Math.ceil((Math.abs(delta) + 15) / q) + 5));
      for (const [remainder, state] of states) {
        for (let adj = -size; adj <= size; adj++) {
          if (base[i] + adj < 0) continue;
          const value = remainder + adj * q;
          if (Math.abs(value - delta) > maxSteps * maxQty) continue;
          const cost = state.cost + Math.abs((base[i] + adj) - exact[i]);
          const previous = next.get(value);
          if (!previous || previous.cost > cost) next.set(value, { cost, changes: [...state.changes, adj] });
        }
      }
      // Limitar memoria, retendo os restos proximos da diferenca desejada.
      if (next.size > 1600) {
        states = new Map([...next.entries()].sort((x,y) => Math.abs(x[0]-delta) - Math.abs(y[0]-delta)).slice(0,1600));
      } else states = next;
    }
    const adjusted = states.get(delta);
    if (!adjusted) throw new Error('Nao consegui distribuir o total exatamente entre os SKUs sem inventar valores. Cotacao bloqueada.');
    const values = base.map((v, i) => v + adjusted.changes[i]);
    if (values.reduce((acc, v, i) => acc + v * lines[i].qty, 0) !== total) throw new Error('Falha de conferencia dos centavos da venda.');
    return values;
  }
  async function tryChooseSkuOption(sku) {
    // Nao selecionar SKU parecido: 1002 e 10020 nao sao o mesmo produto.
    const wanted = norm(sku);
    for (let pass = 0; pass < 8; pass++) {
      const options = [...document.querySelectorAll('[role="option"], .el-select-dropdown__item, .autocomplete-suggestion li, .dropdown-item')]
        .filter(visible).filter(el => {
          const text = norm(el.textContent);
          return (text === wanted || text.startsWith(wanted + ' ') || text.startsWith(wanted + ' -')) &&
            position(el).bottom < innerHeight && position(el).top >= 0;
        });
      if (options.length === 1) { userClick(options[0]); return true; }
      if (options.length > 1) throw new Error(`SKU ${sku}: sugestoes ambiguas, nao selecionei produto errado.`);
      await sleep(180);
    }
    // Autopreenchimento por eventos de input tambem pode resolver o SKU.
    return false;
  }
  async function writeProducts(data) {
    const prices = distributeTotal(data);
    while (sisfreteRows().length < data.items.length) await addSisfreteRow();
    const rows = sisfreteRows();
    if (rows.length !== data.items.length) throw new Error('O numero de linhas na Sisfrete nao corresponde ao numero de SKUs do Bling.');
    for (let i = 0; i < rows.length; i++) {
      const { sku, qty, unit } = sisfreteRows()[i];
      const item = data.items[i];
      if (!sku || !qty || !unit) throw new Error(`Nao identifiquei todos os campos da linha ${i + 1}.`);
      if (inputText(sku) && inputText(sku) !== item.sku) throw new Error(`Linha ${i + 1} contem SKU de outra cotacao. Abra Nova Cotacao em branco; nao vou substituir os dados.`);
      setNativeValue(sku, item.sku);
      await sleep(200);
      await tryChooseSkuOption(item.sku);
      await waitFor(() => sisfreteRows().length === data.items.length, 3500, 'linhas de produtos');
      const fresh = sisfreteRows()[i];
      if (!fresh || inputText(fresh.sku) !== item.sku) throw new Error(`SKU ${item.sku} nao ficou gravado na linha ${i+1}.`);
      setNativeValue(fresh.qty, item.qty);
      setNativeValue(fresh.unit, brMoney(prices[i]));
      // O SKU deve vir cadastrado na Sisfrete para popular peso/dimensoes.
      await waitFor(() => {
        const r = sisfreteRows()[i];
        if (!r || inputText(r.sku) !== item.sku) return false;
        const weight = decimal(r.weight?.value);
        const dimensions = [r.length, r.width, r.height].map(el => decimal(el?.value));
        return weight > 0 || dimensions.every(v => v > 0);
      }, 3800, `dimensoes ou peso do SKU ${item.sku}`);
      await sleep(220);
    }
    return prices;
  }
  async function validateSisfrete(data, prices) {
    const rows = sisfreteRows();
    if (rows.length !== data.items.length) throw new Error('Numero de produtos diferente do pedido.');
    let sum = 0;
    for (let i = 0; i < rows.length; i++) {
      const row = rows[i], item = data.items[i];
      if (inputText(row.sku) !== item.sku) throw new Error(`SKU da linha ${i + 1} nao confere.`);
      if (quantity(row.qty?.value) !== item.qty) throw new Error(`Quantidade da linha ${i + 1} nao confere.`);
      const unitCents = moneyCents(row.unit?.value);
      if (unitCents !== prices[i]) throw new Error(`Valor unitario da linha ${i + 1} nao confere.`);
      sum += unitCents * item.qty;
      const rowTotal = inputText(row.total);
      if (rowTotal) {
        const reported = moneyCents(rowTotal);
        if (Number.isFinite(reported) && reported !== unitCents * item.qty) {
          throw new Error(`Valor total calculado pela Sisfrete na linha ${i+1} e diferente do esperado.`);
        }
      }
      const weight = decimal(row.weight?.value);
      const dimensions = [row.length, row.width, row.height].map(el => decimal(el?.value));
      if (!(weight > 0 || dimensions.every(v => v > 0))) {
        throw new Error(`Produto ${item.sku} sem peso e sem dimensoes preenchidos na Sisfrete. Verifique se o SKU foi reconhecido; cotacao automatica bloqueada.`);
      }
    }
    if (sum !== data.totalCents) throw new Error(`Somatorio das linhas R$ ${brMoney(sum)} difere da venda do Bling R$ ${brMoney(data.totalCents)}.`);
    const orderField = requireField('Numero do Pedido');
    if (inputText(orderField) !== data.order) throw new Error('Numero de pedido incorreto na Sisfrete.');
    const cepField = requireField('CEP de Destino');
    if (digits(cepField.value) !== data.cep) throw new Error('CEP divergente na Sisfrete.');
    const productsStart = textOne('Produtos')?.rect.top;
    const summary = fieldByName('Valor Total (R$)', { before: productsStart });
    if (summary && inputText(summary)) {
      const calculated = moneyCents(summary.value);
      if (Number.isFinite(calculated) && calculated !== data.totalCents) {
        throw new Error(`Resumo da Sisfrete = R$ ${brMoney(calculated)}; venda Bling = R$ ${brMoney(data.totalCents)}. Cotacao bloqueada.`);
      }
    }
    return true;
  }
  // ------------------- COMPARACAO DAS TRANSPORTADORAS -------------------
  // SOMENTE LEITURA do que a propria Sisfrete mostrou no resultado.
  // Se as colunas/cartoes nao forem reconhecidos, nao cria estimativas.
  function parseTransportPrice(s) {
    const t = String(s || '').trim();
    // Uma cifra explicita elimina o risco de confundir 'prazo 10' com R$ 10.
    const match = t.match(/R\$\s*([0-9][0-9.,]*)/i) ||
      t.match(/(?:^|\s)([0-9][0-9.]*,[0-9]{2})(?:\s|$)/);
    if (!match) return NaN;
    return moneyCents(match[1]);
  }
  function parseTransportTables() {
    if (!IS_SIS) return [];
    const collected = [];
    const tables = [...document.querySelectorAll('table')].filter(el => visible(el));
    for (const table of tables) {
      const trs = [...table.querySelectorAll('tr')].filter(visible);
      if (!trs.length) continue;
      const headers = [...(table.querySelector('thead tr') || trs[0]).querySelectorAll('th, td')]
        .map(el => norm(el.textContent));
      const nameCol = headers.findIndex(s => /transportadora|transportador|empresa de transporte|prestador|servico de entrega/.test(s));
      const valueCol = headers.findIndex(s => /valor.*frete|preco.*frete|custo.*frete|valor do transporte|preco do transporte|^frete$|^valor$|^preco$/.test(s));
      const daysCol = headers.findIndex(s => /prazo|previsao de entrega|dias uteis|dias de entrega/.test(s));
      if (nameCol < 0 || valueCol < 0 || daysCol < 0) continue;
      for (const tr of trs) {
        if (tr === trs[0] && !table.querySelector('thead')) continue;
        const cells = [...tr.querySelectorAll('td')];
        if (cells.length <= Math.max(nameCol, valueCol, daysCol)) continue;
        const name = (cells[nameCol].innerText || cells[nameCol].textContent || '').trim().replace(/\s+/g, ' ');
        const costText = cells[valueCol].innerText || cells[valueCol].textContent || '';
        const cents = parseTransportPrice(costText);
        const deadline = (cells[daysCol].innerText || cells[daysCol].textContent || '').trim().replace(/\s+/g, ' ');
        if (!name || name.length > 110 || !Number.isSafeInteger(cents) || cents < 0 || !deadline || deadline.length > 90) continue;
        collected.push({ company: name, priceCents: cents, deadline, source: 'tabela' });
      }
    }
    return collected;
  }
  function parseTransportCards() {
    if (!IS_SIS) return [];
    const out = [];
    const candidates = [...document.querySelectorAll('.el-card, .ant-card, .card, [class*="carrier-option"], [class*="freight-option"]')].filter(visible);
    for (const card of candidates) {
      // Campos explicitamente identificados: 'Transportadora', 'Prazo' e 'Frete'.
      // Nao extrair do conteudo geral do formulario ou do painel da macro.
      if (card.closest('#bs-quote-panel')) continue;
      const raw = (card.innerText || '').trim();
      if (raw.length < 25 || raw.length > 650) continue;
      if (!/transportador/i.test(raw) || !/prazo|entrega/i.test(raw) || !/frete/i.test(raw)) continue;
      const companyMatch = raw.match(/transportadora?\s*:?\s*([^\n\r]{2,100})/i);
      const deadlineMatch = raw.match(/(?:prazo(?:\s+de\s+entrega)?|entrega\s+em)\s*:?\s*([^\n\r]{1,70})/i);
      const priceMatch = raw.match(/(?:frete|valor do frete|preco do frete)[^\n\r]{0,45}?R\$\s*([\d.,]+)/i);
      if (!companyMatch || !deadlineMatch || !priceMatch) continue;
      const cents = moneyCents(priceMatch[1]);
      const name = companyMatch[1].trim(), deadline = deadlineMatch[1].trim();
      if (!name || !deadline || !Number.isSafeInteger(cents) || cents < 0) continue;
      out.push({ company: name, priceCents: cents, deadline, source: 'cartao' });
    }
    return out;
  }
  function readTransportResults() {
    const entries = [...parseTransportTables(), ...parseTransportCards()];
    const seen = new Set();
    return entries.filter(it => {
      const id = [norm(it.company), it.priceCents, norm(it.deadline)].join('::');
      if (seen.has(id)) return false;
      seen.add(id);
      return true;
    }).sort((a, b) => a.priceCents - b.priceCents || a.company.localeCompare(b.company, 'pt-BR'));
  }
  function comparisonToken() {
    if (!IS_SIS) return null;
    let token;
    try { token = JSON.parse(sessionStorage.getItem(COMPARE_KEY) || 'null'); } catch (_) { token = null; }
    if (!token) return null;
    const current = getData();
    if (!token.account || token.account !== sisAccountKey() ||
        token.order !== current?.order ||
        !Number.isFinite(Number(token.at)) ||
        Date.now() - Number(token.at) > COMPARE_MAX_AGE_MS) {
      sessionStorage.removeItem(COMPARE_KEY);
      return null;
    }
    return token;
  }
  function showComparisons(rows, token) {
    if (!resultSection || !resultList || !resultMeta) return;
    resultSection.hidden = false;
    lastComparison = rows;
    resultList.replaceChildren();
    if (!rows.length) {
      resultMeta.textContent = 'Ainda nao reconheci uma tabela/cartao com transportadora, preco e prazo. Aguarde o resultado ou envie o Diagnostico; nao vou inventar valores.';
      return;
    }
    const reference=getData()?.blingFreightCents;
    const comparable=Number.isSafeInteger(reference)&&reference>=0;
    resultMeta.textContent=`${rows.length} opcao(oes) lida(s) | pedido ${token.order}. `+
      (comparable ? `Frete Bling (Transportador): R$ ${brMoney(reference)}. Confirme se as modalidades sao comparaveis.` :
        'Frete Bling nao identificado; diferenca indisponivel.');
    for (const r of rows) {
      const line = document.createElement('div');
      line.style.cssText = 'border-top:1px solid #d1fae5;padding:7px 0;display:grid;gap:2px';
      const name = document.createElement('strong'); name.textContent = r.company;
      const info=document.createElement('span');
      const diff=comparable?r.priceCents-reference:null;
      info.textContent=`R$ ${brMoney(r.priceCents)} | Prazo: ${r.deadline}`+
        (diff==null?'':` | vs Bling: ${diff===0?'igual':('R$ '+brMoney(Math.abs(diff))+(diff<0?' abaixo':' acima'))}`);
      line.append(name,info);
      resultList.append(line);
    }
  }
  function collectComparisons() {
    const token = comparisonToken();
    if (!token) {
      if (resultSection) resultSection.hidden = true;
      return 0;
    }
    const rows = readTransportResults();
    if (rows.length) {
      showComparisons(rows,token);
      markStatus(`Comparei ${rows.length} transportadora(s) do pedido ${token.order}. Confira preco/prazo na tela antes de escolher.`);
    }
    return rows.length;
  }
  function startCompareWatch() {
    if (!IS_SIS || !comparisonToken() || comparisonTimer) return;
    comparisonBusy = false;
    const token = comparisonToken();
    if (resultSection) { resultSection.hidden = false; showComparisons([], token); }
    let tries = 0;
    comparisonTimer = setInterval(() => {
      tries++;
      if (!comparisonToken() || tries >= 60) {
        clearInterval(comparisonTimer); comparisonTimer = null;
        if (tries >= 60 && !lastComparison.length && resultMeta) resultMeta.textContent = 'A cotacao foi solicitada, mas nao identifiquei o formato do resultado. Veja as transportadoras na Sisfrete e envie o Diagnostico para adaptar a leitura.';
        return;
      }
      try {
        if (collectComparisons() > 0) {
          clearInterval(comparisonTimer); comparisonTimer = null;
        }
      } catch (err) { console.warn(msgPrefix, 'Leitura de transportadoras', err); }
    }, 1100);
  }
  function addResultSection() {
    if (!IS_SIS) return;
    resultSection = document.createElement('details');
    resultSection.open = true;
    resultSection.hidden = true;
    resultSection.style.cssText = 'margin-top:8px;padding-top:7px;border-top:1px solid #bbf7d0';
    const head = document.createElement('summary');
    head.textContent = 'Comparar transportadoras (sem contratar)';
    head.style.cssText = 'font-weight:600;cursor:pointer;margin-bottom:6px';
    resultSection.append(head);
    resultMeta = document.createElement('div');
    resultMeta.style.cssText = 'font-size:11px;color:#334155;line-height:1.35';
    resultList = document.createElement('div');
    resultList.style.cssText = 'max-height:185px;overflow:auto;font-size:11px';
    resultSection.append(resultMeta, resultList);
    const controlsRow = document.createElement('div');
    controlsRow.style.cssText = 'display:flex;gap:6px;margin-top:6px';
    const read = document.createElement('button');
    read.type = 'button'; read.textContent = 'Ler resultados';
    read.style.cssText = 'padding:6px;border:1px solid #047857;background:white;color:#065f46;border-radius:5px;cursor:pointer;font-size:11px;flex:1';
    read.addEventListener('click', () => {
      const token = comparisonToken();
      if (!token) { markStatus('Comparacao disponivel somente apos cotacao recente nesta conta/pedido.', true); return; }
      const rows = readTransportResults();
      showComparisons(rows,token);
    });
    const copy = document.createElement('button');
    copy.type = 'button'; copy.textContent = 'Copiar comparativo';
    copy.style.cssText = 'padding:6px;border:1px solid #047857;background:white;color:#065f46;border-radius:5px;cursor:pointer;font-size:11px;flex:1';
    copy.addEventListener('click', () => {
      const token = comparisonToken();
      if (!token || !lastComparison.length) { markStatus('Nao ha resultados verificados para copiar.', true); return; }
      const ref=getData()?.blingFreightCents;
      const valid=Number.isSafeInteger(ref)&&ref>=0;
      const lines=[`Pedido ${token.order} | Conta ${token.account}`,
        valid?`Frete Bling (Transportador): R$ ${brMoney(ref)}`:'Frete Bling: N/D',
        'Transportadora\tFrete (R$)\tPrazo\tDiferenca vs Bling (R$)'];
      for(const r of lastComparison)lines.push([r.company,brMoney(r.priceCents),r.deadline,
        valid?brMoney(r.priceCents-ref):'N/D'].join('\t'));
      GM_setClipboard(lines.join('\n'), 'text');
      markStatus('Comparativo copiado. Transportadoras nao foram selecionadas nem contratadas.');
    });
    controlsRow.append(read,copy);
    resultSection.append(controlsRow);
    panel.append(resultSection);
  }

  // ------------------- DESTINO CONFIGURAVEL POR CONTA -------------------
  // A conta visivel no cabecalho, por ex. "969 - BAB", separa as preferencias.
  // Nao usa "CDs: Selecione" nem os dados do pedido como identificacao da conta.
  function sisAccountLabel() {
    if (!IS_SIS) return '';
    const accountPattern = /^\d{2,8}\s*-\s*[\p{L}0-9_. -]{2,32}$/u;
    // Buscar texto EXATO em elementos pequenos do cabecalho. Nunca filtrar
    // por coordenadas: o identificador pode mudar de lugar em zoom alto.
    const groups = [
      document.querySelectorAll('header *, nav *, .navbar *, .el-header *, [class*="topbar"] *, [class*="header"] *'),
      document.querySelectorAll('body *')
    ];
    for (const group of groups) {
      const matches = [...group].filter(el => {
        if (!visible(el) || el.closest('#bs-quote-panel') || el.closest('#bs-quote-launcher')) return false;
        const name = (el.textContent || '').trim().replace(/\s+/g, ' ');
        if (!accountPattern.test(name)) return false;
        return ![...el.children].some(child => (child.textContent || '').trim().replace(/\s+/g, ' ') === name);
      });
      const unique = [...new Set(matches.map(el => el.textContent.trim().replace(/\s+/g, ' ')))];
      if (unique.length === 1) return unique[0];
      if (unique.length > 1) return ''; // ambiguo, nao usar conta errada
    }
    return '';
  }
  function sisAccountKey() {
    // Nunca compartilhar configuracao de CD/canal entre contas nao identificadas.
    // Em v1.5, __sem_id_visivel__ podia agrupar contas diferentes.
    return sisAccountLabel() || null;
  }
  function readDestinationMap() {
    try {
      const raw = GM_getValue(DEST_KEY, {}) || {};
      return raw && typeof raw === 'object' && !Array.isArray(raw) ? raw : {};
    } catch (_) { return {}; }
  }
  function destination() {
    if (!IS_SIS || !sisAccountKey()) return null;
    const entry = readDestinationMap()[sisAccountKey()];
    if (!entry || typeof entry !== 'object') return null;
    const cd = String(entry.cd || '').trim();
    const channel = String(entry.channel || '').trim();
    return cd && channel ? { cd, channel } : null;
  }
  function saveDestination(cd, channel) {
    if (!sisAccountKey()) throw new Error('Nao consegui identificar a conta da Sisfrete no topo. Para evitar usar o CD de outra conta, nao salvarei a configuracao.');
    const cleanCD = String(cd || '').trim().replace(/\s+/g, ' ');
    const cleanChannel = String(channel || '').trim().replace(/\s+/g, ' ');
    if (!cleanCD || !cleanChannel || /^(selecione|centro de distribuicao|canal de vendas)$/i.test(cleanCD) ||
        /^(selecione|canal de vendas)$/i.test(cleanChannel)) {
      throw new Error('Escolha um CD e um canal validos antes de salvar.');
    }
    const map = readDestinationMap();
    map[sisAccountKey()] = { cd: cleanCD, channel: cleanChannel };
    GM_setValue(DEST_KEY, map);
    updateDestinationLabels();
    return map[sisAccountKey()];
  }
  function updateDestinationLabels() {
    if (!IS_SIS) return;
    const d = destination();
    const acct = sisAccountLabel() || 'conta nao identificada';
    if (destinationSubtitle) destinationSubtitle.textContent = d
      ? `Destino: Sisfrete | ${acct} | CD: ${d.cd} | Canal: ${d.channel}`
      : `Destino: Sisfrete | ${acct} | configure CD e canal`;
    if (destinationSummary) destinationSummary.textContent = d
      ? `Conta ${acct} | CD: ${d.cd} | Canal: ${d.channel}`
      : `Conta ${acct} | Nenhum CD configurado: salve as preferencias abaixo.`;
  }
  function requireDestination() {
    if (!sisAccountKey()) throw new Error('Conta Sisfrete nao identificada. Cotacao automatica bloqueada para evitar selecionar CD da conta errada.');
    const d = destination();
    if (!d) throw new Error('Configure e salve Centro de Distribuicao e Canal de Vendas no painel da macro antes de cotar.');
    return d;
  }

  async function fillSisfrete(quoteAfter = false) {
    if (!IS_SIS || !IS_SIS_QUOTE()) throw new Error('Abra a tela Nova Cotacao da Sisfrete para preencher o pedido.');
    const data = getData();
    if (!data?.order || !data?.items?.length) throw new Error('Capture um pedido de venda no Bling antes de cotar.');
    if (Date.now() - new Date(data.capturedAt).getTime() > 12 * 60 * 60 * 1000) {
      throw new Error('Captura com mais de 12 horas. Reabra e capture o pedido atualizado no Bling.');
    }
    if (data.items.length > 30) throw new Error('Mais de 30 produtos: cotacao automatica bloqueada por seguranca.');
    const accountAtStart = sisAccountKey();
    const dest = requireDestination();
    const existingOrder = inputText(requireField('Numero do Pedido'));
    if (existingOrder && existingOrder !== data.order) {
      throw new Error(`A tela Sisfrete ja contem pedido ${existingOrder}. Abra uma Nova Cotacao vazia para evitar misturar pedidos.`);
    }
    stage('selecionar-CD');
    markStatus(`Preenchendo pedido ${data.order} | CD ${dest.cd} | Canal ${dest.channel}...`);
    await chooseByLabel('Centro de Distribuicao', dest.cd);
    // O canal so fica disponivel apos o CD terminar de atualizar a interface.
    await sleep(1000);
    if (!valueInControl(selectContext('Centro de Distribuicao'), dest.cd)) {
      await chooseByLabel('Centro de Distribuicao', dest.cd);
    }
    stage('selecionar-Canal');
    await chooseByLabel('Canal de Vendas', dest.channel);
    await sleep(1000);
    if (!valueInControl(selectContext('Canal de Vendas'), dest.channel)) {
      await chooseByLabel('Canal de Vendas', dest.channel);
    }
    if (sisAccountKey() !== accountAtStart) throw new Error('A conta Sisfrete mudou durante a selecao de CD/canal. Interrompi por seguranca.');
    stage('consultar-CEP');
    await lookupCep(data.cep, data.city || '');
    setNativeValue(requireField('Numero do Pedido'), data.order);
    stage('preencher-produtos');
    const prices = await writeProducts(data);
    await sleep(650);
    if (!valueInControl(selectContext('Canal de Vendas'), dest.channel)) {
      markStatus('Canal de Vendas foi limpo pela Sisfrete; selecionando novamente...');
      await chooseByLabel('Canal de Vendas', dest.channel);
    }
    stage('validar-formulario');
    await validateSisfrete(data, prices);
    await sleep(650);
    if (sisAccountKey() !== accountAtStart || !valueInControl(selectContext('Centro de Distribuicao'), dest.cd) || !valueInControl(selectContext('Canal de Vendas'), dest.channel)) {
      throw new Error('A conta, o CD ou o Canal mudou antes da cotacao. Nada foi enviado.');
    }
    markStatus(`Conferido: pedido ${data.order}, ${data.items.length} SKU(s), R$ ${brMoney(data.totalCents)}.`);
    if (!quoteAfter) {
      stage('preenchimento-validado');
      markStatus('Preenchimento concluido e validado. Confira a tela antes de cotar.');
      return;
    }
    const quoteLabel = textOne('Cotar Frete');
    const btn = quoteLabel?.node.closest('button,[role="button"]') || [...document.querySelectorAll('button')].find(el => norm(el.textContent) === 'cotar frete');
    if (!btn || btn.disabled) throw new Error('Formulario conferido, mas nao encontrei botao Cotar Frete habilitado.');
    // Armazenar a intencao ANTES do clique; a Sisfrete pode navegar de pagina.
    const comparisonToken = { order: data.order, account: accountAtStart, at: Date.now(), source: data.source };
    stage('solicitar-cotacao');
    submitOnce(accountAtStart,data.order);
    sessionStorage.setItem(COMPARE_KEY, JSON.stringify(comparisonToken));
    userClick(btn);
    startCompareWatch();
    markStatus(`Cotacao solicitada para pedido ${data.order}. Vou ler as transportadoras quando aparecerem (sem selecionar/contratar nenhuma).`);
  }

  function diagnostics() {
    const data = getData();
    const r = { versao:VERSION, etapa:stageName, acao:actionName, ultimaFalha:failures().at(-1)||null,
      freteBlingTransportador: Number.isSafeInteger(data?.blingFreightCents) ? brMoney(data.blingFreightCents) : null,
      pagina: location.pathname, ambiente: IS_BLING ? 'bling' : 'sisfrete',
      origemCapturada: data?.order || null, itensCapturados: data?.items?.map(x => ({sku:x.sku, quantidade:x.qty, centavosLinha:x.lineCents})) || [], ultimoErro: lastError,
      ...(IS_SIS ? { contaIdentificada: sisAccountLabel() || null, destinoConfigurado: destination() } : {}) };
    if (IS_BLING) {
      const b = afterSection('Endereco de entrega', 'Dados adicionais');
      r.labels = ['Total da venda', 'CEP'].map(x => ({ campo: x, valor: x === 'CEP' ? getBlingValue(x, b) : getBlingValue(x) }));
      r.itens = (() => { try { return blingItems(); } catch (e) { return e.message; } })();
    } else {
      r.labels = ['Centro de Distribuicao', 'Canal de Vendas', 'CEP de Destino', 'Destino', 'Numero do Pedido']
        .map(x => {
          const f = fieldByName(x);
          const ctx = /Centro de Distribuicao|Canal de Vendas/.test(x) ? selectContext(x) : null;
          return { campo: x, encontrado: !!f,
            ...(ctx ? { seletor: !!ctx.root, textoNoControle: (ctx.root.textContent || '').trim().slice(0, 80),
              valorInterno: ctx.input?.value || '', placeholder: ctx.input?.getAttribute('placeholder') || '',
              desabilitado: isControlDisabled(ctx),
              selecaoEsperada: !!destination() && valueInControl(ctx, x === 'Centro de Distribuicao' ? destination().cd : destination().channel),
              detalheSeletor: {
                classes: String(ctx.root?.className||'').slice(0,110),
                textoPai: String(ctx.root?.parentElement?.innerText||'').slice(0,150),
                controles: [...ctx.root.querySelectorAll('input,select,[role="combobox"]')].slice(0,3).map(el=>({
                  tipo:el.tagName,valor:String(el.value||'').slice(0,75),titulo:String(el.getAttribute('title')||'').slice(0,75)
                }))
              } } : {}) };
        });
      r.linhas = (() => { try { return sisfreteRows().map((row, index) => ({ linha: index+1, sku: inputText(row.sku), quantidade: inputText(row.qty), peso: inputText(row.weight), comprimento: inputText(row.length), largura: inputText(row.width), altura: inputText(row.height), valorUnitario: inputText(row.unit), valorTotal: inputText(row.total) })); } catch (e) { return e.message; } })();
      r.transportadorasReconhecidas = (() => { try { return readTransportResults(); } catch (e) { return e.message; } })();
      r.comparacaoPendente = !!comparisonToken();
      r.estruturaCamposProdutos = (() => { try { const p = textOne('Produtos'), q = textOne('Cotar Frete'); return controls().filter(el => beforeInDom(p?.node, el) && beforeInDom(el, q?.node)).map(el => ({tipo:el.tagName,placeholder:el.getAttribute('placeholder') || '',aria:el.getAttribute('aria-label') || ''})).slice(0,75); } catch (e) { return e.message; } })();
      r.zoomRelatado = 'Informe a porcentagem de zoom ao enviar este diagnostico';
    }
    GM_setClipboard(JSON.stringify(r, null, 2), 'text');
    markStatus('Diagnostico copiado; pode colar nesta conversa.');
    if (previewEl) { previewEl.hidden = false; previewEl.textContent = JSON.stringify(r, null, 2); }
  }
  async function execute(task) {
    if (busy) return;
    busy = true;
    for (const btn of panel.querySelectorAll('button')) btn.disabled = true;
    actionName=task.name||'comando-manual';stage('iniciar');
    try { await task(); lastError = ''; stage('concluido'); }
    catch (e) { lastError = String(e?.message || e); saveFailure(e); markStatus('BLOQUEADO: ' + lastError, true); console.error(msgPrefix, e); }
    finally { busy = false; for (const btn of panel.querySelectorAll('button')) btn.disabled = false; }
  }

  // ------------------- RETOMADA SEGURA DEPOIS DA NAVEGACAO -------------------
  // A sessao desta guia recebe o pedido do Bling. Mesmo apos navegar de
  // /nova-cotacao para /form, a macro retoma o preenchimento sem outro F8.
  function resumeOnQuotePage() {
    if (!IS_SIS || !IS_SIS_QUOTE() || busy) return;
    let p;
    try { p = JSON.parse(sessionStorage.getItem(RESUME_KEY) || 'null'); } catch (_) { p = null; }
    if (!p) return;
    sessionStorage.removeItem(RESUME_KEY); // nunca cotar duas vezes no refresh
    if (Date.now() - Number(p.at) > 60000 || p.order !== getData()?.order) {
      markStatus('Retomada de cotacao expirada ou pedido mudou. Pressione F8 novamente.', true);
      return;
    }
    // A conta pode ser exibida somente depois de o app Vue carregar.
    execute(async () => {
      const account = await waitFor(() => sisAccountKey(), 12000, 'identificacao da conta Sisfrete');
      if (p.account && p.account !== account) {
        throw new Error('A conta Sisfrete mudou durante a navegacao. Operacao interrompida.');
      }
      if (!p.account && !p.newTab) {
        throw new Error('A conta de origem da navegacao nao foi identificada com seguranca.');
      }
      await waitFor(() => textOne('Produtos') && textOne('Numero do Pedido'),
        12000, 'formulario da Nova Cotacao');
      await fillSisfrete(p.quote === true);
    });
  }

  // ------------------- ATALHO CONFIGURAVEL -------------------
  // Mesma tecla em ambos os sites, mas a acao depende da pagina atual.
  // Nao interferir na digitacao ou nos atalhos reservados dos navegadores.
  function keyCombo(event) {
    const k = String(event.key || '').toUpperCase();
    if (!(/^F(?:[1-9]|1[0-2])$/.test(k) || /^[A-Z0-9]$/.test(k))) return null;
    return [event.ctrlKey ? 'Ctrl' : '', event.altKey ? 'Alt' : '',
      event.shiftKey ? 'Shift' : '', k].filter(Boolean).join('+');
  }
  function hotkeyAllowed(combo) {
    if (!combo) return false;
    // F8/F9 sao simples, sem colidir com refresh, tela cheia, ferramentas etc.
    if (combo === 'F8' || combo === 'F9') return true;
    // Outras teclas exigem Ctrl+Alt para evitar disparos por digitar letras.
    if (/^Ctrl\+Alt\+(?:Shift\+)?[A-Z0-9]$/.test(combo)) return true;
    return false;
  }
  function settings() {
    let raw;
    try { raw = GM_getValue(HOTKEY_KEY, {}) || {}; }
    catch (e) { raw = {}; }
    return {
      hotkey: hotkeyAllowed(raw.hotkey) ? raw.hotkey : DEFAULT_SETTINGS.hotkey,
      openAfterCapture: typeof raw.openAfterCapture === 'boolean' ? raw.openAfterCapture : DEFAULT_SETTINGS.openAfterCapture,
      sisAction: raw.sisAction === 'fill' ? 'fill' : DEFAULT_SETTINGS.sisAction,
      // Na v1.4 ocultar no Bling tambem ocultava na Sisfrete.
      // Agora cada site tem sua propria preferencia (Sisfrete inicia visivel).
      panelHidden: IS_SIS ? raw.panelHiddenSisfrete === true :
        (typeof raw.panelHiddenBling === 'boolean' ? raw.panelHiddenBling : raw.panelHidden === true)
    };
  }
  function saveSettings(changes) {
    let stored = {};
    try { stored = GM_getValue(HOTKEY_KEY, {}) || {}; } catch (_) { /* defaults */ }
    const next = { ...settings(), ...changes };
    const updated = { ...stored, hotkey: next.hotkey,
      openAfterCapture: next.openAfterCapture, sisAction: next.sisAction };
    if (Object.prototype.hasOwnProperty.call(changes, 'panelHidden')) {
      updated[IS_SIS ? 'panelHiddenSisfrete' : 'panelHiddenBling'] = !!changes.panelHidden;
    }
    GM_setValue(HOTKEY_KEY, updated);
    refreshHotkeySummary();
    setPanelVisibility(next.panelHidden);
    return next;
  }
  function setPanelVisibility(hidden) {
    // Apenas esconde a interface; nao remove o listener do atalho F8.
    if (panel) panel.style.display = hidden ? 'none' : '';
    if (launcher) launcher.style.display = hidden ? 'flex' : 'none';
  }
  function refreshHotkeySummary() {
    if (!hotkeySummary) return;
    const s = settings();
    hotkeySummary.textContent = `Tecla: ${s.hotkey} | Bling: capturar${s.openAfterCapture ? ' e abrir Sisfrete' : ''} | Sisfrete: ${s.sisAction === 'quote' ? 'preencher e cotar' : 'so preencher'}`;
  }
  function isEditing(event) {
    const target = event.target;
    return !!(target?.isContentEditable || target?.closest?.('input, textarea, select, [contenteditable="true"], [role="textbox"]'));
  }
  function primaryAction() {
    const s = settings();
    if (IS_BLING) {
      const data = captureBling();
      if (s.openAfterCapture) return openOrReuseSisfrete({
        autoFill: true, data, quote: s.sisAction === 'quote'
      });
    } else if (IS_SIS) {
      if (!IS_SIS_QUOTE()) {
        const data = getData();
        if (!data?.order) throw new Error('Capture o pedido no Bling antes de iniciar a cotacao.');
        // Somente a acao F8 iniciada pelo usuario autoriza preencher depois da navegacao.
        sessionStorage.setItem(RESUME_KEY, JSON.stringify({ order: data.order, account: sisAccountKey(), at: Date.now(), quote: s.sisAction === 'quote' }));
        markStatus('Abrindo Nova Cotacao; ao carregar, continuarei o preenchimento automaticamente.');
        location.assign(URL_SISFRETE);
        return;
      }
      return fillSisfrete(s.sisAction === 'quote');
    }
  }
  function onHotkey(event) {
    if (event.isComposing || event.repeat) return;
    if (recordingHotkey) {
      event.preventDefault(); event.stopImmediatePropagation();
      if (event.key === 'Escape') {
        recordingHotkey = false;
        if (recordButton) recordButton.textContent = 'Mudar tecla';
        markStatus('Alteracao do atalho cancelada.');
        return;
      }
      const combo = keyCombo(event);
      // Ctrl/Alt/Shift sozinhos nao finalizam a captura.
      if (!combo && /^(Control|Shift|Alt|Meta)$/.test(event.key)) return;
      if (!hotkeyAllowed(combo)) {
        markStatus('Tecla nao permitida. Use F8, F9 ou Ctrl+Alt+letra/numero. Esc cancela.', true);
        return;
      }
      saveSettings({ hotkey: combo });
      recordingHotkey = false;
      if (recordButton) recordButton.textContent = 'Mudar tecla';
      markStatus(`Atalho ${combo} salvo no Tampermonkey.`);
      return;
    }
    if (busy) return;
    const configured = settings().hotkey;
    // Teclas de funcao continuam disponiveis mesmo com foco num campo.
    // Combinacoes de letras nao interferem na edicao do usuario.
    if (isEditing(event) && !['F8', 'F9'].includes(configured)) return;
    if (keyCombo(event) !== configured) return;
    event.preventDefault(); event.stopImmediatePropagation();
    execute(primaryAction);
  }
  function addKeyboardOptions() {
    const wrapper = document.createElement('details');
    wrapper.style.cssText = 'margin-top:8px;padding-top:6px;border-top:1px solid #bbf7d0';
    const heading = document.createElement('summary');
    heading.textContent = 'Atalho e configuracoes';
    heading.style.cssText = 'font-weight:600;cursor:pointer;margin-bottom:5px;user-select:none';
    wrapper.appendChild(heading);
    hotkeySummary = document.createElement('div');
    hotkeySummary.style.cssText = 'color:#475569;font-size:11px;line-height:1.45;margin-bottom:7px';
    wrapper.appendChild(hotkeySummary);
    recordButton = document.createElement('button');
    recordButton.type = 'button'; recordButton.textContent = 'Mudar tecla';
    recordButton.style.cssText = 'font:12px Arial;padding:6px 10px;border:1px solid #047857;background:#fff;color:#065f46;border-radius:5px;cursor:pointer;margin-bottom:8px';
    recordButton.addEventListener('click', ev => {
      ev.preventDefault(); ev.stopPropagation();
      if (busy) return;
      recordingHotkey = true;
      recordButton.textContent = 'Pressione a tecla...';
      markStatus('Pressione F8, F9 ou Ctrl+Alt+letra/numero (Esc cancela).');
      recordButton.blur();
    });
    wrapper.appendChild(recordButton);
    const line1 = document.createElement('label');
    line1.style.cssText = 'display:flex;align-items:center;gap:6px;line-height:1.3;margin-bottom:8px;cursor:pointer';
    const openCheckbox = document.createElement('input');
    openCheckbox.type = 'checkbox'; openCheckbox.checked = settings().openAfterCapture;
    openCheckbox.addEventListener('change', () => {
      saveSettings({ openAfterCapture: openCheckbox.checked });
      markStatus(openCheckbox.checked ? 'Apos capturar, reutilizara a Sisfrete aberta ou abrira nova guia.' : 'Apos capturar, permanecera no Bling.');
    });
    line1.append(openCheckbox, document.createTextNode('Apos capturar no Bling, abrir Sisfrete'));
    wrapper.appendChild(line1);
    const line2 = document.createElement('label');
    line2.style.cssText = 'display:grid;gap:4px;font-size:11px';
    line2.appendChild(document.createTextNode('Acao do atalho na Sisfrete:'));
    const sisSelect = document.createElement('select');
    sisSelect.style.cssText = 'width:100%;padding:6px;border:1px solid #cbd5e1;border-radius:5px;font-size:12px;background:white;color:#0f172a';
    [['quote','Preencher e cotar'],['fill','So preencher (para conferir)']].forEach(([value, text]) => {
      const opt = document.createElement('option'); opt.value = value; opt.textContent = text; sisSelect.appendChild(opt);
    });
    sisSelect.value = settings().sisAction;
    sisSelect.addEventListener('change', () => {
      saveSettings({ sisAction: sisSelect.value });
      markStatus('Acao do atalho na Sisfrete: ' + (sisSelect.value === 'quote' ? 'preencher e cotar.' : 'so preencher.'));
    });
    line2.appendChild(sisSelect); wrapper.appendChild(line2);
    panel.appendChild(wrapper);
    refreshHotkeySummary();
  }

  // Configuracoes persistentes para a conta exibida na Sisfrete. A selecao
  // "Outro" aceita o nome completo de qualquer novo CD/canal exibido no site.
  function addDestinationOptions() {
    if (!IS_SIS) return;
    const wrapper = document.createElement('details');
    wrapper.style.cssText = 'margin-top:8px;padding-top:7px;border-top:1px solid #bbf7d0';
    const heading = document.createElement('summary');
    heading.textContent = 'Centro de Distribuicao e Canal';
    heading.style.cssText = 'font-weight:600;cursor:pointer;margin-bottom:6px;user-select:none';
    wrapper.appendChild(heading);
    destinationSummary = document.createElement('div');
    destinationSummary.style.cssText = 'color:#475569;font-size:11px;line-height:1.35;margin-bottom:8px;overflow-wrap:anywhere';
    wrapper.appendChild(destinationSummary);

    const fieldStyle = 'width:100%;box-sizing:border-box;padding:6px;border:1px solid #cbd5e1;border-radius:5px;font-size:12px;background:white;color:#0f172a';
    const fieldRow = (labelText, options) => {
      const label = document.createElement('label');
      label.style.cssText = 'display:grid;gap:4px;margin-bottom:7px;font-size:11px';
      label.appendChild(document.createTextNode(labelText));
      const select = document.createElement('select'); select.style.cssText = fieldStyle;
      for (const [val, text] of options) {
        const opt = document.createElement('option'); opt.value = val; opt.textContent = text; select.appendChild(opt);
      }
      label.appendChild(select);
      const custom = document.createElement('input');
      custom.type = 'text'; custom.placeholder = 'Nome exato da opcao no site';
      custom.style.cssText = fieldStyle + ';display:none;margin-top:4px';
      custom.maxLength = 180;
      label.appendChild(custom);
      const updateCustom = () => { custom.style.display = select.value === '__outro__' ? '' : 'none'; };
      select.addEventListener('change', updateCustom);
      return { label, select, custom, updateCustom };
    };

    const cd = fieldRow('Centro de Distribuicao:', [
      ['', 'Selecione o CD'], ['BABUS', 'BABUS'], [CD_LONG, CD_LONG], ['__outro__', 'Outro (nome exato)']
    ]);
    const ch = fieldRow('Canal de Vendas:', [
      ['Sisfrete', 'Sisfrete'], ['__outro__', 'Outro (nome exato)']
    ]);
    wrapper.append(cd.label, ch.label);

    function showCurrent() {
      const saved = destination();
      const init = (field, value) => {
        const known = [...field.select.options].some(o => o.value === value && value !== '__outro__');
        field.select.value = known ? value : (value ? '__outro__' : '');
        field.custom.value = known ? '' : value || '';
        field.updateCustom();
      };
      init(cd, saved?.cd || '');
      init(ch, saved?.channel || 'Sisfrete');
      updateDestinationLabels();
    }
    showCurrent();

    const save = document.createElement('button');
    save.type = 'button'; save.textContent = 'Salvar CD e Canal';
    save.style.cssText = 'width:100%;padding:7px;border:1px solid #047857;border-radius:5px;background:#078a61;color:white;font:12px Arial;cursor:pointer';
    save.addEventListener('click', e => {
      e.preventDefault(); e.stopPropagation();
      if (busy) return;
      const read = field => field.select.value === '__outro__' ? field.custom.value : field.select.value;
      try {
        const d = saveDestination(read(cd), read(ch));
        markStatus(`Preferencias salvas para ${sisAccountLabel() || 'conta sem ID visivel'}: CD ${d.cd} | Canal ${d.channel}.`);
      } catch (err) { markStatus(err.message, true); }
    });
    wrapper.appendChild(save);

    const tip = document.createElement('div');
    tip.style.cssText = 'font-size:10px;color:#64748b;line-height:1.45;margin-top:6px';
    tip.textContent = 'As preferencias sao salvas por conta Sisfrete. O CD e selecionado antes de liberar o Canal. Se a conta nao for identificada, confirme as preferencias ao trocar de painel.';
    wrapper.appendChild(tip);
    panel.appendChild(wrapper);
    updateDestinationLabels();
  }

  // ------------------- PAINEL DE CONTROLE -------------------
  function button(label, handler, secondary = false) {
    const btn = document.createElement('button');
    btn.type = 'button'; btn.textContent = label;
    btn.style.cssText = 'border:1px solid #047857;padding:8px 7px;border-radius:5px;cursor:pointer;font:12px Arial,sans-serif;' +
      (secondary ? 'background:white;color:#065f46;' : 'background:#078a61;color:white;');
    btn.addEventListener('click', e => { e.preventDefault(); e.stopPropagation(); execute(handler); });
    return btn;
  }
  function renderActionButtons() {
    if (!actionGrid) return;
    actionGrid.replaceChildren();
    if (IS_BLING) {
      actionGrid.appendChild(button('Capturar pedido', () => captureBling()));
      actionGrid.appendChild(button('Abrir Sisfrete', () => openOrReuseSisfrete(), true));
    } else if (IS_SIS_QUOTE()) {
      actionGrid.appendChild(button('Preencher e cotar', () => fillSisfrete(true)));
      actionGrid.appendChild(button('So preencher', () => fillSisfrete(false), true));
    } else {
      actionGrid.appendChild(button('Abrir Nova Cotacao', () => { location.assign(URL_SISFRETE); }));
    }
    actionGrid.appendChild(button('Ver pedido', () => showData(), true));
    actionGrid.appendChild(button('Diagnostico', () => diagnostics(), true));
  }
  function initUI() {
    if (document.querySelector('#bs-quote-panel')) return;
    panel = document.createElement('section'); panel.id = 'bs-quote-panel';
    panel.style.cssText = 'position:fixed;right:12px;bottom:12px;z-index:2147483647;width:280px;max-height:80vh;overflow:auto;' +
      'background:#fff;color:#183c2f;border:1px solid #059669;border-radius:10px;box-shadow:0 4px 20px #0003;padding:12px;' +
      'font-family:Arial,sans-serif;font-size:12px;box-sizing:border-box;';
    const titleRow = document.createElement('div');
    titleRow.style.cssText = 'display:flex;align-items:center;justify-content:space-between;gap:7px;margin-bottom:5px';
    const title = document.createElement('div'); title.textContent = 'Bling → Sisfrete | Cotar pedido v'+VERSION;
    title.style.cssText = 'font-weight:bold;font-size:14px';
    const closeButton = document.createElement('button');
    closeButton.type = 'button';
    closeButton.textContent = '×';
    closeButton.title = 'Ocultar painel (atalho continua funcionando)';
    closeButton.setAttribute('aria-label', 'Ocultar painel da macro');
    closeButton.style.cssText = 'border:0;background:transparent;color:#475569;font:bold 22px Arial;cursor:pointer;line-height:1;padding:0 2px;min-width:24px;';
    closeButton.addEventListener('click', e => {
      e.preventDefault(); e.stopPropagation();
      saveSettings({ panelHidden: true });
    });
    titleRow.append(title, closeButton);
    panel.appendChild(titleRow);
    noticeVersion=document.createElement('div');
    noticeVersion.hidden=true;
    noticeVersion.style.cssText='background:#fff7ed;border:1px solid #fdba74;padding:7px;border-radius:6px;color:#9a3412;font-size:11px;margin-bottom:8px';
    panel.appendChild(noticeVersion);
    refreshVersionNotice();
    const sub = document.createElement('div'); sub.style.cssText = 'color:#64748b;margin-bottom:8px';
    sub.textContent = IS_BLING ? 'Origem: Bling · Pedido de venda' : 'Destino: Sisfrete · configure CD e Canal';
    if (IS_SIS) destinationSubtitle = sub;
    panel.appendChild(sub);
    actionGrid = document.createElement('div');
    actionGrid.style.cssText = 'display:grid;grid-template-columns:1fr 1fr;gap:6px';
    renderActionButtons();
    panel.appendChild(actionGrid);
    addResultSection();
    addKeyboardOptions();
    addDestinationOptions();
    statusEl = document.createElement('p'); statusEl.style.cssText = 'font-size:11px;line-height:1.4;margin:8px 0 0';
    statusEl.textContent = getData()?.order ? `Pedido salvo: ${getData().order}.` : 'Nenhum pedido capturado.';
    panel.appendChild(statusEl);
    previewEl = document.createElement('pre'); previewEl.hidden = true;
    previewEl.style.cssText = 'white-space:pre-wrap;word-break:break-word;font-size:10px;max-height:220px;overflow:auto;background:#f1f5f9;padding:8px;border-radius:5px;';
    panel.appendChild(previewEl);
    document.body.appendChild(panel);

    launcher = document.createElement('button');
    launcher.id = 'bs-quote-launcher';
    launcher.type = 'button';
    launcher.textContent = '🚚';
    launcher.title = 'Abrir painel Bling → Sisfrete (F8 funciona com painel oculto)';
    launcher.setAttribute('aria-label', 'Reabrir painel da macro de cotacao');
    launcher.style.cssText = 'position:fixed;right:12px;bottom:12px;z-index:2147483647;width:42px;height:42px;' +
      'display:none;align-items:center;justify-content:center;background:#047857;color:white;border:1px solid #065f46;' +
      'border-radius:50%;box-shadow:0 4px 14px #0004;font:21px Arial;cursor:pointer;';
    launcher.addEventListener('click', e => {
      e.preventDefault(); e.stopPropagation();
      saveSettings({ panelHidden: false });
    });
    document.body.appendChild(launcher);

    // Preferencia de painel independente no Bling e na Sisfrete, preservada ao navegar.
    setPanelVisibility(settings().panelHidden);
    checkNewVersion();
    document.addEventListener('keydown', onHotkey, true);
    // Recupera o painel se um framework reconstruir o <body> ao navegar sem recarregar.
    let currentRoute = location.pathname;
    setInterval(() => {
      if (document.body && panel && !panel.isConnected) document.body.appendChild(panel);
      if (document.body && launcher && !launcher.isConnected) document.body.appendChild(launcher);
      if (IS_SIS && currentRoute !== location.pathname) {
        // Sisfrete pode navegar por SPA sem recarregar o userscript.
        currentRoute = location.pathname;
        renderActionButtons();
        updateDestinationLabels();
        pingSisfreteTab();
        resumeOnQuotePage();
        if (comparisonToken()) startCompareWatch();
      }
    }, 1500);
  }
  // Escutar pedidos de reutilizacao em QUALQUER pagina da Sisfrete.
  if (IS_SIS) listenForReuseRequest();
  if (IS_BLING && !/vendas\.php/i.test(location.pathname)) return;
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', initUI, { once: true });
  else initUI();
  if (IS_SIS) {
    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', () => {
      consumeNewTabRequest(); resumeOnQuotePage(); startCompareWatch();
    }, { once: true });
    else { consumeNewTabRequest(); resumeOnQuotePage(); startCompareWatch(); }
  }
})();
