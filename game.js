'use strict';
/* データは cards.js と nobles.js に分離。読み込み順序は index.html を参照。 */
const GAME_DATA = {cards: GEM_CARDS, nobles: GEM_NOBLES};
const COLORS=['white','blue','green','red','black'];
const ALL=[...COLORS,'gold'];
const CNAME={white:'白',blue:'青',green:'緑',red:'赤',black:'黒',gold:'金'};
const CARDMAP=Object.fromEntries(GAME_DATA.cards.map(c=>[c.id,c]));
const NOBLEMAP=Object.fromEntries(GAME_DATA.nobles.map(n=>[n.id,n]));
const $=id=>document.getElementById(id);
const escapeHtml=v=>String(v??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const dup=x=>JSON.parse(JSON.stringify(x));
const num=(x)=>Number(x)||0;
const rng=(a)=>Math.floor(Math.random()*a);
const shuffled=a=>{const b=[...a]; for(let i=b.length-1;i>0;i--){let j=rng(i+1); [b[i],b[j]]=[b[j],b[i]];}return b;};
const total=o=>ALL.reduce((a,c)=>a+num(o[c]),0);
const emptyGems=()=>Object.fromEntries(ALL.map(c=>[c,0]));
const baseBank=180000, basicTurn=20000;
let expandedPlayerId='', network=null, roomCode='', state=null, seenUpdate='', activeUser='', clientName=localStorage.getItem('gem_name')||'', activeMode='', presence={}, serverOffset=0, isBusy=false, selected=[], takeMode='diff', modal=null, view='game', toastTimer=null, uiTimer=null;

function now(){return Date.now()+serverOffset;}
function showToast(msg){const el=$('toast');el.textContent=msg;el.classList.add('visible');clearTimeout(toastTimer);toastTimer=setTimeout(()=>el.classList.remove('visible'),3600);}
function fail(msg){showToast(msg||'操作できませんでした');}
function cfg(){return {...FIREBASE_DEFAULT_CONFIG};}
function cfgReady(){const v=cfg();return Boolean(v.apiKey&&v.databaseURL&&v.projectId&&v.appId);}
function asArray(x){if(Array.isArray(x))return x;if(x&&typeof x==='object')return Object.keys(x).sort((a,b)=>Number(a)-Number(b)).map(k=>x[k]);return [];}
function normalizeState(s){if(!s)return s;
 s.history=asArray(s.history);s.players=asArray(s.players);
 if(s.game){const g=s.game;g.turnOrder=asArray(g.turnOrder);g.nobles=asArray(g.nobles);g.nobleCandidates=asArray(g.nobleCandidates);
  g.deck=g.deck||{};g.market=g.market||{};
  for(const tier of [1,2,3]){g.deck[tier]=asArray(g.deck[tier]);const slots=g.market[tier]||{};g.market[tier]=Array.from({length:4},(_,i)=>Number(slots[i])||0);}
  for(const p of Object.values(g.p||{})){p.cards=asArray(p.cards);p.reserve=asArray(p.reserve);p.nobles=asArray(p.nobles);}
 }
 return s;
}
function makeLobby(host,name){return {version:1,status:'lobby',host,players:[{id:host,name,ready:false,view:'lobby'}],game:null,history:[],lastChange:now()};}
function newGame(players,t){
 const deck={};const market={};
 for(let tier=1;tier<=3;tier++){
   const ids=shuffled(GAME_DATA.cards.filter(c=>c.level===tier).map(c=>c.id));
   market[tier]=ids.splice(0,4);deck[tier]=ids;
 }
 const p={};for(const pl of players)p[pl.id]={chips:emptyGems(),cards:[],reserve:[],nobles:[],bank:baseBank};
 const supply=emptyGems();COLORS.forEach(c=>supply[c]=players.length===2?4:players.length===3?5:7);supply.gold=5;
 return {turnOrder:shuffled(players.map(p=>p.id)),p,supply,market,deck,nobles:shuffled(GAME_DATA.nobles.map(n=>n.id)).slice(0,players.length+1),phase:'turn',turnIndex:0,turnStart:t,nobleStart:0,nobleCandidates:[],completed:0,ending:false,log:'ゲーム開始',seq:0};
}
function activeId(g){return g.turnOrder[g.turnIndex];}
function owner(){if(activeMode==='local')return state?.game?activeId(state.game):'local-1';return activeUser;}
function playerName(id){return state?.players?.find(p=>p.id===id)?.name||'プレイヤー';}
function bonuses(g,id){const res={white:0,blue:0,green:0,red:0,black:0};(g.p[id]?.cards||[]).forEach(cardId=>{res[CARDMAP[cardId].color]++});return res;}
function vp(g,id){const pp=g.p[id];return (pp.cards||[]).reduce((sum,c)=>sum+CARDMAP[c].points,0)+(pp.nobles||[]).length*3;}
function canPay(g,id,card){const b=bonuses(g,id),chips=g.p[id].chips;let gold=0;const payment=emptyGems();for(const c of COLORS){const need=Math.max(0,num(card.cost[c])-num(b[c]));const using=Math.min(need,num(chips[c]));payment[c]=using;gold+=need-using;}payment.gold=gold;return {ok:gold<=num(chips.gold),payment};}
function getRefill(g,tier,slot){g.market[tier][slot]=(g.deck[tier]||[]).length?g.deck[tier].pop():0;}
function candidates(g,id){const b=bonuses(g,id);return (g.nobles||[]).filter(nid=>COLORS.every(c=>num(b[c])>=num(NOBLEMAP[nid].cost[c])));}
function currentUsed(g,t){return Math.max(0,t-g.turnStart-basicTurn);}
function currentBank(g,t){return Math.max(0,num(g.p[activeId(g)].bank)-currentUsed(g,t));}
function expired(g,t){return t>=g.turnStart+basicTurn+num(g.p[activeId(g)].bank);}
function addGems(g,id,add,returned={}){
 const pp=g.p[id];const local=emptyGems();
 for(const c of ALL){const n=num(add[c]),r=num(returned[c]);if(!Number.isInteger(n)||!Number.isInteger(r)||n<0||r<0||r>num(pp.chips[c])+n)return false;
   local[c]=num(pp.chips[c])+n-r;
 }
 if(total(local)>10)return false;
 for(const c of ALL){pp.chips[c]=local[c];g.supply[c]=num(g.supply[c])-num(add[c])+num(returned[c]);if(g.supply[c]<0)return false;}
 return true;
}
function reserveTake(g){return g.supply.gold>0?{gold:1}:{gold:0};}
function isAllowedTake(g,a){if(a.kind==='take2')return COLORS.includes(a.color)&&num(g.supply[a.color])>=4;
 if(a.kind!=='take')return false;
 if(!Array.isArray(a.colors)||a.colors.length<1||a.colors.length>3||new Set(a.colors).size!==a.colors.length)return false;
 return a.colors.every(c=>COLORS.includes(c)&&num(g.supply[c])>=1);
}
function finishTurn(s,t){
 const g=s.game;g.completed++;
 if(vp(g,activeId(g))>=15)g.ending=true;
 if(g.ending && g.completed%g.turnOrder.length===0){g.phase='results';s.status='results';
  const results=g.turnOrder.map(id=>({id,name:s.players.find(p=>p.id===id)?.name||'参加者',points:vp(g,id),cards:g.p[id].cards.length,nobles:g.p[id].nobles.length,bank:g.p[id].bank})).sort((a,b)=>b.points-a.points||a.cards-b.cards);
  results.forEach((v,i)=>v.rank=i>0&&v.points===results[i-1].points&&v.cards===results[i-1].cards?results[i-1].rank:i+1);
  s.history=s.history||[];s.history.push({at:t,results});
  for(const pl of s.players){pl.ready=false;pl.view='results';}
 }else{g.turnIndex=(g.turnIndex+1)%g.turnOrder.length;g.turnStart=t;g.phase='turn';}
 g.seq++;
}
function postMove(s,t){
 const g=s.game,id=activeId(g),valid=candidates(g,id);
 if(valid.length===1){g.p[id].nobles.push(valid[0]);g.nobles=g.nobles.filter(n=>n!==valid[0]);g.log=playerName(id)+'が貴族を獲得';finishTurn(s,t);}
 else if(valid.length>1){g.phase='noble';g.nobleCandidates=valid;g.nobleStart=t;g.seq++;}
 else finishTurn(s,t);
}
function randomAuto(g,id){
 const choices=[];
 const available=COLORS.filter(c=>num(g.supply[c])>0);
 if(available.length){choices.push({kind:'take',colors:shuffled(available).slice(0,Math.min(3,available.length))});}
 for(const c of COLORS)if(num(g.supply[c])>=4)choices.push({kind:'take2',color:c});
 if(!choices.length)return {kind:'pass'};
 const a=choices[rng(choices.length)];let arr=a.kind==='take2'?[a.color,a.color]:a.colors;
 const taken=emptyGems();for(const c of arr)taken[c]++;
 const test=emptyGems();for(const c of ALL)test[c]=num(g.p[id].chips[c])+num(taken[c]);
 const back=emptyGems();while(total(test)>10){let list=ALL.filter(c=>test[c]>0);let c=list[rng(list.length)];test[c]--;back[c]++;}
 return {...a,returned:back};
}
function transitionLobbyIfReady(s){if(s.status==='results'&&s.players.every(p=>p.view==='lobby')){s.status='lobby';s.game=null;s.players.forEach(p=>{p.ready=false;});}}
function apply(s,uid,a,t){
 if(!s||!a)return null;
 s=normalizeState(dup(s)); s.lastChange=t;
 if(a.kind==='join'){
   if(s.status!=='lobby'||s.players.length>=4||s.players.some(p=>p.id===uid))return null;
   s.players.push({id:uid,name:(a.name||'ゲスト').slice(0,18),ready:false,view:'lobby'});return s;
 }
 if(a.kind==='leave'){
   if(!s.players.some(p=>p.id===uid))return null;
   if(uid===s.host)return null; // host closes room by removing Firebase state.
   if(s.status==='playing')return null;
   s.players=s.players.filter(p=>p.id!==uid);transitionLobbyIfReady(s);return s;
 }
 if(a.kind==='kick'){
   if(s.host!==uid||s.status==='playing'||uid===a.target||a.target===s.host)return null;
   s.players=s.players.filter(p=>p.id!==a.target);transitionLobbyIfReady(s);return s;
 }
 if(a.kind==='ready'){
   if(s.status!=='lobby')return null;
   const p=s.players.find(p=>p.id===uid);if(!p)return null;p.ready=Boolean(a.value);return s;
 }
 if(a.kind==='start'){
   if(s.status!=='lobby'||s.host!==uid||s.players.length<2||!s.players.every(p=>p.ready))return null;
   s.game=newGame(s.players,t);s.status='playing';return s;
 }
 if(a.kind==='returnLobby'){
   if(s.status!=='results')return null;
   const p=s.players.find(p=>p.id===uid);if(!p)return null;p.view='lobby';p.ready=false;transitionLobbyIfReady(s);return s;
 }
 if(s.status!=='playing'||!s.game)return null;
 const g=s.game,id=activeId(g);
 if(a.kind==='timeout'){
   if(g.phase==='noble'){
     if(t<g.nobleStart+10000)return null;
     const chosen=g.nobleCandidates[rng(g.nobleCandidates.length)];if(!chosen)return null;
     g.p[id].nobles.push(chosen);g.nobles=g.nobles.filter(x=>x!==chosen);g.log='貴族の選択時間切れ';finishTurn(s,t);return s;
   }
   if(g.phase!=='turn'||!expired(g,t))return null;
   const auto=randomAuto(g,id);g.p[id].bank=0;
   if(auto.kind==='take'||auto.kind==='take2'){
     const add=emptyGems();for(const c of auto.kind==='take2'?[auto.color,auto.color]:auto.colors)add[c]++;
     if(!addGems(g,id,add,auto.returned))return null;
   }
   g.log=playerName(id)+'が時間切れ：自動で宝石取得';postMove(s,t);return s;
 }
 if(id!==uid)return null;
 if(a.expected!==g.seq)return null;
 if(g.phase==='noble'){
   if(a.kind!=='noble'||!g.nobleCandidates.includes(a.id)||t>=g.nobleStart+10000)return null;
   g.p[id].nobles.push(a.id);g.nobles=g.nobles.filter(x=>x!==a.id);g.log=playerName(id)+'が貴族を選択';finishTurn(s,t);return s;
 }
 if(g.phase!=='turn'||expired(g,t))return null;
 const bankUsed=Math.max(0,t-g.turnStart-basicTurn), pp=g.p[id];
 if(a.kind==='take'||a.kind==='take2'){
   if(!isAllowedTake(g,a))return null;
   const added=emptyGems();for(const c of a.kind==='take2'?[a.color,a.color]:a.colors)added[c]++;
   if(!addGems(g,id,added,a.returned||{}))return null;
   g.log=playerName(id)+'が宝石を取得';
 }else if(a.kind==='reserve'){
   if(pp.reserve.length>=3)return null;
   let cardId=0;
   if(a.source==='market'){
     const arr=g.market[a.tier];if(!arr||!arr[a.slot])return null;cardId=arr[a.slot];getRefill(g,a.tier,a.slot);
   }else if(a.source==='deck'){
     if(!(g.deck[a.tier]||[]).length)return null;cardId=g.deck[a.tier].pop();
   }else return null;
   pp.reserve.push(cardId);
   if(!addGems(g,id,reserveTake(g),a.returned||{}))return null;
   g.log=playerName(id)+'がカードを予約';
 }else if(a.kind==='buy'){
   let cardId=0;
   if(a.source==='market'){cardId=g.market[a.tier]?.[a.slot];}
   if(a.source==='reserved'){cardId=pp.reserve[a.slot];}
   if(!cardId)return null;
   const card=CARDMAP[cardId],pay=canPay(g,id,card);if(!pay.ok)return null;
   for(const c of ALL){pp.chips[c]-=pay.payment[c];g.supply[c]+=pay.payment[c];}
   pp.cards.push(cardId);
   if(a.source==='market')getRefill(g,a.tier,a.slot);else pp.reserve.splice(a.slot,1);
   g.log=playerName(id)+'がLv.'+card.level+'カードを購入';
 }else return null;
 pp.bank=Math.max(0,pp.bank-bankUsed);
 postMove(s,t);return s;
}
function timeText(ms){return Math.ceil(Math.max(0,ms)/1000)+'秒';}
function gemIcon(c,n,variant='chip'){return `<span class="gem ${variant} ${c}" title="${CNAME[c]}"><span>${n??''}</span></span>`;}
function costs(cost){return COLORS.filter(c=>num(cost[c])>0).map(c=>`<span class="costpill">${gemIcon(c,'','mini')}<b>${cost[c]}</b></span>`).join('')||'<span class="muted">なし</span>';}
function visualArt(card){const hue={white:38,blue:210,green:150,red:350,black:245}[card.color];const v=(card.id*17)%5;
return `<svg class="card-art" viewBox="0 0 140 90" preserveAspectRatio="xMidYMid slice" aria-hidden="true"><defs><linearGradient id="sky${card.id}" x2="0" y2="1"><stop stop-color="hsl(${hue},40%,70%)"/><stop offset="1" stop-color="hsl(${hue},40%,23%)"/></linearGradient></defs><rect width="140" height="90" fill="url(#sky${card.id})"/><circle cx="112" cy="18" r="14" fill="#fff4c9" opacity=".67"/><path d="M0 77 L25 49 L48 64 L76 35 L112 58 L140 43 L140 90 L0 90" fill="#243a49" opacity=".6"/>${v===0?'<path d="M25 80V28H44V80 M44 43L60 28L76 43V80 M76 80V22H94V80" fill="#ede4d1" stroke="#766e68" stroke-width="2"/>':v===1?'<path d="M23 80L38 37H101L116 80Z" fill="#cfbca3" stroke="#6e5b4e" stroke-width="2"/><path d="M55 80V48H84V80" fill="#675649"/>':v===2?'<path d="M20 80V42H118V80Z" fill="#cbb59a" stroke="#6c5f55" stroke-width="2"/><path d="M42 42V23H58V42M80 42V19H98V42" fill="#e2d7bd"/><path d="M62 80V55H77V80" fill="#584d48"/>':v===3?'<path d="M16 81L55 32L87 81Z M60 81L96 44L128 81" fill="#a28e79" stroke="#544d48" stroke-width="2"/><path d="M51 82L61 62L75 82" fill="#2f3037"/>':'<path d="M29 81V28L69 16L109 28V81" fill="#c7bba6" stroke="#625c52" stroke-width="2"/><path d="M49 81V45H88V81" fill="#82776a"/><path d="M24 29H114" stroke="#e7d7a8" stroke-width="5"/>'}</svg>`;}
function cardHtml(id,source,tier,slot,meId){if(!id)return `<div class="card empty"><span>売り切れ</span></div>`;
const c=CARDMAP[id],g=state.game,affordable=g&&meId&&g.p[meId]&&canPay(g,meId,c).ok;
const costTxt=costs(c.cost),isMine=source==='reserved';
return `<button class="card ${c.color} ${affordable?'affordable':''}" data-open-card="1" data-source="${source}" data-tier="${tier||c.level}" data-slot="${slot}" type="button" aria-label="Lv.${c.level} ${c.points}点 ${CNAME[c.color]}ボーナス"><div class="card-top"><span class="bonus">${gemIcon(c.color,'','bonusGem')}</span><b>${c.points?c.points+'点':''}</b></div>${visualArt(c)}<div class="card-cost">${costTxt}</div>${affordable?'<div class="buyable">購入可</div>':''}${isMine?'<div class="reserved-tag">予約</div>':''}</button>`;}
function nobleHtml(nid,available){const n=NOBLEMAP[nid];return `<div class="noble ${available?'noble-available':''}"><div class="noble-top">♛ <b>3点</b></div><div class="noble-cost">${costs(n.cost)}</div></div>`;}
function chipsHTML(gems){return `<div class="chips">${ALL.map(c=>`<div class="chip-unit">${gemIcon(c,num(gems[c]))}<small>${CNAME[c]}</small></div>`).join('')}</div>`;}
function discountsHTML(g,id){const b=bonuses(g,id);return `<div class="discounts">${COLORS.map(c=>`<span>${gemIcon(c,b[c],'small')}</span>`).join('')}</div>`;}
function bankUI(g,id){const val=id===activeId(g)&&g.phase==='turn'?currentBank(g,now()):g.p[id].bank;return timeText(val);}
function panelHTML(g,id,detail){const me=id===owner(),pp=g.p[id],name=escapeHtml(playerName(id)),isPlaying=id===activeId(g),pts=vp(g,id);
return `<section class="player ${isPlaying?'playing':''}"><div class="player-head"><div><strong>${name}${me?'（自分）':''}</strong>${isPlaying?'<span class="playing-mark">手番中</span>':''}</div><div class="score">${pts}<small> / 15点</small></div></div><div class="player-meta"><span>購入 ${pp.cards.length}枚</span><span>貴族 ${pp.nobles.length}枚</span><span>予約 ${pp.reserve.length}/3</span><span class="bank-el" data-bank-id="${escapeHtml(id)}">持ち時間 ${bankUI(g,id)}</span></div>${!detail||(!me&&g.turnOrder.length>2)?`<button class="smallbtn" data-expand-player="${escapeHtml(id)}">${detail?'詳細を閉じる':'詳細を見る'}</button>`:''}${detail?`<div class="player-detail"><div class="tiny-title">所持宝石</div>${chipsHTML(pp.chips)}<div class="tiny-title">購入割引</div>${discountsHTML(g,id)}<div class="tiny-title">購入済みカード ${pp.cards.length}枚</div><div class="owned">${COLORS.map(c=>`<span class="owned-color ${c}">${CNAME[c]} ${pp.cards.filter(cid=>CARDMAP[cid].color===c).length}</span>`).join('')}</div><div class="tiny-title">貴族</div><div class="mini-nobles">${pp.nobles.length?pp.nobles.map(nid=>nobleHtml(nid,false)).join(''):'まだ獲得していません'}</div>${me?`<div class="tiny-title">予約カード（本人のみ）</div><div class="reserved-row">${pp.reserve.map((cid,slot)=>cardHtml(cid,'reserved',CARDMAP[cid].level,slot,id)).join('')}${pp.reserve.length===0?'<span class="muted">予約なし</span>':''}</div>`:''}</div>`:''}</section>`;}
function renderMenu(){view='menu';$('app').innerHTML=`<div class="menu-layout"><div class="hero"><span class="hero-emblem">✦</span><h1>GEM COURT</h1><p>宝石と発展カードの戦略ボードゲーム</p><p class="smallnote">原作ベース・2〜4人／20秒＋持ち時間180秒</p></div><div class="menu-panel"><label>プレイヤー名<input id="nameInput" maxlength="18" placeholder="プレイヤー名" value="${escapeHtml(clientName)}"></label><div class="menu-buttons"><button class="primary" data-act="local">この端末でテスト対戦</button><button data-act="online">オンライン対戦</button></div><p class="footnote">テスト対戦は1台で交代して遊べます。オンライン対戦は共通のFirebaseに自動接続します。</p></div></div>`;}
function renderOnlineStart(){view='onlineStart';$('app').innerHTML=`<div class="wrap online-start"><h2>オンライン対戦</h2><p class="muted">ルームを作るか、6文字のコードで参加してください。</p><div class="two-cols"><section class="pane"><h3>ルームを作成</h3><button class="primary" data-act="createRoom">新しいルームを作成</button></section><section class="pane"><h3>ルームに参加</h3><input id="joinCode" maxlength="6" placeholder="例：A7K2XM" autocapitalize="characters"><button data-act="joinRoom">参加する</button></section></div><button class="ghost" data-act="menu">タイトルへ戻る</button></div>`;}
function renderLobby(){view='lobby';const host=state.host===owner();const p=state.players.find(p=>p.id===owner()),allReady=state.players.length>=2&&state.players.every(p=>p.ready);
 $('app').innerHTML=`<div class="wrap lobby"><div class="toprow"><h2>対戦ルーム</h2><span class="room-code" data-act="copyCode" title="押してコピー">${escapeHtml(roomCode||'ローカル')}</span></div><p class="muted">2〜4人参加・全員準備完了後にホストが開始します</p><div class="pane"><h3>参加者 ${state.players.length} / 4</h3>${state.players.map(pl=>`<div class="lobby-person"><span>${escapeHtml(pl.name)} ${pl.id===state.host?'<b>♛ ホスト</b>':''}</span><span>${pl.ready?'<span class="ok">✓ 準備完了</span>':'準備中'}</span>${host&&pl.id!==owner()?`<button class="smallbtn" data-act="kick" data-target="${escapeHtml(pl.id)}">退出させる</button>`:''}</div>`).join('')}</div><div class="row actions"><button class="primary" data-act="toggleReady">${p?.ready?'準備を取り消す':'準備完了'}</button>${host?`<button ${allReady?'':'disabled'} data-act="start">ゲーム開始</button>`:''}<button class="danger" data-act="leave">${host?'ルームを解散':'退出'}</button></div><p class="smallnote">${activeMode==='local'?'ローカルのテスト対戦は2人で開始します。':'対戦中に切断した場合、同じブラウザから復帰できます。'}</p></div>`;
}
function renderResults(){view='results';const last=(state.history||[]).slice(-1)[0];if(!last){renderLobby();return;}
const finished=state.players.find(p=>p.id===owner())?.view==='lobby';
$('app').innerHTML=`<div class="wrap results"><div class="hero small"><span class="hero-emblem">♛</span><h1>対戦終了</h1><p>第${(state.history||[]).length}試合</p></div><div class="pane"><table class="results-table"><thead><tr><th>順位</th><th>プレイヤー</th><th>得点</th><th>カード</th><th>貴族</th><th>持ち時間</th></tr></thead><tbody>${last.results.map(r=>`<tr><td>${r.rank}位</td><td>${escapeHtml(r.name)}</td><td><b>${r.points}</b></td><td>${r.cards}</td><td>${r.nobles}</td><td>${timeText(r.bank)}</td></tr>`).join('')}</tbody></table><h3>ルーム内対戦記録</h3><div class="history">${(state.history||[]).map((h,i)=>`<p>第${i+1}試合：${h.results.filter(r=>r.rank===1).map(r=>escapeHtml(r.name)).join('・')}（${h.results.filter(r=>r.rank===1)[0]?.points||0}点）</p>`).join('')}</div></div><div class="row actions">${activeMode==='local'?'<button class="primary" data-act="local">もう一度テスト対戦</button>':''}${finished?'<p class="ok">待機画面に戻る準備ができています。ほかの参加者を待っています。</p>':`<button class="primary" data-act="backLobby">待機画面に戻る</button>`}${state.host===owner()?'<button class="danger" data-act="leave">ルームを解散</button>':''}</div></div>`;
}
function renderGame(){view='game';const g=state.game,id=owner(),actor=activeId(g),myTurn=id===actor&&g.phase==='turn';const me=g.p[id];
 if(!me){$('app').innerHTML='<div class="wrap">自分のプレイヤーデータがありません。</div>';return;}
 $('app').innerHTML=`<div class="game-layout"><header class="game-head"><div><div class="brand">✦ GEM COURT</div><div class="subbrand">${escapeHtml(roomCode||'ローカル対戦')} · ${g.turnOrder.length}人 · 手番${g.completed+1}</div></div><div class="clockbox"><span>${escapeHtml(playerName(actor))}のターン</span><strong id="turnClock">20秒</strong><small id="turnMode">基本時間</small></div><button class="ghost menu-quit" data-act="leave">退出</button></header><main class="game-main"><div class="board"><section class="board-panel nobles-panel"><div class="section-title"><h3>貴族</h3><span>条件を満たすと獲得</span></div><div class="nobles-list">${(g.nobles||[]).map(nid=>nobleHtml(nid,candidates(g,id).includes(nid))).join('')||'<span class="muted">貴族なし</span>'}</div></section>${[3,2,1].map(tier=>`<section class="board-panel"><div class="section-title"><h3>Lv.${tier} 発展カード</h3><button class="deck-button" ${!myTurn||!((g.deck[tier]||[]).length)||me.reserve.length>=3?'disabled':''} data-open-deck="${tier}">山札予約 · 残り${(g.deck[tier]||[]).length}枚</button></div><div class="card-grid">${(g.market[tier]||[]).map((cid,slot)=>cardHtml(cid,'market',tier,slot,id)).join('')}</div></section>`).join('')}<section class="board-panel take-panel"><div class="section-title"><h3>宝石の取得</h3><span>現在の所持数：${total(me.chips)}/10個</span></div><div class="supply">${ALL.map(c=>`<div class="supply-item"><button class="token-pick ${selected.includes(c)?'picked':''}" ${c==='gold'||!myTurn||g.supply[c]===0?'disabled':''} data-select-gem="${c}">${gemIcon(c,num(g.supply[c]))}</button><small>${CNAME[c]}</small></div>`).join('')}</div><div class="take-controls"><div class="tabs"><button class="${takeMode==='diff'?'active':''}" data-take-mode="diff">異なる色（最大3個）</button><button class="${takeMode==='same'?'active':''}" data-take-mode="same">同色2個</button></div><div id="selectionHelp" class="muted">${takeMode==='same'?'同色2個は在庫4個以上必要です':'色を選択してください'}</div><button class="primary" data-act="take" ${myTurn&&selected.length?'':'disabled'}>選んだ宝石を取得する</button></div></section></div><aside class="side-panel"><div class="side-title">プレイヤー情報 <span>持ち時間は全員公開</span></div>${g.turnOrder.map(pid=>panelHTML(g,pid,pid===id||g.turnOrder.length===2||expandedPlayerId===pid)).join('')}<div class="statuslog">${escapeHtml(g.log||'')}</div></aside></main></div>`;
 updateTimers();
 if(g.phase==='noble'&&id===actor)openNobleModal();
}
function render(){if(!state){renderMenu();return;}if(state.status==='lobby')renderLobby();else if(state.status==='results')renderResults();else if(state.status==='playing')renderGame();}
function updateTimers(){const g=state?.game;if(!g||state.status!=='playing')return;
 const t=now(),turn=$('turnClock'),mode=$('turnMode');if(turn){let elapsed=Math.max(0,t-g.turnStart),base=Math.max(0,basicTurn-elapsed),bank=currentBank(g,t);
 if(g.phase==='noble'){turn.textContent=timeText(Math.max(0,10000-(t-g.nobleStart)));if(mode)mode.textContent='貴族選択';}
 else{turn.textContent=timeText(base>0?base:bank);turn.classList.toggle('urgent',base<=0||base<5000);if(mode)mode.textContent=base>0?'基本時間':'持ち時間を消費中';}
 }
 document.querySelectorAll('.bank-el').forEach(e=>{const pid=e.dataset.bankId;if(!g.p[pid])return;e.textContent='持ち時間 '+bankUI(g,pid);});
 const mTime=$('modalNobleTime');if(mTime&&g.phase==='noble')mTime.textContent=timeText(Math.max(0,10000-(t-g.nobleStart)));
}
function closeModal(){modal=null;$('modal').innerHTML='';$('modal').classList.add('hidden');}
function showModal(inner){$('modal').innerHTML=`<div class="dialog">${inner}</div>`;$('modal').classList.remove('hidden');}
function openNobleModal(){const g=state.game;if(g.phase!=='noble'||owner()!==activeId(g))return;
 if(modal?.type==='noble'&&modal.seq===g.seq)return;
 modal={type:'noble',seq:g.seq};showModal(`<div class="dialog-head"><h3>貴族を1枚選択</h3><strong id="modalNobleTime">10秒</strong></div><p class="muted">条件を満たした貴族から1枚獲得できます。</p><div class="noble-options">${g.nobleCandidates.map(nid=>`<button data-pick-noble="${nid}">${nobleHtml(nid,true)}</button>`).join('')}</div>`);
}
function findCardModal(source,tier,slot){const g=state.game;const cid=source==='market'?g.market[tier]?.[slot]:g.p[owner()].reserve[slot];return cid?CARDMAP[cid]:null;}
function openCardModal(source,tier,slot){if(state.status!=='playing')return;const g=state.game,card=findCardModal(source,tier,slot);if(!card)return;
 const canAct=activeId(g)===owner()&&g.phase==='turn';const pay=canPay(g,owner(),card),reserveOK=canAct&&source==='market'&&g.p[owner()].reserve.length<3;
 modal={type:'card',source,tier,slot};showModal(`<div class="dialog-head"><h3>Lv.${card.level} カード</h3><button class="iconbtn" data-act="closeModal">×</button></div><div class="modal-card">${cardHtml(card.id,source,tier,slot,owner())}</div><p>勝利点 <b>${card.points}</b>点 · 購入割引 <b>${CNAME[card.color]}</b></p><div class="bigcost">必要な宝石：${costs(card.cost)}</div><p class="muted">${pay.ok?'現在購入できます。':'所持宝石が不足しています。'}</p><div class="row actions"><button class="primary" ${!canAct||!pay.ok?'disabled':''} data-choose="buy">購入する</button>${source==='market'?`<button ${!reserveOK?'disabled':''} data-choose="reserve">予約する</button>`:''}<button data-act="closeModal">戻る</button></div>`);
}
function openDeckModal(tier){if(state.status!=='playing')return;modal={type:'deck',tier};showModal(`<div class="dialog-head"><h3>Lv.${tier}の山札から予約</h3><button class="iconbtn" data-act="closeModal">×</button></div><p>山札の一番上に相当するカードを1枚、内容を見ずに予約します。</p><p class="muted">相手には内容が表示されません。予約上限は3枚です。</p><div class="row actions"><button class="primary" data-choose="reserveDeck">予約を確認</button><button data-act="closeModal">戻る</button></div>`);}
function proposalReturn(a,extra){const g=state.game,p=g.p[owner()],res=emptyGems();
 const resulting=emptyGems();for(const c of ALL)resulting[c]=num(p.chips[c])+num(extra[c]);
 const requireBack=Math.max(0,total(resulting)-10);
 modal={type:'confirm',action:a,extra,resulting,returned:res,need:requireBack};
 renderConfirm();
}
function renderConfirm(){const m=modal;if(!m||m.type!=='confirm')return;
 const left=m.need-total(m.returned),isReturn=m.need>0;const title=m.action.kind==='buy'?'カードを購入しますか？':m.action.kind==='reserve'?'カードを予約しますか？':'宝石を取得しますか？';
 let message=m.action.kind==='buy'?'購入費用は自動的に支払われます。':m.action.kind==='reserve'?'金トークンが残っていれば1個獲得します。':'この色の宝石を取得します。';
 showModal(`<div class="dialog-head"><h3>${title}</h3><button class="iconbtn" data-act="closeModal">×</button></div><p>${message}</p>${isReturn?`<div class="return-panel"><h4>所持上限のため${m.need}個返却してください</h4><p class="muted">返却する色をタップして選びます。金も返却可能です。</p><div class="return-grid">${ALL.map(c=>`<button data-return-gem="${c}" ${num(m.returned[c])>=num(m.resulting[c])?'disabled':''}>${gemIcon(c,num(m.returned[c]),'small')}<small>${CNAME[c]} 所持${m.resulting[c]}</small></button>`).join('')}</div><div class="row"><span>あと <b>${left}</b> 個返却</span><button data-act="resetReturn">選び直す</button></div></div>`:''}<div class="row actions"><button class="primary" data-act="commit" ${left!==0?'disabled':''}>確定する</button><button data-act="closeModal">キャンセル</button></div>`);
}
function startConfirmation(kind){if(!modal)return;const src=modal.type==='card'?modal.source:modal.type==='deck'?'deck':'';
 if(kind==='buy'||kind==='reserve'){
 const a={kind,source:src,tier:modal.tier,slot:modal.slot};proposalReturn(a,kind==='reserve'?reserveTake(state.game):emptyGems());return;
 }
 if(kind==='reserveDeck'){proposalReturn({kind:'reserve',source:'deck',tier:modal.tier},reserveTake(state.game));}
}
function checkTake(){const g=state.game;if(!selected.length)return fail('宝石の色を選択してください');let a;
 if(takeMode==='same'){if(selected.length!==1)return fail('同色2個では1色を選択してください');a={kind:'take2',color:selected[0]};}
 else a={kind:'take',colors:[...selected]};
 if(!isAllowedTake(g,a))return fail('この宝石は取得できません');
 const extra=emptyGems();for(const c of a.kind==='take2'?[a.color,a.color]:a.colors)extra[c]++;
 proposalReturn(a,extra);
}
async function saveAction(a){if(isBusy)return;isBusy=true;const t=now(),origSeq=state?.game?.seq;
 if(a.kind==='take'||a.kind==='take2'||a.kind==='reserve'||a.kind==='buy'||a.kind==='noble')a.expected=origSeq;
 try{
  if(activeMode==='local'){
    const next=apply(state,owner(),a,t);if(!next)throw new Error('この操作は現在実行できません');state=next;selected=[];closeModal();render();return;
  }
  if(!network||!roomCode)throw new Error('Firebaseに接続していません');
  let valid=false;
  const r=await network.ref('rooms/'+roomCode+'/state').transaction(cur=>{
   if(!cur)return;
   const next=apply(cur,activeUser,a,t);
   if(!next)return;
   valid=true;return next;
  },undefined,false);
  if(!r.committed)throw new Error(valid?'更新が競合しました。もう一度お試しください。':'現在の状態では操作できません');
  selected=[];closeModal();
 }catch(e){fail(e.message);}finally{isBusy=false;}
}
function localStart(){activeMode='local';roomCode='';activeUser='local-1';state=makeLobby('local-1',clientName||'プレイヤー1');state.players.push({id:'local-2',name:'プレイヤー2',ready:true,view:'lobby'});state.players[0].ready=true;state=apply(state,'local-1',{kind:'start'},now());render();}
function resetNetwork(){if(network&&roomCode){network.ref('rooms/'+roomCode+'/state').off();network.ref('rooms/'+roomCode+'/presence').off();if(activeUser)network.ref('rooms/'+roomCode+'/presence/'+activeUser).onDisconnect().cancel().catch(()=>{});}presence={};network=null;roomCode='';state=null;activeMode='';closeModal();}
async function initFirebase(){if(!cfgReady())throw new Error('Firebaseへの接続設定が公開側に登録されていません。管理者にご確認ください');if(typeof firebase==='undefined')throw new Error('Firebase SDKを読み込めませんでした。インターネット接続を確認してください');
 const v=cfg();if(!firebase.apps.length)firebase.initializeApp(v);const auth=firebase.auth();await auth.setPersistence(firebase.auth.Auth.Persistence.LOCAL);const u=auth.currentUser|| (await auth.signInAnonymously()).user;activeUser=u.uid;network=firebase.database();network.ref('.info/serverTimeOffset').on('value',sn=>{serverOffset=num(sn.val());});}
function genCode(){const chars='ABCDEFGHJKLMNPQRSTUVWXYZ23456789';return Array.from({length:6},()=>chars[rng(chars.length)]).join('');}
async function onlineMode(){try{await initFirebase();activeMode='online';renderOnlineStart();}catch(e){fail(e.message);}}
async function attachRoom(code){roomCode=code;activeMode='online';network.ref('rooms/'+code+'/state').on('value',snap=>{const next=snap.val();if(!next){showToast('ルームが解散・削除されました');resetNetwork();renderMenu();return;}
 if(next.players&&!next.players.some(p=>p.id===activeUser)){showToast('ルームから退出しました');resetNetwork();renderMenu();return;}
 normalizeState(next);const signature=JSON.stringify([next.status,next.game?.seq,next.players?.map(p=>[p.id,p.ready,p.view]),next.history?.length,next.lastChange]);const changed=signature!==seenUpdate;state=next;if(changed){seenUpdate=signature;closeModal();render();}
 },e=>fail('ルームの読み取りエラー: '+e.message));
 const presenceRef=network.ref('rooms/'+code+'/presence/'+activeUser);
 try{await presenceRef.onDisconnect().set({online:false,at:firebase.database.ServerValue.TIMESTAMP});await presenceRef.set({online:true,at:firebase.database.ServerValue.TIMESTAMP});}catch(e){fail('在席状態の登録に失敗: '+e.message);}
 network.ref('rooms/'+code+'/presence').on('value',sn=>{presence=sn.val()||{};});
}
async function createRoom(){if(isBusy)return;isBusy=true;try{
 for(let i=0;i<10;i++){
  const code=genCode(),ref=network.ref('rooms/'+code+'/state');const res=await ref.transaction(cur=>cur===null?makeLobby(activeUser,clientName||'ホスト'):undefined,undefined,false);
  if(res.committed){await attachRoom(code);return;}
 }
 throw new Error('ルームを作れませんでした。もう一度お試しください');
 }catch(e){fail(e.message);}finally{isBusy=false;}}
async function joinRoom(){if(isBusy)return;isBusy=true;try{
 const code=String($('joinCode')?.value||'').trim().toUpperCase();
 if(!/^[A-HJ-NP-Z2-9]{6}$/.test(code))throw new Error('6文字のルームコードを入力してください');
 const ref=network.ref('rooms/'+code+'/state');
 const existing=normalizeState((await ref.once('value')).val());
 if(!existing)throw new Error('ルームが見つかりません');
 if(!existing.players.some(p=>p.id===activeUser)){
  if(existing.status!=='lobby')throw new Error('このルームは対戦開始済みです');
  if(existing.players.length>=4)throw new Error('このルームは満員です');
  // Firebase transactions may first receive null even for a room which exists
  // on the server. Use the snapshot already read above only for that first pass.
  let firstPass=true;
  const action={kind:'join',name:clientName||'ゲスト'};
  const result=await ref.transaction(cur=>{
   if(cur===null && firstPass)cur=existing;
   firstPass=false;
   return apply(cur,activeUser,action,now())||undefined;
  },undefined,false);
  if(!result.committed){
   const latest=normalizeState((await ref.once('value')).val());
   if(!latest)throw new Error('ルームが解散されました');
   if(latest.status!=='lobby')throw new Error('このルームは対戦開始済みです');
   if(latest.players.length>=4)throw new Error('このルームは満員です');
   if(!latest.players.some(p=>p.id===activeUser))throw new Error('参加処理を完了できませんでした。再度お試しください');
  }
 }
 await attachRoom(code);
 }catch(e){fail('ルーム参加エラー: '+(e?.message||String(e)));}finally{isBusy=false;}}
async function leave(){if(!state){resetNetwork();renderMenu();return;}
 if(activeMode==='local'){state=null;activeMode='';renderMenu();return;}
 try{
 const code=roomCode,host=state.host===activeUser;
 if(host){if(!confirm('ルームを解散します。参加者全員の対戦も終了します。よろしいですか？'))return;
  await network.ref('rooms/'+code+'/presence/'+activeUser).onDisconnect().cancel();await network.ref('rooms/'+code).remove();resetNetwork();renderMenu();}
 else{await network.ref('rooms/'+code+'/state').transaction(cur=>apply(cur,activeUser,{kind:'leave'},now())||undefined,undefined,false);try{await network.ref('rooms/'+code+'/presence/'+activeUser).onDisconnect().cancel();await network.ref('rooms/'+code+'/presence/'+activeUser).remove();}catch{}resetNetwork();renderMenu();}
 }catch(e){fail(e.message);}
}
async function backLobby(){await saveAction({kind:'returnLobby'});}
function localReenter(){if(activeMode==='local')render();}
// Timeouts and disconnect cleanup are driven by connected clients. A separate scheduled backend is needed for guaranteed cleanup with zero clients online.
async function doMaintenance(){if(isBusy||!state)return;
 if(activeMode==='local'&&state.status==='playing'){const g=state.game,t=now();if(g.phase==='turn'&&expired(g,t)||g.phase==='noble'&&t>=g.nobleStart+10000){const next=apply(state,owner(),{kind:'timeout'},t);if(next){state=next;closeModal();render();}}return;}
 if(activeMode!=='online'||!network)return;
 const g=state.game,t=now();
 if(state.status==='playing'&&g){if(g.phase==='turn'&&expired(g,t)||g.phase==='noble'&&t>=g.nobleStart+10000){await saveAction({kind:'timeout'});}return;}
 if(state.status==='lobby'||state.status==='results'){
  const hostPresence=presence[state.host];
  if(hostPresence&&hostPresence.online===false&&t-num(hostPresence.at)>5*60*1000){try{await network.ref('rooms/'+roomCode).remove();}catch{}}
  for(const pl of state.players){if(pl.id===state.host)continue;
   const pr=presence[pl.id];if(pr&&pr.online===false&&t-num(pr.at)>3*60*1000){await saveAction({kind:'kick',target:pl.id});break;}
  }
 }
}
function showError(e){fail(e?.message||String(e));}
function setClientName(){clientName=String($('nameInput')?.value||'').trim().slice(0,18)||'プレイヤー';localStorage.setItem('gem_name',clientName);}
async function handleClick(e){const el=e.target.closest('button, [data-act]');if(!el||el.disabled)return;const act=el.dataset.act;
 try{
 if(act==='menu'){resetNetwork();renderMenu();return;}
 if(el.dataset.expandPlayer){expandedPlayerId=expandedPlayerId===el.dataset.expandPlayer?'':el.dataset.expandPlayer;renderGame();return;}
 if(act==='local'){setClientName();localStart();return;}
 if(act==='online'){setClientName();await onlineMode();return;}
 if(act==='createRoom'){await createRoom();return;}
 if(act==='joinRoom'){await joinRoom();return;}
 if(act==='copyCode'){try{await navigator.clipboard.writeText(roomCode);showToast('ルームコードをコピーしました');}catch{showToast(roomCode);}return;}
 if(act==='toggleReady'){let pl=state.players.find(p=>p.id===owner());await saveAction({kind:'ready',value:!pl?.ready});return;}
 if(act==='start'){await saveAction({kind:'start'});return;}
 if(act==='kick'){if(confirm('このプレイヤーをルームから退出させますか？'))await saveAction({kind:'kick',target:el.dataset.target});return;}
 if(act==='leave'){await leave();return;}
 if(act==='backLobby'){await backLobby();return;}
 if(act==='closeModal'){closeModal();return;}
 if(act==='take'){checkTake();return;}
 if(act==='resetReturn'){if(modal?.type==='confirm'){modal.returned=emptyGems();renderConfirm();}return;}
 if(act==='commit'){if(modal?.type==='confirm'){const a={...modal.action,returned:modal.returned};await saveAction(a);}return;}
 if(el.dataset.pickNoble){await saveAction({kind:'noble',id:Number(el.dataset.pickNoble)});return;}
 if(el.dataset.choose){startConfirmation(el.dataset.choose);return;}
 if(el.dataset.openCard){openCardModal(el.dataset.source,Number(el.dataset.tier),Number(el.dataset.slot));return;}
 if(el.dataset.openDeck){openDeckModal(Number(el.dataset.openDeck));return;}
 if(el.dataset.takeMode){takeMode=el.dataset.takeMode;selected=[];renderGame();return;}
 if(el.dataset.selectGem){const c=el.dataset.selectGem;if(!COLORS.includes(c))return;
  if(takeMode==='same')selected=[c];else selected=selected.includes(c)?selected.filter(x=>x!==c):selected.length<3?[...selected,c]:selected;renderGame();return;
 }
 if(el.dataset.returnGem&&modal?.type==='confirm'){const c=el.dataset.returnGem;if(total(modal.returned)>=modal.need||modal.returned[c]>=modal.resulting[c])return;modal.returned[c]++;renderConfirm();return;}
 }catch(error){showError(error);}}
document.addEventListener('click',handleClick);
document.addEventListener('keydown',e=>{if(e.key==='Escape'&&modal?.type!=='noble')closeModal();});
renderMenu();
uiTimer=setInterval(()=>{updateTimers();doMaintenance();},600);
