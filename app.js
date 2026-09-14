const DIFFICULTY = {
  easy:   {avg:3.8, max:5, min:1, label:'Easy'},
  medium: {avg:3.0, max:4, min:1, label:'Medium'},
  hard:   {avg:2.4, max:4, min:1, label:'Hard'},
  expert: {avg:2.0, max:3, min:2, label:'Expert'}
};
// Allowed (cageSize → Set of valid sums) derived from sum.csv columns 1-2
// sum.csv defines valid sums for distinct 1-9 cages; e.g. size 3 → 6..24 (25 is not listed and is invalid)
// Fallback embedded copy; will be overwritten at runtime by fetching sum.csv if available
const ALLOWED_SUMS_FALLBACK = {
  2: new Set([3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]),
  3: new Set([6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]),
  4: new Set([10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]),
  5: new Set([15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]),
  // size 1 not in CSV: every 1..9 is valid (single-cell cage shows its own value)
  1: new Set([1,2,3,4,5,6,7,8,9]),
};

function fetchText(url){
  // safe fallback for environments without fetch
  if(typeof fetch !== 'function') return Promise.reject(new Error('no fetch'));
  return fetch(url).then(r=>r.ok?r.text():Promise.reject(new Error('fetch failed')));
}
let ALLOWED_SUMS = ALLOWED_SUMS_FALLBACK;
// try to load authoritative data from sum.csv (columns 1=Cage Size, 2=Sum)
fetchText('sum.csv').then(text=>{
  const lines=text.trim().split(/\r?\n/);
  const map={};
  for(let i=1;i<lines.length;i++){
    const line=lines[i].trim(); if(!line) continue;
    // CSV: size,sum,... — need only first two columns
    const parts=line.split(',');
    const k=parseInt(parts[0],10), s=parseInt(parts[1],10);
    if(isNaN(k)||isNaN(s)) continue;
    if(!map[k]) map[k]=new Set();
    map[k].add(s);
  }
  if(Object.keys(map).length){
    // keep size 1 fallback if CSV has no 1s
    if(!map[1]) map[1]=ALLOWED_SUMS_FALLBACK[1];
    ALLOWED_SUMS=map;
  }
  // we reuse fetchText wrapper below so tests/old Node don't hard-fail
}).catch(()=>{ /* keep fallback */ });

let difficulty='medium';
let solution, cages, cageMap, cageSums;
let board, notes, given;
let selected=null;
let isNoteMode=false;
let autoCheck=true;
let lightningMode=true;
let lightningDigit=null;
let mistakes=0;

// Lightning helpers — armed digit highlights everywhere and drives grid taps
function updateLightningUI(){
  const sw=document.getElementById('lightningSwitch');
  if(sw) sw.classList.toggle('active', lightningMode);
  document.querySelectorAll('.num').forEach(b=>{
    const n=parseInt(b.dataset.n,10);
    b.classList.toggle('lightning-active', !!lightningMode && lightningDigit===n);
  });
}
function setLightningDigit(n){
  if(!lightningMode) return false;
  lightningDigit = (lightningDigit===n) ? null : n;
  updateLightningUI();
  render();
  return true;
}
function clearLightningDigit(){
  lightningDigit=null;
  updateLightningUI();
  render();
}
let timerSec=0, timerId=null, paused=false;
let gameOver=false;
let history=[];
let cageCellsSet=[];

function shuffle(a){for(let i=a.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));[a[i],a[j]]=[a[j],a[i]]}return a}
function generateSolution(){
  const g=Array(9).fill(0).map(()=>Array(9).fill(0));
  function valid(r,c,n){for(let i=0;i<9;i++)if(g[r][i]===n||g[i][c]===n) return false; const br=Math.floor(r/3)*3, bc=Math.floor(c/3)*3; for(let rr=br;rr<br+3;rr++)for(let cc=bc;cc<bc+3;cc++)if(g[rr][cc]===n) return false; return true}
  function solve(idx){
    if(idx===81) return true;
    const r=Math.floor(idx/9), c=idx%9;
    if(g[r][c]!==0) return solve(idx+1);
    const nums=shuffle([1,2,3,4,5,6,7,8,9].slice());
    for(const n of nums){ if(valid(r,c,n)){g[r][c]=n; if(solve(idx+1)) return true; g[r][c]=0} }
    return false;
  }
  // fill diagonal boxes for speed
  for(let b=0;b<9;b+=3){ const nums=shuffle([1,2,3,4,5,6,7,8,9].slice()); let k=0; for(let r=b;r<b+3;r++)for(let c=b;c<b+3;c++) g[r][c]=nums[k++]}
  // clear and solve rest? Actually solving from current partially filled will work faster; reset non-diagonal?
  // We'll just run solver on empty with heuristics — but above diagonal fill+ solver is fast
  // Clear non-diagonal to avoid conflict: keep diagonal boxes, solve rest
  // Our solver handles filled cells, so proceed
  // To ensure full solve, we continue solving sequentially
  solve(0);
  return g;
}

function generateCages(sol, diffKey){
  const cfg=DIFFICULTY[diffKey];
  const used=Array(9).fill(0).map(()=>Array(9).fill(false));
  const cages=[];
  const dirs=[[1,0],[-1,0],[0,1],[0,-1]];
  const minSize = cfg.min || 1;
  let id=0;
  const cellsList=[];
  for(let r=0;r<9;r++)for(let c=0;c<9;c++) cellsList.push([r,c]);
  shuffle(cellsList);

  function cageValues(cells){ return new Set(cells.map(([r,c])=> sol[r][c])); }
  function hasDuplicate(cells){
    const s=new Set(); for(const [r,c] of cells){ const v=sol[r][c]; if(s.has(v)) return true; s.add(v); }
    return false;
  }
  function sumAllowed(k, sum){
    const set=ALLOWED_SUMS[k] || ALLOWED_SUMS_FALLBACK[k];
    if(!set) return true; // unknown size — don't block generation
    return set.has(sum);
  }

  for(const [sr,sc] of cellsList){
    if(used[sr][sc]) continue;
    let target;
    if(diffKey==='expert'){
      // Expert: 50% cages size 2, remainder randomized (2–3)
      const r=Math.random();
      if(r < 0.50) target=2;
      else target = cfg.min + Math.floor(Math.random() * (cfg.max - cfg.min + 1));
    } else {
      target = Math.max(minSize, Math.min(cfg.max, Math.round(cfg.avg + (Math.random()*2-1)*1.2 )));
      if(minSize === 1 && Math.random()<0.08) target=1;
    }
    // Killer rule: no repeat inside a cage, so cage must contain distinct solution digits.
    // A cage of k distinct digits 1-9 has feasible sum interval:
    //   min(k)=1+2+...+k, max(k)=9+8+...+(10-k).  E.g. k=3 => 6..24, so 25 is impossible.
    // We therefore filter growth candidates that would introduce a duplicate.
    const cageCells=[[sr,sc]];
    let cageVals=new Set([sol[sr][sc]]);
    used[sr][sc]=true;
    let frontier=[[sr,sc]];
    while(cageCells.length < target){
      const candidates=[];
      for(const [r,c] of frontier){
        for(const [dr,dc] of dirs){
          const nr=r+dr,nc=c+dc;
          if(nr>=0&&nr<9&&nc>=0&&nc<9&&!used[nr][nc] && !cageVals.has(sol[nr][nc])) candidates.push([nr,nc]);
        }
      }
      if(!candidates.length) break;
      shuffle(candidates);
      const pick=candidates[0];
      used[pick[0]][pick[1]]=true;
      cageCells.push(pick);
      cageVals.add(sol[pick[0]][pick[1]]);
      frontier.push(pick);
      if(cageCells.length>=7) break;
    }
    // compute sum (by construction distinct, so sum is always in feasible interval — e.g. 3 cells max 9+8+7=24)
    let sum=0; for(const [r,c] of cageCells) sum+=sol[r][c];
    cages.push({id:String(id++), cells:cageCells, sum});
  }
  // fix-up pass: Expert must have no single-cell cages — merge each 1-cell with a neighbor, preserving distinctness and sum feasibility
  const needFix = minSize > 1;
  if(needFix){
    let i = 0;
    while(i < cages.length){
      if(cages[i].cells.length >= minSize){ i++; continue; }
      const [r0,c0] = cages[i].cells[0];
      const neighborIdxs = new Set();
      for(const [dr,dc] of dirs){
        const nr=r0+dr, nc=c0+dc;
        if(nr<0||nr>=9||nc<0||nc>=9) continue;
        const ni = cages.findIndex((cg, idx2) => idx2 !== i && cg.cells.some(([rr,cc]) => rr===nr && cc===nc));
        if(ni !== -1) neighborIdxs.add(ni);
      }
      // prefer neighbor that keeps distinctness and keeps the resulting sum allowed by sum.csv
      let best = -1, bestScore = Infinity;
      for(const ni of neighborIdxs){
        const combined=[...cages[ni].cells, ...cages[i].cells];
        if(hasDuplicate(combined)) continue;
        const k=combined.length;
        const sum=combined.reduce((a,[rr,cc])=>a+sol[rr][cc],0);
        if(!sumAllowed(k, sum)) continue;
        const merged = combined.length;
        const over = merged > cfg.max ? 100 + merged : merged;
        if(over < bestScore){ bestScore = over; best = ni; }
      }
      if(best === -1){
        // no sum.csv-preserving neighbor — try any distinct neighbor (fallback)
        for(const ni of neighborIdxs){
          const combined=[...cages[ni].cells, ...cages[i].cells];
          if(hasDuplicate(combined)) continue;
          const merged = combined.length;
          const over = merged > cfg.max ? 100 + merged : merged;
          if(over < bestScore){ bestScore = over; best = ni; }
        }
        if(best === -1){
          // still none — try any neighbor (last resort, will be caught by final retry)
          for(const ni of neighborIdxs){
            const merged = cages[ni].cells.length + cages[i].cells.length;
            const over = merged > cfg.max ? 100 + merged : merged;
            if(over < bestScore){ bestScore = over; best = ni; }
          }
          if(best === -1){ i++; continue; }
        }
      }
      cages[best].cells.push(...cages[i].cells);
      let newSum=0; for(const [rr,cc] of cages[best].cells) newSum+=sol[rr][cc];
      cages[best].sum = newSum;
      cages.splice(i, 1);
    }
  }
  // final validation against sum.csv: every cage sum must be listed for its size (col1 × col2)
  // e.g. size 3 sum 25 is not in CSV (valid 6..24) → invalid, triggers retry
  function feasibleRange(k){ // distinct 1-9 (fallback if CSV incomplete)
    let mn=0,mx=0; for(let i=1;i<=k;i++) mn+=i; for(let i=0;i<k;i++) mx+=(9-i); return [mn,mx];
  }
  const bad = cages.some(cg=>{
    if(hasDuplicate(cg.cells)) return true;
    if(!sumAllowed(cg.cells.length, cg.sum)) return true;
    const [mn,mx]=feasibleRange(cg.cells.length);
    if(cg.sum < mn || cg.sum > mx) return true;
    return false;
  });
  if(bad){
    return generateCages(sol, diffKey);
  }
  return cages;
}

function buildMaps(){
  cageMap=Array(9).fill(0).map(()=>Array(9).fill(-1));
  cageSums={};
  cages.forEach((cg,idx)=>{ cageSums[idx]=cg.sum; cg.cells.forEach(([r,c])=> cageMap[r][c]=idx); });
}

function showGameOver(){
  gameOver=true;
  clearInterval(timerId);
  paused=true;
  const el=document.getElementById('gameOverOverlay');
  if(el) el.style.display='grid';
}
function hideGameOver(){
  gameOver=false;
  paused=false;
  const el=document.getElementById('gameOverOverlay');
  if(el) el.style.display='none';
}
function newGame(diff){
  if(diff) difficulty=diff;
  document.querySelectorAll('.diff-btn').forEach(b=>b.classList.toggle('active', b.dataset.diff===difficulty));
  document.getElementById('difficultyPill').textContent=DIFFICULTY[difficulty].label;
  solution=generateSolution();
  cages=generateCages(solution,difficulty);
  buildMaps();
  board=Array(9).fill(0).map(()=>Array(9).fill(0));
  notes=Array(9).fill(0).map(()=>Array(9).fill(0).map(()=>new Set()));
  given=Array(9).fill(0).map(()=>Array(9).fill(false));
  selected=null; mistakes=0; isNoteMode=false; lightningDigit=null; history=[];
  hideGameOver();
  document.getElementById('mistakes').textContent='0/3';
  updateNotesBtn();
  updateLightningUI();
  // auto-fill pencil marks at start so player sees candidates immediately
  for(let r=0;r<9;r++) for(let c=0;c<9;c++){
    if(board[r][c]!==0 || given[r][c]){ notes[r][c].clear(); continue; }
    const cand=getCandidates(r,c);
    notes[r][c]=new Set(cand);
  }
  resetTimer();
  startTimer();
  render();
}

function startTimer(){ clearInterval(timerId); timerId=setInterval(()=>{ if(!paused){ timerSec++; renderTimer(); }},1000); }
function resetTimer(){ timerSec=0; paused=false; document.getElementById('pauseOverlay').style.display='none'; const pb=document.getElementById('pauseBtn'); if(pb) pb.textContent='⏸'; renderTimer(); }
function renderTimer(){ const m=String(Math.floor(timerSec/60)).padStart(2,'0'), s=String(timerSec%60).padStart(2,'0'); document.getElementById('timer').textContent=`${m}:${s}` }
function togglePause(){
  if(gameOver) return;
  paused=!paused;
  document.getElementById('pauseOverlay').style.display= paused?'grid':'none';
  const pb=document.getElementById('pauseBtn'); if(pb) pb.textContent= paused?'▶':'⏸';
}

function pushHistory(){
  history.push({board: board.map(r=>r.slice()), notes: notes.map(r=>r.map(s=>new Set(s))), mistakes});
  if(history.length>100) history.shift();
}
function undo(){
  if(!history.length) return;
  const h=history.pop();
  board=h.board; notes=h.notes; mistakes=h.mistakes;
  document.getElementById('mistakes').textContent=`${mistakes}/3`;
  if(gameOver && mistakes < 3){
    hideGameOver();
    startTimer();
  }
  render();
}

function getErrors(){
  const err=Array(9).fill(0).map(()=>Array(9).fill(false));
  // row/col/box duplicates
  for(let r=0;r<9;r++) for(let c=0;c<9;c++) if(board[r][c]){
    const v=board[r][c];
    for(let k=0;k<9;k++){ if(k!==c && board[r][k]===v) err[r][c]=err[r][k]=true; if(k!==r && board[k][c]===v) err[r][c]=err[k][c]=true; }
    const br=Math.floor(r/3)*3, bc=Math.floor(c/3)*3;
    for(let rr=br;rr<br+3;rr++)for(let cc=bc;cc<bc+3;cc++) if((rr!==r||cc!==c)&& board[rr][cc]===v) {err[r][c]=true; err[rr][cc]=true}
  }
  // cage duplicates & sum exceed
  cages.forEach(cg=>{
    const seen={};
    let sum=0, filled=0;
    cg.cells.forEach(([r,c])=>{
      const v=board[r][c];
      if(v){ sum+=v; filled++; if(seen[v]){ cg.cells.forEach(([rr,cc])=>{ if(board[rr][cc]===v) err[rr][cc]=true}); } seen[v]=true; }
    });
    if(filled===cg.cells.length && sum!==cg.sum) cg.cells.forEach(([r,c])=> err[r][c]=true);
    if(filled < cg.cells.length && sum >= cg.sum) cg.cells.forEach(([r,c])=>{ if(board[r][c]) err[r][c]=true });
    // also if sum > cage sum even before fill, mark
    if(sum > cg.sum) cg.cells.forEach(([r,c])=> err[r][c]=true);
  });
  // incorrect vs solution -> red (Killer Sudoku: any wrong digit is an error)
  if(solution){
    for(let r=0;r<9;r++) for(let c=0;c<9;c++) if(board[r][c] && solution[r][c] && board[r][c]!==solution[r][c]) err[r][c]=true;
  }
  return err;
}

function selectCell(r,c){
  selected=[r,c];
  render();
  updateCageInfo();
}
function updateCageInfo(){
  const el=document.getElementById('cageDetail');
  if(!selected){ el.textContent='Select a cell to see cage sum and remaining.'; return; }
  const [r,c]=selected; const idx=cageMap[r][c]; const cg=cages[idx];
  let sum=0, filled=0; cg.cells.forEach(([rr,cc])=>{ if(board[rr][cc]){sum+=board[rr][cc]; filled++;}});
  const rem=cg.sum - sum;
  const need=cg.cells.length - filled;
  el.innerHTML=`<b>Cage #${idx+1}</b> — sum <b>${cg.sum}</b> • ${cg.cells.length} cells<br>
  Filled ${filled}/${cg.cells.length} • current ${sum} • remaining <b>${rem}</b> ${need?`• ${need} empty`:'• <span style="color:var(--success)">complete</span>'}<br>
  <span style="font-size:11px;color:var(--muted)">Cells: ${cg.cells.map(([rr,cc])=> String.fromCharCode(65+cc)+(rr+1)).join(', ')}</span>`;
}

function setValue(n){
  if(gameOver) return;
  if(!selected) return;
  const [r,c]=selected;
  if(given[r][c]) return;
  pushHistory();
  if(isNoteMode){
    const s=notes[r][c];
    if(s.has(n)) s.delete(n); else s.add(n);
    // if adding note, clear value if present? keep value but hide notes when value present
    if(board[r][c]) { board[r][c]=0; }
  } else {
    // clear notes when placing value
    notes[r][c].clear();
    if(board[r][c]===n) board[r][c]=0; else {
      board[r][c]=n;
      // auto-remove this number from notes in same row, column and 3×3 box
      for(let k=0;k<9;k++){
        if(k!==c) notes[r][k].delete(n);
        if(k!==r) notes[k][c].delete(n);
      }
      const br=Math.floor(r/3)*3, bc=Math.floor(c/3)*3;
      for(let rr=br;rr<br+3;rr++) for(let cc=bc;cc<bc+3;cc++){
        if(rr===r && cc===c) continue;
        notes[rr][cc].delete(n);
      }
    }
    if(board[r][c] && board[r][c]!==0 && solution[r][c]!==board[r][c] && autoCheck){
      mistakes++;
      document.getElementById('mistakes').textContent=`${mistakes}/3`;
      if(mistakes>=3){ render(); showGameOver(); return; }
    }
  }
  render();
  checkWin();
}
function erase(){
  if(gameOver) return;
  if(!selected) return;
  const [r,c]=selected; if(given[r][c]) return;
  pushHistory();
  board[r][c]=0; notes[r][c].clear(); render();
}
function hint(){
  if(gameOver) return;
  // pick a random empty cell (not yet filled) — ignores current selection, like sudoku.com
  const empties=[];
  for(let r=0;r<9;r++) for(let c=0;c<9;c++) if(board[r][c]===0) empties.push([r,c]);
  // if board full but has mistakes, hint a random wrong cell instead
  let pool = empties;
  if(pool.length===0){
    const wrongs=[];
    for(let r=0;r<9;r++) for(let c=0;c<9;c++) if(board[r][c]!==0 && board[r][c]!==solution[r][c]) wrongs.push([r,c]);
    if(wrongs.length===0) return;
    pool = wrongs;
  }
  const [r,c]=pool[Math.floor(Math.random()*pool.length)];
  selected=[r,c];
  pushHistory();
  const n=solution[r][c];
  board[r][c]=n; notes[r][c].clear();
  // same auto-cleanup as setValue: remove this number's notes in row/col/box
  for(let k=0;k<9;k++){ if(k!==c) notes[r][k].delete(n); if(k!==r) notes[k][c].delete(n); }
  const br=Math.floor(r/3)*3, bc=Math.floor(c/3)*3;
  for(let rr=br;rr<br+3;rr++) for(let cc=bc;cc<bc+3;cc++){ if(rr!==r||cc!==c) notes[rr][cc].delete(n); }
  render(); checkWin();
  // flash
  const cellEl=document.querySelector(`[data-r="${r}"][data-c="${c}"]`);
  if(cellEl){ cellEl.classList.add('hint'); setTimeout(()=>cellEl.classList.remove('hint'),600)}
  if(typeof updateCageInfo==='function') updateCageInfo();
}

function checkWin(){
  for(let r=0;r<9;r++)for(let c=0;c<9;c++) if(board[r][c]!==solution[r][c]) return false;
  // verify all filled
  for(let r=0;r<9;r++)for(let c=0;c<9;c++) if(board[r][c]===0) return false;
  clearInterval(timerId);
  setTimeout(()=>{ alert(`🎉 Killer Sudoku solved in ${document.getElementById('timer').textContent}!`); },150);
  return true;
}

function doCheck(){
  const err=getErrors();
  let hasError=false;
  for(let r=0;r<9;r++)for(let c=0;c<9;c++) if(err[r][c]) hasError=true;
  if(!hasError && board.flat().every(v=>v!==0)){
    // also verify against solution cage sums already
    checkWin();
    if(!checkWin()) alert('No errors found, but puzzle not yet solved — keep going!');
    else return;
  }
  if(hasError) alert('There are mistakes highlighted in red — check cage sums and duplicates.');
  else alert('No errors so far — keep going!');
  render();
}

function solvePuzzle(){
  if(!confirm('Solve the puzzle? This will fill all cells.')) return;
  for(let r=0;r<9;r++)for(let c=0;c<9;c++){ board[r][c]=solution[r][c]; notes[r][c].clear(); }
  render(); clearInterval(timerId);
}

function updateNotesBtn(){
  const b=document.getElementById('notesBtn');
  b.classList.toggle('active', isNoteMode);
}

function getCandidates(r,c){
  if(board[r][c]!==0) return [];
  const idx=cageMap[r][c];
  const cage=cages[idx];
  const usedRow=new Set(), usedCol=new Set(), usedBox=new Set(), usedCage=new Set();
  for(let k=0;k<9;k++){ if(board[r][k]) usedRow.add(board[r][k]); if(board[k][c]) usedCol.add(board[k][c]); }
  const br=Math.floor(r/3)*3, bc=Math.floor(c/3)*3;
  for(let rr=br;rr<br+3;rr++) for(let cc=bc;cc<bc+3;cc++) if(board[rr][cc]) usedBox.add(board[rr][cc]);
  let cageSumSoFar=0, cageFilled=0;
  for(const [rr,cc] of cage.cells){
    const v=board[rr][cc];
    if(v){ usedCage.add(v); cageSumSoFar+=v; cageFilled++; }
  }
  // candidates that respect row/col/box + cage duplicate + cage sum feasibility
  const out=[];
  const totalCells=cage.cells.length;
  const cageSum=cage.sum;
  const remainingAfter = totalCells - (cageFilled + 1); // after placing n
  for(let n=1;n<=9;n++){
    if(usedRow.has(n) || usedCol.has(n) || usedBox.has(n) || usedCage.has(n)) continue;
    const sumWith = cageSumSoFar + n;
    if(remainingAfter < 0) continue;
    if(remainingAfter === 0){
      if(sumWith !== cageSum) continue;
    } else {
      if(sumWith >= cageSum) continue;
      // feasible sum interval for the still-empty cells (distinct digits, not in usedCage nor n)
      const forbidden=new Set(usedCage); forbidden.add(n);
      const avail=[];
      for(let d=1;d<=9;d++) if(!forbidden.has(d)) avail.push(d);
      if(avail.length < remainingAfter) continue;
      avail.sort((a,b)=>a-b);
      let minRem=0, maxRem=0;
      for(let i=0;i<remainingAfter;i++) minRem+=avail[i];
      for(let i=0;i<remainingAfter;i++) maxRem+=avail[avail.length-1-i];
      if(sumWith + minRem > cageSum) continue;
      if(sumWith + maxRem < cageSum) continue;
    }
    out.push(n);
  }
  return out;
}

function fillNotes(){
  if(gameOver) return;
  // fill pencil marks (candidates) in every empty cell; skip cells that already have a value
  let filledCount=0;
  const anyEmpty = board.some(row=>row.some(v=>v===0));
  if(!anyEmpty) return;
  pushHistory();
  for(let r=0;r<9;r++) for(let c=0;c<9;c++){
    if(board[r][c]!==0){ notes[r][c].clear(); continue; }
    if(given[r][c]){ notes[r][c].clear(); continue; }
    const cand=getCandidates(r,c);
    notes[r][c]=new Set(cand);
    if(cand.length) filledCount++;
  }
  render();
  // brief feedback on button
  const btn=document.getElementById('fillNotesBtn');
  if(btn){
    const orig=btn.innerHTML;
    btn.innerHTML='<i>✓</i> Filled';
    btn.classList.add('active');
    setTimeout(()=>{ btn.innerHTML=orig; btn.classList.remove('active'); }, 900);
  }
}

function render(){
  const grid=document.getElementById('grid');
  grid.innerHTML='';
  // incorrect numbers are always red, even when Auto-check is off
  let errors;
  if(autoCheck) errors = getErrors();
  else {
    errors = Array(9).fill(0).map(()=>Array(9).fill(false));
    if(solution){
      for(let r=0;r<9;r++) for(let c=0;c<9;c++) if(board[r][c] && solution[r][c] && board[r][c]!==solution[r][c]) errors[r][c]=true;
    }
  }
  const selVal = selected ? board[selected[0]][selected[1]] : null;
  // Lightning ON: highlight only the armed digit; don't carry over the old selection highlight from when Lightning was OFF
  const highlightNum = lightningMode ? lightningDigit : (selVal && selVal !== 0 ? selVal : null);
  // find cage first cell for sum label
  const cageFirst=new Map();
  cages.forEach((cg,idx)=>{
    let minR=9,minC=9,first=null;
    cg.cells.forEach(([r,c])=>{ if(r<minR || (r===minR && c<minC)){minR=r;minC=c;first=[r,c] }});
    cageFirst.set(idx, first);
  });
  for(let r=0;r<9;r++) for(let c=0;c<9;c++){
    const val=board[r][c];
    const div=document.createElement('div');
    div.className='cell';
    if(c===2 || c===5) div.classList.add('box-right');
    if(r===2 || r===5) div.classList.add('box-bottom');
    div.dataset.r=r; div.dataset.c=c;
    if(!lightningMode && selected && selected[0]===r && selected[1]===c) div.classList.add('selected');
    else if(highlightNum && val===highlightNum && val!==0) div.classList.add('same-value');
    if(errors[r][c]) div.classList.add('error');
    if(given[r][c]) div.classList.add('given'); else if(val) div.classList.add('user');
    // cage borders
    const idx=cageMap[r][c];
    const cage=cages[idx];
    // sum label — sits ON the top dashed border; its opaque background erases the dash underneath, leaving a clean gap
    const first=cageFirst.get(idx);
    if(first && first[0]===r && first[1]===c){
      const sumEl=document.createElement('div');
      sumEl.className='cage-sum';
      sumEl.textContent=cage.sum;
      div.appendChild(sumEl);
      div.classList.add('cage-has-sum');
    }
    // value or notes — when a filled square is selected, matching pencil marks highlight too
    if(val){
      div.appendChild(document.createTextNode(val));
    } else if(notes[r][c].size){
      const nwrap=document.createElement('div');
      nwrap.className='notes';
      for(let n=1;n<=9;n++){
        const s=document.createElement('span');
        const has=notes[r][c].has(n);
        s.textContent= has ? n : '';
        if(highlightNum && has && n===highlightNum) s.classList.add('note-hl');
        nwrap.appendChild(s);
      }
      div.appendChild(nwrap);
    }
    // cage dashes — per-cage perimeter: every side where neighbor is different cage gets its own dash.
    // Adjacent cages therefore draw two parallel dashes with a ~2.3px gap between them (not a single shared line).
    const isTop = r===0 || cageMap[r-1][c]!==idx;
    const isBottom = r===8 || cageMap[r+1][c]!==idx;
    const isLeft = c===0 || cageMap[r][c-1]!==idx;
    const isRight = c===8 || cageMap[r][c+1]!==idx;
    const boldTop = r===3 || r===6;
    const boldBottom = r===2 || r===5;
    const boldLeft = c===3 || c===6;
    const boldRight = c===2 || c===5;
    if(isTop){ const d=document.createElement('div'); d.className='cage-dash top' + (boldTop?' on-bold':''); div.appendChild(d); }
    if(isBottom){ const d=document.createElement('div'); d.className='cage-dash bottom' + (boldBottom?' on-bold':''); div.appendChild(d); }
    if(isLeft){ const d=document.createElement('div'); d.className='cage-dash left' + (boldLeft?' on-bold':''); div.appendChild(d); }
    if(isRight){ const d=document.createElement('div'); d.className='cage-dash right' + (boldRight?' on-bold':''); div.appendChild(d); }

    div.addEventListener('click',()=>{
      if(gameOver) return;
      if(lightningMode && lightningDigit){
        if(given[r][c]) { selectCell(r,c); return; }
        // Notes ON: cells with a main value are untouched (spec)
        if(isNoteMode && board[r][c]!==0) { selectCell(r,c); return; }
        pushHistory();
        if(isNoteMode){
          // Notes ON → toggle note for armed digit
          if(board[r][c]!==0){ selectCell(r,c); return; }
          const s=notes[r][c];
          if(s.has(lightningDigit)) s.delete(lightningDigit); else s.add(lightningDigit);
        } else {
          // Notes OFF → insert main number (if already same, toggle off; else replace)
          if(board[r][c]===lightningDigit){ board[r][c]=0; }
          else { notes[r][c].clear(); board[r][c]=lightningDigit;
            for(let k=0;k<9;k++){ if(k!==c) notes[r][k].delete(lightningDigit); if(k!==r) notes[k][c].delete(lightningDigit); }
            const br=Math.floor(r/3)*3, bc=Math.floor(c/3)*3;
            for(let rr=br;rr<br+3;rr++) for(let cc=bc;cc<bc+3;cc++){ if(rr!==r||cc!==c) notes[rr][cc].delete(lightningDigit); }
            if(solution[r][c]!==lightningDigit && autoCheck){
              mistakes++; document.getElementById('mistakes').textContent=`${mistakes}/3`;
              if(mistakes>=3){ render(); showGameOver(); return; }
            }
          }
        }
        selected=[r,c];
        render(); checkWin(); updateCageInfo(); return;
      }
      selectCell(r,c);
    });
    grid.appendChild(div);
  }
  // progress
  const filled=board.flat().filter(v=>v!==0).length;
  document.getElementById('progress').textContent=`${Math.round(filled/81*100)}% filled`;
  // disable used numbers? show count
  updateNumpadCounts();
  updateLightningUI();
}

function updateNumpadCounts(){
  const counts=Array(10).fill(0);
  board.flat().forEach(v=>{ if(v) counts[v]++ });
  document.querySelectorAll('.num').forEach(btn=>{
    const n=parseInt(btn.dataset.n);
    const left=9 - counts[n];
    btn.querySelector('small').textContent = left>0 ? `${left}` : '✓';
    btn.disabled = left<=0 ? false : false; // keep enabled but show check
    if(left===0) btn.style.opacity='.55';
    else btn.style.opacity='1';
  });
}

// numpad — with Lightning: clicking a digit arms it (highlights) instead of placing into selected cell
const np=document.getElementById('numpad');
for(let n=1;n<=9;n++){
  const b=document.createElement('button');
  b.className='num'; b.dataset.n=n;
  b.innerHTML=`${n}<small></small>`;
  b.addEventListener('click',()=>{
    if(lightningMode){
      if(setLightningDigit(n)) return;
    }
    setValue(n);
  });
  np.appendChild(b);
}

// events
document.getElementById('newGameBtn').addEventListener('click',()=>newGame());
document.getElementById('restartBtn')?.addEventListener('click',()=>{
  if(!confirm('Restart this puzzle?')) return;
  board=Array(9).fill(0).map(()=>Array(9).fill(0));
  notes=Array(9).fill(0).map(()=>Array(9).fill(0).map(()=>new Set()));
  mistakes=0; document.getElementById('mistakes').textContent='0/3';
  history=[]; selected=null; render();
});
document.getElementById('checkBtn')?.addEventListener('click',doCheck);
document.getElementById('solveBtn')?.addEventListener('click',solvePuzzle);
document.getElementById('fillNotesBtn').addEventListener('click',fillNotes);
document.getElementById('undoBtn').addEventListener('click',undo);
document.getElementById('notesBtn').addEventListener('click',()=>{
  // per spec Notes button always toggles pencil mode, even with Lightning ON
  isNoteMode=!isNoteMode;
  updateNotesBtn();
  if(lightningMode && lightningDigit) render();
  updateLightningUI();
});
document.getElementById('hintBtn').addEventListener('click',hint);
document.getElementById('pauseBtn')?.addEventListener('click',togglePause);
document.querySelectorAll('.diff-btn').forEach(b=>b.addEventListener('click',()=>newGame(b.dataset.diff)));
document.getElementById('autoCheckSwitch')?.addEventListener('click',function(){ autoCheck=!autoCheck; this.classList.toggle('active',autoCheck); render();});
document.getElementById('lightningSwitch').addEventListener('click',function(){
  lightningMode=!lightningMode;
  if(!lightningMode) lightningDigit=null;
  this.classList.toggle('active', lightningMode);
  updateLightningUI();
  render();
});

document.addEventListener('keydown',e=>{
  if(gameOver && (e.key==='z' || e.key==='Z') && (e.ctrlKey||e.metaKey)){ undo(); e.preventDefault(); return; }
  if(gameOver) return;
  if(e.key==='n' || e.key==='N'){ isNoteMode=!isNoteMode; updateNotesBtn(); e.preventDefault(); return; }
  // Lightning hotkey: pressing 1-9 arms highlight without needing selection
  if(lightningMode && e.key>='1' && e.key<='9'){
    const n=parseInt(e.key,10);
    if(e.target && e.target.closest && e.target.closest('input,textarea')) return;
    // if no cell is selected, arm the digit; if a cell is selected respect normal setValue
    if(!selected) { setLightningDigit(n); e.preventDefault(); return; }
  }
  if(!selected && ['ArrowUp','ArrowDown','ArrowLeft','ArrowRight'].includes(e.key)) { selected=[4,4]; render(); }
  if(selected){
    let [r,c]=selected;
    if(e.key==='ArrowUp') r=Math.max(0,r-1);
    else if(e.key==='ArrowDown') r=Math.min(8,r+1);
    else if(e.key==='ArrowLeft') c=Math.max(0,c-1);
    else if(e.key==='ArrowRight') c=Math.min(8,c+1);
    else if(e.key>='1' && e.key<='9'){ setValue(parseInt(e.key)); return; }
    else if(e.key==='Backspace' || e.key==='Delete' || e.key==='0'){ erase(); return; }
    else return;
    selected=[r,c]; render(); updateCageInfo(); e.preventDefault();
  }
});

// init — default: create a game immediately when the page loads
if(document.readyState === 'loading'){
  document.addEventListener('DOMContentLoaded', ()=> newGame('medium'));
} else {
  newGame('medium');
}
