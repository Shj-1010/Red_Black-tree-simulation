(()=> {
/* ===== 공용 DOM ===== */
const svg = document.getElementById('canvas');
const modeSel = document.getElementById('mode');
const degBox  = document.getElementById('degBox');
const orderM  = document.getElementById('orderM');
const btnStart= document.getElementById('btnStart');
const btnPrev = document.getElementById('btnPrev');
const btnNext = document.getElementById('btnNext');
const btnReset= document.getElementById('btnReset');
const seqIns  = document.getElementById('seqIns');
const seqDel  = document.getElementById('seqDel');
const logBox  = document.getElementById('log');
const curStep = document.getElementById('curStep');
const leftCnt = document.getElementById('leftCnt');
const legendRBT = document.getElementById('legendRBT');
const legendB   = document.getElementById('legendB');

/* ===== 유틸 ===== */
function shuffle(a){ for(let i=a.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1)); [a[i],a[j]]=[a[j],a[i]];} return a; }
function sample(n, lo, hi){ const arr=[]; for(let v=lo; v<=hi; v++) arr.push(v); return shuffle(arr).slice(0,n); }
function makeSVG(tag, attrs, text=''){ const el=document.createElementNS('http://www.w3.org/2000/svg', tag); for(const k in attrs) el.setAttribute(k, attrs[k]); if(text) el.textContent=text; return el; }
function css(v){ return getComputedStyle(document.documentElement).getPropertyValue(v).trim(); }
function log(s){ logBox.textContent += s + "\n"; logBox.scrollTop = logBox.scrollHeight; }

/* ===== 상태 ===== */
let steps=[], stepPtr=0; // [{op:'ins'|'del', val:number}]
let ins=[], dels=[];
let engine=null; // RBT or BTree

/* ================= RBT ================= */
const RED=true, BLACK=false;
class RBNode{ constructor(key=null,color=BLACK,left=null,right=null,parent=null){ this.key=key; this.color=color; this.left=left; this.right=right; this.parent=parent; } }
class RBT{
  constructor(){ this.NIL=new RBNode(null,BLACK); this.root=this.NIL; }
  leftRotate(x){ const y=x.right; x.right=y.left; if(y.left!==this.NIL) y.left.parent=x; y.parent=x.parent;
    if(x.parent===this.NIL) this.root=y; else if(x===x.parent.left) x.parent.left=y; else x.parent.right=y; y.left=x; x.parent=y; }
  rightRotate(x){ const y=x.left; x.left=y.right; if(y.right!==this.NIL) y.right.parent=x; y.parent=x.parent;
    if(x.parent===this.NIL) this.root=y; else if(x===x.parent.right) x.parent.right=y; else x.parent.left=y; y.right=x; x.parent=y; }
  insert(k){ const z=new RBNode(k,RED,this.NIL,this.NIL,this.NIL); let y=this.NIL,x=this.root;
    while(x!==this.NIL){ y=x; x=(z.key<x.key)?x.left:x.right; } z.parent=y; if(y===this.NIL) this.root=z; else if(z.key<y.key) y.left=z; else y.right=z; this.fixInsert(z); }
  fixInsert(z){ while(z.parent.color===RED){ if(z.parent===z.parent.parent.left){ const u=z.parent.parent.right;
        if(u.color===RED){ z.parent.color=BLACK; u.color=BLACK; z.parent.parent.color=RED; z=z.parent.parent; }
        else{ if(z===z.parent.right){ z=z.parent; this.leftRotate(z); } z.parent.color=BLACK; z.parent.parent.color=RED; this.rightRotate(z.parent.parent); } }
      else{ const u=z.parent.parent.left; if(u.color===RED){ z.parent.color=BLACK; u.color=BLACK; z.parent.parent.color=RED; z=z.parent.parent; }
        else{ if(z===z.parent.left){ z=z.parent; this.rightRotate(z); } z.parent.color=BLACK; z.parent.parent.color=RED; this.leftRotate(z.parent.parent); } } }
    this.root.color=BLACK; }
  transplant(u,v){ if(u.parent===this.NIL) this.root=v; else if(u===u.parent.left) u.parent.left=v; else u.parent.right=v; v.parent=u.parent; }
  minimum(x){ while(x.left!==this.NIL) x=x.left; return x; }
  find(k){ let z=this.root; while(z!==this.NIL && z.key!==k) z=(k<z.key)?z.left:z.right; return z; }
  delete(k){ let z=this.find(k); if(z===this.NIL) return false; let y=z, ycol=y.color, x;
    if(z.left===this.NIL){ x=z.right; this.transplant(z,z.right); }
    else if(z.right===this.NIL){ x=z.left; this.transplant(z,z.left); }
    else{ y=this.minimum(z.right); ycol=y.color; x=y.right; if(y.parent===z) x.parent=y;
      else{ this.transplant(y,y.right); y.right=z.right; y.right.parent=y; }
      this.transplant(z,y); y.left=z.left; y.left.parent=y; y.color=z.color; }
    if(ycol===BLACK) this.fixDelete(x); return true; }
  fixDelete(x){ while(x!==this.root && x.color===BLACK){ if(x===x.parent.left){ let w=x.parent.right;
        if(w.color===RED){ w.color=BLACK; x.parent.color=RED; this.leftRotate(x.parent); w=x.parent.right; }
        if(w.left.color===BLACK && w.right.color===BLACK){ w.color=RED; x=x.parent; }
        else{ if(w.right.color===BLACK){ w.left.color=BLACK; w.color=RED; this.rightRotate(w); w=x.parent.right; }
          w.color=x.parent.color; x.parent.color=BLACK; w.right.color=BLACK; this.leftRotate(x.parent); x=this.root; } }
      else{ let w=x.parent.left;
        if(w.color===RED){ w.color=BLACK; x.parent.color=RED; this.rightRotate(x.parent); w=x.parent.left; }
        if(w.right.color===BLACK && w.left.color===BLACK){ w.color=RED; x=x.parent; }
        else{ if(w.left.color===BLACK){ w.right.color=BLACK; w.color=RED; this.leftRotate(w); w=x.parent.left; }
          w.color=x.parent.color; x.parent.color=BLACK; w.left.color=BLACK; this.rightRotate(x.parent); x=this.root; } } }
    x.color=BLACK; }
  positions(){ const pos=new Map(); let i=0; const dfs=(n,d=0)=>{ if(n===this.NIL) return; dfs(n.left,d+1); pos.set(n,{x:i++,y:d}); dfs(n.right,d+1); }; dfs(this.root,0); return pos; }
}

/* ================= B-Tree ================= */
class BNode{
  constructor(M, leaf=true){ this.M=M; this.keys=[]; this.child=[]; this.leaf=leaf; }
  get maxKeys(){ return this.M-1; }
  get minKeys(){ return Math.ceil(this.M/2)-1; } // 루트 제외
}
class BTree{
  constructor(M=4){ this.M=M; this.root=new BNode(M,true); }
  _splitChild(p,i){
    const y=p.child[i], M=this.M, mid=Math.floor((M-1)/2);
    const z=new BNode(M,y.leaf);
    z.keys = y.keys.splice(mid+1);
    const up = y.keys.splice(mid,1)[0];
    if(!y.leaf) z.child = y.child.splice(mid+1);
    p.child.splice(i+1,0,z);
    p.keys.splice(i,0,up);
  }
  insert(k){
    if(this.root.keys.length===this.root.maxKeys){
      const s=new BNode(this.M,false);
      s.child=[this.root];
      this.root=s;
      this._splitChild(s,0);
    }
    this._insertNonFull(this.root,k);
  }
  _insertNonFull(x,k){
    let i=x.keys.length-1;
    if(x.leaf){
      while(i>=0 && k<x.keys[i]) i--;
      x.keys.splice(i+1,0,k);
    }else{
      while(i>=0 && k<x.keys[i]) i--;
      i++;
      if(x.child[i].keys.length===x.child[i].maxKeys){
        this._splitChild(x,i);
        if(k>x.keys[i]) i++;
      }
      this._insertNonFull(x.child[i],k);
    }
  }
  _borrowOrMerge(parent, ci){
    const node=parent.child[ci], left=ci-1, right=ci+1;
    if(left>=0 && parent.child[left].keys.length>parent.child[left].minKeys){
      const L=parent.child[left];
      node.keys.unshift(parent.keys[left]);
      if(!node.leaf) node.child.unshift(L.child.pop());
      parent.keys[left]=L.keys.pop();
      return {action:'borrow-left'};
    }
    if(right<parent.child.length && parent.child[right].keys.length>parent.child[right].minKeys){
      const R=parent.child[right];
      node.keys.push(parent.keys[ci]);
      if(!node.leaf) node.child.push(R.child.shift());
      parent.keys[ci]=R.keys.shift();
      return {action:'borrow-right'};
    }
    if(left>=0){
      const L=parent.child[left];
      L.keys.push(parent.keys[left], ...node.keys);
      if(!node.leaf) L.child.push(...node.child);
      parent.keys.splice(left,1);
      parent.child.splice(ci,1);
      return {action:'merge-left', merged:L};
    }else{
      const R=parent.child[right];
      node.keys.push(parent.keys[ci], ...R.keys);
      if(!node.leaf) node.child.push(...R.child);
      parent.keys.splice(ci,1);
      parent.child.splice(right,1);
      return {action:'merge-right', merged:node};
    }
  }
  delete(k){
    this._deleteRec(this.root,k);
    if(!this.root.leaf && this.root.keys.length===0){
      this.root=this.root.child[0];
    }
  }
  _deleteRec(x,k){
    let idx=x.keys.findIndex(v=>v===k);
    if(idx!==-1){
      if(x.leaf){
        x.keys.splice(idx,1);
      }else{
        let L=x.child[idx], R=x.child[idx+1];
        if(L.keys.length>L.minKeys){
          let cur=L; while(!cur.leaf) cur=cur.child[cur.child.length-1];
          const pred=cur.keys[cur.keys.length-1];
          x.keys[idx]=pred; this._deleteRec(L,pred);
        }else if(R.keys.length>R.minKeys){
          let cur=R; while(!cur.leaf) cur=cur.child[0];
          const succ=cur.keys[0];
          x.keys[idx]=succ; this._deleteRec(R,succ);
        }else{
          L.keys.push(x.keys[idx], ...R.keys);
          if(!L.leaf) L.child.push(...R.child);
          x.keys.splice(idx,1); x.child.splice(idx+1,1);
          this._deleteRec(L,k);
        }
      }
      return;
    }
    let i=0; while(i<x.keys.length && k>x.keys[i]) i++;
    if(x.leaf) return;
    let child=x.child[i];
    if(child.keys.length===child.minKeys){
      const fix=this._borrowOrMerge(x,i);
      if(fix.action==='merge-left'){ child=fix.merged; }
    }
    this._deleteRec(child,k);
  }
  _width(n){ if(n.leaf) return Math.max(1,n.keys.length); let s=0; for(const c of n.child) s+=this._width(c); return Math.max(s,n.keys.length); }
  positions(){
    const pos=new Map(); const gapX=70, gapY=90, boxH=32;
    const measure=(n)=>this._width(n);
    const dfs=(n,d,left)=>{
      const w=measure(n), cx=left+w/2;
      pos.set(n,{x:cx,y:d});
      if(!n.leaf){
        let cur=left;
        for(const ch of n.child){
          const cw=measure(ch);
          dfs(ch,d+1,cur);
          cur+=cw;
        }
      }
    };
    dfs(this.root,0,0);
    const px=new Map(); let maxX=0,maxY=0;
    for(const [n,p] of pos.entries()){
      const x=p.x*gapX+60, y=p.y*gapY+60;
      px.set(n,{x,y}); if(x>maxX)maxX=x; if(y>maxY)maxY=y;
    }
    return {px, size:{w:maxX+100,h:maxY+80}, boxH};
  }
}

/* ============== 그리기 ============== */
function drawRBT(tree){
  svg.innerHTML='';
  if(tree.root===tree.NIL){
    svg.appendChild(makeSVG('text',{x:24,y:40,fill:'#93a3b8','font-size':16},'empty'));
    return;
  }
  const pos=tree.positions(), nodes=[...pos.keys()];
  const xs=nodes.map(n=>pos.get(n).x), ys=nodes.map(n=>pos.get(n).y);
  const maxX=Math.max(...xs), maxY=Math.max(...ys), dx=90,dy=90,pad=60;
  svg.setAttribute('viewBox',`0 0 ${pad*2+dx*(maxX+1)} ${pad*2+dy*(maxY+1)}`);

  for(const n of nodes){
    const p=pos.get(n);
    for(const c of [n.left,n.right]){
      if(c!==tree.NIL){
        const pc=pos.get(c);
        svg.appendChild(makeSVG('line',{x1:pad+p.x*dx,y1:pad+p.y*dy+6,x2:pad+pc.x*dx,y2:pad+pc.y*dy-6,stroke:css('--edge'),'stroke-width':2}));
      }
    }
  }
  for(const n of nodes){
    const p=pos.get(n), cx=pad+p.x*dx, cy=pad+p.y*dy, fill=(n.color===RED)?css('--red'):css('--black');
    svg.appendChild(makeSVG('circle',{cx,cy,r:20,fill}));
    svg.appendChild(makeSVG('text',{x:cx,y:cy+5,'font-size':16,'font-weight':700,'text-anchor':'middle',fill:(n.color===RED?'#111827':'#e5e7eb')}, String(n.key)));
  }
}
function drawBTree(tree){
  svg.innerHTML='';
  const {px,size,boxH}=tree.positions();
  svg.setAttribute('viewBox',`0 0 ${size.w} ${size.h}`);
  for(const [n,p] of px.entries()){
    if(!n.leaf){
      for(const ch of n.child){
        const pc=px.get(ch);
        svg.appendChild(makeSVG('line',{x1:p.x,y1:p.y+boxH/2,x2:pc.x,y2:pc.y-boxH/2,stroke:css('--line'),'stroke-width':2}));
      }
    }
  }
  for(const [n,p] of px.entries()){
    const keys=n.keys, keyW=30,gap=6,totalW=keys.length*keyW+(Math.max(0,keys.length-1))*gap, x0=p.x-totalW/2, y0=p.y-(boxH/2);
    svg.appendChild(makeSVG('rect',{x:x0-8,y:y0-6,width:totalW+16,height:boxH+12,rx:8,ry:8,fill:css('--btBox'),stroke:css('--btBorder'),'stroke-width':2}));
    keys.forEach((k,i)=>{ const x=x0+i*(keyW+gap);
      svg.appendChild(makeSVG('rect',{x,y:y0,width:keyW,height:boxH,rx:6,ry:6,fill:'#22365f'}));
      svg.appendChild(makeSVG('text',{x:x+keyW/2,y:y0+boxH/2+5,fill:css('--btKey'),'font-weight':800,'text-anchor':'middle'}, String(k)));
    });
  }
}

/* ============== 흐름 ============== */
function rebuildEngine(){
  if(modeSel.value==='rbt'){ engine=new RBT(); legendRBT.style.display='flex'; legendB.style.display='none'; }
  else{ engine=new BTree(Number(orderM.value)); legendRBT.style.display='none'; legendB.style.display='block'; }
}
function draw(){ (modeSel.value==='rbt') ? drawRBT(engine) : drawBTree(engine); }

function start(){
  rebuildEngine(); svg.innerHTML=''; logBox.textContent=''; stepPtr=0;
  const isB = (modeSel.value==='btree');
  const N_INS = isB ? 25 : 10;
  const N_DEL = isB ? 10 : 5;
  ins  = shuffle(sample(N_INS, 1, 50));
  dels = shuffle(ins.slice()).slice(0, N_DEL);
  steps=[]; ins.forEach(v=>steps.push({op:'ins',val:v})); dels.forEach(v=>steps.push({op:'del',val:v}));
  seqIns.textContent = '삽입: ' + ins.join(', ');
  seqDel.textContent = '삭제: ' + dels.join(', ');
  curStep.textContent='—'; leftCnt.textContent=String(steps.length-stepPtr);
  btnPrev.disabled=true; btnNext.disabled = steps.length===0;
  draw();
}
function replayTo(n){
  rebuildEngine();
  for(let i=0;i<n;i++){ const s=steps[i]; if(s.op==='ins') engine.insert(s.val); else engine.delete(s.val); }
  draw();
}
function prev(){
  if(stepPtr<=0) return;
  stepPtr--; replayTo(stepPtr);
  curStep.textContent = stepPtr>0 ? (steps[stepPtr-1].val + (steps[stepPtr-1].op==='ins'?' 삽입 완료':' 삭제 완료')) : '—';
  leftCnt.textContent = String(steps.length-stepPtr);
  btnPrev.disabled = stepPtr===0; btnNext.disabled = stepPtr>=steps.length;
  log('⏪ 되돌리기');
}
function next(){
  if(stepPtr>=steps.length) return;
  const s=steps[stepPtr++];
  if(s.op==='ins'){ engine.insert(s.val); log('삽입: '+s.val); curStep.textContent=`${s.val} 삽입`; }
  else { engine.delete(s.val); log('삭제: '+s.val); curStep.textContent=`${s.val} 삭제`; }
  draw();
  leftCnt.textContent = String(steps.length-stepPtr);
  btnPrev.disabled = stepPtr===0; btnNext.disabled = stepPtr>=steps.length;
}
function resetAll(){
  steps=[]; stepPtr=0; ins=[]; dels=[]; rebuildEngine(); svg.innerHTML=''; logBox.textContent='';
  seqIns.textContent='삽입: -'; seqDel.textContent='삭제: -'; curStep.textContent='—'; leftCnt.textContent='0';
  btnPrev.disabled=true; btnNext.disabled=true; draw();
}

/* ============== 이벤트 ============== */
function syncStartLabel(){
  btnStart.textContent = (modeSel.value==='btree') ? '시작 (무작위 25/10)' : '시작 (무작위 10/5)';
}
modeSel.addEventListener('change', ()=>{ degBox.style.display = (modeSel.value==='btree') ? 'inline-block' : 'none'; syncStartLabel(); resetAll(); });
orderM.addEventListener('change', ()=>{ if(modeSel.value==='btree') resetAll(); });
btnStart.addEventListener('click', start);
btnPrev.addEventListener('click', prev);
btnNext.addEventListener('click', next);
btnReset.addEventListener('click', resetAll);

/* 초기화 */
syncStartLabel(); rebuildEngine(); draw();

})(); // IIFE
