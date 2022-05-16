/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
/*
the case where a query reaches uneffective traces of propagated queries is problem.
*/


package coins.ssa;

import coins.backend.lir.LirIconst;
import coins.backend.lir.LirFconst;
import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.Type;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.cfg.BasicBlk;
import coins.backend.util.BiList;
import coins.backend.util.BiLink;
import coins.backend.Op;
import coins.backend.lir.LirLabelRef;
import coins.backend.ana.Postdominators;
import coins.backend.ana.Dominators;
import coins.backend.sym.Symbol;
import coins.backend.util.ImList;
import coins.backend.ana.DFST;
import java.util.Hashtable;
import java.util.Stack;
import java.util.Vector;
import java.util.Enumeration;
import coins.backend.lir.LirIconst;

public class PREQP implements LocalTransformer {
    private boolean debugFlag;

    public boolean doIt(Data data, ImList args) { return true; }
    public String name() { return "PREQP"; }
    public String subject() {
	return "Optimizatin with efficient question propagation.";
    }

    private class MemTrace {
	public Hashtable instMap;
	private Hashtable varMap;
	
	MemTrace(Function f, int mode) {
	    instMap = new Hashtable();

	    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
		BasicBlk blk=(BasicBlk)p.elem();
		varMap = new Hashtable();

		for(BiLink q=blk.instrList().last();!q.atEnd();q=q.prev()){
		    LirNode node=(LirNode)q.elem();
		    BiList memRands = util.findTargetLir(node,Op.MEM,new BiList());
		    if (mode == 3) {
			memRands.append(util.findTargetLir(node,Op.MUL,new BiList()));
			memRands.append(util.findTargetLir(node,Op.DIVU,new BiList()));
			memRands.append(util.findTargetLir(node,Op.DIVS,new BiList()));
			memRands.append(util.findTargetLir(node,Op.MODU,new BiList()));
			memRands.append(util.findTargetLir(node,Op.MODS,new BiList()));
			/*
			memRands.append(util.findTargetLir(node,Op.CONVSX,new BiList()));
			memRands.append(util.findTargetLir(node,Op.CONVZX,new BiList()));
			memRands.append(util.findTargetLir(node,Op.CONVIT,new BiList()));
			memRands.append(util.findTargetLir(node,Op.CONVFX,new BiList()));
			memRands.append(util.findTargetLir(node,Op.CONVFT,new BiList()));
			memRands.append(util.findTargetLir(node,Op.CONVFI,new BiList()));
			memRands.append(util.findTargetLir(node,Op.CONVSF,new BiList()));
			memRands.append(util.findTargetLir(node,Op.CONVUF,new BiList()));
			*/
		    }
		    for(BiLink qq=memRands.first();!qq.atEnd();qq=qq.next()){
			LirNode mem = (LirNode)qq.elem();
			BiList varRands=util.findTargetLir(mem,Op.REG,new BiList());
			for(BiLink qqq=varRands.first();!qqq.atEnd();qqq=qqq.next()){
			    LirSymRef varRef = (LirSymRef)qqq.elem();
			    varMap.put(varRef.symbol, Boolean.TRUE);
			}
		    }
		    if (node.opCode == Op.SET) {
			if (node.kid(0).opCode == Op.REG && varMap.get(((LirSymRef)node.kid(0)).symbol) != null) {
			    
			    instMap.put(node,Boolean.TRUE);
			    
			    BiList varRands=util.findTargetLir(node.kid(1),Op.REG,new BiList());
			    for(BiLink q2=varRands.first();!q2.atEnd();q2=q2.next()){
				LirSymRef varRef = (LirSymRef)q2.elem();
				varMap.put(varRef.symbol, Boolean.TRUE);
			    }
			}
		    }
		}
	    }
	}
    }


    /**
     * Elements of the Stack. It represents that the symbol `s' is in the
     * block `blk'.
     **/

    private class StackElem{
	Symbol s;
	//boolean isDom = false;
	//boolean isRelevant = false;
	BasicBlk blk;
	LirNode node;
	LirNode exp;
	boolean isLater;
	boolean isSelf;

	StackElem() {
	    s = null;
	    node = null;
	    blk = null;
	    isLater = false;
	}
	/*
	StackElem(Symbol sym,BasicBlk block, boolean _isLater){
	    s=sym;
	    node = env.lir.symRef(Op.REG,s.type,s,ImList.Empty);
	    blk=block;
	    isLater = _isLater;
	    isSelf = false;
	}

	StackElem(Symbol sym,BasicBlk block, boolean _isLater, boolean _isSelf){
	    s=sym;
	    node = env.lir.symRef(Op.REG,s.type,s,ImList.Empty);
	    blk=block;
	    isLater = _isLater;
	    isSelf = _isSelf;
	}

	*/
	StackElem(LirNode n,BasicBlk block){
	    if (n.opCode == Op.REG) 
		s=((LirSymRef)n).symbol;
	    else s = null;
	    node = n;//.makeCopy(env.lir);
	    blk=block;
	    isSelf = false;
	}

	StackElem(LirNode n,BasicBlk block, boolean _isLater){
	    if (n.opCode == Op.REG) 
		s=((LirSymRef)n).symbol;
	    else s = null;
	    node = n;//.makeCopy(env.lir);
	    blk=block;
	    isLater = _isLater;
	    isSelf = false;
	}

	StackElem(LirNode n,BasicBlk block, boolean _isLater, boolean _isSelf){
	    if (n.opCode == Op.REG) 
		s=((LirSymRef)n).symbol;
	    else s = null;
	    node = n;//.makeCopy(env.lir);
	    blk=block;
	    isLater = _isLater;
	    isSelf = _isSelf;
	}

	StackElem(LirNode n, LirNode e, BasicBlk block){
	    s = null;
	    node = n;//.makeCopy(env.lir);
	    exp = e;
	    blk=block;
	    isLater = false;
	    isSelf = false;
	}

	StackElem(LirNode n, LirNode e, BasicBlk block, boolean _isLater){
	    s = null;
	    node = n;//.makeCopy(env.lir);
	    exp = e;
	    blk=block;
	    isLater = _isLater;
	    isSelf = false;
	}

	StackElem(LirNode n, LirNode e, BasicBlk block, boolean _isLater, boolean _isSelf){
	    s = null;
	    node = n;//.makeCopy(env.lir);
	    exp = e;
	    blk=block;
	    isLater = _isLater;
	    isSelf = _isSelf;
	}

	LirNode lirNode(){
	    /*	    if(s!=null)
		return(env.lir.symRef(Op.REG,s.type,s,ImList.Empty));
	    return(null);
	    */
	    return node;
	}

	StackElem makeCopy() {
	    StackElem tmp = new StackElem(node,exp,blk,isLater,isSelf);
	    //tmp.isDom = isDom;
	    tmp.s = s;
	    return tmp;
	}
    }

    int maxId = 0;

    private class VNode {
	int id=0;
	int opCode;
	int type;
	LirNode node;
	LirNode code;
	
	Vector operands;

	VNode (int opCode, int type) {
	    this.opCode = opCode;
	    this.type = type;
	    this.node =node;
	    this.operands = null;
	    this.id = maxId++;
	    this.code = null;
	}

	VNode (LirNode node) {
	    this.opCode = node.opCode;
	    this.type = node.type;
	    this.node =node;
	    this.operands = null;
	    this.id = maxId++;
	}

	boolean equals (VNode vn) {
	    return this.id == vn.id;
	}

	Vector rands() {
	    if (operands == null) 
		operands = new Vector();
	    return operands;
	}
    }

    private class VElem{
	//boolean isDom = false;
	//boolean isRelevant = false;
	BasicBlk blk;
	VNode node;
	LirNode exp;
	boolean isLater;
	boolean isSelf;

	VElem() {
	    node = null;
	    blk = null;
	    isLater = false;
	}
	/*
	VElem(VNode n,BasicBlk block){
	    node = n;//.makeCopy(env.lir);
	    blk=block;
	    isSelf = false;
	}

	VElem(VNode n,BasicBlk block, boolean _isLater){
	    node = n;//.makeCopy(env.lir);
	    blk=block;
	    isLater = _isLater;
	    isSelf = false;
	}

	VElem(VNode n,BasicBlk block, boolean _isLater, boolean _isSelf){
	    node = n;//.makeCopy(env.lir);
	    blk=block;
	    isLater = _isLater;
	    isSelf = _isSelf;
	}
	*/
	VElem(VNode n, LirNode e, BasicBlk block){
	    node = n;//.makeCopy(env.lir);
	    exp = e;
	    blk=block;
	    isLater = false;
	    isSelf = false;
	}

	VElem(VNode n, LirNode e, BasicBlk block, boolean _isLater){
	    node = n;//.makeCopy(env.lir);
	    exp = e;
	    blk=block;
	    isLater = _isLater;
	}

	VElem(VNode n, LirNode e, BasicBlk block, boolean _isLater, boolean _isSelf){
	    node = n;//.makeCopy(env.lir);
	    exp = e;
	    blk=block;
	    isLater = _isLater;
	    isSelf = _isSelf;
	}

	VElem makeCopy() {
	    VElem tmp = new VElem(node,exp,blk,false,false);
	    return tmp;
	}
    }

    private int mode;

    private Util util;
    private String tmpSymName="_preqp";
    public static final int THR=SsaEnvironment.OptThr;
    /** The threshold of debug print **/
    public static final int THR2=SsaEnvironment.AllThr;
    private SsaEnvironment env;
    private SsaSymTab sstab;
    private Function f;
    // private LirNode[] visited; // for EQP
    private LirNode[] pVisited; // visited' : for postEQP
    private Stack stack;
    //    StackElem[] availVar;
    VElem unavailVar = new VElem();

    private Dominators dom;
    private DFST dfst;
    // Copy Propagation
    private DDCopyPropagation cpy;
    private CopyPropagation cpyp;

    // Tables
    Hashtable occurMap;
    Hashtable modMap;

    Hashtable phiMap; // These maps are used by variable substitution based on phi-function.
    Hashtable rPhiMap;

    private Hashtable vNodeMap;

    private Hashtable antMap;
    private Hashtable availMap;
    private Symbol invalidSym;
    private Symbol bottomSym;

    Hashtable cpMap;

    //private Hashtable bigPhiDefMap;
    // Hashtable leaderMap;

    private MemTrace memTrace;

    boolean initialized[];

    private boolean isLICM = false;
    //private boolean isOsr = false;
    MemoryAliasAnalyze alias;
    /*    private Hashtable memArgs;*/
    boolean[] memArray;

    /**
     * Constructor
     * @param e The environment of the SSA module
     * @param tab The symbol tabel of the SSA module
     * @param function The current function
     * @param m The current mode
     **/
    public PREQP(SsaEnvironment e, SsaSymTab tab, int m){
      env=e;
      env.println("  Partial Redundancy Elimination Based on Question Propagation "+
                    "on SSA form",SsaEnvironment.MsgThr);
      sstab=tab;
      mode = m; // 0 -> PRE, 1 -> PRE + LICM of the all instructions,
                // 2 -> PRE + LICM of MEM, 
                // 3 -> PRE + LICM of MEM, MUL, DIV and MOD
      invalidSym =  sstab.newSsaSymbol(tmpSymName+"@",Type.INT);
      bottomSym = sstab.newSsaSymbol("@"+tmpSymName,Type.INT);
    }


    /**
     * The main routine of Efficient Question Propagation.
     * Return the answer of the question to the expression `e' in the basic 
     * block `v'.
     * @param e The current expression
     * @param org The original expression
     * @param v The current basic block
     * @param lower The threshold of rank
     * @return The answer of the question
     **/


    boolean modGraph(VElem v) {
	
	VNode vn = v.node;
	LirNode exp = v.exp;
	BasicBlk blk = v.blk;
	if (vn.opCode == Op.REG) {
	    if (vn.node != null) {
		// if (vn.node.opCode == Op.REG) // reaching occurrences of the expression
		return true;
	    }
	    else {// reaching compensation code
		if (vn.operands == null) {
                    return false;
		}
		else {
		    return true;
		}
	    }
	}
	else if (vn.opCode == Op.PHI) {
	    Enumeration operands = vn.operands.elements();

	    Vector laterVec = new Vector();
	    boolean isLater = true;
	    BiLink pp= blk.predList().first();
	    while (operands.hasMoreElements()) {
		VElem elem = (VElem)operands.nextElement();
		if (!modGraph(elem)) {
		    elem.node.node = null;
		    elem.node.opCode = Op.REG;		    
		    elem.blk = (BasicBlk)pp.elem();
		    laterVec.add(elem);
		}
		else isLater = false;
		pp = pp.next();
	    }
	    if (isLater || 
		(laterVec.size()> 1 && postEqp(exp, blk, 
		  new LirNode[f.flowGraph().idBound()])== Boolean.FALSE))
		return false;

	    Enumeration laterOperands = laterVec.elements();

	    while (laterOperands.hasMoreElements()) {
		VElem elem = (VElem)laterOperands.nextElement();
		elem.node.node = elem.exp;
		elem.node.opCode = Op.REG;
	    }
	    return true;
	}
	else { // reaching args for expressions
            return true;
	}
    }
	

    LirNode insertPhi (VElem v) {

	//	VElem phiElem = (StackElem)bigPhiDefMap.get(v);
	VNode vn = v.node;
	LirNode exp = v.exp;
	BasicBlk blk = v.blk;
	if (vn.opCode == Op.REG) {
	    if (vn.node != null) {
		// if (vn.node.opCode == Op.REG) // reaching occurrences of the expression
		    return vn.node;
	    }
	    else {// reaching compensation code
		if (vn.operands == null) {
		    //System.out.println("#");
/*
		    Symbol sym=sstab.newSsaSymbol(tmpSymName,vn.type);
		    LirNode dst = env.lir.symRef(Op.REG, vn.type, sym,ImList.Empty);
		    LirNode setNode=env.lir.operator(Op.SET, vn.type, dst,
						     exp.makeCopy(env.lir),ImList.Empty);
		    vn.node = dst;
		    BiLink qq = blk.instrList().first();
		    for(; !qq.atEnd(); qq=qq.next()){
			LirNode n = (LirNode)qq.elem();
			if (n.opCode != Op.PHI) break;
		    }
		    qq.addBefore(setNode);
		    maintainTableInsertExp(qq.prev(), setNode, blk);
		    return dst;
*/
                    return null;
		}
		else {
		    //System.out.println("@");
		    vn.node = ((VElem)vn.operands.elementAt(0)).node.node;
		    return vn.node;
		}
	    }
	}
	else if (vn.opCode == Op.PHI) {
	    Enumeration operands = vn.operands.elements();
	    LirNode phi = createPhi(blk,exp);
	    vn.node = phi.kid(0);

	    Vector laterVec = new Vector();
	    boolean isLater = true;
	    BiLink pp= blk.predList().first();
	    while (operands.hasMoreElements()) {
		VElem elem = (VElem)operands.nextElement();
		elem.node.node = insertPhi(elem);
		elem.node.opCode = Op.REG;		    
		if (elem.node.node != null) {
		    isLater = false;
		}
		else {
		    elem.blk = (BasicBlk)pp.elem();
		    laterVec.add(elem);
		}
		pp = pp.next();
	    }
	    if (isLater || 
		(laterVec.size()> 1 && postEqp(exp, blk, 
		  new LirNode[f.flowGraph().idBound()])== Boolean.FALSE))
		return null;

	    Enumeration laterOperands = laterVec.elements();

	    while (laterOperands.hasMoreElements()) {
		VElem elem = (VElem)laterOperands.nextElement();
		elem.node.node = elem.exp;
		elem.node.node = insertPhi(elem);
		elem.node.opCode = Op.REG;
	    }

	    setArgToPhi (phi, blk, vn.operands);
	    
	    LirNode oldPhi = (LirNode)occurMap.get(makeLocalKey(blk,phi));
	    if (oldPhi == null) {
		BiLink q= blk.instrList().first();
		q.addBefore(phi.makeCopy(env.lir));
		maintainTableInsertPhi(q.prev(),phi,blk);
	    }
	    else phi = oldPhi;
	    return phi.kid(0);
	}
	else { // reaching args for expressions
	    Symbol sym=sstab.newSsaSymbol(tmpSymName,vn.type);
	    LirNode dst = env.lir.symRef(Op.REG, vn.type, sym,ImList.Empty);
	    LirNode setNode=env.lir.operator(Op.SET, vn.type, dst,
					     exp.makeCopy(env.lir),ImList.Empty);
	    vn.node = dst;
	    BiLink qq=blk.instrList().last();
	    qq.addBefore(setNode);
	    maintainTableInsertExp(qq.prev(), setNode, blk);
            return dst;
	}
    }


    private boolean modPhi(LirNode e,BasicBlk v){
      BiList operands=util.findTargetLir(e,Op.REG,new BiList());

      for(BiLink q=operands.first();!q.atEnd();q=q.next()){
	  StackElem phi = (StackElem)phiMap.get(((LirSymRef)q.elem()).symbol);
	  if (phi != null && phi.blk == v)
	      return true;
      }
      return false;
    }

    boolean propagate (LirNode e,BasicBlk v,LirNode[] visited) {
	if (v.predList().length() == 0) {
	    availMap.put(makeLocalKey(v,e),unavailVar);
	    return false;
	}

	boolean isAvail;

	if (!initialized[v.id]) localInit(v);

	StackElem stackElem=null;

	String localExpKey = makeLocalKey(v,e);
	//availMap.put(tmpPhiKey, new StackElem(phi.kid(0),v,true));

	Vector tmpInsert = new Vector();
	int pNum = 0;
	LirNode ep;
	boolean isAllLater = true;
	boolean isSomeRealAvail = false;
	boolean isAllAvail = true;
	boolean isSameArgs = true;
	boolean isSelf = false;
	Boolean isSafe = null;
	VNode argSym = null;
	VElem top = null;
	VElem domTop=null;

	for(BiLink pp= v.predList().first();!pp.atEnd();pp=pp.next()){
	    BasicBlk p=(BasicBlk)pp.elem();
	    ep=transPhi(e,v,++pNum);

	    if (eqp(ep,p,v,visited)) {
		top = (VElem)stack.pop();
		if (!top.isLater) {
		    isSomeRealAvail = true;
		    isAllLater = false;
		    if (top.isSelf) isSelf = true;
		}

                if (argSym == null) {
		    argSym = top.node;
		}
		else if (argSym != top.node) {
                    isSameArgs = false;
		}
		tmpInsert.add(top);
	    }
	    else {
		isAllLater = false;
		isAllAvail = false;
		isSameArgs = false;
		if (isSafe == null) {
		    isSafe = postEqp(e,v,new LirNode[f.flowGraph().idBound()]);
		    if(isSafe != null) antMap.put(localExpKey,isSafe);
		}

		if (e.opCode == Op.MEM && !memIsHoistable(p,e)) {
		    availMap.put(localExpKey,unavailVar);
		    return false;
		}
		/*
		Symbol sym=sstab.newSsaSymbol(tmpSymName,ep.type);
		LirNode dst = env.lir.symRef(Op.REG,ep.type,sym,ImList.Empty);
		LirNode setNode=env.lir.operator(Op.SET,ep.type,dst,
					      ep.makeCopy(env.lir),ImList.Empty);
		*/
		//bigPhiDefMap.put(((LirSymRef)dst).symbol, new StackElem(setNode, ep, p));
		top = new VElem(new VNode(ep), ep, p);
		tmpInsert.add(top);
	    }
	    if ((!modPhi(e,v)) && dom.dominates(top.blk,v)) domTop = top;
	    
	}	    

	VElem newTop;

	if (((isSomeRealAvail && (isSafe == Boolean.TRUE)) || isAllAvail)  || (isSelf && isLICM)) {

	    if (domTop != null) {
		newTop = new VElem(domTop.node,e,domTop.blk,isAllLater,isSelf);

	    }
	    else {
		/*
		LirNode phi = createPhi(v,e);
		setArgToPhi (phi, v, tmpInsert);
		*/
		VNode phi = new VNode(Op.PHI, e.type);
		phi.operands = tmpInsert;
		/*
		VElem phiElem = new VElem(phi,e,v,isAllLater);
		VNode phiDst = new VNode(Op.REG, e.type);
		bigPhiDefMap.put(phiDst, new VElem(phi,e,v));		
		*/
		newTop = new VElem(phi,e,v,isAllLater,isSelf);
	    }

	    VElem cpDstE = (VElem)cpMap.get(localExpKey);
	    if (cpDstE != null) {
		/*
		LirNode newSet=env.lir.operator(Op.SET,e.type,cpDst,
						newTop.node,ImList.Empty);
		BiLink instLast = v.instrList().last();
		instLast.addBefore(newSet);
		maintainTableInsertExp(instLast.prev(), newSet, v);
		*/
		//bigPhiDefMap.put(cpDstE.node, new VElem(newTop.node, newTop.exp, cpDstE.blk));
		cpDstE.node.rands().add(newTop);
	    }
	    stack.push(newTop);
	    if (!isAllLater)
		availMap.put(localExpKey, newTop);
	    return true;
	}
	else {
	    availMap.put(localExpKey, unavailVar);
	    return false;
	}
    }

    boolean eqp(LirNode e,  BasicBlk v, BasicBlk succ, LirNode[] visited){
	//env.println("EQP : question about "+e+" goes into block "+v.id,THR2);

      if (v == null) return false; // for entry

      if (isOccurWithStackPush(e,v)) {

	  //availMap.put(makeLocalKey(v,e),stackElem.makeCopy());
	  return true;
      }

      // corresponding to isMod
      /*
      BiList operands=util.findTargetLir(e,Op.REG,new BiList());
      for(BiLink q=operands.first();!q.atEnd();q=q.next()){
	  BiLink tq = (BiLink)modMap.get(makeLocalKey(v,(LirNode)q.elem()));
	  if (tq != null) {

	      return false;
	  }
      }
      */
      if (isMod(e,v)) return false;

      if(visited[v.id]!=null && visited[v.id] != e) { 

	  env.println("EQP : question returns FALSE from block "+v.id+
		      " at section 2",THR2);
	  return(false);
      }

      VElem availElem = (VElem)availMap.get(makeLocalKey(v,e));
      if(availElem != null) {

	  if ( availElem == unavailVar) {
	      return false;
	  }
	  else {
     //	      availElem.node = getLeader(availElem.node);
	      stack.push(availElem);
	      return true;
	  }
      }

      if(visited[v.id] == e) {
	  VNode tmpDst = new VNode (Op.REG, e.type);
	  stack.push(new VElem(tmpDst, e, v, true));
	  cpMap.put(makeLocalKey(v,e),new VElem(tmpDst,e,succ));
	  return true;
      }

      visited[v.id] = e;
      boolean result = propagate(e,v,visited);
      //visited[v.id] = null;
      return result;
    }


    /**
     * Check whether the expression e is exist in the basic block v
     * as the right hand side value.
     * @param e The target expression
     * @param v The target basic block
     * @return true if the check is OK
     **/

    private boolean isOccur(LirNode e,BasicBlk v){

      LirNode node = (LirNode)occurMap.get(makeLocalKey(v,e));
      if (node != null) 
	  return true;
      else
	  return false;
    }

    private boolean isOccurWithStackPush(LirNode e,BasicBlk v){
      LirNode node = (LirNode)occurMap.get(makeLocalKey(v,e));

      boolean isSelf = false;
      if (node != null) {

	  if (node.kid(1) == e) isSelf = true;

	  VNode dst = (VNode)vNodeMap.get(((LirSymRef)node.kid(0)).symbol);
	  if (dst == null) dst = new VNode(node.kid(0));
	  VElem elem =  new VElem(dst,e,v,false, isSelf);
	  stack.push(elem);
	  availMap.put(makeLocalKey(v,e),elem);
        env.println("EQP : stack push "+((LirSymRef)node.kid(0)).symbol+
                    " "+v.id,THR2);

        return true;
      }
      else {
	  if (e.opCode == Op.MEM) {
	      node = (LirNode)occurMap.get(makeLocalKey(v,e)+"=");
	      if (node != null) {
		  //stack.push(new StackElem(((LirSymRef)node.kid(1)).symbol,v,true,true));
		  if (node.kid(0) == e) isSelf = true;

		  stack.push(new VElem(new VNode(node.kid(1)),e,v,false,isSelf));
		  return true;
	      }
	  }
	  return false;
      }
    }



    /**
     * Create a new phi instruction in the basic block v.
     * @param v The target basic block
     **/

    private LirNode createPhi(BasicBlk v, LirNode e) {
	// Make a new phi instruction
	Symbol sym=sstab.newSsaSymbol(tmpSymName,e.type);
	if (sym == null) System.err.println("sym==null");
	return util.makePhiInst(sym,v);
    }

    private LirNode setArgToPhi(LirNode phi, BasicBlk v, Vector ins){
      //env.output.println("create phi instruction");
      VElem[] args=new VElem[v.predList().length()];
      int type=-1;
      for(int i = v.predList().length()-1; i >= 0; i--){
        args[i]=(VElem)ins.get(i);
        // Error if there are several types in the argument of the phi
        // instruction
        if(args[i]!=null && args[i].node.opCode == Op.REG){
//System.out.println("args[i].node="+args[i].node);
	    if(type==-1) 
		type= args[i].node.type;
	    else if(type!=args[i].node.type){
		System.err.println("Phi instruction has several types of variable");
		System.err.println("phi node: "+phi.kid(0).toString()+" = phi(...,"+args[i].node.toString()+"...)");
		System.exit(1);
	    }
        }
      }

      // make the arguments of the new phi instruction
      for(int i=0; i < args.length ;i++) {
	  LirNode arg = args[i].node.node;
	  if (arg != null) {
	      if (arg.opCode == Op.REG) arg = arg.makeCopy(env.lir);
	      phi.kid(i+1).setKid(0,arg);
	  }
      }

      return phi;
    }

    /**
     * Check whether the operands of the expression e are modified in the
     * basic block v. Register variables are only permitted for operands
     * of the expression e.
     * @param e The target expression
     * @param v The target basic block
     * @return True if the operands of e are modified in v
     **/
    private boolean isMod(LirNode e,BasicBlk v){
	if (e.opCode == Op.MEM && memArray[v.id]) 
	    return true;
	BiList operands=util.findTargetLir(e,Op.REG,new BiList());
	for(BiLink q=operands.first();!q.atEnd();q=q.next()){
	    if(modMap.get(makeLocalKey(v,(LirNode)q.elem())) != null)
		return true;
	}
	return false;
    }


    /**
     * Replace the operands of e when the phi instruction defines them
     * and the question propagates through the phi instruction.
     * The target basic block of the question is p-th  argument of the phi
     * instruction and the variable which is the result of replacement is 
     * the variable which is concerned with p-th argument.
     * @param e The current expression
     * @param v The current basic block
     * @param p The place of argument of the phi instruction
     * @return The replaced expression
     **/

    private LirNode transPhi(LirNode e,BasicBlk v,int p){
	LirNode result=e.makeCopy(env.lir);

	/*
	if(e == result) {
	    System.out.println("e: "+e+", result: "+result);
	    System.err.println("e == result"); System.exit(1);
	}
	*/

	Stack stk=new Stack();
	stk.push(result);
	
	boolean mod = false;
	while(!stk.empty()){
	    LirNode n=(LirNode)stk.pop();
	    for(int i=0;i<n.nKids();i++){
		if (n.kid(i).opCode == Op.REG) {
		    StackElem phiElem = (StackElem)phiMap.get(((LirSymRef)n.kid(i)).symbol);
		    if(phiElem != null && phiElem.blk == v) {
			LirNode phi = phiElem.node;
			n.setKid(i,phi.kid(p).kid(0).makeCopy(env.lir));
			mod = true;
		    }
		}
		else stk.push(n.kid(i));
	    }
	}
	if (mod) return result;
	else return e;
    }

    private LirNode rTransPhi(LirNode e, BasicBlk v, BasicBlk s) {
	LirNode result=e.makeCopy(env.lir);

	Stack stk=new Stack();
	stk.push(result);
	boolean mod = false;
	while(!stk.empty()){
	    LirNode n=(LirNode)stk.pop();
	    for(int i=0;i<n.nKids();i++){
		if (n.kid(i).opCode == Op.REG) {
		    LirNode phi = (LirNode)rPhiMap.get(makeLocalKey2(v,s,n.kid(i)));
		    if(phi != null) {
			mod = true;
			n.setKid(i,phi.kid(0).makeCopy(env.lir));
		    }
		}
		else stk.push(n.kid(i));
	    }
	}
	if (mod) return result;
	else return e;
    }


    /**
     * Sort the arguments of the phi instruction.
     **/
    private void sortPhiArgs() {
      for(BiLink b=f.flowGraph().basicBlkList.first();!b.atEnd();b=b.next()){
        BasicBlk blk=(BasicBlk)b.elem();
        for(BiLink inst=blk.instrList().first();!inst.atEnd();
            inst=inst.next()){
	    LirNode node=(LirNode)inst.elem();
	    if(node.opCode!=Op.PHI) break;

	    LirNode[] args = new LirNode[node.nKids()];
	    int i = 0;
	    int argN = 1;
	    for(BiLink p=blk.predList().first();!p.atEnd();p=p.next(),argN++){
		BasicBlk pred=(BasicBlk)p.elem();
		for(; true ;i++, i %= node.nKids()-1){
		    LirLabelRef nLab=(LirLabelRef)node.kid(i+1).kid(1);
		    BasicBlk phiPred=nLab.label.basicBlk();
		    if(phiPred == pred) {
			args[argN] = node.kid(i+1);
			i++; i %= node.nKids()-1;
			break;
		    }
		}
	    }

	    for (argN = 1; argN < node.nKids(); argN++) {
		node.setKid(argN,args[argN].makeCopy(env.lir));
	    }
	    //          String key = makePhiKey(blk,node);
	    //          if (key != null) 
	    occurMap.put(makeLocalKey(blk,node), node);
        }
      }
    }

    /**
     * Make keys for management phi instructions by map.
     **/

    /**
     * Make keys for expressions.
     * @param blk The current basic block
     * @param node The current expression
     * @return Key for the specified expression
     **/

    String makeTmpPhiKey(BasicBlk blk, LirNode n) {
	String key = blk.id+":PHI@"+makeExpKey(n);
	return key;
    }

    String makeLocalKey(BasicBlk blk, LirNode n) {
	String key = blk.id+"";
	switch (n.opCode) {
	case Op.PHI: {
	    key+=":PHI";
	    n = n.makeCopy(env.lir);
	    for (int i = 1; i < n.nKids(); i++) {
		key +=  ","+n.kid(i).kid(0).toString();
	    }
	    return key;
	}
	case Op.LIST:
	    return key+","+((LirSymRef)n.kid(0)).symbol.name;
	case Op.REG:
	    return key+","+((LirSymRef)n).symbol.name;
	}
	return key+makeExpKey(n);
    }

    String makeLocalKey2(BasicBlk blk, BasicBlk succ, LirNode n) {
	switch(n.opCode){
	case Op.LIST: n = n.kid(0); break;
	case Op.REG: break;
	default: return null;
	}
	return (blk.id+","+succ.id+((LirSymRef)n).symbol.name);
    }

    String makeExpKey(LirNode n) {
	n = n.makeCopy(env.lir);
	/*
	if ((mode & 0x4) == 0) {
	    switch(n.opCode){
	    case Op.ADD: 
	    case Op.MUL: 

		if (n.kid(0).opCode == Op.REG || n.kid(1).opCode == Op.REG) {
		    if (n.kid(0).opCode == Op.INTCONST || n.kid(0).opCode == Op.FLOATCONST) {
			LirNode tmp = n.kid(1);
			n.setKid(1,n.kid(0));
			n.setKid(0,tmp);
		    }
		    else {
			if (n.kid(0).opCode == Op.REG && n.kid(1).opCode == Op.REG) 
			    if (((LirSymRef)n.kid(0)).symbol.id > ((LirSymRef)n.kid(1)).symbol.id) {
				LirNode tmp = n.kid(1);
				n.setKid(1,n.kid(0));
				n.setKid(0,tmp);
			    }
		    }
		}
		break;
	    }
	}
	*/
	return n.toString();
    }


    Boolean postEqp (LirNode e,  BasicBlk v, LirNode[] pVisited) {
	env.println("POSTEQP : question about "+e+" goes into block "+v.id,THR2);

	Boolean isAnt = (Boolean)antMap.get(makeLocalKey(v,e));
	if (isAnt==Boolean.TRUE) return Boolean.TRUE;
	if (isAnt==Boolean.FALSE) return Boolean.FALSE;

	if(pVisited[v.id]==e){
	  env.println("POSTEQP : question returns TRUE from block "+v.id+
		      " at section 1",THR2);
	  return null;
	}

	if (!initialized[v.id]) localInit(v);

	if(
	   f.flowGraph().exitBlk()==v || // If v is an end block
	   isMod(e,v)
	   ) { // If already visited v
	    env.println("POSTEQP : question returns FALSE from block "+v.id+
			" at section 2",THR2);
	    return(Boolean.FALSE);
	}

	if (isOccur(e,v)) {
	    antMap.put(makeLocalKey(v,e),Boolean.TRUE);
	    return Boolean.TRUE;
	}
	else if (pVisited[v.id]!=null) return Boolean.FALSE;

	pVisited[v.id]=e;

	LirNode ep;
	boolean isNonNull = false;
	for(BiLink ss= v.succList().first();!ss.atEnd();ss=ss.next()){
	    BasicBlk s=(BasicBlk)ss.elem();
	    ep = rTransPhi(e, v, s);
	    Boolean rlstPostEqp = postEqp(ep,s,pVisited);
	    if( rlstPostEqp ==Boolean.FALSE ){
		//		env.println("POSTEQP : stack push "+elem.s+" "+elem.blk.id,THR2);
		antMap.put(makeLocalKey(v,e),Boolean.FALSE);
		return Boolean.FALSE;
	    }
	    else if (rlstPostEqp != null) isNonNull =true;
	}

	if (isNonNull) {
	    antMap.put(makeLocalKey(v,e),Boolean.TRUE);
	    return Boolean.TRUE;
	}
	else return null;
    }

    void maintainTableInsertExp(BiLink q, LirNode node, BasicBlk b) {

	if (q.elem() != node) {
	    System.err.println("Element of BiLink is not node");
	    System.exit(1);
	}

	if (initialized[b.id]) {
	    occurMap.put(makeLocalKey(b, node.kid(1)),node);
	    Symbol s = ((LirSymRef)node.kid(0)).symbol;
	    modMap.put(makeLocalKey(b, node.kid(0)), q);
	}

	BiList operands=util.findTargetLir(node.kid(1),Op.REG,new BiList());
	for(BiLink op=operands.first();!op.atEnd();op=op.next()){
	    String str = ((LirSymRef)op.elem()).symbol.name;
	    Hashtable h = (Hashtable)cpy.variableMap.get(str);
	    if (h == null) {
		h = new Hashtable();
		cpy.variableMap.put(str, h);
	    }
	    
	    String bNKey = cpy.makeBNKey(b,node);
	    if(h.get(bNKey) == null) {
		Object[] pair = {b, q};
		h.put(bNKey,pair);
	    }
	}
    }

    void maintainTableInsertPhi(BiLink q, LirNode node, BasicBlk b) {
	/*
	if (q.elem() != node) {
	    System.err.println("Element of BiLink is not node");
	    System.exit(1);
	}
	*/

	if (initialized[b.id]) {
	    occurMap.put(makeLocalKey(b,node),node);
	    phiMap.put(((LirSymRef)node.kid(0)).symbol, new StackElem(node,b));
	}
	int argN=1;
	for(BiLink p=b.predList().first();!p.atEnd();p=p.next(),argN++){
	    BasicBlk pred=(BasicBlk)p.elem();		    
	    LirNode snode = node.kid(argN);
	    if (snode.kid(0).opCode != Op.REG) continue;
	    if (initialized[b.id]) {
		String key = makeLocalKey2(pred,b,snode);
		rPhiMap.put(key, node);
	    }
	    Hashtable h = (Hashtable)cpy.variableMap.get(((LirSymRef)snode.kid(0)).symbol.name);
	    if (h == null) {
		h = new Hashtable();
		cpy.variableMap.put(((LirSymRef)snode.kid(0)).symbol.name, h);
	    }
	    if(h.get(cpy.makeBNKey(b,node)) == null) {
		Object[] pair = {b,q};
		h.put(cpy.makeBNKey(b,node),pair);
	    }
			
	    // There can be some objects for a key, but we adopt the first object.
	}
    }

    void maintainTableDeleteExp(LirNode node, BasicBlk b) {
	if (initialized[b.id]) {
	    String eKey = makeLocalKey(b,node.kid(1));
	    occurMap.remove(eKey);
	}
	BiList operands=util.findTargetLir(node.kid(1),Op.REG,new BiList());
	for(BiLink q=operands.first();!q.atEnd();q=q.next()){
	    LirNode n = (LirNode)q.elem();
	    if (n.opCode != Op.REG) continue;
	    Hashtable h = (Hashtable)cpy.variableMap.get(((LirSymRef)n).symbol.name);
	    if (h != null) h.remove(cpy.makeBNKey(b,node));
	}
	modMap.remove(makeLocalKey(b,node.kid(0)));
    }

    void maintainTableReplaceExp(LirNode old, LirNode newN,  BasicBlk b) {
	if (!initialized[b.id]) return;

	String expKey = makeLocalKey(b,old.kid(1));
	String expKey2 = makeLocalKey(b,newN.kid(1));
	if (occurMap.get(expKey) != null) 
	    occurMap.remove(expKey);
	occurMap.put(expKey2,newN);
	if (old.kid(0).opCode == Op.MEM && 
	    (old.kid(0).opCode == Op.REG || old.kid(0).opCode == Op.INTCONST || old.kid(0).opCode == Op.FLOATCONST)) {
	    expKey = expKey+"=";
	    expKey2 = expKey2+"=";
	    if (occurMap.get(expKey) != null) 
		occurMap.remove(expKey);
	    occurMap.put(expKey2,newN);
	}
    }

    void maintainTableDeletePhi(LirNode node, LirNode orgNode, BasicBlk b) {
	if (initialized[b.id]) {
	    occurMap.remove(makeLocalKey(b,node));
	    phiMap.remove(((LirSymRef)node.kid(0)).symbol);
	}
	BiLink ps = b.predList().first();
	for (int i = 1; i < node.nKids() && !ps.atEnd(); i++,ps=ps.next()) {
	    BasicBlk p = (BasicBlk)ps.elem();
	    if (initialized[b.id])
		rPhiMap.remove(makeLocalKey2(p,b,node.kid(i)));	      
	    Hashtable h = (Hashtable)cpy.variableMap.get(((LirSymRef)node.kid(i).kid(0)).symbol.name);
	    if (h != null) { //if (h.get(cpy.makeBNKey(b,orgNode))!=null) System.out.println("target exists");
		h.remove(cpy.makeBNKey(b,orgNode));
	    }
	}
    }

    void maintainTableReplacePhi(LirNode old, LirNode newN, BasicBlk b) {
	if (!initialized[b.id]) return;

	String expKey = makeLocalKey(b,old);
	String expKey2 = makeLocalKey(b,newN);
	if (occurMap.get(expKey) != null) 
	    occurMap.remove(expKey);
	occurMap.put(expKey2,newN);
	BiLink ps= b.predList().first();
	for (int i = 1; i < newN.nKids() && !ps.atEnd(); i++,ps=ps.next()) {
		BasicBlk p = (BasicBlk)ps.elem();
		LirNode oldSrc = old.kid(i);
		LirNode newNSrc = newN.kid(i);
		if (oldSrc.kid(0).opCode == Op.REG) rPhiMap.remove(makeLocalKey2(p,b,oldSrc));
		if (newNSrc.kid(0).opCode == Op.REG)  rPhiMap.put(makeLocalKey2(p,b,newNSrc), newN);
	}
    }

    boolean memIsHoistable(BasicBlk target, LirNode e) {
	if(alias.blkRank(target) != ((LirIconst)e.kid(1)).value)
	    return false;
	else return true;
    }
    /*
    LirNode getLeader(LirNode var) {
	LirNode prev = null;
	for(LirNode leader = var; leader != null;
	    prev = leader,
		leader = (LirNode)leaderMap.get(((LirSymRef)leader).symbol)) 
	    System.out.print("*");
	if (var != null && prev != null && ((LirSymRef)var).symbol != ((LirSymRef)prev).symbol) 
	    leaderMap.put(((LirSymRef)var).symbol, prev);
	return prev;
    }
    */
	    
    /**
     * Do optimization using Efficient Question Propagation.
     **/
    void invoke() {

      // Local CSE
      cpy = new DDCopyPropagation(env, f, this);
      antMap = new Hashtable();
      //availMap = new Hashtable();
      //leaderMap = new Hashtable();
      if (mode > 1)
	  memTrace = new MemTrace(f,mode);

      BasicBlk[] bVecInOrderOfRPost = dfst.blkVectorByRPost();
      for (int i = 1; i <  bVecInOrderOfRPost.length; i++) {
	  BasicBlk b = bVecInOrderOfRPost[i];

	  if (!initialized[b.id]) localInit(b);

	  Hashtable map = new Hashtable();
	  for(BiLink pi=b.instrList().first();!pi.atEnd();pi=pi.next()){
	      LirNode node=(LirNode)pi.elem();
	      /*
	      if ((mode & 0x1) != 0) isHoistable = false;
	      else isHoistable = true;
	      */
	      switch(node.opCode){
	      case Op.SET:
		  if(node.kid(0).opCode==Op.REG &&
		     node.kid(1).opCode==Op.REG) {
		      cpy.doIt(b,node.makeCopy(env.lir));
		      pi.unlink();
		      continue;
		  }
		  if(node.kid(0).opCode==Op.MEM && 
		     (node.kid(1).opCode == Op.REG || 
		      node.kid(1).opCode == Op.INTCONST ||
		      node.kid(1).opCode == Op.FLOATCONST)) 
		      map.put(makeExpKey(node.kid(0)),node.kid(1));

		  if(node.kid(0).opCode==Op.REG && 
		     node.kid(1).opCode!=Op.INTCONST &&
		     node.kid(1).opCode!=Op.FLOATCONST &&
		     node.kid(1).opCode!=Op.REG &&
		     node.kid(1).opCode!=Op.CALL &&
		     node.kid(1).opCode!=Op.USE &&
		     //node.kid(1).opCode!=Op.MEM && 
		     //node.kid(1).opCode!=Op.SUBREG && // temoporal addition
		     node.kid(1).opCode!=Op.CLOBBER) {
		      switch (mode) {
		      case 0: isLICM = false; break;
		      case 1: isLICM = true; break;
		      case 3: 
			  if (node.kid(1).opCode == Op.MUL 
			      || node.kid(1).opCode == Op.DIVS
			      || node.kid(1).opCode == Op.DIVU
			      || node.kid(1).opCode == Op.MODS
			      || node.kid(1).opCode == Op.MODU)
			      isLICM = true;
		      case 2: 
			  if (node.kid(0).opCode == Op.MEM 
			      || node.kid(1).opCode == Op.MEM
			      /*
			      || node.kid(1).opCode == Op.CONVSX
			      || node.kid(1).opCode == Op.CONVZX
			      || node.kid(1).opCode == Op.CONVIT
			      || node.kid(1).opCode == Op.CONVFX
			      || node.kid(1).opCode == Op.CONVFT
			      || node.kid(1).opCode == Op.CONVFI
			      || node.kid(1).opCode == Op.CONVSF
			      || node.kid(1).opCode == Op.CONVUF
			      */)
			      isLICM = true;
		      default:
			  if (memTrace.instMap.get(node) != null)
			      isLICM = true;
		      }

		      // Local CSE
		      LirNode ref = (LirNode)map.get(makeExpKey(node.kid(1)));
		      if (ref != null) {
			  
			  LirNode newReg  = ref.makeCopy(env.lir);

			  modMap.remove(makeLocalKey(b,node.kid(0)));
			  node.setKid(1,newReg);
			  cpy.doIt(b,node.makeCopy(env.lir));
			  pi.unlink();
		      }
		      else {
			  // The array size is the number of basic blocks
			  //visited=new LirNode[f.flowGraph().idBound()];
			  
			  // The elements of the list below are the instance of `InsertElem'
			  stack = new Stack();
			  cpMap = new Hashtable();
			  //bigPhiDefMap = new Hashtable();
			  String expStr = makeExpKey(node.kid(1));
			  availMap = new Hashtable();
			  vNodeMap = new Hashtable();
			  maxId = 0;

			  if ((!isMod(node.kid(1),b)) && propagate (node.kid(1), b, new LirNode[f.flowGraph().idBound()])) {

			      VElem elem = (VElem)stack.pop();
			      if (elem == unavailVar || elem.isLater) {

				  map.put(expStr, node.kid(0));
				  continue;
			      }
			      //VNode newReg = elem.node;
			      //bigPhiDefMap.put(((LirSymRef)node.kid(0)).symbol,elem);
			      /*
			      leaderMap.put(((LirSymRef)node.kid(0)).symbol, 
					    newReg.makeCopy(env.lir));
			      */
			      if (modGraph(elem)) {
				  LirNode finalNewReg =  insertPhi(elem);
			      /*
			      if (finalNewReg != null) {
				  if (finalNewReg.opCode != Op.SET) {
				      if (((LirSymRef)finalNewReg).symbol != ((LirSymRef)newReg).symbol) {
					  leaderMap.put(((LirSymRef)newReg).symbol, finalNewReg);
					  newReg =finalNewReg;
				      }

				  }
			      }
			      */

				  /*
				    if (finalNewReg != null && finalNewReg.opCode == Op.REG) {
				  */
				  maintainTableDeleteExp(node,b);
				  
				  node.setKid(1,finalNewReg.makeCopy(env.lir));

				  map.put(expStr, finalNewReg);

				  cpy.doIt(b,node.makeCopy(env.lir)); 
				  pi.unlink();	
			      }
			  }
			  else map.put(expStr, node.kid(0));
		      }
		  }
	      }
	  }
      }
    }

    void localInit(BasicBlk v) {
	initialized[v.id] = true;
	for(BiLink p=v.instrList().first();!p.atEnd();p=p.next()){
	    LirNode node=(LirNode)p.elem();
	  
	    switch(node.opCode){
            case Op.SET:
		if(node.kid(0).opCode==Op.MEM) {
		    if(node.kid(1).opCode==Op.REG || node.kid(1).opCode==Op.INTCONST || node.kid(1).opCode==Op.FLOATCONST) {
			occurMap.put(makeLocalKey(v,node.kid(0))+"=", node);

		    }
		    memArray[v.id] = true;
		}

		if(node.kid(0).opCode==Op.REG) {
		    Symbol s=((LirSymRef)node.kid(0)).symbol;
		    modMap.put(makeLocalKey(v,node.kid(0)), p);
		}
	    
		if(node.kid(0).opCode==Op.REG && 
		   node.kid(1).opCode!=Op.INTCONST &&
		   node.kid(1).opCode!=Op.FLOATCONST &&
		   node.kid(1).opCode!=Op.REG &&
		   node.kid(1).opCode!=Op.CALL &&
		   node.kid(1).opCode!=Op.USE &&
		   //node.kid(1).opCode!=Op.MEM && // temporal addition
		   node.kid(1).opCode!=Op.CLOBBER) {
		    String key = makeLocalKey(v,node.kid(1));
		    if (occurMap.get(key) == null) 
			occurMap.put(key, node);
		}
		break;
            case Op.CALL:
		if(node.kid(2).nKids()>0 && node.kid(2).kid(0).opCode==Op.REG){
		    Symbol s=((LirSymRef)node.kid(2).kid(0)).symbol;
		    modMap.put(makeLocalKey(v,node.kid(2).kid(0)), p);
		}
		break;
            case Op.PHI:
		phiMap.put(((LirSymRef)node.kid(0)).symbol, new StackElem(node,v));
		// It requires that all phi-arguments have been sorted. 
		int argN = 1;

		for(BiLink pr=v.predList().first();!pr.atEnd();pr=pr.next(),argN++){
		    BasicBlk pred=(BasicBlk)pr.elem();		    
		    if (node.kid(argN).kid(0).opCode != Op.REG) continue;
		    rPhiMap.put(makeLocalKey2(pred,v,node.kid(argN)), node);
		}
		break;
	    }
	}
    }

  /**
   * Do optimize using Efficient Question Propagation.
   * @param f The current function
   **/
    public boolean doIt(Function function,ImList args) {
      //

      long startTime = System.currentTimeMillis();

      //
    f = function;
    util=new Util(env,f);
    env.println("****************** doing PREQP to "+
    f.symbol.name,SsaEnvironment.MinThr);
    alias=new MemoryAliasAnalyze(env,f);

    // 1/3 
    dfst=(DFST)f.require(DFST.analyzer);
    dom=(Dominators)f.require(Dominators.analyzer);

    // Check the occurence of each expressions
    modMap = new Hashtable();
    phiMap = new Hashtable();
    rPhiMap = new Hashtable();
    occurMap = new Hashtable();

    initialized = new boolean[f.flowGraph().idBound()];

    // Sort the arguments of all phi instructions
    sortPhiArgs();
    /*    memArgs = new Hashtable();*/
    memArray = new boolean[f.flowGraph().idBound()];
    /*

    for(BiLink pp=f.flowGraph().basicBlkList.first();!pp.atEnd();pp=pp.next()){
        BasicBlk v=(BasicBlk)pp.elem();
	for(BiLink p=v.instrList().first();!p.atEnd();p=p.next()){
	    LirNode node=(LirNode)p.elem();
	  
	    switch(node.opCode){
            case Op.SET:
		if(node.kid(0).opCode==Op.MEM && (node.kid(1).opCode==Op.REG || 
						  node.kid(1).opCode==Op.INTCONST || 
						  node.kid(1).opCode==Op.FLOATCONST)) {
		    occurMap.put(makeLocalKey(v,node.kid(0))+"=", node);

		}

		if(node.kid(0).opCode==Op.REG) {
		    Symbol s=((LirSymRef)node.kid(0)).symbol;
		    modMap.put(makeLocalKey(v,node.kid(0)), p);
		}
	    
		if(node.kid(0).opCode==Op.REG && 
		   node.kid(1).opCode!=Op.INTCONST &&
		   node.kid(1).opCode!=Op.FLOATCONST &&
		   node.kid(1).opCode!=Op.REG &&
		   node.kid(1).opCode!=Op.CALL &&
		   node.kid(1).opCode!=Op.USE &&
		   //node.kid(1).opCode!=Op.MEM && // temporal addition
		   node.kid(1).opCode!=Op.CLOBBER) {
		    String key = makeLocalKey(v,node.kid(1));
		    if (occurMap.get(key) == null) 
			occurMap.put(key, node);
		}
		break;
            case Op.CALL:
		if(node.kid(2).nKids()>0 && node.kid(2).kid(0).opCode==Op.REG){
		    Symbol s=((LirSymRef)node.kid(2).kid(0)).symbol;
		    modMap.put(makeLocalKey(v,node.kid(2).kid(0)), p);
		}
		break;
            case Op.PHI:
		phiMap.put(((LirSymRef)node.kid(0)).symbol, new StackElem(node,v));
		// It requires that all phi-arguments have been sorted. 
		int argN = 1;
		for(BiLink pr=v.predList().first();!pr.atEnd();pr=pr.next(),argN++){
		    BasicBlk pred=(BasicBlk)pr.elem();		    
		    if (node.kid(argN).kid(0).opCode != Op.REG) continue;
		    rPhiMap.put(makeLocalKey2(pred,v,node.kid(argN)), node);
		}
		break;
	    }
	}

    }
*/


    // 1/3
        /*
       System.out.println("------------------------ input ----------------------------------");
    
       f.flowGraph().printIt(new java.io.PrintWriter(System.out, true)); 
       System.out.println("--------------------------  end  --------------------------------");
       */


    /*
    if (f.toString().equals("<Function get_pin>")) {
	f.flowGraph().printIt(new java.io.PrintWriter(System.out, true)); 
        System.out.println("================================================");
    }
    */
    invoke();
    alias.annul();

    //(new MakeLargeExp (env)).doIt(f, ImList.Empty);

    //    if (f.toString().equals("<Function get_pin>"))
    /*
    System.out.println("------------------------ output ----------------------------------");    
    f.flowGraph().printIt(new java.io.PrintWriter(System.out, true)); 
    System.out.println("--------------------------  end  --------------------------------");
    */
    //

    /*
    long stopTime = System.currentTimeMillis();
    System.out.println("\t"+(stopTime-startTime));
    */

    //
    f.flowGraph().touch();
    return(true);
  }
}

