/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */

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
import coins.backend.sym.Symbol;
import coins.backend.util.ImList;
import java.util.Hashtable;
import java.util.Stack;
import java.util.Vector;
import java.util.Enumeration;
import coins.backend.lir.LirIconst;
import coins.ssa.BitVector;

/**
 * Demand driven partial dead code elimination.
 **/
public class DCE implements LocalTransformer {
  /** Debug flag **/
    private boolean debugFlag;

    public boolean doIt(Data data, ImList args) { return true; }
  // Begin(2009.1.23)
//    public String name() { return "PREQP"; }
    public String name() { return "DCE"; }
// End(2009.1.2)
    public String subject() {
	return "Optimizatin with efficient question propagation.";
    }

  /** The utility class **/
    private Util util;
  /** The temporary SSA symbol name **/
    private String tmpSymName="_pdeqp";
    public static final int THR=SsaEnvironment.OptThr;
    /** The threshold of debug print **/
    public static final int THR2=SsaEnvironment.AllThr;
  /** The current SSA environment **/
    private SsaEnvironment env;
  /** The current SSA symbol table **/
    private SsaSymTab sstab;
  /** The current function **/
    private Function f;

    Hashtable idMap;
    Hashtable dstMap;
    Hashtable[] candMaps;

    Vector stmtq;
    Stack stack;
    
    BitVector[] used;
    BitVector[] mod;
    BitVector[] ndead;
    BitVector[] xdead;

    int stmtId = 0;
    int idBound;

    // for exhaustive execution
    boolean mode = false;
    boolean modified = false;

  /**
   * Constructor.
   * @param e The environment of the SSA module
   * @param tab The current SSA symbol table
   **/
    public DCE(SsaEnvironment e, SsaSymTab tab){
      env=e;
      sstab=tab;
    }

    public DCE(SsaEnvironment e, SsaSymTab tab, String ex){
      env=e;
      sstab=tab;
      // for exhaustive execution
      mode = true;
    }


  /**
   * Make a key from an expression and a basic block.
   * @param blk The specified basic block
   * @param n The specified expression
   **/
    LirNode mkKey(LirNode n) {
	return n.makeCopy(env.lir);
    }

    void collectStmt() {


	for(BiLink pp=f.flowGraph().basicBlkList.first();!pp.atEnd();pp=pp.next()){
	    BasicBlk v=(BasicBlk)pp.elem();


	    for(BiLink p=v.instrList().first();!p.atEnd();p=p.next()){
		LirNode node=(LirNode)p.elem();


		switch(node.opCode){
		case Op.SET:
		    if(node.kid(0).opCode==Op.REG && 
		       node.kid(1).opCode!=Op.CALL &&
		       node.kid(1).opCode!=Op.USE &&
		       node.kid(1).opCode!=Op.SUBREG && // temoporal addition
		       node.kid(1).opCode!=Op.CLOBBER) {
			LirNode dst = node.kid(0);

			// id をふる
			Integer id = (Integer)idMap.get(node);
			if (id == null) {
			    id = new Integer(stmtId++);
			    idMap.put(mkKey(node), id);
			    stmtq.add(node);
			}
			/*
			if (node.kid(1).opCode ==Op.MEM) 
			    memq.add(id);
			*/
		    }
		}
	    }

	}	
    }


    /**
     * Initialize the information of the node.
     * @param v The specified node
     **/

    void setUsed(LirNode node, BitVector used, BitVector mod) {
	BiList regs=util.findTargetLir(node,Op.REG,new BiList());			
	for(BiLink rq=regs.first();!rq.atEnd();rq=rq.next()){
	    Symbol s = ((LirSymRef)rq.elem()).symbol;
	    Enumeration keys = idMap.keys();
	    while (keys.hasMoreElements()) {
		LirNode key = (LirNode)keys.nextElement();
		Integer iD =  (Integer)idMap.get(key);
		int id = iD.intValue();
		if (((LirSymRef)key.kid(0)).symbol == s) {
		    used.setBit(id);
		    // mod.resetBit(id);
		}
	    }
	}
    }

    void setMod(LirNode dst, BitVector used, BitVector mod) {
	//locdelayed[v.id].setBit(iD.intValue());

	Enumeration keys = idMap.keys();
	while (keys.hasMoreElements()) {
	    LirNode key = (LirNode)keys.nextElement();

	    Symbol dstS = ((LirSymRef)dst).symbol;
	    Symbol keyS = ((LirSymRef)key.kid(0)).symbol;
	    Integer iD = (Integer)idMap.get(key);
	    int id = iD.intValue();
	    if(keyS == dstS) {
		mod.setBit(id);
		used.resetBit(id);
	    }
	}
    }

    void cancelUsed (LirNode node, Hashtable dceMap) {
	BiList regs=util.findTargetLir(node,Op.REG,new BiList());			
	for(BiLink rq=regs.first();!rq.atEnd();rq=rq.next()){
	    LirNode dst = (LirSymRef)rq.elem();
	    if (dceMap.get(dst) != null) 
		dceMap.remove(dst);
	}
    }

    void initLocal() {
	for(BiLink pp=f.flowGraph().basicBlkList.first();!pp.atEnd();pp=pp.next()){
	    BasicBlk v=(BasicBlk)pp.elem();

	    Hashtable liveMap = new Hashtable();
	    for(BiLink p=v.instrList().last();!p.atEnd();p=p.prev()){
		LirNode node=(LirNode)p.elem();

		switch(node.opCode){
		case Op.SET:
		    if(node.kid(0).opCode==Op.REG) {	    
			LirNode dst = node.kid(0);
			LirNode src = node.kid(1);
		
			//for dead code
			//BiLink lk = (BiLink)liveMap.get(dst);
			//if (lk != null) {
			Integer iD = (Integer)idMap.get(node);
			if (iD != null && used[v.id].getBit(iD.intValue()) == 0 && mod[v.id].getBit(iD.intValue()) == 1) {
			    p.unlink();
			    continue;
			}
			else if ( node.kid(1).opCode!=Op.CALL &&
				  node.kid(1).opCode!=Op.USE &&
				  node.kid(1).opCode!=Op.SUBREG && 
				  node.kid(1).opCode!=Op.CLOBBER) {
			    liveMap.put(mkKey(dst), p);
			    //Integer iD =  (Integer)idMap.get(node);
			    if (iD != null) {
				int id = iD.intValue();
				if (used[v.id].getBit(id) == 0) 
				    candMaps[v.id].put(iD, p);
			    }
			}

			// for dead code
			setMod(dst, used[v.id], mod[v.id]);
			setUsed(src, used[v.id], mod[v.id]);
			cancelUsed(src, liveMap);
		    }
		    else {
			// for dead code
			cancelUsed(node, liveMap);
			setUsed(node, used[v.id], mod[v.id]);
		    }
		    break;
		case Op.CALL:
		    if(node.kid(2).nKids()>0 && node.kid(2).kid(0).opCode==Op.REG){
			if (node.kid(2).nKids() > 1) {
			    System.err.println("too many return values");
			    System.exit(1);
			}

			liveMap.put(mkKey(node.kid(2).kid(0)), p);
		/*
		BiLink lk = (BiLink)dceMap.get(node.kid(2).kid(0));
		if (lk != null) {
		    p.unlink();
		    return true;
		}
		*/
			setMod(node.kid(2).kid(0), used[v.id], mod[v.id]);
			for (int i = 0; i < node.nKids(); i++) {
			    if (i == 2) 
				// for code sinking
				continue;
			    
			    setUsed(node.kid(i), used[v.id], mod[v.id]);
			    cancelUsed(node.kid(i), liveMap);
			}
		    }
		    else {
			// for dead code
			setUsed(node, used[v.id], mod[v.id]);
			cancelUsed(node, liveMap);
		    }
		    break;
		default: 
		    // for dead code
		    setUsed(node, used[v.id], mod[v.id]);
		    cancelUsed(node, liveMap);
		}
	    }
	}
    }


    void init () {
	initLocal();
	stack = new Stack();

	for(BiLink bb=f.flowGraph().basicBlkList.first();!bb.atEnd();bb=bb.next()){
	    BasicBlk v=(BasicBlk)bb.elem();

	    // 各節について，in から out を計算．
	    BitVector notused = new BitVector(stmtId);
	    BitVector plus = new BitVector(stmtId);
	    used[v.id].vectorNot(notused);
	    xdead[v.id].vectorOr(mod[v.id], ndead[v.id]);
	    notused.vectorAnd(ndead[v.id], ndead[v.id]);
	    long[] inWords = ndead[v.id].getVectorWord();

	    // out のいずれかのビットが0なら，stack に覚える．
	    for (int i = 0; i < ndead[v.id].getWordLength(); i++)
		if (inWords[i] != ~0x0) {
		    Object[] pair = {v, i};
		    stack.push(pair);
		}
	}
    }
    

    void settle () {
	// stack から取り出し，伝播させる．
	while(!stack.empty()) {
	    Object[] pair = (Object[])stack.pop();
	    BasicBlk v = (BasicBlk)pair[0];
	    int id = ((Integer)pair[1]).intValue();
	    propagate(v,id);
	}
    }
	

    void propagate ( BasicBlk v, int id) {
	// 後続節への伝播．
	for(BiLink ss= v.predList().first();!ss.atEnd();ss=ss.next()){
	    BasicBlk pred = (BasicBlk)ss.elem();
	    // 後続節の in を更新．
	    xdead[pred.id].getVectorWord()[id] &= ndead[v.id].getVectorWord()[id];

	    long old = ndead[pred.id].getVectorWord()[id];
	    // 後続節の in から out を計算．
	    ndead[pred.id].getVectorWord()[id] = (~used[pred.id].getVectorWord()[id]) & 
		(xdead[pred.id].getVectorWord()[id] | mod[pred.id].getVectorWord()[id]);
	    // out に変化があれば，さらに伝播．
	    if (old != ndead[pred.id].getVectorWord()[id]) 
		propagate(pred, id);
	}
    }

    void update () {
	// 実際に，式を除去する．

	for(BiLink pp=f.flowGraph().basicBlkList.first();!pp.atEnd();pp=pp.next()){
	    BasicBlk v=(BasicBlk)pp.elem();
	    
	    for (int i = 0; i < stmtId; i++) {
		if (xdead[v.id].getBit(i) == 1) {
		    LirNode node = (LirNode)stmtq.elementAt(i);
		    BiLink l = (BiLink)candMaps[v.id].get(new Integer(i));
		    if (l != null && ((LirNode)l.elem()).opCode != Op.CALL) {
			l.unlink();
			// for exhaustive execution
			modified = true;
		    }
		}
	    }
	}
    }
		    
    void result() {
	for(BiLink bb=f.flowGraph().basicBlkList.first();!bb.atEnd();bb=bb.next()){
	    BasicBlk v=(BasicBlk)bb.elem();
	    
	    System.out.println("["+v.id+"]");
	    for(BiLink ss= v.succList().first();!ss.atEnd();ss=ss.next()){
		BasicBlk succ = (BasicBlk)ss.elem();
		System.out.println("\t-> ["+succ.id+"]");
	    }
	    System.out.print("\tused:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+used[v.id].getBit(i));
	    System.out.print("\n\tmod:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+mod[v.id].getBit(i));
	    System.out.print("\n\tndead:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+ndead[v.id].getBit(i));
	    System.out.print("\n\txdead:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+xdead[v.id].getBit(i));
	    System.out.print("\n\tninsert:\t");

	    System.out.print("\n");
	    for (int j = 0; j < stmtId; j++) 
		System.out.println ("\t"+j+": "+
				    ((LirNode)stmtq.elementAt(j)).toString());
	    Enumeration lives = candMaps[v.id].elements();
	    while(lives.hasMoreElements()) {
		BiLink ll = (BiLink)lives.nextElement();
		LirNode live = (LirNode)ll.elem();
		Integer iD = (Integer)idMap.get(live);
		int id = iD.intValue();
		if (xdead[v.id].getBit(id) == 1) System.out.print("*");
		System.out.println("\tc["+id+"]: "+live.toString());
	    }
	}
    }


    /**
     * Invoke the main routine of DCE.
     **/
    void invoke() {

	idMap = new Hashtable();
	dstMap = new Hashtable();
	candMaps = new Hashtable[idBound];
	//	memq = new Vector();
	stmtq = new Vector();

	used = new BitVector[idBound];
	mod  = new BitVector[idBound];
	ndead = new BitVector[idBound];
	xdead = new BitVector[idBound];
	
	collectStmt();

	for (int i = 0; i < f.flowGraph().idBound(); i++) {
	    used[i] = new BitVector(stmtId);
	    mod[i] = new BitVector(stmtId);
	    ndead[i] = new BitVector(stmtId);
	    xdead[i] = new BitVector(stmtId);

	    xdead[i].vectorNot(xdead[i]);
	    //xdelayed[i].vectorNot(xdelayed[i]);

	    candMaps[i] = new Hashtable();
	}

	init();
	settle();
	update();

    }


    /**
     * Do Demand driven partial dead code elimination.
     * @param function The current function
     * @param args The list of options
     **/
    public boolean doIt(Function function,ImList args) {

	f = function;
	idBound = f.flowGraph().idBound();
	util=new Util(env,f);
	env.println("****************** doing DCE to "+
//
		    f.symbol.name,SsaEnvironment.MinThr);

	//	result();

	invoke();

	/*
	  if (f.symbol.name.intern() == "getAndMoveToFrontDecode".intern())
	  f.flowGraph().printIt(new java.io.PrintWriter(System.out, true)); 
	*/
	//	result();

	f.flowGraph().touch();

	if (mode) return modified;
	else return(true);
    }
}

