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
public class CS implements LocalTransformer {
  /** Debug flag **/
    private boolean debugFlag;

    public boolean doIt(Data data, ImList args) { return true; }
  // Begin(2009.1.23)
//    public String name() { return "PREQP"; }
    public String name() { return "CS"; }
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
    Hashtable[] candMap;
    Vector memq;
    Vector stmtq;
    Stack stack;
    
    BitVector[] locblocked;
    BitVector[] locdelayed;
    BitVector[] ndelayed;	
    BitVector[] xdelayed;
    BitVector[] ninsert;
    BitVector[] xinsert;

    int stmtId = 0;
    int idBound;

    // for exhaustive execution
    boolean mode = false; // if you would like to perform it in exhaustive, set the mode true
    boolean modified = false;

  /**
   * Constructor.
   * @param e The environment of the SSA module
   * @param tab The current SSA symbol table
   **/
    public CS(SsaEnvironment e, SsaSymTab tab){
      env=e;
      sstab=tab;
    }

    public CS(SsaEnvironment e, SsaSymTab tab, String ex){
      env=e;
      sstab=tab;
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
			// id をふる
			Integer id = (Integer)idMap.get(node);
			if (id == null) {
			    id = new Integer(stmtId++);
			    idMap.put(mkKey(node), id);
			    stmtq.add(node);
			}
			BiList mems=util.findTargetLir(node.kid(1),Op.MEM,new BiList());
			if (mems.length() > 0)
			    memq.add(id);
		    }
		    break;
		}
	    }
	}	
    }


    /**
     * Initialize the information of the node.
     * @param v The specified node
     **/

    void setBlk(LirNode dst, BasicBlk v) {
	//locdelayed[v.id].setBit(iD.intValue());

	Enumeration keys = idMap.keys();
	while (keys.hasMoreElements()) {
	    LirNode key = (LirNode)keys.nextElement();

	    Symbol dstS = ((LirSymRef)dst).symbol;
	    Integer iD = (Integer)idMap.get(key);
	    int id = iD.intValue();
	    //System.out.println("stmtId="+stmtId+", id="+id);
	    BiList regs=util.findTargetLir(key,Op.REG,new BiList());			
	    for(BiLink rq=regs.first();!rq.atEnd();rq=rq.next()){
		Symbol s = ((LirSymRef)rq.elem()).symbol;
		if (s == dstS){
		    locblocked[v.id].setBit(id);
		    locdelayed[v.id].resetBit(id);
		    candMap[v.id].remove(key);
		    break;
		}
	    }
	}
    }

    void setBlkU(LirNode node, BasicBlk v) {
	BiList refs=util.findTargetLir(node,Op.REG,new BiList());
	for(BiLink rl=refs.first();!rl.atEnd();rl=rl.next()){
		Symbol sref = ((LirSymRef)rl.elem()).symbol;
		Enumeration keys = idMap.keys();
		while (keys.hasMoreElements()) {
		    LirNode key = (LirNode)keys.nextElement();
		    Symbol dstS = ((LirSymRef)key.kid(0)).symbol;
		    if (sref == dstS) {
			Integer iD = (Integer)idMap.get(key);
			int id = iD.intValue();
			
			locblocked[v.id].setBit(id);
			locdelayed[v.id].resetBit(id);
			candMap[v.id].remove(key);
		    }
		}
	}
    }
	
    void setMem(BasicBlk v) {
	for (int i = 0; i < memq.size(); i++) {
	    Integer mID = (Integer)memq.elementAt(i);
	    int mid = mID.intValue();
	    LirNode mem = (LirNode)stmtq.elementAt(mid);

	    locblocked[v.id].setBit(mid);
	    locdelayed[v.id].resetBit(mid);
	    candMap[v.id].remove(mem);
	}
    }


    void initLocal() {
	for(BiLink pp=f.flowGraph().basicBlkList.first();!pp.atEnd();pp=pp.next()){
	    BasicBlk v=(BasicBlk)pp.elem();
	    for(BiLink p=v.instrList().first();!p.atEnd();p=p.next()){
		LirNode node=(LirNode)p.elem();

		switch(node.opCode){
		case Op.SET:

		if (node.kid(0).opCode==Op.MEM) {
		    setMem(v);
		    setBlkU(node,v);
		}
		else if(node.kid(0).opCode==Op.REG) {	    
		    LirNode dst = node.kid(0);
		    LirNode src = node.kid(1);

		    setBlk(dst,v);
		    setBlkU(src,v);

		    Integer iD = (Integer)idMap.get(node);
		    int id = iD.intValue();
		    if (iD != null) {
			locdelayed[v.id].setBit(iD.intValue());
			candMap[v.id].put(mkKey(node), p);
		    }
		}
		else setBlkU(node,v);
		break;

		case Op.CALL:
		    if (node.kid(2).nKids()>0 && node.kid(2).kid(0).opCode == Op.REG) 
			for(int i = 0; i < node.nKids(); i++) {
			    if (i == 2) 
				setBlk(node.kid(2).kid(0),v);
			    else
				setBlkU(node.kid(i),v);
			}
		    else
			setBlkU(node,v);
		    setMem(v);
		    break;
		default: setBlkU(node,v);
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
	    BitVector notblocked = new BitVector(stmtId);
	    BitVector prod = new BitVector(stmtId);
	    locblocked[v.id].vectorNot(notblocked);
	    ndelayed[v.id].vectorAnd(notblocked, prod);
	    locdelayed[v.id].vectorOr(prod, xdelayed[v.id]);
		
	    long[] outWords = xdelayed[v.id].getVectorWord();

	    // out のいずれかのビットが0なら，stack に覚える．
	    for (int i = 0; i < xdelayed[v.id].getWordLength(); i++)
		if (outWords[i] != ~0x0) {
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
	for(BiLink ss= v.succList().first();!ss.atEnd();ss=ss.next()){
	    BasicBlk succ = (BasicBlk)ss.elem();
	    // 後続節の in を更新．
	    ndelayed[succ.id].getVectorWord()[id] &= xdelayed[v.id].getVectorWord()[id];

	    long old = xdelayed[succ.id].getVectorWord()[id];
	    // 後続節の in から out を計算．
	    xdelayed[succ.id].getVectorWord()[id] = locdelayed[succ.id].getVectorWord()[id] | 
		(ndelayed[succ.id].getVectorWord()[id] & (~(locblocked[succ.id].getVectorWord()[id])));
	    // out に変化があれば，さらに伝播．
	    if (old != xdelayed[succ.id].getVectorWord()[id]) 
		propagate(succ, id);
	}
    }

    void update () {
	// 実際に，式を除去する．

	for(BiLink pp=f.flowGraph().basicBlkList.first();!pp.atEnd();pp=pp.next()){
	    BasicBlk v=(BasicBlk)pp.elem();
	    
	    for (int i = 0; i < xdelayed[v.id].getWordLength(); i++) {
		ninsert[v.id].getVectorWord()[i] = ndelayed[v.id].getVectorWord()[i] & locblocked[v.id].getVectorWord()[i];

		for(BiLink ss= v.succList().first();!ss.atEnd();ss=ss.next()){
		    BasicBlk succ = (BasicBlk)ss.elem();
		    xinsert[v.id].getVectorWord()[i] |= ~ndelayed[succ.id].getVectorWord()[i];
		}
		xinsert[v.id].getVectorWord()[i] = xdelayed[v.id].getVectorWord()[i] & xinsert[v.id].getVectorWord()[i];
	    }

	    Enumeration rms = candMap[v.id].elements();
	    while (rms.hasMoreElements()) 
		((BiLink)rms.nextElement()).unlink();

	    for (int j = 0; j < stmtId; j++) {

		if (ninsert[v.id].getBit(j) == 1) {
		    LirNode node = (LirNode)stmtq.elementAt(j);
		    v.instrList().first().addBefore(node.makeCopy(env.lir));
		}
		if (xinsert[v.id].getBit(j) == 1) {
		    LirNode node = (LirNode)stmtq.elementAt(j);
		    v.instrList().last().addBefore(node.makeCopy(env.lir));
		}

		// for exhaustive execution
		if (xinsert[v.id].getBit(j) == 0 && locdelayed[v.id].getBit(j) == 1) modified = true;
	    }
	}
    }

		    
    /**
     * Invoke the main routine of CS.
     **/
    void invoke() {

	idMap = new Hashtable();
	dstMap = new Hashtable();
	memq = new Vector();
	stmtq = new Vector();

	locblocked = new BitVector[idBound];
	locdelayed = new BitVector[idBound];
	ndelayed = new BitVector[idBound];	
	xdelayed = new BitVector[idBound];
	ninsert = new BitVector[idBound];
	xinsert = new BitVector[idBound];

	candMap = new Hashtable[idBound];
	
	collectStmt();

	for(BiLink bb=f.flowGraph().basicBlkList.first();!bb.atEnd();bb=bb.next()){
	    BasicBlk v=(BasicBlk)bb.elem();

	    locblocked[v.id] = new BitVector(stmtId);
	    locdelayed[v.id] = new BitVector(stmtId);
	    ndelayed[v.id] = new BitVector(stmtId);
	    xdelayed[v.id] = new BitVector(stmtId);
	    ninsert[v.id] = new BitVector(stmtId);
	    xinsert[v.id] = new BitVector(stmtId);

	    candMap[v.id] = new Hashtable();

	    if (v != f.flowGraph().entryBlk() &&
		v != f.flowGraph().exitBlk())
		ndelayed[v.id].vectorNot(ndelayed[v.id]);
	}

	init();
	settle();
	update();
    }


    void result() {
	for(BiLink bb=f.flowGraph().basicBlkList.first();!bb.atEnd();bb=bb.next()){
	    BasicBlk v=(BasicBlk)bb.elem();
	    
	    System.out.println("["+v.id+"]");
	    for(BiLink ss= v.succList().first();!ss.atEnd();ss=ss.next()){
		BasicBlk succ = (BasicBlk)ss.elem();
		System.out.println("\t-> ["+succ.id+"]");
	    }
	    System.out.print("\tlocblocked:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+locblocked[v.id].getBit(i));
	    System.out.print("\n\tlocdelayed:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+locdelayed[v.id].getBit(i));
	    System.out.print("\n\tndelayed:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+ndelayed[v.id].getBit(i));
	    System.out.print("\n\txdelayed:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+xdelayed[v.id].getBit(i));
	    System.out.print("\n\tninsert:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+ninsert[v.id].getBit(i));
	    System.out.print("\n\txinsert:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+xinsert[v.id].getBit(i));

	    System.out.print("\n");
	    for (int j = 0; j < stmtId; j++) 
		System.out.println ("\t"+j+": "+
				    ((LirNode)stmtq.elementAt(j)).toString());
	}
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
	env.println("****************** doing CS to "+
//
		    f.symbol.name,SsaEnvironment.MinThr);

	invoke();
	
	//result();

	f.flowGraph().touch();

	if (mode) return modified;
	else return(true);
    }
}

