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
import coins.backend.ana.ReverseDFST;
import coins.backend.ana.DominanceFrontiers;
import java.util.Hashtable;
import java.util.Stack;
import java.util.Vector;
import java.util.Enumeration;
import coins.backend.lir.LirIconst;

/**
 * Demand driven partial dead code elimination.
 **/
public class PDEQP implements LocalTransformer {
  /** Debug flag **/
    private boolean debugFlag;

    public boolean doIt(Data data, ImList args) { return true; }
  // Begin(2009.1.23)
//    public String name() { return "PREQP"; }
    public String name() { return "PDEQP"; }
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
    private LirNode[] pVisited; // visited' : for postEQP

/** Reverse Depth First Spanning Tree of the CFG. */
    private ReverseDFST dfst;

  /** The map of occurrence **/
    Hashtable occurMap;
  /** The map of modification **/
    Hashtable modMap;
  /** The map of usedness **/
    Hashtable usedMap;
  /** The map of  **/
    Hashtable deadMemMap;
    Hashtable usedMemMap;
    
    Hashtable tmpMap;
    Boolean[] answer;
    Boolean[] safe;

    // FBitVector is a flexible bit vector
    FBitVector stVisited;

    Vector bro;
    BitVector broVec;
    BitVector insVec;
    BitVector loadedMemVec;
    BitVector storedMemVec;
    BitVector anyStoredMemVec;
    BitVector anyLoadedMemVec;

  /** The initialized flags **/
    boolean initialized[];
  /** The current dominance frontiers **/
    DominanceFrontiers df;
  /** The current dominance forontier flags **/
    BitVector dfs;

  /** The size of symbols **/
    int idBound;

  /**
   * Constructor.
   * @param e The environment of the SSA module
   * @param tab The current SSA symbol table
   **/
    public PDEQP(SsaEnvironment e, SsaSymTab tab){
      env=e;
      sstab=tab;
    }

    public BasicBlk[] blkVectorByRPost(ReverseDFST dfst) {
	BasicBlk[] vec = new BasicBlk[dfst.maxDfn + 1];
	for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
	    BasicBlk blk = (BasicBlk)p.elem();
	    if (dfst.dfn[blk.id] != 0)
		vec[dfst.dfn[blk.id]] = blk;
	}
	return vec;
    }

  /**
   * Check critical edges.
   **/
    public void eSpltCheck() {
	for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
		BasicBlk blk=(BasicBlk)p.elem();
		if (blk.predList().length() > 1) {
		    for(BiLink ss= blk.predList().first();!ss.atEnd();ss=ss.next()){
			BasicBlk s=(BasicBlk)ss.elem();
			if (s.succList().length() > 1) {
			    System.err.println("Edge splitting is uncomplete");
			    System.exit(1);
			}
		    }
		}
	}
    }
		    

    /**
     * Split self-modified statements.
     **/
    public void stmtSplt() {
	for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
		BasicBlk blk=(BasicBlk)p.elem();
		for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
		    LirNode node=(LirNode)q.elem();
		    switch(node.opCode) {
		    case Op.SET: 
			if (node.kid(0).opCode == Op.REG &&
			    node.kid(1).opCode!=Op.CALL &&
			    node.kid(1).opCode!=Op.USE &&
			    node.kid(1).opCode!=Op.SUBREG && // temoporal addition
			    node.kid(1).opCode!=Op.CLOBBER) {
			    LirNode dst = node.kid(0);
			    LirNode refs = node.kid(1);
			    BiList operands=util.findTargetLir(refs,Op.REG,new BiList());
			    for(BiLink qq=operands.first();!qq.atEnd();qq=qq.next()){
				LirNode refReg = (LirNode)qq.elem();
				if (((LirSymRef)refReg).symbol == ((LirSymRef)dst).symbol) {
				    LirNode tmp = (LirNode)tmpMap.get(makeExpKey(node));
				    if (tmp == null) {
					Symbol sym=sstab.newSsaSymbol(tmpSymName,dst.type);
					if (sym == null) {
					    System.err.println("no tmp");
					    System.exit(1);
					}
					tmp = env.lir.symRef(Op.REG, dst.type, sym,ImList.Empty);
					tmpMap.put(makeExpKey(node), tmp);
				    }
				    LirNode newStmt = env.lir.operator(Op.SET, dst.type, tmp.makeCopy(env.lir),
								    refs.makeCopy(env.lir),ImList.Empty);
				    node.setKid(1,tmp.makeCopy(env.lir));
				    q.addBefore(newStmt);
				    break;
				}
			    }
			}
		    }
		}
	}
    }

    /**
     * Check whether the specified statement is dead.
     * @param stmt The specified statement
     * @param current 
     * @param v The specified node
     **/
    boolean isDead(LirNode stmt, BiLink current, BasicBlk v) {

	for(BiLink q=current;!q.atEnd(); q=q.next()){
	    LirNode node = (LirNode)q.elem();
	    LirNode ref = node;
	    LirNode dst = null;

	    switch (node.opCode) {
	    case Op.SET: 
		if (node.kid(0).opCode == Op.REG) {
		    dst = node.kid(0);
		    ref = node.kid(1);
		}
		break;
	    case Op.CALL:
		if(node.kid(2).nKids()>0 && node.kid(2).kid(0).opCode==Op.REG){
		    dst = node.kid(2).kid(0);
		    ref = node.makeCopy(env.lir);
		    ref.setKid(2,null);
		}
	    }
		    
	    BiList operands=util.findTargetLir(ref,Op.REG,new BiList());
	    for(BiLink qq=operands.first();!qq.atEnd();qq=qq.next()){
		LirNode reg = (LirNode)qq.elem();
		if (((LirSymRef)reg).symbol == ((LirSymRef)stmt.kid(0)).symbol)
		    return false;
	    }

	    if (dst != null && ((LirSymRef)dst).symbol == ((LirSymRef)stmt.kid(0)).symbol)
		break;
	}

	Stack pool = new Stack();

	for(BiLink s=v.succList().first();!s.atEnd();s=s.next()){	
	    BasicBlk ss = (BasicBlk)s.elem();
	    pool.push(ss);
	}

	boolean[] init = new boolean[idBound];

	while(!pool.empty()) {
	    BasicBlk b = (BasicBlk)pool.pop();

	    if (init[b.id]) continue;
	    init[b.id] = true;
	    for(BiLink q=b.instrList().first();!q.atEnd(); q=q.next()){
		LirNode node = (LirNode)q.elem();
		LirNode ref = node;
		LirNode dst = null;

		switch (node.opCode) {
		case Op.SET: 
		    if (node.kid(0).opCode == Op.REG) {
			dst = node.kid(0);
			ref = node.kid(1);
		    }
		    break;
		case Op.CALL:
		    if(node.kid(2).nKids()>0 && node.kid(2).kid(0).opCode==Op.REG){
			dst = node.kid(2).kid(0);
			ref = node.makeCopy(env.lir);
			ref.setKid(2,null);
		    }
		}
		
		BiList operands=util.findTargetLir(ref,Op.REG,new BiList());
		for(BiLink qq=operands.first();!qq.atEnd();qq=qq.next()){
		    LirNode reg = (LirNode)qq.elem();
		    if (((LirSymRef)reg).symbol == ((LirSymRef)stmt.kid(0)).symbol)
			return false;
		}

		if (dst != null && ((LirSymRef)dst).symbol == ((LirSymRef)stmt.kid(0)).symbol)
		    break;

		if (node == stmt) break;

	    }

	    for(BiLink s=b.succList().first();!s.atEnd();s=s.next()){	
		BasicBlk ss = (BasicBlk)s.elem();
		pool.push(ss);
	    }
	}
	return true;
    }
	

  /**
   * Merge statements.
   **/
    public void stmtMerge() {
	for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
		BasicBlk blk=(BasicBlk)p.elem();
		BiLink q2 = null;
		for(BiLink q=blk.instrList().first();!q.atEnd();q2 = q, q=q.next()){
		    if (q2 == null) continue;

		    LirNode prev = (LirNode)q2.elem();

		    switch(prev.opCode) {
		    case Op.SET: 
			if (prev.kid(0).opCode == Op.REG) {

			    for(BiLink qq=q;!qq.atEnd();qq=qq.next()){
				LirNode other = (LirNode)qq.elem();
				LirNode dst = null;
				
				Vector cand = new Vector();
				Stack pool = new Stack();
				pool.push(other);
				while (!pool.empty()) {
				    LirNode n = (LirNode)pool.pop();
	
				    int i;
				    if (n.opCode == Op.SET) {
					i = 1;
					if (n.kid(0).opCode == Op.REG) dst = n.kid(0);
				    }
				    else i = 0;

				    for(; i < n.nKids(); i++) {
					if (n.opCode == Op.CALL && n.kid(2).nKids() > 0 && 
					    n.kid(2).kid(0).opCode == Op.REG && i == 2) {
					    dst = n.kid(2).kid(0);
					    continue;
					}
					if (n.kid(i).opCode == Op.REG) {
					    if(((LirSymRef)n.kid(i)).symbol == ((LirSymRef)prev.kid(0)).symbol){
						Object[] pair = {n, new Integer(i)};
						cand.add(pair);
					    }
					}
					else pool.push(n.kid(i));
				    }
				}
				
				if (cand.size() > 0) {
				    if (isDead(prev,q.next(),blk)) {
					if (prev.kid(1).opCode == Op.INTCONST || 
					    prev.kid(1).opCode == Op.FLOATCONST ||
					    prev.kid(1).opCode == Op.REG ||
					    prev.kid(1).opCode == Op.FRAME /*||
					    prev.kid(1).opCode == Op.STATIC ||
					    prev.kid(1).opCode == Op.FRAME ||
					    prev.kid(1).opCode == Op.LABEL*/) {
					    for (int j = 0; j < cand.size(); j++) {
						Object[] pair = (Object[])cand.elementAt(j);
						LirNode n = (LirNode)pair[0];
						Integer c = (Integer)pair[1];
						n.setKid(c.intValue(), prev.kid(1).makeCopy(env.lir));
					    }
					    q2.unlink();
					    break;
					}
					else if (cand.size() == 1) {
					    Object[] pair = (Object[])cand.elementAt(0);
					    LirNode n = (LirNode)pair[0];
					    Integer c = (Integer)pair[1];
					    n.setKid(c.intValue(), prev.kid(1).makeCopy(env.lir));
					    q2.unlink();
					    break;
					}
				    }
				    break;
				}

				if (dst != null) {
				    if (((LirSymRef)dst).symbol == ((LirSymRef)prev.kid(0)).symbol)
					break;
				    boolean mod = false;
				    BiList operands=util.findTargetLir(prev.kid(1),Op.REG,new BiList());
				    for(BiLink qq2=operands.first();!qq2.atEnd();qq2=qq2.next()){
					LirNode reg = (LirNode)qq2.elem();
					if (((LirSymRef)dst).symbol == ((LirSymRef)reg).symbol) {
					    mod = true;
					    break;
					}
				    }
				    if (mod) break;
				}
			    }
			}
		    }
		}
	}
    }

    /**
     * Propagate a query.
     * @param st The specified statement
     * @param v The specified node
     * @param canInsert The indicator of the statement insertion
     * @param prevBro
     * @param visited The visited flags
     **/
    Boolean propagate (LirNode st,BasicBlk v, boolean canInsert, Vector prevBro, boolean[] visited) {

	boolean isSafe=true;
	Vector tmpBro = new Vector();
	tmpBro.addAll(prevBro);
	if (canInsert) {
	    if (v.predList().length() > 1) {
		isSafe = postEqp(st, v, tmpBro, new boolean[idBound]);
	    }
// Begin
//	    safe[v.id] = isSafe;
	    safe[v.id] = Boolean.valueOf(isSafe);
// End
	}
	else isSafe = false;

	Boolean result = null;
	if (v.succList().length() == 0) 
	    if (st.kid(0).opCode == Op.MEM/* && st.kid(0).kid(0).opCode != Op.FRAME*/)
		result = Boolean.FALSE;
	    else
		result = Boolean.TRUE;


	Vector results = new Vector();
	for(BiLink ss= v.succList().first();!ss.atEnd();ss=ss.next()){
	    BasicBlk s=(BasicBlk)ss.elem();

	    Boolean tmp = local(st, s, isSafe, tmpBro,  visited);

	    if ((!isSafe) && tmp == Boolean.FALSE) {
		result = Boolean.FALSE;
		break;
	    }

	    if (tmp == Boolean.FALSE)
		results.add(s);

	    if (result != Boolean.TRUE && tmp != null) 
		result = tmp;
	}

	if (result == Boolean.TRUE) {
	    for(int sNum = 0; sNum < results.size(); sNum++) {
		BasicBlk succ = (BasicBlk)results.elementAt(sNum);
		succ.instrList().first().addBefore(st.makeCopy(env.lir));
		maintainTableInsertStmt(st,succ,succ.instrList().first());
	    }

	    if (results.size() > 0) bro.addAll(tmpBro);
	}

	return result;
    }

    /**
     * Check local solutions.
     * @param st The specified statement
     * @param v The specified node
     * @param canInsert The indicator of the statement insertion
     * @param tmpBro
     * @param visited The visited flags
     **/
    Boolean local(LirNode st, BasicBlk v, boolean canInsert, Vector tmpBro, boolean[] visited) {

	if (!initialized[v.id]) localInit(v);

	LirNode dst = st.kid(0);
	LirNode src = st.kid(1);

	if (dst.opCode == Op.REG) {
	    if (isUsed(dst,v)) {
		return Boolean.FALSE;
	    }
	    if (isMod(dst,v)) {
		return Boolean.TRUE;
	    }
	    if (src.opCode == Op.MEM) {
		if (src.kid(0).opCode == Op.FRAME || src.kid(0).opCode == Op.STATIC) {
		    if (storedMemVec.getBit(v.id) == 1 || 
			deadMemMap.get(makeLocalKey(v,st.kid(1))) == Boolean.TRUE)
			canInsert = false;
		}
		else {
		    if (anyStoredMemVec.getBit(v.id) == 1) canInsert = false;
		}
	    }
	}
	else {
	    if ((Boolean)deadMemMap.get(makeLocalKey(v,st.kid(0))) == Boolean.TRUE) return Boolean.TRUE;
	    if (dst.kid(0).opCode == Op.FRAME || dst.kid(0).opCode == Op.STATIC) {
		if (usedMemMap.get(makeLocalKey(v, st.kid(0))) == Boolean.TRUE ||
		    loadedMemVec.getBit(v.id) == 1)
		    return Boolean.FALSE;
		if (storedMemVec.getBit(v.id) == 1)
		    canInsert = false;
	    }
	    else {
		if(anyLoadedMemVec.getBit(v.id) == 1 || isMod(dst,v))
		    return Boolean.FALSE;
		if (anyStoredMemVec.getBit(v.id) == 1)
		    canInsert = false;
	    }
	}

	if (isMod(st,v)) canInsert = false;

	if (visited[v.id]) {
	    Boolean ans = answer[v.id];
	    if (ans == null) return Boolean.TRUE;
	    else return ans;
	}

	visited[v.id] = true;


	Boolean ans = propagate(st, v, canInsert, tmpBro, visited);

	if (ans != null)
	    answer[v.id] = ans;
	return ans;
    }


    /**
     * Check whetther 
     * @param n The specified expression
     * @param v The specified node
     **/
    boolean isUsed(LirNode n, BasicBlk v) {
	if (usedMap.get(makeLocalKey(v, n)) != null) 
	    return true;
	else return false;
    }

    /**
     * Check whetther 
     * @param n
     * @param v
     **/
    private boolean isMod(LirNode n,BasicBlk v){
	BiList operands=util.findTargetLir(n,Op.REG,new BiList());
	for(BiLink q=operands.first();!q.atEnd();q=q.next()){
	    if(modMap.get(makeLocalKey(v,(LirNode)q.elem())) != null)
		return true;
	}
	return false;
    }

    /**
     * Check whetther 
     * @param n
     * @param v
     **/
    private boolean isOccur(LirNode e,BasicBlk v){

      BiLink rlt = (BiLink)occurMap.get(makeLocalKey(v,e));
      if (rlt != null) 
	  return true;
      else
	  return false;
    }


  /**
   * Make a key from an expression and a basic block.
   * @param blk The specified basic block
   * @param n The specified expression
   **/
    String makeLocalKey(BasicBlk blk, LirNode n) {
	String key = blk.id+"";
	switch (n.opCode) {
	case Op.LIST:
	    return key+","+((LirSymRef)n.kid(0)).symbol.name;
	case Op.REG:
	    return key+","+((LirSymRef)n).symbol.name;
	}
	return key+makeExpKey(n);
    }


  /**
   * Make a key from an expression.
   * @param n The specified expression
   **/
    String makeExpKey(LirNode n) {
	return n.toString();
    }

  /**
   * @param st
   * @param blk
   * @param bro
   * @param pVisited
   **/
    boolean postEqp (LirNode st,  BasicBlk blk, Vector bro, boolean[] pVisited) {

	Stack sunkPool = new Stack();

	sunkPool.push(blk);

	while(!sunkPool.empty()) {
	    BasicBlk v = (BasicBlk)sunkPool.pop();

	    Boolean isSafe = safe[v.id];//answer on exit
	    if (isSafe==Boolean.FALSE) return false;
	    if (isSafe==Boolean.TRUE) continue;

	    if (!initialized[v.id]) localInit(v);

	    BiLink link = (BiLink)occurMap.get(makeLocalKey(v,st));

	    if (link != null) {
		if (broVec.getBit(v.id) == 0) {
		    broVec.setBit(v.id);
		    Object[] pair = {link,v};
		    bro.add(pair);
		}
		continue;
	    }

	    if(v.predList().length() == 0 || // If v is the start block
	       isMod(st,v)) return false;
	    if (st.kid(0).opCode == Op.REG) {
		if (isUsed(st.kid(0),v)) return false;
		if (st.kid(1).opCode == Op.MEM) {
		    if (st.kid(1).kid(0).opCode == Op.FRAME || st.kid(1).kid(0).opCode == Op.STATIC) {
			if (storedMemVec.getBit(v.id) == 1 || 
			    deadMemMap.get(makeLocalKey(v,st.kid(1))) == Boolean.TRUE)
			    return false;
		    }
		    else {
			if (anyStoredMemVec.getBit(v.id) == 1) return false;
		    }
		}
	    }
	    else {
		LirNode dst = st.kid(0);
		if (dst.kid(0).opCode == Op.FRAME || dst.kid(0).opCode == Op.STATIC) {
		    if (deadMemMap.get(makeLocalKey(v, st.kid(0))) == Boolean.TRUE ||
			usedMemMap.get(makeLocalKey(v, st.kid(0))) == Boolean.TRUE ||
			storedMemVec.getBit(v.id) == 1 ||
			loadedMemVec.getBit(v.id) == 1) return false;
		}
		else {
		    if (anyStoredMemVec.getBit(v.id) == 1 || anyLoadedMemVec.getBit(v.id) == 1)
			return false;
		}
	    }


	    if(pVisited[v.id]) continue;
	    pVisited[v.id] = true;

	    for(BiLink pp= v.predList().first();!pp.atEnd();pp=pp.next()){
		BasicBlk p =(BasicBlk)pp.elem();
		sunkPool.push(p);
	    }
	}

	return true;
    }

    /**
     * @param b
     **/
    void maintainTableDeleteStmt(/*LirNode node,*/ BasicBlk b) {

	if (initialized[b.id]) {
	    storedMemVec.resetBit(b.id);
	    loadedMemVec.resetBit(b.id);
	    anyStoredMemVec.resetBit(b.id);
	    anyLoadedMemVec.resetBit(b.id);

	    for(BiLink pi=b.instrList().last();!pi.atEnd();pi=pi.prev()){
		LirNode node=(LirNode)pi.elem();
		LirNode refs = node;
		LirNode dst = null;
		switch(node.opCode) {
		case Op.SET: 
		    if (node.kid(0).opCode == Op.REG) {
			modMap.remove (makeLocalKey(b,node.kid(0)));
			refs = node.kid(1);
			if (node.kid(1).opCode!=Op.CALL &&
			    node.kid(1).opCode!=Op.USE &&
			    node.kid(1).opCode!=Op.SUBREG && // temoporal addition
			    node.kid(1).opCode!=Op.CLOBBER) {
			    occurMap.remove(makeLocalKey(b,node));
			}
		    }
		    if (node.kid(0).opCode == Op.MEM) {
			deadMemMap.remove(makeLocalKey(b, node.kid(0)));
			occurMap.remove(makeLocalKey(b,node));
		    }
		    if (node.kid(1).opCode == Op.MEM) 
			usedMemMap.remove(makeLocalKey(b, node.kid(1)));
		    break;
		case Op.CALL:
		    if(node.kid(2).nKids()>0 && node.kid(2).kid(0).opCode==Op.REG){
			if (node.kid(2).nKids() > 1) {
			    System.err.println("too many return values");
			    System.exit(1);
			}

			modMap.remove(makeLocalKey(b,node.kid(2).kid(0)));
			refs = node.makeCopy(env.lir);
			refs.setKid(2,null);
		    }
		}
		BiList operands=util.findTargetLir(refs,Op.REG,new BiList());
		for(BiLink q=operands.first();!q.atEnd();q=q.next()){
		    LirNode refReg = (LirNode)q.elem();
		    usedMap.remove(makeLocalKey(b,refReg));
		}
	    }
	    initialized[b.id] = false;
	}
    }

    /**
     * Maintain maps for statements insertion
     * @param node The specified statement
     * @param v The specified node
     * @param link 
     **/
    void maintainTableInsertStmt(LirNode node, BasicBlk v, BiLink link) {
	if (initialized[v.id]) {
	    LirNode dst = node.kid(0);
	    LirNode refs = node;
	    String key = makeLocalKey(v,node);

	    switch (node.kid(0).opCode) {
	    case Op.REG:
		refs = node.kid(1);
		LirNode src = node.kid(1);
		if (node.kid(1).opCode == Op.MEM) {
		    LirNode addr = src.kid(0);
		    if (addr.opCode == Op.FRAME || addr.opCode == Op.STATIC) {

			if (!isMod(node, v) && !isUsed(dst,v) &&
			    deadMemMap.get(makeLocalKey(v,node.kid(1))) == null && storedMemVec.getBit(v.id) == 0)
			    occurMap.put(key, link);
			usedMemMap.put(makeLocalKey(v,node.kid(1)), Boolean.TRUE);
			deadMemMap.remove(makeLocalKey(v,node.kid(1)));

		    }
		    else {

			if (!isMod(node, v) && !isUsed(dst,v) && anyStoredMemVec.getBit(v.id) == 0)
			    occurMap.put(key, link);

			for(BiLink pi=v.instrList().last();!pi.atEnd();pi=pi.prev()){
			    LirNode mem=(LirNode)pi.elem();
			    if (mem.opCode == Op.SET && mem.kid(0).opCode == Op.MEM) {
				deadMemMap.remove(makeLocalKey(v,mem.kid(0)));
			    }
			}


			usedMemMap.put(makeLocalKey(v,node.kid(1)), Boolean.TRUE);
			occurMap.put(key, link);
			loadedMemVec.setBit(v.id);
		    }
		    anyLoadedMemVec.setBit(v.id);
		}
		usedMap.remove(makeLocalKey(v,dst));

		break;
	    case Op.MEM:
		LirNode addr = node.kid(0).kid(0);

		if (addr.opCode == Op.FRAME || addr.opCode == Op.STATIC) {

		    if (loadedMemVec.getBit(v.id) == 0 && storedMemVec.getBit(v.id) == 0 &&
			usedMemMap.get(makeLocalKey(v,node.kid(0))) == null && 
			deadMemMap.get(makeLocalKey(v,node.kid(0))) == null && !isMod(node,v))
			occurMap.put(makeLocalKey(v,node), link);

		    deadMemMap.put(makeLocalKey(v, dst), Boolean.TRUE);
		    usedMemMap.remove(makeLocalKey(v, dst));
		}
		else {
		    storedMemVec.setBit(v.id);
		}
		anyStoredMemVec.setBit(v.id);
	    }
	    BiList operands=util.findTargetLir(refs,Op.REG,new BiList());
	    for(BiLink q=operands.first();!q.atEnd();q=q.next()){
		LirNode refReg = (LirNode)q.elem();
		usedMap.put(makeLocalKey(v, refReg), Boolean.TRUE);
	    }
	    if (node.kid(0).opCode == Op.REG)
		modMap.put(makeLocalKey(v,dst), Boolean.TRUE);
	}
    }


    /**
     * Check whether the expression has a valid type.
     * @param n The specified expression
     **/
    boolean isValidType(LirNode n) {
	if (Type.tag(n.type) != Type.INT && Type.tag(n.type) != Type.FLOAT) return false;
	else return true;
    }

    /**
     * @param n
     * @param modMap
     **/
    boolean isLocalMod(LirNode n, Hashtable modMap) {
	BiList operands=util.findTargetLir(n,Op.REG,new BiList());
	for(BiLink q=operands.first();!q.atEnd();q=q.next()){
	    LirNode reg = (LirNode)q.elem();
	    if(modMap.get(((LirSymRef)reg).symbol) != null)
		return true;
	}
	return false;
    }
	

    /**
     * Invoke the main routine of PDEQP.
     **/
    void invoke() {

	tmpMap = new Hashtable();
	stmtSplt();

	occurMap = new Hashtable();
	modMap = new Hashtable();
	usedMap = new Hashtable();
	storedMemVec = new BitVector(idBound);
	anyStoredMemVec = new BitVector(idBound);
	anyLoadedMemVec = new BitVector(idBound);
	loadedMemVec = new BitVector(idBound);
	deadMemMap = new Hashtable();
	usedMemMap = new Hashtable();
	stVisited = new FBitVector(env.lir.idBound());
	
      BasicBlk[] bVecInOrderOfRPost = blkVectorByRPost(dfst);
      for (int i = 1; i <  bVecInOrderOfRPost.length; i++) {
	  BasicBlk b = bVecInOrderOfRPost[i];
	  Hashtable localUsedMap = new Hashtable();
	  Hashtable localModMap = new Hashtable();
	  Hashtable localModMemMap = new Hashtable();
	  Hashtable localUsedMemMap = new Hashtable();

	  boolean isLoaded = false;
	  boolean isStored = false;

	  boolean isAnyStored = false;
	  boolean isAnyLoaded = false;

	  for(BiLink pi=b.instrList().last();!pi.atEnd();pi=pi.prev()){
	      LirNode node=(LirNode)pi.elem();
	      if (stVisited.getBit(node.id) == 1) continue;
	      stVisited.setBit(node.id);

	      LirNode dst = null;
	      LirNode refs = node;
	      Boolean rlt = Boolean.FALSE;

	      switch(node.opCode){
	      case Op.CALL: 
		  isLoaded = true;
		  isStored = true;

		  isAnyLoaded = true;
		  isAnyStored = true;

		  if(node.kid(2).nKids()>0 && node.kid(2).kid(0).opCode==Op.REG){
		      if (node.kid(2).nKids() > 1) {
			  System.err.println("too many return values");
			  System.exit(1);
		      }

		      dst=node.kid(2).kid(0);
		      refs = node.makeCopy(env.lir);
		      refs.setKid(2,null);
		  }
		  break;
	      case Op.SET:

		  boolean use = false;
		  boolean isMovable = true;

		  if (node.kid(0).opCode==Op.MEM /* &&  isValidType(node.kid(0))*/) {
		      LirNode addr = node.kid(0).kid(0);
		      
		      if (addr.opCode == Op.FRAME || addr.opCode == Op.STATIC) {
			  if (isLoaded || localUsedMemMap.get(makeExpKey(node.kid(0))) == Boolean.TRUE) {
			      use = true;
			      isMovable = false;
			  }
			  else if (localModMemMap.get(makeExpKey(node.kid(0))) == Boolean.TRUE) {
			      maintainTableDeleteStmt(b);
			      pi.unlink();
			      continue;

			  }
			  else {
			      if (isStored) isMovable = false;
			  }
		      }
		  }

		  if (node.kid(0).opCode == Op.REG) {
		      dst = node.kid(0);
		      refs = node.kid(1);

		      LirNode src = node.kid(1);

		      if ( node.kid(1).opCode!=Op.CALL &&
			  node.kid(1).opCode!=Op.USE &&
			  node.kid(1).opCode!=Op.SUBREG && // temoporal addition
			  node.kid(1).opCode!=Op.CLOBBER) {
			  if (localUsedMap.get(((LirSymRef)dst).symbol) == null &&
			      localModMap.get(((LirSymRef)dst).symbol) != null) {

			      maintainTableDeleteStmt(b);
			      pi.unlink();
			      continue;

			  }

			  if (dst != null && localUsedMap.get(((LirSymRef)dst).symbol) != null) {
			      use = true;
			      isMovable = false;
			  }
		      }

		  }

		  if(node.kid(1).opCode==Op.MEM/* && isValidType(src)*/) {
		      LirNode addr = node.kid(1).kid(0);
		      if (addr.opCode == Op.FRAME || addr.opCode == Op.STATIC) {

			  if (localModMemMap.get(makeExpKey(node.kid(1))) != null || isStored) {
			      isMovable = false;
			  }
		      }
		      else {
			  if (isAnyStored) isMovable = false;
		      }
		  }


		  BiList operands=util.findTargetLir(refs,Op.REG,new BiList());
		  for(BiLink q=operands.first();!q.atEnd();q=q.next()){
		      LirNode refReg = (LirNode)q.elem();

		      if (localModMap.get(((LirSymRef)refReg).symbol) != null
			  /* || (dst != null && ((LirSymRef)dst).symbol == ((LirSymRef)refReg).symbol))*/) 
			  isMovable = false;
		  }

		  if(!use && 
		     (node.kid(0).opCode==Op.REG || 
		      (node.kid(0).opCode == Op.MEM && 
		       (node.kid(0).kid(0).opCode == Op.FRAME || node.kid(0).kid(0).opCode == Op.STATIC)
		       && isValidType(node.kid(0)))) && 
		     node.kid(1).opCode!=Op.CALL &&
		     node.kid(1).opCode!=Op.USE &&
		     node.kid(1).opCode!=Op.SUBREG && // temoporal addition
		     node.kid(1).opCode!=Op.CLOBBER) {

		      dfs = new BitVector(idBound);
		      for(BiLink q=df.frontiers[b.id].first();!q.atEnd();q=q.next()){
			  BasicBlk frontier=(BasicBlk)q.elem();
			  dfs.setBit(frontier.id);
		      }
		      
		      bro = new Vector();
		      broVec = new BitVector(idBound);

		      broVec.setBit(b.id);
		      Stack rlts = new Stack();

		      answer = new Boolean[idBound];
		      safe = new Boolean[idBound];
		      
		      BitVector checkVec = new BitVector(idBound);
		      checkVec.setBit(b.id);
		      boolean[] visited = new boolean[idBound];
		      rlt = propagate(node, b, isMovable, new Vector(), visited );
		      if (rlt == Boolean.TRUE) {

			  maintainTableDeleteStmt( b);
			  pi.unlink();


			  for (int k = 0; k < bro.size(); k++) {
			      if (checkVec.getBit(k) == 1) continue;
			      else checkVec.setBit(k);

			      Object[] broPair = (Object[])bro.elementAt(k);
			      BiLink cand = (BiLink)broPair[0];
			      LirNode n = (LirNode)cand.elem();
			      stVisited.setBit(n.id);

			      BasicBlk v = (BasicBlk)broPair[1];
			      Boolean rlt2 = propagate(n, v, true, new Vector(), visited);
			      if (rlt2 == Boolean.TRUE) {
				  maintainTableDeleteStmt(v);
				  cand.unlink();
			      }
			      else {
				  System.err.println("all the brother statements have to be elimiated with "+n.toString()+" at "+v.id+" in "+f.toString());
				  System.exit(1);
			      }
			  }
		      }
		  }
	      }

	      if (rlt != Boolean.TRUE) {
		  if (node.opCode == Op.SET) {
		      if(node.kid(0).opCode == Op.REG) {
			  localUsedMap.remove(((LirSymRef)node.kid(0)).symbol) ;
		      }
			      
		      if(node.kid(0).opCode == Op.MEM/* && isValidType(node.kid(0))*/) {
			  if(node.kid(0).kid(0).opCode == Op.FRAME || node.kid(0).kid(0).opCode ==Op.STATIC) { 
			      localModMemMap.put(makeExpKey(node.kid(0)), Boolean.TRUE);
			      localUsedMemMap.remove(makeExpKey(node.kid(0)));
			  }
			  else {
			      isStored = true;
			  }
			  isAnyStored = true;
		      }


		      if (node.kid(1).opCode == Op.MEM) {
			  if (node.kid(1).kid(0).opCode == Op.FRAME || 
			      node.kid(1).kid(0).opCode ==Op.STATIC){ 
			      localUsedMemMap.put(makeExpKey(node.kid(1)), Boolean.TRUE);
			  }
			  else {
			      isLoaded = true;
			  }
			  isAnyLoaded = true;
		      }
		  }	
	  
		  BiList operands=util.findTargetLir(refs,Op.REG,new BiList());
		  for(BiLink q=operands.first();!q.atEnd();q=q.next()){
		      LirNode refReg = (LirNode)q.elem();
		      localUsedMap.put(((LirSymRef)refReg).symbol, Boolean.TRUE);
		  }
		  if (dst != null && dst.opCode == Op.REG) {
		      localModMap.put(((LirSymRef)dst).symbol, Boolean.TRUE);

		  }

	      }
	  }
      }
    }

    int failureCount;

    /**
     * Initialize the information of the node.
     * @param v The specified node
     **/
    void localInit(BasicBlk v) {
	initialized[v.id] = true;
	Vector killMemList = null;

	for(BiLink p=v.instrList().last();!p.atEnd();p=p.prev()){
	    LirNode node=(LirNode)p.elem();

	    LirNode dst = null;	  
	    LirNode refs = node;
	    String key = makeLocalKey(v,node);

	    switch(node.opCode){
            case Op.SET:

		if (node.kid(0).opCode==Op.MEM/* && isValidType(node.kid(0))*/) {

		    LirNode addr = node.kid(0).kid(0);
		    if (addr.opCode == Op.FRAME || addr.opCode == Op.STATIC) {
			if (loadedMemVec.getBit(v.id) == 0 && storedMemVec.getBit(v.id) == 0 &&
			    usedMemMap.get(makeLocalKey(v,node.kid(0))) == null && 
			    deadMemMap.get(makeLocalKey(v,node.kid(0))) == null && !isMod(node,v))
			    occurMap.put(makeLocalKey(v,node), p);
			if (killMemList == null) killMemList = new Vector();
			killMemList.add(node.kid(0));
			deadMemMap.put(makeLocalKey(v,node.kid(0)), Boolean.TRUE);
			usedMemMap.remove(makeLocalKey(v,node.kid(0)));
		    }
		    else {
			storedMemVec.setBit(v.id);
		    }
		    anyStoredMemVec.setBit(v.id);
		}

		if(node.kid(0).opCode==Op.REG) {	    
		    dst = node.kid(0);
		    LirNode src = node.kid(1);

		    if (node.kid(1).opCode!=Op.CALL &&
		       node.kid(1).opCode!=Op.USE &&
		       node.kid(1).opCode!=Op.MEM && // temporal addition
		       node.kid(1).opCode!=Op.CLOBBER) {
			if (!isMod(node, v) && !isUsed(dst,v)) {
			    occurMap.put(key, p);
			}
		    }

		    usedMap.remove(makeLocalKey(v,dst));

		    refs = node.kid(1);
		}

		if(node.kid(1).opCode==Op.MEM) {
		    LirNode src = node.kid(1);
		    LirNode addr = src.kid(0);

		    if (addr.opCode == Op.FRAME || addr.opCode == Op.STATIC) {
			if (!isMod(node, v) && dst != null && !isUsed(dst,v) && 
			    deadMemMap.get(makeLocalKey(v,node.kid(1))) == null && storedMemVec.getBit(v.id) == 0)
			    occurMap.put(key, p);
			usedMemMap.put(makeLocalKey(v,src),Boolean.TRUE);
			deadMemMap.remove(makeLocalKey(v,src));
		    }
		    else {
			if (!isMod(node, v) && dst != null && !isUsed(dst,v) && anyStoredMemVec.getBit(v.id) == 0)
			    occurMap.put(key,p);
			for (int i = 0; killMemList != null && i < killMemList.size(); i++) {
			    LirNode mem = (LirNode)killMemList.elementAt(i);
			    deadMemMap.remove(makeLocalKey(v,mem));
			}
			killMemList = null;
			
			usedMemMap.put(makeLocalKey(v,src),Boolean.TRUE);
			deadMemMap.remove(makeLocalKey(v,src));
			loadedMemVec.setBit(v.id);
		    }

		    anyLoadedMemVec.setBit(v.id);
		}
		
		break;
	    case Op.CALL:

		for (int i = 0; killMemList != null && i < killMemList.size(); i++) {
		    LirNode mem = (LirNode)killMemList.elementAt(i);
		    deadMemMap.remove(makeLocalKey(v,mem));
		}
		killMemList = null;
		if(node.kid(2).nKids()>0 && node.kid(2).kid(0).opCode==Op.REG){
		    if (node.kid(2).nKids() > 1) {
			System.err.println("too many return values");
			System.exit(1);
		    }

		    dst = node.kid(2).kid(0);
		    usedMap.remove(makeLocalKey(v,dst));
		    refs = node.makeCopy(env.lir);
		    refs.setKid(2,null);
		}
		storedMemVec.setBit(v.id);
		loadedMemVec.setBit(v.id);		
		anyStoredMemVec.setBit(v.id);
		anyLoadedMemVec.setBit(v.id);
	    }
	    BiList operands=util.findTargetLir(refs,Op.REG,new BiList());
	    for(BiLink q=operands.first();!q.atEnd();q=q.next()){
		LirNode refReg = (LirNode)q.elem();
		usedMap.put(makeLocalKey(v, refReg), Boolean.TRUE);
	    }
	    if (dst != null && dst.opCode == Op.REG) {
		modMap.put(makeLocalKey(v,dst), Boolean.TRUE);
	    }
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
//	env.println("****************** doing PREQP to "+
	env.println("****************** doing PDEQP to "+
//
		    f.symbol.name,SsaEnvironment.MinThr);

	dfst=(ReverseDFST)f.require(ReverseDFST.analyzer);
	df=(DominanceFrontiers)f.require(DominanceFrontiers.analyzer);
	BitVector dfs;

	initialized = new boolean[idBound];

	invoke();

	stmtMerge();

	f.flowGraph().touch();
	return(true);
    }
}

