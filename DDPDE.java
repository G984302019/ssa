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
import coins.backend.ana.ReverseDFST;
import coins.backend.ana.LiveVariableAnalysis;
import coins.backend.ana.LiveVariableSlotwise;



/**
 * Demand driven partial dead code elimination.
 **/
public class DDPDE implements LocalTransformer {
  /** Debug flag **/
    private boolean debugFlag;

    public boolean doIt(Data data, ImList args) { return true; }
  // Begin(2009.1.23)
//    public String name() { return "PREQP"; }
    public String name() { return "DDPDE"; }
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
    Hashtable midMap;
    Vector stmtq;
    Stack stack;
    BitVector ready;
    int stmtId = 0;
    int idBound;

    // for DD
    /*
    Stack poolS;
    Stack poolD;
    Stack poolU;
    */

    // for code sinking
    Hashtable dstMap;
    //Hashtable[] candMap;
    Vector memq;

    //for dead code
    //Hashtable[] liveMaps;

    // for code sinking
    BitVector[] locblocked;
    BitVector[] locdelayed;
    Hashtable[] locdelayedMap;

    /*
    BitVector[] ndelayed;	
    BitVector[] xdelayed;
    */
    boolean[] ndelayed;
    boolean[] xdelayed;
    
    // for dead code
    BitVector[] used;
    BitVector[] mod;

    BitVector[] ndead;
    BitVector[] xdead;
    BitVector[] _xdead;

    // for up-safety
    boolean[]  nsafe;
    boolean[] _nsafe;

    // for start node
    BasicBlk _startBlk = null;
    BiLink _nextNode = null;
    BitVector _used = null;
    BitVector _mod = null;
    BitVector _locblocked = null;
    BitVector _locdelayed = null;
    Hashtable _locdelayedMap = null;

    //    BitVector[] processed;

    boolean[] ninsert;
    boolean[] xinsert;

  /**
   * Constructor.
   * @param e The environment of the SSA module
   * @param tab The current SSA symbol table
   **/
    public DDPDE(SsaEnvironment e, SsaSymTab tab){
      env=e;
      sstab=tab;
    }


    boolean isInFrame(LirNode node) {
	Stack stk = new Stack();
	stk.push(node);
	while(!stk.empty()) {
	    LirNode tg = (LirNode)stk.pop();
	    for (int i = 0; i < tg.nKids(); i++) {
		LirNode inode = tg.kid(i);
		switch(inode.opCode) {
		case Op.MEM: continue;
		case Op.FRAME: return true;
		default: stk.push(inode);
		}
	    }
	}
	return false;
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
		if (node.opCode != Op.SET) continue;

		LirNode dst = node.kid(0);
		LirNode src = node.kid(1);

		if(src.opCode!=Op.CALL &&
		   src.opCode!=Op.USE &&
		   src.opCode!=Op.SUBREG && // temoporal addition
		   src.opCode!=Op.CLOBBER) {

		    switch(dst.opCode){
		    case Op.REG:

			// id をふる
			Integer iD = (Integer)idMap.get(node);
			if (iD == null) {
			    iD = new Integer(stmtId++);
			    idMap.put(mkKey(node), iD);
			    stmtq.add(node);
			    BiList mems=util.findTargetLir(src,Op.MEM,new BiList());
			    if (mems.length() > 0)
				memq.add(iD);
			}
			break;
			/*
		    case Op.MEM:
			Integer mID = (Integer)midMap.get(node);
			if (mID == null) {
			    mID = new Integer(stmtId++);
			    midMap.put(mkKey(node), mID);
			    stmtq.add(node);
			    memq.add(mID);
			}
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

	
    void setMem(BitVector locblocked/*, BitVector locdelayed, Hashtable map*/) {
	for (int i = 0; i < memq.size(); i++) {
	    Integer mID = (Integer)memq.elementAt(i);
	    int mid = mID.intValue();
	    //LirNode mem = (LirNode)stmtq.elementAt(mid);

	    locblocked.setBit(mid);
	    //locdelayed.resetBit(mid);
	    //map.remove(mID);
	}
    }

    void setBlk(LirNode dst, BitVector locblocked/*, BitVector locdelayed, Hashtable map*/) {
	//locdelayed[v.id].setBit(iD.intValue());

	for(int id = 0; id < stmtId; id++) {
	    LirNode key = (LirNode)stmtq.elementAt(id);
		Symbol dstS = ((LirSymRef)dst).symbol;

		BiList regs=util.findTargetLir(key,Op.REG,new BiList());			
		for(BiLink rq=regs.first();!rq.atEnd();rq=rq.next()){
		    Symbol s = ((LirSymRef)rq.elem()).symbol;
		    if (s == dstS){
			locblocked.setBit(id);
			//locdelayed.resetBit(id);
			//map.remove(iD);
			break;
		    }
		}
	}
    }

    void setBlkU(LirNode node, BitVector locblocked/*, BitVector locdelayed, Hashtable map*/) {
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
			
			locblocked.setBit(id);
			//locdelayed.resetBit(id);
			//map.remove(iD);
		    }
		}
	}
    }


    void setMemBlkU(LirNode node, BitVector locblocked/*, BitVector locdelayed, Hashtable map*/) {

	if (node == null || 
	    util.findTargetLir(node, Op.MEM,new BiList()).length() > 0) {
	    Enumeration keys = midMap.keys();
	    while (keys.hasMoreElements()) {
		LirNode key = (LirNode)keys.nextElement();
		Integer mID = (Integer)midMap.get(key);
		int id = mID.intValue();

		locblocked.setBit(id);
	    }
	}
    }


    void setPMemBlkU(LirNode node, BitVector locblocked/*, BitVector locdelayed, Hashtable map*/) {

	if (node == null || util.findTargetLir(node, Op.MEM, new BiList()).length() > 1) {
	    Enumeration keys = midMap.keys();
	    while (keys.hasMoreElements()) {
		LirNode key = (LirNode)keys.nextElement();
		Integer mID = (Integer)midMap.get(key);
		int id = mID.intValue();

		locblocked.setBit(id);
	    }
	}
    }

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
		    //mod.resetBit(id);
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

    void setMemUsed(LirNode node, BitVector used, BitVector mod) {
	if (node == null || util.findTargetLir(node,Op.MEM,new BiList()).length() > 0) {
	    Enumeration keys = midMap.keys();
	    while (keys.hasMoreElements()) {
		LirNode key = (LirNode)keys.nextElement();
		Integer mID = (Integer)midMap.get(key);
		int id = mID.intValue();

		used.setBit(id);
	    }
	}
    }

    void setMemUsedExFrame (LirNode node, BitVector used, BitVector mod) {

	    Enumeration keys = midMap.keys();
	if (util.findTargetLir(node,Op.MEM,new BiList()).length() > 0) {
	    while (keys.hasMoreElements()) {
		LirNode key = (LirNode)keys.nextElement();
		Integer mID = (Integer)midMap.get(key);
		int id = mID.intValue();

		used.setBit(id);
	    }
	}
	else {
	    while (keys.hasMoreElements()) {
		LirNode key = (LirNode)keys.nextElement();
		if (!isInFrame(key.kid(0))) {
		    Integer mID = (Integer)midMap.get(key);
		    int id = mID.intValue();
		    
		    used.setBit(id);
		}
	    }
	}
    }

    void setPMemUsed(LirNode node, BitVector used, BitVector mod) {
	if (node == null || util.findTargetLir(node, Op.MEM, new BiList()).length() > 1) {
	    Enumeration keys = midMap.keys();
	    while (keys.hasMoreElements()) {
		LirNode key = (LirNode)keys.nextElement();
		Integer mID = (Integer)midMap.get(key);
		int id = mID.intValue();

		used.setBit(id);
	    }
	}
    }

    void setMemRegUsed(LirNode dst, BitVector used) {  // [x] = 
                                                       //  x = 
	Enumeration keys = midMap.keys();
	while (keys.hasMoreElements()) {
	    LirNode key = (LirNode)keys.nextElement();
	    Integer mID = (Integer)midMap.get(key);
	    int id = mID.intValue();
	    LirNode mem = key.kid(0);
	    BiList regs=util.findTargetLir(mem,Op.REG,new BiList());
	    for(BiLink rq=regs.first();!rq.atEnd();rq=rq.next()){
		Symbol s = ((LirSymRef)rq.elem()).symbol;
		if (s == ((LirSymRef)dst).symbol) {
		    used.setBit(id);
		    break;
		}
	    }
	}
    }

    void setMemMemUsed(BitVector used) {   // [...[ ] ...] =
                                           // [] = 
	Enumeration keys = midMap.keys();
	while (keys.hasMoreElements()) {
	    LirNode key = (LirNode)keys.nextElement();
	    Integer mID = (Integer)midMap.get(key);
	    int id = mID.intValue();
	    LirNode dst = key.kid(0);
	    BiList mems=util.findTargetLir(dst,Op.MEM,new BiList());

	    if (mems.length() > 1) 
		used.setBit(id);
	}
    }

    void setMemMod(LirNode dst, BitVector used, BitVector mod) {
	Enumeration keys = midMap.keys();
	while (keys.hasMoreElements()) {
	    LirNode key = (LirNode)keys.nextElement();
	    LirNode dst2 = key.kid(0);
	    Integer iD = (Integer)midMap.get(key);
	    int id = iD.intValue();
	    if (dst2.equals(dst)) {
		mod.setBit(id);
		used.resetBit(id);
	    }
	    //else {
		BiList mems= new BiList();
		for (int i = 0; i < dst2.nKids(); i++) {
		    mems = util.findTargetLir(dst2.kid(i),Op.MEM,mems);
		    if (mems.length() > 0) {
			used.setBit(id);
			break;
		    }
		}
		//	    }
	}
    }

    void init() {
	for (int i = 0; i < idBound; i++) {
	    _xdead[i] = new BitVector(stmtId);
	    /*
	    ndelayed[i] = new BitVector(stmtId);
	    xdelayed[i] = new BitVector(stmtId);
	    */
	    ndead[i] = new BitVector(stmtId);
	    xdead[i] = new BitVector(stmtId);
	    /*
	    nsafe[i] = new BitVector(stmtId);
	    _nsafe[i] = new BitVector(stmtId);
	    */
	    //processed[i] = new BitVector(stmtId);
	}
	ready = new BitVector(idBound);
    }

    boolean initNode(BiLink p, BitVector used, BitVector mod, BitVector locblocked, 
		     BitVector locdelayed, Hashtable locdelayedMap) {
	//    void setMem(BitVector locblocked) {
	//    void setBlk(LirNode dst, BitVector locblocked) {
	//    void setBlkU(LirNode node, BitVector locblocked) {
	//    void setUsed(LirNode node, BitVector used, BitVector mod) {
	//    void setMod(LirNode dst, BitVector used, BitVector mod) {
	//    void cancelUsed (LirNode node, Hastable dceMap) {

	LirNode node = (LirNode)p.elem();
	switch(node.opCode){
	case Op.SET:
	    LirNode dst = node.kid(0);
	    LirNode src = node.kid(1);


	    if (dst.opCode==Op.MEM) {
		// [...] = ...
		Integer iD = (Integer)midMap.get(node);
		/*
		if (iD == null) {
		    System.err.println("cannot deal with such a SET statement!");
		    System.exit(1);
		}

		if (used.getBit(iD.intValue()) == 0 && mod.getBit(iD.intValue()) == 1) {
		    p.unlink();
		    return true;
		}

		if (locblocked.getBit(iD.intValue()) == 0) {
		    locdelayed.setBit(iD.intValue());
		    locdelayedMap.put(iD, p);
		}
		*/
		// for code sinking
		setMem(locblocked);
		setBlkU(node, locblocked);
		// for dead code
		/*
		setMemMod(dst, used, mod);

		setMemMemUsed(used);
		setMemUsed(src, used, mod);
		setPMemUsed(dst, used, mod);
		*/
		setUsed(node, used, mod);
	    }
	    else if(node.kid(0).opCode==Op.REG) {	    
		
		//for dead code
		Integer iD = (Integer)idMap.get(node);
		//int id = iD.intValue();

		if (iD == null) {
		    System.err.println("cannot deal with such a SET statement!");
		    System.exit(1);
		}

		if (used.getBit(iD.intValue()) == 0 && mod.getBit(iD.intValue()) == 1) {
		    p.unlink();
		    return true;
		}

		// for code sinking
		if (locblocked.getBit(iD.intValue()) == 0) {
		    locdelayed.setBit(iD.intValue());
		    locdelayedMap.put(iD, p);
		}
		
		// for code sinking
		setBlk(dst, locblocked);
		setBlkU(src, locblocked);
		//		setMemBlkU(src, locblocked);
		// for dead code
		setMod(dst, used, mod);
		setUsed(src, used, mod);
		/*
		setMemUsed(src, used, mod);
		setMemRegUsed(dst, used);
		*/
	    }
	    else {
		// for code sinking
		setBlkU(node, locblocked);
		//		setMemBlkU(node, locblocked);
		// for dead code
		setUsed(node, used, mod);
		//		setMemUsed(node, used, mod);
	    }
	    break;
	case Op.CALL:
	    if(node.kid(2).nKids()>0 && node.kid(2).kid(0).opCode==Op.REG){
		if (node.kid(2).nKids() > 1) {
		    System.err.println("too many return values");
		    System.exit(1);
		}

		// liveMaps[v.id].remove(node.kid(2).kid(0));
		LirNode rlt = node.kid(2).kid(0);
		setMod(rlt, used, mod);
		setBlk(rlt, locblocked);
		for (int i = 0; i < node.nKids(); i++) {
		    if (i == 2) {
			// for code sinking
			continue;
		    }

			// for code sinking
		    setBlkU(node.kid(i), locblocked);
		    setUsed(node.kid(i), used, mod);
		}
	    }
	    else {
		// for code sinking
		setBlkU(node, locblocked);
		// for dead code
		setUsed(node, used, mod);
	    }
	    setMem(locblocked);
	    //setMemUsed(null, used, mod);
	    break;
	case Op.EPILOGUE: 
	    setBlkU(node, locblocked);
	    setMem(locblocked);
	    setUsed(node, used, mod);
	    //setMemUsedExFrame(node, used, mod);
	    break;
	default: 
	    // for code sinking
	    setBlkU(node, locblocked);
	    //	    setMemBlkU(node, locblocked);
	    // for dead code
	    setUsed(node, used, mod);
	    //	    setMemUsed(node, used, mod);
	}
	return false;
    }

    void initBlk(BasicBlk v) {
	if (ready.getBit(v.id) == 1) return;
	ready.setBit(v.id);
	BiLink current = null;

	used[v.id] = new BitVector(stmtId);
	mod[v.id] = new BitVector(stmtId); 
	locblocked[v.id] = new BitVector(stmtId);
	locdelayed[v.id] = new BitVector(stmtId);

	if (_startBlk == v) {
	    _used.vectorCopy(used[v.id]);
	    _mod.vectorCopy(mod[v.id]);
	    _locblocked.vectorCopy(locblocked[v.id]);
	    _locdelayed.vectorCopy(locdelayed[v.id]);
	    locdelayedMap[v.id] = (Hashtable)_locdelayedMap.clone();
	    current = _nextNode;
	}
	else {
		    // for code sinking
	    locdelayedMap[v.id] = new Hashtable();
	    //candMap[v.id] = new Hashtable();

	    // for dead code
	    current = v.instrList().last();
	}

	for(BiLink p=current;!p.atEnd();p=p.prev()){
	    initNode(p, used[v.id], mod[v.id], locblocked[v.id], locdelayed[v.id], locdelayedMap[v.id]);
	}

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


    void settleUpdate () {
	BasicBlk[] bVecInOrderOfRPost = blkVectorByRPost((ReverseDFST)f.require(ReverseDFST.analyzer));

	for (int i = 1; i <  bVecInOrderOfRPost.length; i++) {
	    BasicBlk b = bVecInOrderOfRPost[i];
	    _used = new BitVector(stmtId);
	    _mod = new BitVector(stmtId);
	    _locblocked = new BitVector(stmtId);
	    _locdelayed = new BitVector(stmtId);
	    _locdelayedMap = new Hashtable();
	    _startBlk = b;

	    BiLink p;
	    for(p=b.instrList().last();!p.atEnd();p=p.prev()){
		LirNode node=(LirNode)p.elem();
		Integer iD = null;
		if (node.opCode == Op.SET)
		    if (node.kid(0).opCode == Op.REG)
			iD = (Integer)idMap.get(node);
		    else iD = (Integer)midMap.get(node);
		if (iD != null) {
		    int id = iD.intValue();
		    if (_used.getBit(id) == 0) {
			if(_mod.getBit(id) == 1) {
			    p.unlink();
			    ready.resetBit(b.id);
			    continue;
			}
			else if (_locblocked.getBit(id) == 1) {
			    _nextNode = p;

			    if (isDead(id, b)) {
				p.unlink();
				ready.resetBit(b.id);
				continue;
			    }
			}
			else {
			    _nextNode = p;

			    nsafe = new boolean[idBound];
			    _nsafe = new boolean[idBound];
			    ndelayed = new boolean[idBound];
			    xdelayed = new boolean[idBound];
			    ninsert = new boolean[idBound];
			    xinsert = new boolean[idBound];

			    if (insert(p, iD, b)) {
				p.unlink();
				ready.resetBit(b.id);
				continue;
			    }
			    /*
			    else {
				b.instrList().last().addBefore(p.elem());
				p.unlink();
				initNode(b.instrList().last().prev(), _used, _mod, _locblocked, _locdelayed, _locdelayedMap);
				ready.resetBit(b.id); // <- check
				continue;
			    }
			    */
			}
		    }
		}
		initNode(p, _used, _mod, _locblocked, _locdelayed, _locdelayedMap);
	    }
	    if (ready.getBit(b.id) == 0) {
		_nextNode = p;
		initBlk(b);
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
		if (used[v.id] == null) System.out.print("_0");
		else System.out.print(" "+used[v.id].getBit(i));
	    System.out.print("\n\tmod:\t");
	    for(int i = 0; i < stmtId; i++) 
		if (mod[v.id] == null) System.out.print("_0");
		else System.out.print(" "+mod[v.id].getBit(i));
	    System.out.print("\n\tlocblocked:\t");
	    for(int i = 0; i < stmtId; i++) 
		if (locblocked[v.id] == null) System.out.print("_0");
		else System.out.print(" "+locblocked[v.id].getBit(i));
	    System.out.print("\n\tlocdelayed:\t");
	    for(int i = 0; i < stmtId; i++) 
		if (locdelayed[v.id] == null) System.out.print("_0");
		else System.out.print(" "+locdelayed[v.id].getBit(i));

	    System.out.print("\n\tndead:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+ndead[v.id].getBit(i));
	    System.out.print("\n\txdead:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+xdead[v.id].getBit(i));
	    System.out.print("\n\tninsert:\t");

	    /*
	    System.out.print("\n\tndelayed:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+ndelayed[v.id].getBit(i));
	    System.out.print("\n\txdelayed:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+xdelayed[v.id].getBit(i));

	    System.out.print("\n\tnsafe:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+nsafe[v.id].getBit(i));
	    System.out.print("\n\t_nsafe:\t");
	    for(int i = 0; i < stmtId; i++) 
		System.out.print(" "+_nsafe[v.id].getBit(i));
	    */
	    System.out.print("\n");
	    for (int j = 0; j < stmtId; j++) 
		System.out.println ("\t"+j+": "+
				    ((LirNode)stmtq.elementAt(j)).toString());
	}
    }


    boolean isUpSafe (int id, BasicBlk b/*, BiList more*/) {
	if (_nsafe[b.id]) 
	    return nsafe[b.id];

	if (b == f.flowGraph().entryBlk()) return false;

	boolean[] query = new boolean[idBound];
	Stack poolU = new Stack(); // for up safety

	poolU.push(b);
	while(!poolU.empty()) {
	    BasicBlk v = (BasicBlk)poolU.pop();
	    query[v.id] = true;


	    for(BiLink pp= v.predList().first();!pp.atEnd();pp=pp.next()){
		BasicBlk pred = (BasicBlk)pp.elem();
		initBlk(pred);

		if (locdelayed[pred.id].getBit(id) == 1) {
		    if (!done[pred.id])  {
			done[pred.id] = true;
			//more.addFirst(pred);
			cands.push(pred);
		    }
		    continue;
		}
		else if (locblocked[pred.id].getBit(id) == 1) {
		    _nsafe[b.id] = true;
		    //nsafe[b.id].resetBit(id);
		    return false;
		}
		else  if (pred == f.flowGraph().entryBlk()) {
		    _nsafe[b.id] = true;
		    return false;
		}
		else if (_nsafe[pred.id]) {
		    if (nsafe[pred.id]) continue;
		    else return false;
		}
		else if (!query[pred.id]) 
		    poolU.push(pred);
	    }
	}
	
	_nsafe[b.id] = true;
	nsafe[b.id] = true;
	return true;
    }

    boolean isDead(int id, BasicBlk b) {
	if (_xdead[b.id].getBit(id) == 1) {
	    if (xdead[b.id].getBit(id) == 1) return true;
	    else return false;
	}
	boolean[] query = new boolean[idBound];

	Stack poolD = new Stack(); // for dead code	
	poolD.push(b);
	while (!poolD.empty()) {
	    BasicBlk v = (BasicBlk)poolD.pop();
	    query[v.id] = true;
	    for(BiLink ss= v.succList().first();!ss.atEnd();ss=ss.next()){
		BasicBlk succ = (BasicBlk)ss.elem();
		initBlk(succ);
		
		if (used[succ.id].getBit(id) == 1) {
		    _xdead[b.id].setBit(id);
		    //xdead[b.id].resetBit(id);
		    return false;
		}
		else if (mod[succ.id].getBit(id) == 1) 
		    continue;
		else if (_xdead[succ.id].getBit(id) == 1) {
		    if (xdead[succ.id].getBit(id) == 1) continue;
		    else {
			_xdead[b.id].setBit(id);
			//xdead[b.id].resetBit(id);
			return false;
		    }
		}
		else if (!query[succ.id]) 
		    poolD.push(succ);
	    }
	}
	
	_xdead[b.id].setBit(id);
	xdead[b.id].setBit(id);
	return true;
    }

    boolean[] done = null;
    //BiList list = null;
    Stack cands = null;


    boolean insert(BiLink lk, Integer iD, BasicBlk b) {
	LirNode node = (LirNode)lk.elem();
	/*
	Integer iD = (Integer)idMap.get(node);
	if (iD == null) return;
	*/

	int id = iD.intValue();
	done = new boolean[idBound];
	Vector ninsertCand = new Vector();
	Vector xinsertCand = new Vector();

	cands = new Stack();
	xdelayed[b.id] = true;
	done[b.id] = true;
	cands.push(b);

	BiList list = new BiList();
	//for(BiLink e = list.first(); !e.atEnd(); e = e.next()) {
	while(!cands.empty()) {
	    BasicBlk next = (BasicBlk)cands.pop();
	    //BasicBlk next = (BasicBlk)e.elem();
	    //done[next.id] = true;
	    list.add(next);
	    insertEach(id, next, ninsertCand, xinsertCand);
	    //processed[next.id].setBit(id);
	}

	for (int i = 0 ; i < ninsertCand.size(); i++) {
	    BasicBlk v = (BasicBlk)ninsertCand.elementAt(i);
	    v.instrList().first().addBefore(node.makeCopy(env.lir));

	    if (ready.getBit(v.id)==1)
		initNode(v.instrList().first(), 
			 used[v.id], mod[v.id], locblocked[v.id], locdelayed[v.id], locdelayedMap[v.id]);
	}
	for (int i = 0 ; i < xinsertCand.size(); i++) {
	    BasicBlk v = (BasicBlk)xinsertCand.elementAt(i);
	    if (v != b && locdelayed[v.id].getBit(id) == 0) {
		v.instrList().last().addBefore(node.makeCopy(env.lir));
		ready.resetBit(v.id);
	    }
	    //processed[v.id].setBit(id);
	}

	boolean isRemoved = false;
	for(BiLink e2 = list.first(); !e2.atEnd(); e2 = e2.next()) {
	    BasicBlk next = (BasicBlk)e2.elem();

	    if (xinsert[next.id]) continue;

	    if (b == next) 
		isRemoved = true;
	    else {
		((BiLink)locdelayedMap[next.id].get(iD)).unlink();
		ready.resetBit(next.id);
	    }
	}
	return isRemoved;
    }

    void insertEach (int id, BasicBlk b, Vector ninsertCand, Vector xinsertCand) {
	BiList more = new BiList();

	Stack poolS = new Stack(); // for code sinking
	poolS.push(b);

	while (!poolS.empty()) {
	    BasicBlk v = (BasicBlk)poolS.pop();
	    for(BiLink ss= v.succList().first();!ss.atEnd();ss=ss.next()){
		BasicBlk succ = (BasicBlk)ss.elem();
                if (ndelayed[succ.id]) {
                    continue;
		}

		if (f.flowGraph().exitBlk() == succ) {
		    if (!xinsert[v.id] && !isDead(id, v)) {
			xinsert[v.id] = true;
			xinsertCand.add(v);
		    }
		    break;
		}
		else if (succ.predList().length() > 1) {
		    if (isUpSafe(id, succ/*, more*/)){
			//list.append(more);
		    }
		    else {
			if (!xinsert[v.id] && !isDead(id, v)) {
			    xinsert[v.id] = true;
			    xinsertCand.add(v);
			}

			break;
		    }
		}
		else {
		    _nsafe[succ.id] = true;
		    nsafe[succ.id] = true;
		}			
		ndelayed[succ.id] = true;

		initBlk(succ);

		if (locblocked[succ.id].getBit(id)==1) {
		    if (!ninsert[succ.id] && 
				 (used[succ.id].getBit(id) == 1 || 
				  !(mod[succ.id].getBit(id)==1 || isDead(id, succ)))) {
			ninsert[succ.id] = true;
			ninsertCand.add(succ);
		    }

                     continue;
		}
		
		if (!xdelayed[succ.id]) {
		    xdelayed[succ.id] = true;
		    poolS.push(succ);
		}
	    }
	}
    }
    

    /**
     * Invoke the main routine of DDPDE.
     **/
    void invoke() {

	idMap = new Hashtable();
	midMap = new Hashtable();
	stmtq = new Vector();

	// for DD
	// for code sinking
	// dstMap = new Hashtable();
	memq = new Vector();
	// candMap = new Hashtable[idBound];
	locblocked = new BitVector[idBound];
	locdelayed = new BitVector[idBound];
	locdelayedMap = new Hashtable[idBound];
	/*
	ndelayed = new BitVector[idBound];	
	xdelayed = new BitVector[idBound];
	*/
	// for dead code 
	//liveMaps = new Hashtable[idBound];
	used = new BitVector[idBound];
	mod  = new BitVector[idBound];
	ndead = new BitVector[idBound];
	xdead = new BitVector[idBound];
	_xdead = new BitVector[idBound];
	/*
	nsafe = new BitVector[idBound];
	_nsafe = new BitVector[idBound];
	*/
	//processed = new BitVector[idBound];

	collectStmt();

	init();
	settleUpdate();
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
	env.println("****************** doing DDPDE to "+
//
		    f.symbol.name,SsaEnvironment.MinThr);

	invoke();

	//result();

	/*
	System.out.println("\n"+f.toString());
	f.flowGraph().printIt(new java.io.PrintWriter(System.out, true)); 
	*/
	f.flowGraph().touch();
	return(true);
    }


    class Trace {
	private Util util;
	private SsaEnvironment env;
	private SsaSymTab sstab;
	Function f;

	public Trace (Function f, SsaEnvironment e, SsaSymTab tab, int loc, LirNode node, BasicBlk b) {
	    this.f = f;
	    this.env = e;
	    this.sstab = tab;
	    this.util = new Util(env,f);
	    f.touch();

	    LiveVariableAnalysis ana;
	    ana=(LiveVariableAnalysis)f.require(LiveVariableSlotwise.analyzer);
	    BiList liveIn = ana.liveIn(f.flowGraph().entryBlk());

	    if (liveIn.length() != 0) {

		System.out.println("There are some undefined variables!");
		for(BiLink qq=liveIn.first();!qq.atEnd();qq=qq.next()){
		    Symbol sym = (Symbol)qq.elem();
		    System.out.println(sym.name);
		    if (sym.name.equals("nSelectors.90%")) return;
		}
		System.out.println("\n");
		if (node != null && b != null) 
		    System.out.println("Trace "+loc+": node = "+node.toString()+" at "+b.id);
		else if (node != null) 
		    System.out.println("Trace "+loc+": node = "+node.toString());
		else if (b != null) 
		    System.out.println("Trace "+loc+" at "+b.id);
		f.flowGraph().printIt(new java.io.PrintWriter(System.out, true)); 
		System.exit(1);
	    }
	}
    }

}

