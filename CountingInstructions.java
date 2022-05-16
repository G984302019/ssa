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
import coins.backend.Keyword;
import coins.backend.Storage;
import java.util.Hashtable;
import java.util.Stack;
import java.util.Vector;
import java.util.BitSet;
import coins.backend.lir.LirIconst;
import coins.ssa.BitVector;
import coins.backend.util.QuotedString;
import java.io.*;

public class CountingInstructions implements LocalTransformer {
    private boolean debugFlag;

    public boolean doIt(Data data, ImList args) { return true; }
    public String name() { return "Counting Instructions"; }
    public String subject() {
	return "Counting Instructions";
    }

    private Util util;
    private String tmpSymName="_ci";
    public static final int THR=SsaEnvironment.OptThr;
    /** The threshold of debug print **/
    public static final int THR2=SsaEnvironment.AllThr;
    private SsaEnvironment env;
    private SsaSymTab sstab;
    private Function f;

    // The name of a counter variable
    private String counterStr="var_cnt.0".intern();
    // The name of the label for string "%lld\n"
    private String fprintfStr="string_cnt.1".intern();
    // The name of the label for string "/tmp/<f.module.name>/<f.symbol.name>.cnt
    private String fileStr="string_cnt.2".intern();
    // The name of the label for string "a", 
    //     which specifies the mode of function "fopen".
    private String modeStr="string_cnt.3".intern();
    // It is not used.
    private String funcValueStr1 = "functionvalue_cnt.1";
    // The name of REG used as the return value of fopen
    private String funcValueStr2 = "functionvalue_cnt.2";
    // The name of REG used as the return value of fprintf
    private String funcValueStr3 = "functionvalue_cnt.3";

    private LirNode funcValueFopen;
    private int mode;
    private int size;

    Symbol cSym, fSym, fSym2, fSym3, dSym, dSym2, dSym3, rSym1, rSym2, rSym3;
    public CountingInstructions(SsaEnvironment e, SsaSymTab tab, int m, int _size){
      env=e;
      sstab=tab;
      mode = m;
      size = _size;
    }

    // Create the code of incrementing the counter variable
    private LirNode makeCounter (int countInBB) {
	LirNode ref = env.lir.symRef(cSym);
	LirNode newMem = env.lir.operator(Op.MEM, cSym.type,
					ref,ImList.Empty);

	LirNode oneInst = null;
	switch (mode) {
	case 0:
	    oneInst = env.lir.iconst(cSym.type,countInBB,ImList.Empty);
	    break;
	case 1:
	    oneInst = env.lir.fconst(cSym.type,countInBB,ImList.Empty);
	}

	LirNode addInst = env.lir.operator(Op.ADD, cSym.type, newMem, oneInst, ImList.Empty);
	LirNode inst = env.lir.operator(Op.SET, cSym.type, newMem,
					addInst,ImList.Empty);
	return inst;
    }

    // Create the declaration and initialization of the counter variable
    private LirNode makeInit () {
	LirNode ref = env.lir.symRef(cSym);
	LirNode newMem = env.lir.operator(Op.MEM, cSym.type, ref,ImList.Empty);
	LirNode oneInst = null;
	switch (mode) {
	case 0:
	    oneInst = env.lir.iconst(cSym.type, 0, ImList.Empty);
	    break;
	case 1: 
	    oneInst = env.lir.fconst(cSym.type, 0.0, ImList.Empty);
	}
	LirNode inst = env.lir.operator(Op.SET, cSym.type, newMem,
					oneInst,ImList.Empty);
	return inst;
    }
    
    // It is not used.
    private LirNode makeCallPrintf() {
	LirNode ref = env.lir.symRef(cSym);
	LirNode newMem = env.lir.operator(Op.MEM, cSym.type,
					ref,ImList.Empty);
	LirNode params = env.lir.operator(Op.LIST, Type.UNKNOWN, env.lir.symRef(dSym), newMem, null);
	LirNode rtns = env.lir.operator(Op.LIST, Type.UNKNOWN, 
					env.lir.operator(Op.MEM, Type.type(Type.INT,32),
							 env.lir.symRef(Op.FRAME, Type.type(Type.INT,32), 
									sstab.newSsaSymbol(tmpSymName,
											   Type.type(Type.INT,32)),
									ImList.Empty), ImList.Empty),null);
	return env.lir.operator(Op.CALL, Type.UNKNOWN, env.lir.symRef(fSym), params, rtns, ImList.Empty);
    }

    // Create the code of the call of function fopen
    private LirNode makeCallFopen() {
	LirNode params = env.lir.operator(Op.LIST, Type.UNKNOWN, env.lir.symRef(dSym2), env.lir.symRef(dSym3), null);
	funcValueFopen = env.lir.operator(Op.MEM, Type.type(Type.INT,32), env.lir.symRef(rSym2),ImList.Empty);
	LirNode rtns = env.lir.operator(Op.LIST, Type.UNKNOWN, funcValueFopen, null);

	return env.lir.operator(Op.CALL, Type.UNKNOWN, env.lir.symRef(fSym2), params, rtns, ImList.Empty);
    }

    
    // Create the code of the call of function fprintf
    private LirNode makeCallFprintf() {
	LirNode ref = env.lir.symRef(cSym);
	LirNode newMem = env.lir.operator(Op.MEM, cSym.type,
					ref,ImList.Empty);
	LirNode params = env.lir.operator(Op.LIST, Type.UNKNOWN, funcValueFopen.makeCopy(env.lir), env.lir.symRef(dSym), newMem, null);
	LirNode rtns = env.lir.operator(Op.LIST, Type.UNKNOWN, 
					env.lir.operator(Op.MEM, Type.type(Type.INT,32),
							 env.lir.symRef(rSym3), ImList.Empty), null);
	return env.lir.operator(Op.CALL, Type.UNKNOWN, env.lir.symRef(fSym3), params, rtns, ImList.Empty);
    }

    // translate a charactor string into a list of charactors
    private ImList toCharList(String s) {
	char[] charArray = s.toCharArray();
	ImList list = ImList.Empty;
	for (int i = 0; i < charArray.length; i++) 
	    list = list.append (new ImList(Integer.toString(((int)charArray[i]))));
	return list;
    }

    // Create data entries for the counter variable
    private void makeGlobalEntry() {
	ImList dataList1 = null;
	switch (mode) {
	case 0:
	    dataList1 = ImList.list(Keyword.DATA, new QuotedString(counterStr), ImList.list("I"+(size*8), "0"));
	    break;
	case 1:
	    dataList1 = ImList.list(Keyword.DATA, new QuotedString(counterStr), ImList.list("F"+(size*8), "0"));
	}

	Data data1 = null;	
	try {
	    data1 = new Data(f.module, dataList1);
	} catch (Exception e) {
	    System.err.println("Syntax error in new Data: "+e);
	}
	env.module.elements.add(data1);	
    }

    // Create data entries for library functions and charactor strings
    private void makeDataEntry () {
       	ImList dataList0 = null; // = ImList.list(Keyword.DATA, new QuotedString(fprintfStr), ImList.list("I8","37","100","10","0"));
	switch (mode) {
	case 0: 
	    if (size == 8)
		dataList0 = ImList.list(Keyword.DATA, new QuotedString(fprintfStr), 
					((new ImList("I8")).append(toCharList("%lld\n"))).append(new ImList("0"))); 
	    else 
		dataList0 = ImList.list(Keyword.DATA, new QuotedString(fprintfStr), 
					((new ImList("I8")).append(toCharList("%d\n"))).append(new ImList("0"))); 
	    break;
	case 1: dataList0 = ImList.list(Keyword.DATA, new QuotedString(fprintfStr), 
					((new ImList("I8")).append(toCharList("%f\n"))).append(new ImList("0"))); break;
	}
  String moduleName=getProperModulename(f.module.name);

	ImList dataList2 = ImList.list(Keyword.DATA, new QuotedString(fileStr), 
				       ((new ImList("I8")).append(toCharList("/tmp/"+moduleName+"."+f.symbol.name+".cnt")))
				       .append(new ImList("0")));
	ImList dataList3 = ImList.list(Keyword.DATA, new QuotedString(modeStr), ImList.list("I8","97","0"));
	Data data0 = null;
	Data data2 = null;
	Data data3 = null;
	try {
	    data0 = new Data(f.module, dataList0);
	    data2 = new Data(f.module, dataList2);
	    data3 = new Data(f.module, dataList3);
	} catch (Exception e) {
	    System.err.println("Syntax error in new Data: "+e);
	}

	env.module.elements.add(data0);
	env.module.elements.add(data2);	
	env.module.elements.add(data3);	
    }


  private String getProperModulename(String str) {
    String separator=File.separator;
    String[] path=str.split(separator);
    if(path.length==0) return str;
    return path[path.length-1];
  }

    public boolean doIt(Function function,ImList args) {

	f = function;
	util=new Util(env,f);

	cSym = f.module.globalSymtab.get(counterStr);
	if (cSym == null) 
	    switch (mode) {
	    case 0:
		cSym = f.module.globalSymtab.addSymbol(counterStr, Storage.STATIC, 
						       Type.type(Type.INT,size*8), size, ".data", "XDEF", 
						       ImList.list("&syminfo", new QuotedString(counterStr), new QuotedString(f.module.name), "1", "0"));
		break;
	    case 1:
		cSym = f.module.globalSymtab.addSymbol(counterStr, Storage.STATIC, 
						       Type.type(Type.FLOAT,size*8), size, ".data", "XDEF", ImList.Empty);
	    }

	// Insert the counter variable
	for(BiLink pp=f.flowGraph().basicBlkList.first();!pp.atEnd();pp=pp.next()){

	    BasicBlk v=(BasicBlk)pp.elem();
	    if (v == f.flowGraph().exitBlk()) continue;

	    int countInBB = 0;
	    for(BiLink p=v.instrList().first();!p.atEnd();p=p.next()){
		LirNode node=(LirNode)p.elem();

		/*
		if (node.opCode == Op.SET && 
		    node.kid(0).opCode == Op.REG && 
		    (node.kid(1).opCode == Op.REG ||
		     node.kid(1).opCode == Op.INTCONST ||
		     node.kid(1).opCode == Op.FLOATCONST))
		    continue;
		if (node.opCode == Op.PHI)
		    continue;
		*/

		countInBB++;
	    }
	    //System.out.println("each last: "+((LirNode)v.instrList().last().elem()).toString());
	    for (BiLink lk = v.instrList().first(); !lk.atEnd(); lk = lk.next()) {
		LirNode pinst = (LirNode)lk.elem();
		if (pinst.opCode == Op.PHI || pinst.opCode == Op.PROLOGUE) continue;

		lk.addBefore(makeCounter(countInBB));
		break;
	    }
	    //		v.instrList().last().addBefore(makeCounter(countInBB));
	}

	
	// Create symbols from the names
	
	fSym2 = f.module.globalSymtab.get("fopen".intern());
	if (fSym2 == null) 
	    fSym2 = sstab.newGlobalSymbol("fopen".intern());
	rSym2 = f.localSymtab.get(funcValueStr2);
	if (rSym2 == null) 
	    rSym2 = f.addSymbol(funcValueStr2, Storage.FRAME, 
				Type.UNKNOWN, 4, 0, ImList.Empty);
	fSym3 = f.module.globalSymtab.get("fprintf".intern());
	if (fSym3 == null) 
	    fSym3 = sstab.newGlobalSymbol("fprintf".intern());
	rSym3 = f.localSymtab.get(funcValueStr3);
	if (rSym3 == null) 
	    rSym3 = f.addSymbol(funcValueStr3, Storage.FRAME, 
				Type.type(Type.INT,32), 4, 0, ImList.Empty);

	boolean isSet = false;
		    
	dSym = f.module.globalSymtab.get(fprintfStr);
	if (dSym == null) 
	    dSym = f.module.globalSymtab.addSymbol(fprintfStr, Storage.STATIC, 
						   Type.UNKNOWN, 1, ".text", "LDEF", ImList.Empty);
	else isSet = true;
		    
	dSym2 = f.module.globalSymtab.get(fileStr);
	if (dSym2 == null) 
	    dSym2 = f.module.globalSymtab.addSymbol(fileStr, Storage.STATIC, 
						    Type.UNKNOWN, 1, ".text", "LDEF", ImList.Empty);
	dSym3 = f.module.globalSymtab.get(modeStr);
	if (dSym3 == null) 
	    dSym3 = f.module.globalSymtab.addSymbol(modeStr, Storage.STATIC, 
						    Type.UNKNOWN, 1, ".text", "LDEF", ImList.Empty);
	if (!isSet)
	    makeDataEntry();

	//LirNode init = makeInit();
	//	    LirNode printf = makeCallPrintf();
	LirNode fopen = makeCallFopen();
	LirNode fprintf = makeCallFprintf();
	BasicBlk entry = f.flowGraph().entryBlk();
	BasicBlk exit = f.flowGraph().exitBlk();

	// Insert output instructions before the call of function exit
	for(BiLink pp=f.flowGraph().basicBlkList.first();!pp.atEnd();pp=pp.next()){
	    BasicBlk v=(BasicBlk)pp.elem();
	    if (v == f.flowGraph().exitBlk()) continue;
		
	    for (BiLink nl = v.instrList().first(); !nl.atEnd(); nl = nl.next()) {
		LirNode ex = ((LirNode)nl.elem());
		
		if (ex.opCode == Op.CALL && 
		    ((LirSymRef)ex.kid(0)).symbol.name.intern()
		    == "exit".intern()) {

		    nl.addBefore(fopen);
		    nl.addBefore(fprintf);
		}
	    }
	}		


	// Insert output instructions before exit node. (It is only for the case of function main.)
	//System.out.println(f.symbol.name.intern());
	if (f.symbol.name.intern() == "main".intern()) {
	    /*
	    fSym = f.module.globalSymtab.get("printf".intern());
	    if (fSym == null) {
		fSym = sstab.newGlobalSymbol("printf".intern());
		rSym1 = f.addSymbol(funcValueStr, Storage.FRAME, 
				    Type.type(Type.INT,32), 4, 0, ImList.Empty);
	    }
	    */

	    makeGlobalEntry();

	    //entry.instrList().first().addAfter(init);
	    //System.out.println("last: "+((LirNode)exit.instrList().first().elem()).toString());
	    BitSet blks = new BitSet(f.flowGraph().idBound());
//	    for(BiLink pp=exit.predList().first();!pp.atEnd();pp=pp.next()){
//	    	BasicBlk p = (BasicBlk)pp.elem();
//	    	if (blks.get(p.id)) continue;
//
//	    	BiLink last = p.instrList().last();
//	    	/*
//			BiLink prev = last.prev();
//			LirNode exn = (LirNode)prev.elem();
//			//System.out.println("exn: "+exn);
//		
//			if (exn.opCode == Op.CALL && 
//		    	((LirSymRef)exn.kid(0)).symbol.name.intern()
//		    	== "exit".intern())
//		    	last = prev;
//	    	 */
//	    	last.addBefore(fopen);
//	    	last.addBefore(fprintf);
//
//	    	blks.set(p.id);
//	    }
		BasicBlk insBlk=f.flowGraph().insertNewBlkBefore(exit);
		for(BiLink pp=exit.predList().first();!pp.atEnd();pp=pp.next()) {
			BasicBlk p=(BasicBlk)pp.elem();
			if(blks.get(p.id)) continue;
			p.replaceSucc(exit, insBlk);
			blks.set(p.id);
		}
		insBlk.replaceSucc(insBlk, exit);
		BiLink last=insBlk.instrList().last();
		last.addBefore(fopen);
		last.addBefore(fprintf);
	}

	f.flowGraph().touch();
	return(true);
    }
}

