/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.Function;
import coins.backend.Op;
import coins.backend.cfg.FlowGraph;
import coins.backend.cfg.BasicBlk;
import coins.backend.util.BiLink;
import coins.backend.util.BiList;
import coins.backend.util.ImList;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.sym.Symbol;

import java.util.Hashtable;
import java.util.Stack;
import java.util.Vector;
import java.util.Enumeration;

class DDCopyPropagation {
  /** The output stream of the compiler **/
    private SsaEnvironment env;
    public static final int THR=SsaEnvironment.OptThr;
    private RankTable expRankMap;
    private RankTable phiRankMap;
    private int[] rank;
    private Function function;
    private Util util;
    Hashtable variableMap;
    private FlowGraph g;
    private Hashtable occurMap;
    private Hashtable phiMap;
    private Hashtable rPhiMap;
    private PREQP pre;

    public DDCopyPropagation(SsaEnvironment e,Function func, PREQP preEqp){

	function = func;
	env=e;
	pre = preEqp;
	util=new Util(env,function);

	g=function.flowGraph();

	variableMap=new Hashtable();

    // Get the information about copy assign expressions.
	for(BiLink p=g.basicBlkList.first();!p.atEnd();p=p.next()){
	    BasicBlk blk=(BasicBlk)p.elem();
	    for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
		LirNode node=(LirNode)q.elem();
		Stack stack=new Stack();
		stack.push(node);

		while(!stack.empty()){
		    LirNode n=(LirNode)stack.pop();

		    for(int i = 0;i<n.nKids();i++){
			if(n.kid(i).opCode==Op.REG){
			    Symbol ref=((LirSymRef)n.kid(i)).symbol;
	      
			    Hashtable v = (Hashtable)variableMap.get(ref.name);
			    if (v == null) {
				v = new Hashtable();
				//System.out.println(" put: "+ref);		
				variableMap.put(ref.name,v);
			    }

			    if (v.get(makeBNKey(blk,node)) == null){
				Object[] pair = {blk,q};
				v.put(makeBNKey(blk,node),pair);
			    }
			}
			else stack.push(n.kid(i));
		    }
		}
	    }
	}
    }

    String makeBNKey(BasicBlk blk, LirNode n) {
	return blk.id+","+n.id;
    }

  public void doIt(BasicBlk blk, LirNode node){

    // Replace copied variable
//System.out.println("cpy by: "+node.toString()+":"+blk.id);
    Vector postCpy = new Vector();
    Symbol dst = ((LirSymRef)node.kid(0)).symbol;
    Hashtable v = (Hashtable)variableMap.get(dst.name);
    if (v == null) v = new Hashtable();
    Enumeration varEnum = v.elements();
//System.out.print(" replace: "+node.toString());
    while (varEnum.hasMoreElements()){
      Object[] bn = (Object[])varEnum.nextElement();
      BasicBlk bk = (BasicBlk)bn[0];
      LirNode nd = (LirNode)((BiLink)bn[1]).elem();
//System.out.println(makeBNKey(bk,nd));
//System.out.println("\t"+nd.toString()+" is modified");
      Stack stack=new Stack();
      stack.push(nd);
      boolean mod = false;

      LirNode oldNd = nd.makeCopy(env.lir);
      while(!stack.empty()){
	LirNode n=(LirNode)stack.pop();
	for(int i = 0;i<n.nKids();i++){
	    if(n.kid(i).opCode==Op.REG) {
		Symbol s=((LirSymRef)n.kid(i)).symbol;
		if  (s == dst) {
		    mod = true;
		    env.println("ACPYP : in "+node+" in block "+blk.id,THR);
		    env.print("ACPYP : "+n.kid(i)+" ---> ",THR);
		    LirNode newNode=node.kid(1).makeCopy(env.lir);
		    n.setKid(i,newNode);
		    env.println(n.kid(i).toString(),THR);
		    g.touch();
		}
	    }
	    else stack.push(n.kid(i));
	}
      }
      switch(nd.opCode){
      case Op.PHI:
	  if (nd.kid(0).opCode != Op.REG) 
	      System.out.println(nd.kid(0).toString());
	  boolean allSameArgs = true;
	  for (int i = 1; i < nd.nKids(); i++) {
	      if(nd.kid(i).kid(0).opCode != Op.REG) { allSameArgs = false; break; }

	      if(((LirSymRef)nd.kid(1).kid(0)).symbol != ((LirSymRef)nd.kid(i).kid(0)).symbol) {
		  allSameArgs = false;
		  break;
	      }
	  }

	  if (allSameArgs) {
	      LirNode left = env.lir.symRef(((LirSymRef)nd.kid(0)).symbol);
	      LirNode right = nd.kid(1).kid(0).makeCopy(env.lir);
	      LirNode newNode = env.lir.operator(Op.SET,nd.type,left,right,
						     ImList.Empty);
	      Object[] pair = {bk, newNode};
	      postCpy.add(pair);
	      pre.maintainTableDeletePhi(oldNd,nd,bk); 
	      ((BiLink)bn[1]).unlink();
	  }
	  if (mod) {
	      pre.maintainTableReplacePhi(oldNd,nd,bk);
	  }
	  
	  break;
      case Op.SET:
	if(nd.kid(0).opCode==Op.REG && 
	   nd.kid(1).opCode!=Op.INTCONST &&
	   nd.kid(1).opCode!=Op.FLOATCONST &&
	   nd.kid(1).opCode!=Op.REG &&
	   nd.kid(1).opCode!=Op.CALL &&
	   nd.kid(1).opCode!=Op.USE &&
	   //nd.kid(1).opCode!=Op.MEM && // temporal addition
	   nd.kid(1).opCode!=Op.CLOBBER) {
	  if (mod) {
	      pre.maintainTableReplaceExp(oldNd,nd,bk);
	  }
	}
	break;
      }
    }
    //env.println("",THR);
    variableMap.remove(dst.name);
    if (node.kid(1).opCode == Op.REG) {
	Symbol src = ((LirSymRef)node.kid(1)).symbol;
	Hashtable cCnt = (Hashtable)variableMap.get(src.name);
	if (cCnt != null ) v.putAll(cCnt);
	variableMap.put(src.name, v);
    }
    Enumeration postCpyE = postCpy.elements();
    while(postCpyE.hasMoreElements()){
	Object[] pair = (Object[])postCpyE.nextElement();
	doIt((BasicBlk)pair[0],(LirNode)pair[1]);
    }

    // Get the information about copy assign expressions.
    /*
    for(BiLink p=function.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk b=(BasicBlk)p.elem();
      for(BiLink q=b.instrList().first();!q.atEnd();q=q.next()){
        LirNode nod=(LirNode)q.elem();
	if (nod ==  node) continue;
	if (nod.opCode == Op.SET) nod = nod.kid(1);
	BiList operands=util.findTargetLir(nod,Op.REG,new BiList());
	for(BiLink pp=operands.first();!pp.atEnd();pp=pp.next()){
	    LirSymRef ref=(LirSymRef)pp.elem();
	    if(ref.symbol == ((LirSymRef)node.kid(0)).symbol) {
		System.err.println("Copy is not completed! at "+ref.symbol.name+" of "+nod.toString()+":"+b.id);
		System.exit(1);
	    }
	}
      }
    }
    */
  }
}

