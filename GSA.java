/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
/*
the case where a query reaches uneffective traces of propagated queries is problem.
*/


package coins.ssa;

import java.util.ArrayList;
import java.util.Arrays;

//import java.util.Enumeration;
//import java.util.Hashtable;
//import java.util.Stack;
//import java.util.Vector;

import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.Type;
import coins.backend.ana.DFST;
import coins.backend.ana.Dominators;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.sym.Symbol;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;

public class GSA implements LocalTransformer {
    private boolean debugFlag;

    public boolean doIt(Data data, ImList args) { return true; }
    public String name() { return "GSA"; }
    public String subject() {
    	return "Optimizatin with efficient question propagation.";
    }
    private String tmpSymName="_gsa";
    
    public static final int THR=SsaEnvironment.OptThr;
    /** The threshold of debug print **/
    public static final int THR2=SsaEnvironment.AllThr;
    private SsaEnvironment env;
    private SsaSymTab sstab;
    private Function f;
    private Dominators dom;
    private DFST dfst;
    // Copy Propagation
    private DDCopyPropagation cpy;
    private CopyPropagation cpyp;
    MemoryAliasAnalyze alias;
    /*    private Hashtable memArgs;*/
	public BasicBlk[] bVecInOrderOfRPost;
    
    int idBound;
	boolean[] nSameAddr;
	boolean[] xSameAddr;
	boolean[] nIsSame;
	boolean[] xIsSame;
	boolean[] nUse;
	boolean[] xUse;
	boolean[] Transp_e;
	boolean[] Transp_addr;
	boolean[] xTransp_addr;
	public boolean[] nDelayed;
	public boolean[] xDelayed;
	public boolean[] nEarliest;
	public boolean[] xEarliest;
	public boolean[] nKeepOrder;
	public boolean[] xKeepOrder;
	public boolean[] nLatest;
	public boolean[] xLatest;
	public boolean[] nUSafe;
	public boolean[] xUSafe;
	public boolean[] nDSafe;
	public boolean[] xDSafe;
	public boolean[] pUSafe;
	public boolean[] pNDSafe;
	public boolean[] pXDSafe;
	public boolean[] nIsolated;
	public boolean[] xIsolated;
	public boolean[] nInsert;
	public boolean[] xInsert;
	public boolean[] nReplace;
	public boolean[] xReplace;
	
    /**
     * Constructor
     * @param e The environment of the SSA module
     * @param tab The symbol tabel of the SSA module
     * @param function The current function
     * @param m The current mode
     **/
    public GSA(SsaEnvironment env, SsaSymTab sstab) {
		this.env = env;
		this.sstab = sstab;
	}
    
    LirNode removingLocalRedundancy(BiLink p,LirNode statement) {
    	for(;!p.atEnd();p=p.prev()) {
    		LirNode ps = (LirNode)p.elem();
//    		System.out.println("** Checking nodes **");
//    		System.out.println(ps);
//    		System.out.println(kill(ps,statement));
    		if(isUse(ps,statement)) break;
    		if(ps.opCode!=Op.SET) continue;
    		if(ps.kid(1).equals(statement.kid(1))){
    			return ps.kid(0);
    		}    	
    	}
    	return null;
    }
    /**
     * Do optimize using Efficient Question Propagation.
     * @param f The current function
     **/
    
    LirNode createNewStatement(LirNode statement) {
    	LirNode newSt = statement.makeCopy(env.lir);
//    	System.out.println("Checking newSt");
//    	System.out.println(newSt);
    	Symbol dstSym = sstab.newSsaSymbol(tmpSymName, newSt.type);
    	LirNode nn = env.lir.symRef(Op.REG, dstSym.type, dstSym, ImList.Empty);
    	LirNode newNode = env.lir.operator(Op.SET, newSt.type, nn, newSt.kid(1),ImList.Empty);
//    	System.out.println("new node:"+newNode);
    	return newNode;
    }    
    
    void printBB(BasicBlk v) {
  	   for(BiLink p=v.instrList().first();!p.atEnd();p=p.next()){
         	LirNode node=(LirNode)p.elem();
         	System.out.println(node);
  	   }
     }
     
     void printBBs() {
  	   for(BiLink pp=f.flowGraph().basicBlkList.first();!pp.atEnd();pp=pp.next()){
  	        BasicBlk v=(BasicBlk)pp.elem();
  	        
  	        System.out.println("");
  	        System.out.println("");
  	        System.out.println("***");
  	        System.out.println("BB:"+v.label() + ". BBID:"+v.id);
  	        for(BiLink p=v.instrList().first();!p.atEnd();p=p.next()){
  	        	LirNode node=(LirNode)p.elem();
  	        	System.out.println(node);
  	        }
  	   }
     }
    
   void displayBasicBlk() {
	   System.out.println("-------------------------------------------");
	   for(BiLink p =f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
		   BasicBlk v=(BasicBlk)p.elem();
		   System.out.println(v.id);
		   for(BiLink bl=v.instrList().first();!bl.atEnd();bl=bl.next()){
			   LirNode node=(LirNode)bl.elem();
			   System.out.println(node);
		   }
	   }
	   System.out.println("-------------------------------------------");
    }
   
    /**
     *s1の左辺とs2の右辺を比較して同じのがないか確認する
     * @param s1 killかどうかを見る命令。
     * @param s2 s1をkillかどうかチェックする右辺。
     * @return
     */
    boolean isUse(LirNode s1, LirNode s2) {
//    	System.out.println("***********************");
//    	System.out.println("s1:" + s1);
//    	System.out.println("s2:" + s2);
    	if(s1.kid(0).equals(s2.kid(1))) {
    		return true;
    	}
    	return false;
    	
    	//元コード
//    	if(s2.kid(1).opCode == Op.MEM) {
//    		if(s1.kid(0).equals(s2.kid(1).kid(0))) {
//    			System.out.println(true);
//    			return true;
//    		}
//    	}
//    	if(s2.opCode==Op.SET&&s2.nKids()>1) {
//    		switch(s2.kid(1).opCode) {
//    		case Op.ADD:
//    		case Op.SUB:
//    		case Op.MUL:
//    		case Op.DIVS:
//    			if(s1.kid(0).equals(s2.kid(1).kid(0))||s1.kid(0).equals(s2.kid(1).kid(1))) {
//    				System.out.println(true);
//    				return true;
//    			}
//    		case Op.CONVSX:
//    			if(s1.kid(0).equals(s2.kid(1).kid(0))) {
//    				System.out.println(true);
//    				return true;
//    			}
//    		}
//    		if(s1.kid(0).equals(s2.kid(1))) {
//    			System.out.println(true);
//    			return true;
//    		}
//    	}
//    	if(s2.opCode==Op.CALL&&s2.nKids()>1) {
//    		if(s2.kid(1).nKids()>0) {
//    			if(s1.kid(0).equals(s2.kid(1).kid(0))) {
//    				System.out.println(true);
//    				return true;
//    			}
//    		}
//    	}
//    	System.out.println(false);
//    	return false;
    		
    	
//    	if(s1.opCode==Op.SET) {
//    		if(s2.kid(1).opCode==Op.MEM && s1.kid(0).opCode==Op.MEM) {
//    			return true;
//    		}
//    		if(s2.kid(1).nKids() < 2) {
//    			if(s1.kid(0).equals(s2.kid(1))) {
//    				return true;
//    			} 
//    		} 
//    		else if(s1.kid(0).equals(s2.kid(1).kid(0))) {
//    			return true;
//    		}  
//    		else if(s1.kid(0).equals(s2.kid(1).kid(1))) {
//    			return true;
//    		}
//    	}  
//    	else if(s1.opCode == Op.CALL){
//    		if(s2.opCode == Op.SET && s2.kid(1).opCode==Op.MEM) {
//    			return true;
//    		}
//    		else if(s2.kid(1).nKids()<2){
//    			if(s1.kid(2).nKids()<2) {
//    				if(s1.kid(2).equals(s2.kid(1))) {
//    					return true;
//    				}
//    			}
//    			else if(s1.kid(2).kid(0).equals(s2.kid(1))){
//    				return true;
//    			} 
//    		} 
//    		else if(s1.kid(2).nKids()<2) {
//    			if(s1.kid(2).equals(s2.kid(1).kid(0))) {
//    				return true;
//    			}
//    			else if(s1.kid(2).equals(s2.kid(1).kid(1))) {
//    				return true;
//    			}
//    		}
//    		else if(s1.kid(2).kid(0).equals(s2.kid(1).kid(0))) {
//    			return true;
//    		}
//    		else if(s1.kid(2).kid(0).equals(s2.kid(1).kid(1))) {
//    			return true;
//    		}
//    	}
//    	return false;
    }
    
    //TODO collectVarsメソッドの内容を確認する。
    public void collectVars(ArrayList vars, LirNode exp){
		for(int i=0;i<exp.nKids();i++){
			if(exp.kid(i).opCode==Op.REG) vars.add(exp.kid(i).makeCopy(env.lir));
//			if(exp.kid(i).opCode==Op.REG) {//
//				System.out.println(":::vars.add"+exp.kid(i));//
//				vars.add(exp.kid(i).makeCopy(env.lir));//
//			}//
			else if(exp.kid(i).nKids()>0) collectVars(vars,exp.kid(i));
		}
	}
    
    //load命令かどうかを判断する
    public boolean isLoad(LirNode node){
//		return (node.opCode==Op.SET && node.kid(0).opCode==Op.REG && node.kid(1).opCode==Op.MEM);
    	return (node.opCode==Op.SET && node.kid(0).opCode==Op.REG);
    }
    
    //store命令かどうかを判断する
    public boolean isStore(LirNode node) {
    	return(node.opCode==Op.SET && node.kid(0).opCode==Op.MEM);
    }
    
    public boolean isGlobalPointer(LirNode node) {
    	if(isStore(node)&&getAddr(node).opCode != Op.FRAME)return true;
    	return false;
    }
    
    
    //そのノードが削除できる可能性があるものなのかを判断するメソッド
    //a[i]=0の時のi,x=yの時のyなど変数の値を変更する可能性があるノード
    //TODO 同様の配列の場合はtrueにするようにする。例えばa[i]の時のa
//    public boolean isKill(LirNode expr, LirNode node, ArrayList vars, BasicBlk blk, BiLink p){
////    	System.out.println("isKill"+node);
//		if(node.opCode==Op.CALL)return true;//何らかの関数呼び出しがあった場合に問答無用でtrueにする。
//		//FRAME,STATIC,REG、
////		if(node.opCode==Op.SET && node.kid(0).opCode==Op.MEM && ddalias.checkAlias(expr, node.kid(0), blk, p))return true;
//		if(vars.contains(node.kid(0)))return true;// conectvarsメソッドと共に何を確認しているかのチェック
////		System.out.println(false);
//		if(isStore(node)) {
//			LirNode addr = getAddr(expr);
//			if(sameAddr(node,addr)) {
//				return false;
//			}else {
//				return true;
//			}
//		}
//		return false;
//	}
    
//    public boolean isKill(LirNode noden, LirNode expr, LirNode node, ArrayList vars, BasicBlk blk, BiLink p){
////    	System.out.println("---isKill---"+node);
////		if(node.opCode==Op.CALL)return true;//何らかの関数呼び出しがあった場合に問答無用でtrueにする。
//		if(noden.equals(node))return false;
//    	
//    	if(node.opCode==Op.CALL) {//
////			System.out.println("++true++CALL");//
//			return true;
//		}
//    	//FRAME,STATIC,REG、
////		if(node.opCode==Op.SET && node.kid(0).opCode==Op.MEM && ddalias.checkAlias(expr, node.kid(0), blk, p))return true;
//		
//		//インスタンスを調べている。a[i]を対象にした場合i=0などの命令を判定。
//		if(vars.contains(node.kid(0))) {
////			System.out.println("++true++contains");
//			return true;// conectvarsメソッドと共に何を確認しているかのチェック
//		}
//		
////		System.out.println(false);
//		if(isStore(node)) {
////			if(!sameAddr(node,getAddr(expr)) || vars.size() > 0) {//
////				if(!sameAddr(node,getAddr(expr))) System.out.println("++true++!sameaddr");
////				if(vars.size()>0)System.out.println("++true++vars.size()>0");
////				return true;
////			}
//			if(!sameAddr(node,getAddr(expr)))return false;
//			
//			if(isGlobalPointer(node)) return true;
//			
//			if(sameAddr(node,getAddr(expr)) && vars.size()>0) {
//				return true;
//			}
//			
//			ArrayList nvars = new ArrayList();
//			collectVars(nvars,node.kid(0));//〇collectvars
//			
////			if(nvars.size() > 0) {
//			if(sameAddr(node,getAddr(expr)) && nvars.size()>0) {//	
////				System.out.println("++true++nvars");
//				return true;
//			}
//			
////			if(!sameAddress(node,expr) || vars.size() > 0) {
////				return true;
////			}
////			if(nvars.size() > 0) {
////				return true;
////			}
//			
//			
////			LirNode addr = getAddr(expr);
////			if(sameAddr(node,addr)) {
////				return false;
////			}else {
////				return true;
////			}
//		}
////		System.out.println("++false++");
//		return false;
//	}
    
    public boolean isKill(LirNode noden,LirNode expr, LirNode node, ArrayList vars, BasicBlk blk, BiLink p){
//    	System.out.println("isKill"+node);
		if(node.opCode==Op.CALL)return true;//何らかの関数呼び出しがあった場合に問答無用でtrueにする。
		//FRAME,STATIC,REG、
//		if(node.opCode==Op.SET && node.kid(0).opCode==Op.MEM && ddalias.checkAlias(expr, node.kid(0), blk, p))return true;
		
		if(vars.contains(node.kid(0)))return true;// conectvarsメソッドと共に何を確認しているかのチェック
//		System.out.println(false);
		if(isStore(node)) {
			if(!sameAddress(node,expr) || vars.size() > 0) {
				return true;
			}
			
			ArrayList nvars = new ArrayList();
			collectVars(nvars,node.kid(0));//〇collectvars
			
			if(nvars.size() > 0) {
				return true;
			}
//			LirNode addr = getAddr(expr);
//			if(sameAddr(node,addr)) {
//				return false;
//			}else {
//				return true;
//			}
		}
		return false;
	}
    
    
    //同様の配列参照を行っている場合true;
    LirNode getAddr(LirNode exp){
    	if(exp.nKids()==0) return exp;
		if(exp.kid(0).nKids()==0) return exp.kid(0);
		else return getAddr(exp.kid(0));
	}
    
    //同様の配列参照をするload命令があった場合にtrue;
  	public boolean sameAddr(LirNode node, LirNode addr){
  		if(isLoad(node)) {
  			return (addr.equals(getAddr(node.kid(1))));
  		}else if(isStore(node)) {
  			return (addr.equals(getAddr(node.kid(0))));
  		}
  		return false;
  	}
    
    //最初にローカルプロパティを全て初期化する。
	void compLocalProperty(LirNode noden, LirNode exp, LirNode addr, ArrayList vars){
		xSameAddr = new boolean[idBound];
		nSameAddr = new boolean[idBound];
		nUse = new boolean[idBound];
		xUse = new boolean[idBound];
		xIsSame = new boolean[idBound];
		nIsSame = new boolean[idBound];
		Transp_e = new boolean[idBound];
		Transp_addr = new boolean[idBound];
		xTransp_addr = new boolean[idBound];
		Arrays.fill(xSameAddr, false);
		Arrays.fill(nSameAddr, false);
//		System.out.println("exp:"+exp);
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			
			nUse[blk.id] = compNUse(noden,exp,addr,vars,blk);
			xUse[blk.id] = compXUse(noden,exp,addr,vars,blk);
			
			nIsSame[blk.id] = compNIsSame(noden,exp,vars,blk);//〇
			xIsSame[blk.id] = compXIsSame(noden,exp,vars,blk);//〇
			
			nSameAddr[blk.id] = isNSameAddr(noden,exp,vars,blk);
			xSameAddr[blk.id] = isXSameAddr(noden,exp,vars,blk);
			
			//変数のkillが内科のチェック
			Transp_e[blk.id] = compTranspe(noden,exp,addr,vars,blk);
			//配列のアクセス順序が崩れていないかのチェック。
			Transp_addr[blk.id] = compTranspAddr(noden,exp,addr,vars,blk);
			//
			xTransp_addr[blk.id] = compXTranspAddr(noden,exp,addr,vars,blk);
		}
//		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
//			BasicBlk blk = bVecInOrderOfRPost[i];
//			System.out.println(blk.id+":id");
//			if(nIsSame[blk.id]) System.out.println("nIsSame");
//			if(xIsSame[blk.id]) System.out.println("xIsSame");
//			if(Transp_e[blk.id]) System.out.println("Transp_e");
//			if(Transp_addr[blk.id]) System.out.println("Transp_addr");
//			if(xTransp_addr[blk.id]) System.out.println("xTransp_addr");
//			if(nSameAddr[blk.id]) System.out.println("nSameAddr");
//			if(xSameAddr[blk.id]) System.out.println("xSameAddr");
//		}
	}
	
	private boolean isNSameAddr(LirNode noden, LirNode exp, ArrayList vars, BasicBlk blk) {
		for (BiLink p = blk.instrList().first(); !p.atEnd(); p = p.next()) {
			LirNode node = (LirNode) p.elem();
//			if(isStore(node) && sameAddress(node.kid(0),exp))return true;//
//			else if(isKill(noden,exp,node,vars,blk,p))return false;//
//			else if(isLoad(node) && sameAddress(node.kid(1),exp))return true;//
			if (isKill(noden,exp,node,vars,blk,p)) {
				return false;
			} else if(isLoad(node) && sameAddress(node.kid(1),exp)) {
				return true;
			} else if (isStore(node) && sameAddress(node.kid(0),exp)) {
				return true;
			}
		}
		return false;
	}
	boolean sameAddress(LirNode exp1, LirNode exp2) {
		LirNode addr1 = getAddr(exp1);
		LirNode addr2 = getAddr(exp2);
		return addr1.equals(addr2);
	}
	
	private boolean isXSameAddr(LirNode noden, LirNode exp, ArrayList vars, BasicBlk blk) {
		for (BiLink p = blk.instrList().last(); !p.atEnd(); p = p.prev()) {
			LirNode node = (LirNode) p.elem();
//			if(isStore(node) && sameAddress(node.kid(0),exp))return true;//
//			else if(isKill(noden,exp,node,vars,blk,p))return false;//
//			else if(isLoad(node) && sameAddress(node.kid(1),exp))return true;//
			if (isKill(noden,exp,node,vars,blk,p)) {
				return false;
			} else if(isLoad(node) && sameAddress(node.kid(1),exp)) {
				return true;
			} else if (isStore(node) && sameAddress(node.kid(0),exp)) {
				return true;
			}
		}
		return false;
	}	
	
	private boolean compNIsSame(LirNode noden,LirNode exp, ArrayList vars, BasicBlk blk){
//		System.out.println("::NisSame"+blk.id);//
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){//渡された基本ブロックの命令をひとつづつ確認している
			LirNode node = (LirNode)p.elem();
//			System.out.println(node);
//			System.out.println(":isKill");
//			if(isStore(node) && node.kid(0).equals(exp)) return true;//
			if(isKill(noden,exp,node,vars,blk,p))break;//isKillがtrueだったらループ終了
			
			/*
//			System.out.println(":isLoad");//
			if(!isLoad(node))continue;//isLoadがfalseだったら次のループ
//			System.out.println(":equals");
//			if(node.kid(1).equals(exp)) return true;//渡されたノードの配列の一つ目と渡されたexpが同じならtrue
			if(node.kid(1).equals(exp)) { 
//				System.out.println("++TrueTrueTrueTrue++");
//				System.out.println(blk.id);
				return true;
			}
			*/
			
//			System.out.println("");
//			System.out.println("node:"+node);
//			System.out.println("load?"+isLoad(node));
//			if(isLoad(node)) System.out.println("kid1 same?"+node.kid(1).equals(exp));
//			System.out.println("store?"+isStore(node));
//			if(isStore(node)) System.out.println("kid0 same?"+node.kid(0).equals(exp));
			if(isLoad(node) && node.kid(1).equals(exp)) return true;
			if(isStore(node) && node.kid(0).equals(exp)) return true;
		}
//		System.out.println("--FalseFalseFalseFalse--");
		return false;
	}

	//変数xIsSameを変更するためのメソッド
	//変数xIsSameはcompDSafeで用いられている
	//同じ変数の定義をしている分がその先にあるかの判定。
//	private boolean compXIsSame(LirNode exp, ArrayList vars, BasicBlk blk){
////		System.out.println("::XisSame"+blk.id);//
//		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
//			LirNode node = (LirNode)p.elem();
////			System.out.println(node);//
////			System.out.println("::isKill");//
//			if(isKill(exp,node,vars,blk,p))break;//
//			//式の右辺を確認しようとしている。
//			//ロード命令省かなくてもいい。
////			System.out.println(":isLoad");//
//			if(!isLoad(node)) continue;//
////			if(!isLoad(node)) {
////				if(node.kid(1).equals(exp))return true;
////			}else if(isStore(node)){
////				if(node.kid(0).equals(exp))return true;
////			}
////			System.out.println(":equals");
//			if(node.kid(1).equals(exp)) {
////				System.out.println("++TrueTrueTrueTrue++");
////				System.out.println(blk.id);
//				return true;
//			}
//		}
////		System.out.println("--FalseFalseFalseFalse--");
//		return false;
//	}
	private boolean compXIsSame(LirNode noden, LirNode exp, ArrayList vars, BasicBlk blk){
//		System.out.println("::XisSame"+blk.id);//
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode node = (LirNode)p.elem();
//			System.out.println(node);//
//			System.out.println("::isKill");//
//			if(isStore(node) && node.kid(0).equals(exp))return true;//
			if(isKill(noden,exp,node,vars,blk,p))break;//
			//式の右辺を確認しようとしている。
			//ロード命令省かなくてもいい。
//			System.out.println(":isLoad");//
			
			/*
			if(!isLoad(node)) continue;//
//			if(!isLoad(node)) {
//				if(node.kid(1).equals(exp))return true;
//			}else if(isStore(node)){
//				if(node.kid(0).equals(exp))return true;
//			}
//			System.out.println(":equals");
			if(node.kid(1).equals(exp)) {
//				System.out.println("++TrueTrueTrueTrue++");
//				System.out.println(blk.id);
				return true;
			}
			*/
			if(isStore(node) && node.kid(0).equals(exp))return true;
			if(isLoad(node) && node.kid(1).equals(exp)) return true;
		}
//		System.out.println("--FalseFalseFalseFalse--");
		return false;
	}
	
	//EarliestをPDE用に更新
	//Earliestは変えていい。
	//dceメソッドを呼び出したタイミングでEarliestをそのブロックでtrueに
//	public void compEarliest() {
//		nEarliest = new boolean[idBound];
//		xEarliest = new boolean[idBound];
//		Arrays.fill(nEarliest, true);
//		Arrays.fill(xEarliest, true);
//		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
//			BasicBlk blk = (BasicBlk)p.elem();
//			boolean n = nUSafe[blk.id] || nDSafe[blk.id];
//			if(n && blk!=f.flowGraph().entryBlk()){
//				n = false;
//				for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()){
//					BasicBlk pred = (BasicBlk)q.elem();
//					if(!(xUSafe[pred.id] || xDSafe[pred.id])){
//						n = true;
//						break;
//					}
//				}
//			}
//			nEarliest[blk.id] = n;
//			xEarliest[blk.id] = (xUSafe[blk.id] || xDSafe[blk.id]) && (!Transp_e[blk.id] || !(nUSafe[blk.id] || nDSafe[blk.id]) && !n);
//		}
//	}
	
	private boolean compNUse(LirNode noden, LirNode exp, LirNode addr, ArrayList vars, BasicBlk blk){
//		System.out.println("::XisSame"+blk.id);//
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
			LirNode node = (LirNode)p.elem();
//			System.out.println("");
//			System.out.println("--");
//			System.out.println("node:" + node);
//			System.out.println("exp:" + exp);
//			System.out.println("isSame?"+(isStore(node) && node.kid(0).equals(exp)));
//			System.out.println("::isKill");//
			if(isKill(noden,exp,node,vars,blk,p))break;//
			
			if(isLoad(node)) {
				if(node.kid(1).equals(exp)) {
					return true;
				}
				
				if(sameAddr(node,addr)) {
					return true;
				}
			}
			
		}
//		System.out.println("--FalseFalseFalseFalse--");
		return false;
	}
	
	private boolean compXUse(LirNode noden, LirNode exp, LirNode addr, ArrayList vars, BasicBlk blk){
//		System.out.println("@compXUse. blk:"+blk.id);
		
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode node = (LirNode)p.elem();
//			System.out.println("");
//			System.out.println("--");
//			System.out.println("node:" + node);
//			System.out.println("exp:" + exp);
//			System.out.println("isSame?"+(isStore(node) && node.kid(0).equals(exp)));
//			System.out.println("isKill?" + isKill(exp,node,vars,blk,p));
//			System.out.println("isLoad?" + isLoad(node));
//			if(isLoad(node)) {
//				System.out.println("isSame?" + node.kid(1).equals(exp));
//				System.out.println("isAddr?" + sameAddr(node,addr));
//			}
			if(isKill(noden,exp,node,vars,blk,p))break;//
			
			if(isLoad(node)) {
				if(node.kid(1).equals(exp)) {
					return true;
				}
				
				if(sameAddr(node,addr)) {
					return true;
				}
			}
			
		}
//		System.out.println("--FalseFalseFalseFalse--");
		return false;
	}
	
	public void compEarliest(BasicBlk blk) {
		xEarliest = new boolean[idBound];
		nEarliest = new boolean[idBound];
		Arrays.fill(xEarliest, false);
		Arrays.fill(nEarliest, false);
		nEarliest[blk.id] = true;
		xEarliest[blk.id] = true;
//		System.out.println("+++"+blk.id+"+++");
//		System.out.println(":xEarliest:"+xEarliest[blk.id]);
	}
	
	
	//TODO DelayedをPDE用に更新
	//xDelay(n)=(nDelay(n)⋀¬use(n))∨Earliest(n)
	//nDelay(n)=Π(p∊pred(n))xDelay(p)
	public void compDelayed() {
		nDelayed = new boolean[idBound];
		xDelayed = new boolean[idBound];
		Arrays.fill(nDelayed, true);
		Arrays.fill(xDelayed, true);
		boolean change = true;
		while(change) {
			change = false;
//			System.out.println("change");
			for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()) {
				BasicBlk blk = (BasicBlk)p.elem();
				boolean n = false;
//				System.out.println("blk:"+blk.id);
				if(nEarliest[blk.id]) {
//					System.out.println("nEarliest");
					n = true;
				}else if(blk!=f.flowGraph().entryBlk()) {
					n = true;
//					System.out.println("else");
					for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()) {
						BasicBlk pred = (BasicBlk)q.elem();
//						System.out.println("pred:"+pred.id);
						if(!xDelayed[pred.id] || !xKeepOrder[pred.id] || xIsSame[pred.id]) {
//							System.out.println("xDelayed");
							n = false;
							break;
						}
					}
//					System.out.println("forbreak");
				}
				boolean x = (n && !nIsSame[blk.id] && nKeepOrder[blk.id]) || xEarliest[blk.id];
				if(nDelayed[blk.id]!=n || xDelayed[blk.id]!=x) change = true;
				nDelayed[blk.id] = n;
				xDelayed[blk.id] = x;
			}
		}
//		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()) {
//			BasicBlk blk = (BasicBlk)p.elem();
//			System.out.println("+++"+blk.id+"+++");
//			System.out.println(":n:"+nDelayed[blk.id]);
//			System.out.println(":x:"+xDelayed[blk.id]);
//		}
//		while(change){
//			change = false;
//			for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
//				BasicBlk blk = (BasicBlk)p.elem();
//				boolean n = false;
//				if(nEarliest[blk.id]){
//					n = true;
//				}else if(blk!=f.flowGraph().entryBlk()){
//					n = true;
//					for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()){
//						BasicBlk pred = (BasicBlk)q.elem();
//						if(!xDelayed[pred.id] || !xKeepOrder[pred.id] || xIsSame[pred.id]){
//							n = false;
//							break;
//						}
//					}
//				}
//				boolean x = xEarliest[blk.id] || (n && !nIsSame[blk.id] && nKeepOrder[blk.id]);
//				if(nDelayed[blk.id]!=n || xDelayed[blk.id]!=x) change = true;
//				nDelayed[blk.id] = n;
//				xDelayed[blk.id] = x;
//			}
//		}
	}
	
	//変数nDSafe,xDSafeを変更するためのメソッド
		//変数nDSafeはノード上部のDownSafe
		//変数xDSafeは
	//TODO downsafeチェックするときにblk.idと何番目の命令なのかを組み込み、そのブロック内ではその下しか見ないようにする。
	public void compDSafe() {
//		System.out.println("compDSafe");
		nDSafe = new boolean[idBound];
		xDSafe = new boolean[idBound];
		Arrays.fill(nDSafe, true);
		Arrays.fill(xDSafe, true);
		boolean change = true;
		while(change){
			change = false;
			for(BiLink p=f.flowGraph().basicBlkList.last();!p.atEnd();p=p.prev()){
				BasicBlk blk = (BasicBlk)p.elem(); 
//				System.out.println("---"+blk.id+"---");//
				boolean x = false;
//				if(xIsSame[blk.id]||xSameAddr[blk.id]) x = true;
				if(xIsSame[blk.id])x=true;
				else if(blk!=f.flowGraph().exitBlk()){
//					System.out.println("__!exit__");
					x = false;
					for(BiLink q=blk.succList().first();!q.atEnd();q=q.next()){
						BasicBlk succ = (BasicBlk)q.elem();
						if(nDSafe[succ.id]){
//							System.out.println(succ.id+":xtrue");
							x = true;
							break;
						}
					}
				}
				boolean n = nIsSame[blk.id]|| x;
				if(nDSafe[blk.id]!=n || xDSafe[blk.id]!=x) change = true;
//				if(change) {
//					if(nDSafe[blk.id]!=n) System.out.println("^^^nnn^^^"+n);
//					if(xDSafe[blk.id]!=x) System.out.println("^^^xxx^^^"+x);
//				}
				nDSafe[blk.id] = n;
				xDSafe[blk.id] = x;
			}
		}
//		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()) {
//			BasicBlk blk = (BasicBlk)p.elem();
//			System.out.println("+++"+blk.id+"+++");
//			System.out.println(":n:"+nDSafe[blk.id]);
//			System.out.println(":x:"+xDSafe[blk.id]);
//		}
	}

	public void compPartialUSafe() {
		pUSafe = new boolean[idBound];
		Arrays.fill(pUSafe, true);
		for (BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();
			boolean us = false;
			if(nUSafe[blk.id]) us = true;
			else{
				for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()){
					BasicBlk pred = (BasicBlk)q.elem();
					if(xUSafe[pred.id]){
						us = true;
						break;
					}
				}
			}
			pUSafe[blk.id] = us;
		}
	}		
	
	public void compPartialDSafe() {
		pNDSafe = new boolean[idBound];
		pXDSafe = new boolean[idBound];
		Arrays.fill(pNDSafe, false);
		Arrays.fill(pXDSafe, false);
		for (BiLink p=f.flowGraph().basicBlkList.last();!p.atEnd();p=p.prev()) {
			BasicBlk blk = (BasicBlk) p.elem();
			boolean x = false;
			if(xDSafe[blk.id]) x = true;
			else{
				for(BiLink q=blk.succList().first();!q.atEnd();q=q.next()){
					BasicBlk succ = (BasicBlk)q.elem();
					if(pNDSafe[succ.id]){
						x = true;
						break;
					}
				}
			}
			pXDSafe[blk.id] = x;
			pNDSafe[blk.id] = nDSafe[blk.id] || x;
		}
	}
	
	
	public void compKeepOrder(){
		nKeepOrder = new boolean[idBound];
		xKeepOrder = new boolean[idBound];
		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
			BasicBlk blk = (BasicBlk)p.elem();
			nKeepOrder[blk.id] =Transp_addr[blk.id] && !nUSafe[blk.id];//
			xKeepOrder[blk.id] =xTransp_addr[blk.id] && !xUSafe[blk.id];//
//			nKeepOrder[blk.id] = !nUSafe[blk.id] || Transp_addr[blk.id];
//			xKeepOrder[blk.id] = !xUSafe[blk.id] || xTransp_addr[blk.id];
		}
	}

	//同様のインスタンスを持つ配列へのストア命令があった場合にfalse,
	//またxsameaddrの更新
	private boolean compTranspe(LirNode noden, LirNode exp, LirNode addr, ArrayList vars, BasicBlk blk){
//		System.out.println("::compTranspe");//
		boolean xt = true;
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
//		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()) {//
			LirNode node = (LirNode)p.elem();
//			System.out.println(node);//
//			System.out.println(":iskill");//
			//対象の配列のインスタンスを変更する可能性がある場合true;
			if(isKill(noden,exp,node,vars,blk,p)){
//				System.out.println("----false----");
				xt = false;
				break;
			}
//			System.out.println(":isload_isstore");//
//			if(!isLoad(node)&&!isStore(node))continue;
//			System.out.println(":sameaddr");//
//			if(sameAddr(node,addr)) xSameAddr[blk.id] = true;
//			if(xSameAddr[blk.id]) System.out.println("xsameaddr");
		}
//		System.out.println("++++"+xt+"++++");
		return xt;
	}
	
	//同様のストア命令に対する変更も、同様の配列と同様の番地へのロード命令もなければtrue;
	private boolean compTranspAddr(LirNode noden, LirNode exp, LirNode addr, ArrayList vars, BasicBlk blk){
//		System.out.println("::compTranspAddr");//
		if(!Transp_e[blk.id])return false;
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
			LirNode node = (LirNode)p.elem();
//			System.out.println(node);//
//			System.out.println(":isKill");//
			if(isKill(noden,exp,node,vars,blk,p)) {
//				if(noden.equals(node))return true;
				return false;
			}
//			System.out.println(":isload&&isstore");//
			if(!isLoad(node)&&!isStore(node))continue;
//			System.out.println(":sameaddr");//
			if(sameAddr(node,addr)){
//				System.out.println(":");//
//				nSameAddr[blk.id] = true;
				if(node.kid(1).equals(exp))break;
			}else{
//				System.out.println("^^^^false^^^^");//
				return false;
			}
		}
		return true;
	}
	
	//同様のストア命令に対する変更も、異なる配列への参照もない場合true;
	//ノードは上げないからいらないかも
	private boolean compXTranspAddr(LirNode noden, LirNode exp, LirNode addr, ArrayList vars, BasicBlk blk){
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode node = (LirNode)p.elem();
//			if(isStore(node)) {//
//				if(sameAddr(node,addr))break;//
//				else return false;//
//			}//
			if(isKill(noden,exp,node,vars,blk,p)) {
//				if(noden.equals(node))return true;
				return false;
			}
			if(!isLoad(node)&&!isStore(node))continue;
			if(sameAddr(node,addr)) break;
			else return false;
		}
		return true;
	}


	
	//TODO Latestの設定の確認
	public void compLatest() {
		nLatest = new boolean[idBound];
		xLatest = new boolean[idBound];
		for(BiLink p=f.flowGraph().basicBlkList.last();!p.atEnd();p=p.prev()){
			BasicBlk blk = (BasicBlk)p.elem();
			boolean x = false;
			if(xDelayed[blk.id]){
				if(xIsSame[blk.id]) x = true;
				else if(blk!=f.flowGraph().exitBlk()){
					for(BiLink q=blk.succList().first();!q.atEnd();q=q.next()){
						BasicBlk succ = (BasicBlk)q.elem();
						if(!nDelayed[succ.id]){
							x = true;
							break;
						}
					}
				}
			}
			xLatest[blk.id] = x;
			nLatest[blk.id] = nDelayed[blk.id] && (!xDelayed[blk.id] || nIsSame[blk.id]);
//			nLatest[blk.id] = nDelayed[blk.id] && xDelayed[blk.id];
		}
//		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()) {
//			BasicBlk blk = (BasicBlk)p.elem();
//			System.out.println("+++"+blk.id+"+++");
//			System.out.println(":n:"+nUSafe[blk.id]);
//			System.out.println(":x:"+xUSafe[blk.id]);
//		}
	}
	
	public void compIsolated(){
		nIsolated = new boolean[idBound];
		xIsolated = new boolean[idBound];
		Arrays.fill(nIsolated, true);
		Arrays.fill(xIsolated, true);
		boolean change = true;
		while(change){
			change = false;
			for(BiLink p=f.flowGraph().basicBlkList.last();!p.atEnd();p=p.prev()){
				BasicBlk blk = (BasicBlk)p.elem();
				boolean x = true;
				if(blk!=f.flowGraph().exitBlk()){
					for(BiLink q=blk.succList().first();!q.atEnd();q=q.next()){
						BasicBlk succ = (BasicBlk)q.elem();
						if(!(nEarliest[succ.id] || !nIsSame[succ.id] && nIsolated[succ.id])){
							x = false;
							break;
						}
					}
				}
				boolean n = !Transp_e[blk.id] || !nIsSame[blk.id] && (xEarliest[blk.id] || x);
//				boolean n = xEarliest[blk.id] || x;
				if(nIsolated[blk.id]!=n || xIsolated[blk.id]!=x) change = true;
				xIsolated[blk.id] = x;
				nIsolated[blk.id] = n;
			}
		}
	}
    
	//Upsafeが必要なのかの確認とGSA用に更新
	//別にいらなくね？
	//upsafeはそのままでよい。
	public void compUSafe() {
		nUSafe = new boolean[idBound];
		xUSafe = new boolean[idBound];
		Arrays.fill(nUSafe, true);
		Arrays.fill(xUSafe, true);
		boolean change = true;
		while(change){
			change = false;
			for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
				BasicBlk blk = (BasicBlk)p.elem();
				boolean n = false;
				if(blk!=f.flowGraph().entryBlk()){
					n = true;
					for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()){
						BasicBlk pred = (BasicBlk)q.elem();
						if(!xUSafe[pred.id]){
							n = false;
							break;
						}
					}
				}
				//開始節の方向に向かって同じ配列にアクセスしているものを見ている。
				boolean x = xSameAddr[blk.id] || n && Transp_e[blk.id];
				if(nUSafe[blk.id]!=n || xUSafe[blk.id]!=x) change = true;
				nUSafe[blk.id] = n;
				xUSafe[blk.id] = x;
			}
		}
//		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()) {
//			BasicBlk blk = (BasicBlk)p.elem();
//			System.out.println("+++"+blk.id+"+++");
//			System.out.println(":n:"+nUSafe[blk.id]);
//			System.out.println(":x:"+xUSafe[blk.id]);
//		}
	}
	
	//TODO checkTypeメソッドでは何を確認しているの？
	public boolean checkType(LirNode exp){
		char type=Type.toString(exp.type).charAt(0);
		return (type=='I' || type=='F');
	}
	
	
	public void compInsert(){
		nInsert = new boolean[idBound];
		xInsert = new boolean[idBound];
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			nInsert[blk.id] = nLatest[blk.id];
			xInsert[blk.id] = xLatest[blk.id];
		}
	}
	
	
	public void compReplace(){
		nReplace = new boolean[idBound];
		xReplace = new boolean[idBound];
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			nReplace[blk.id] = nIsSame[blk.id] && !(nLatest[blk.id] && nIsolated[blk.id]);
			xReplace[blk.id] = xIsSame[blk.id] && !(xLatest[blk.id] && xIsolated[blk.id]);
		}
	}	
	
	//TODO replaceメソッドの見直し
	public void replace(LirNode newNode){
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			if(nReplace[blk.id]){
				for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
					LirNode node = (LirNode)p.elem();
					if(node.equals(newNode))break;
					if(node.opCode!=Op.SET || !node.kid(1).equals(newNode.kid(1)))continue;
					replace(node,newNode,blk,p);
					break;
				}
			}
			if(xReplace[blk.id]){
				for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
					LirNode node = (LirNode)p.elem();
					if(node.equals(newNode))break;
					if(node.opCode!=Op.SET || !node.kid(1).equals(newNode.kid(1)))continue;
					replace(node,newNode,blk,p);
					break;
				}
			}	
		}
	}
	
	//TODO replaceメソッドの見直し
	public void replace(LirNode node, LirNode newNode, BasicBlk blk, BiLink p){
		node.setKid(1, newNode.kid(0).makeCopy(env.lir));
//		LirNode copy = node.makeCopy(env.lir);
//		ddcpyp.cpyp(blk, copy.kid(0), copy.kid(1), p, 1);
	}
	
	private LirNode makeNewNode(LirNode node){
		LirNode newOp = env.lir.symRef(Op.REG, node.type, sstab.newSsaSymbol(tmpSymName,node.kid(0).type) ,ImList.Empty);
		LirNode newNode = node.makeCopy(env.lir);
		newNode.setKid(0, newOp);
		return newNode;
	}
	
	public LirNode getNewNode(LirNode newNode, LirNode expr){
		if(newNode==null) return makeNewNode(expr).makeCopy(env.lir);
		else return newNode.makeCopy(env.lir);
	}
	
	public LirNode insertNewNode(LirNode noden, LirNode addr, ArrayList vars){
		noden = noden.makeCopy(env.lir);
		LirNode newNode = null;
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			if(nInsert[blk.id]){
				boolean same_addr = false;
				boolean insert = false;
				for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
					LirNode node = (LirNode)p.elem();
					if(isKill(noden,noden.kid(0),node,vars,blk,p))break;
					if(!isLoad(node))continue;
					if(node.kid(0).equals(noden.kid(0))){
						newNode = getNewNode(newNode,noden);
						p.addBefore(newNode);
						replace(node,newNode,blk,p);
						insert = true;
						break;
					}
					if(sameAddr(node,addr)) same_addr = true;
					else if(same_addr){
						insert = true;
						newNode = getNewNode(newNode,noden);
						p.addBefore(newNode);
						break;
					}
				}
				if(!insert){
					newNode = getNewNode(newNode,noden);
					for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
						LirNode node = (LirNode)p.elem();
						if(node.opCode!=Op.PROLOGUE){
							p.addBefore(newNode);
							break;
						}
					}
					
				}
			}
			if(xInsert[blk.id]){
				boolean insert = false;
				if(xSameAddr[blk.id]){
					BiLink latest = null;
					for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
						LirNode node = (LirNode)p.elem();
						if(isKill(noden,noden.kid(0),node,vars,blk,p))break;
						if(!isLoad(node))continue;
						if(node.equals(newNode)){
							insert = true;
							break;
						}
						if(node.kid(0).equals(noden.kid(0))){
							newNode = getNewNode(newNode,noden);
							p.addBefore(newNode);
							replace(node,newNode,blk,p);
							insert = true;
							break;
						}
						if(sameAddr(node,addr)){
							if(latest!=null){
								newNode = getNewNode(newNode,noden);
								latest.addBefore(newNode);
								insert = true;
								break;
							}
						}else latest = p;
					}
				}
				if(!insert){
					insert = true;
					newNode = getNewNode(newNode,noden);
					blk.instrList().last().addBefore(newNode);
				}
			}
		}
		return newNode;
	}
	
	
	//冗長な配列参照かabaのようなアクセス順が崩れている物があるかをチェックしている
	boolean checkLocal(LirNode node, LirNode addr, ArrayList localStore, ArrayList localAddr){
//		System.out.println("checklocal:::::");
		if(localStore.contains(node.kid(0)))return true;
//		System.out.println("localStore: "+localStore+": kid(0): "+node.kid(0));//
		if(localAddr.contains(addr)){
//			System.out.println("localAddr: "+localAddr+": addr: "+addr);//
			int pos = localAddr.indexOf(addr);
//			System.out.println("pos: "+pos);//
			for(int i=pos+1;i<localAddr.size();i++){
				LirNode la = (LirNode)localAddr.get(i);
//				System.out.println("la: "+la);//
				if(!la.equals(addr)){
//					System.out.println("!la.equals: true");//
					return true;
				}
			}
		}
		return false;
	}
			
	//TODO localCMメソッドで行っていることの確認
	boolean localCM(LirNode expr, LirNode addr, ArrayList vars, BasicBlk blk, BiLink p){
//		System.out.println("====localCM====");
//		System.out.println("node: "+(LirNode)p.elem());
//		System.out.println("addr: "+addr);
//		System.out.println("vars: "+vars);
		BiLink latest = null;
		for(BiLink q=p.next();!q.atEnd();q=q.next()){
			LirNode node = (LirNode)q.elem();
			if(!isStore(node)&&isKill(expr,expr.kid(0),node,vars,blk,p)) {
//				System.out.println("isKill");
				return false;
			}
			ArrayList nvars = new ArrayList();
			collectVars(nvars,node);
			if(nvars.contains(expr.kid(0))) {
//				System.out.println("contains");				
				return false;
			}
			if(!isStore(node)) {
//				System.out.println("!isStore");
				continue;
			}
			if(node.kid(0).equals(expr.kid(0))){
//				System.out.println("equals_unlink");
				q.addAfter(expr.makeCopy(env.lir));
				p.unlink();
				return true;
			}
			LirNode node_addr = getAddr(node.kid(0));
			if(node_addr.equals(addr)){
//				System.out.println("node_addr");
				if(latest!=null){
//					System.out.println("unlink_latest:"+(LirNode)latest.elem());
					latest.addAfter(expr.makeCopy(env.lir));
					p.unlink();
					return true;
				}
			}else{
//				System.out.println("else");
				latest = q;
			}
		}
//		System.out.println("false:");
		return false;
	}
			
	
	//TODO localCodeMotionメソッドの見直し
	//一つの節内での移動
	public void localCodeMotion(){
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
//			System.out.println(blk.id);
			ArrayList localStore = new ArrayList();
			ArrayList localAddr = new ArrayList();
			for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
				LirNode node = (LirNode)p.elem();
//				System.out.println("node:"+node);
				if(node.opCode==Op.CALL || (node.kid(0).opCode==Op.MEM && getAddr(node.kid(0)).opCode!=Op.FRAME)){
					localStore = new ArrayList();
					localAddr = new ArrayList();
				}
				if(!isStore(node))continue;
				LirNode addr = getAddr(node.kid(0));
				ArrayList vars = new ArrayList();
				collectVars(vars,node.kid(0));
//				System.out.println("addr: "+addr);
//				System.out.println("vars: "+vars);
				//checklocal
				//localcm　同一の配列を纏めるための条件
				if(checkLocal(node,addr,localStore,localAddr)) localCM(node,addr,vars,blk,p);
//				System.out.println(":::::"+checkLocal(node,addr,localStore,localAddr));
				//localload:b[0]の配列があったらb[0]を追加している。
				//localaddr:b[0]の配列があったらbを追加している
				localStore.add(node.kid(0).makeCopy(env.lir));
				localAddr.add(addr.makeCopy(env.lir));
			}
		}
	}
	
	//TODO globalCodeMotionメソッドの見直し
//	private void globalCodeMotion(){
//		//varsは添え字の中の変数
//		ArrayList insertNode = new ArrayList();
//		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
//			BasicBlk blk = bVecInOrderOfRPost[i];
//			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
//				LirNode node = (LirNode)p.elem();
//				if(!isLoad(node) || insertNode.contains(node.kid(1)) || !checkType(node))continue;
//				insertNode.add(node.kid(1).makeCopy(env.lir));
//				//addrは変数名
//				LirNode addr = getAddr(node.kid(1));
//				//varsは添え字
//				ArrayList vars = new ArrayList();
//				collectVars(vars,node.kid(1));
//				printGlobalProp(node);
//				//dceの際はいらないが、コードを移動する際、消してから新しいノードを追加するために必要。
//				LirNode newNode = insertNewNode(node,addr,vars);
//				if(newNode!=null) replace(newNode);
//			}
//		}
//	}
	
	private void testGCM() {
	//varsは添え字の中の変数
		ArrayList insertNode = new ArrayList();
//		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
		for(int i=bVecInOrderOfRPost.length-1;i>0;i--) {
//		for(BiLink pp=f.flowGraph().basicBlkList.last();!pp.atEnd();pp=pp.prev()) {//
			BasicBlk blk = bVecInOrderOfRPost[i];
//			BasicBlk blk = (BasicBlk)pp.elem();//
//			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
//			System.out.println(blk.id);//
			for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()) {
				LirNode node = (LirNode)p.elem();
				if(!isStore(node) || insertNode.contains(node.kid(0)) || !checkType(node))continue;
//				System.out.println(blk.id+":"+node);
//				System.out.println("++++");
//				System.out.println("+++++++++++");
				insertNode.add(node.kid(0).makeCopy(env.lir));
				//addrは変数名,a[1]=0だったらaが出る感じ
//				LirNode addr = getAddr(node.kid(1));
				LirNode addr = getAddr(node.kid(0));//〇getadd
				//varsは添え字、a[x]=0だったらxが出る感じ
				if(addr.opCode != Op.FRAME)continue;
				ArrayList vars = new ArrayList();
				System.out.println("node:"+node);
				System.out.println("blk.id:"+blk.id);
				collectVars(vars,node.kid(0));//〇collectvars
//				compLocalProperty(node.kid(0),addr,vars);
//				compEarliest(blk);
//				compDSafe();
//				pde(node.kid(0),addr,vars,blk,p,node);
				
				if(dce(node,node.kid(0),addr,vars,blk)) {
//					System.out.println("!!!!!!dce!!!!!!!");
					p.unlink();
				}
				
//				printGlobalProp(node);
//				LirNode newNode = insertNewNode(node,addr,vars);
//				if(newNode!=null) replace(newNode);
			}
		}		
	}
	
	public void pde(LirNode noden,LirNode expr, LirNode addr, ArrayList vars, BasicBlk blk,BiLink p) {
		compLocalProperty(noden,expr,addr,vars);
//		System.out.println("---compEarliest---");
		compEarliest(blk);
//		System.out.println("---compDSafe---");
		compDSafe();
		compPartialDSafe();
		if(dce(blk)) {
//			System.out.println("!!!!!!dce!!!!!!!");
			p.unlink();
		}else{
//			System.out.println("---compUSafe---");
			compUSafe();//お前いらねぇっす
//			System.out.println("---compKeepOrder---");
			compKeepOrder();
//			System.out.println("---compDelayed---");
			compDelayed();
//			System.out.println("---compLatest---");
			compLatest();
			
//			compIsolated();
//			compInsert();
//			compReplace();
		}
	}
	
	public void dcedisplay() {
		System.out.println(" ---DISPLAY---");
		for(BiLink p =f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
			   BasicBlk v=(BasicBlk)p.elem();
			   System.out.println(" "+v.id+" :blk.id");
			   if(nUse[v.id])System.out.println("nUse--------:"+nUse[v.id]);
			   if(xUse[v.id])System.out.println("xUse:-------:"+xUse[v.id]);
			   if(nIsSame[v.id])System.out.println("nIsSame-----:"+nIsSame[v.id]);
			   if(xIsSame[v.id])System.out.println("xIsSame-----:"+xIsSame[v.id]);
			   if(nSameAddr[v.id])System.out.println("nSameAddr---:"+nSameAddr[v.id]);
			   if(xSameAddr[v.id])System.out.println("xSameAddr---:"+xSameAddr[v.id]);
			   if(Transp_e[v.id])System.out.println("Transp_e----:"+Transp_e[v.id]);
			   if(Transp_addr[v.id])System.out.println("nTransp_addr:"+Transp_addr[v.id]);
			   if(xTransp_addr[v.id])System.out.println("xTransp_addr:"+xTransp_addr[v.id]);
			   if(nDSafe[v.id])System.out.println("nDSafe------:"+nDSafe[v.id]);
			   if(xDSafe[v.id])System.out.println("xDSafe------:"+xDSafe[v.id]);
			   if(pNDSafe[v.id])System.out.println("pNDSafe-----:"+pNDSafe[v.id]);
			   if(pXDSafe[v.id])System.out.println("pXDSafe-----:"+pXDSafe[v.id]);
		 }
	}
	
	
	public boolean dce(LirNode noden, LirNode expr, LirNode addr, ArrayList vars, BasicBlk blk) {
        //for文でIsSameを各ノードに適用させながら、compDSafeを適用させ、除去できるかを判定。dceに結果を格納する。
        //exitノードで結果がtrueだったのなら除去可能。
		compLocalProperty(noden,expr,addr,vars);
//		System.out.println("---compEarliest---");
		compEarliest(blk);
//		System.out.println("---compDSafe---");
		compDSafe();
//		System.out.println("---compPartialDSafe---");
		compPartialDSafe();
//		System.out.println("\\\\dce\\\\");
		dcedisplay();
		boolean isTarget = dce(blk);
		return isTarget;
	}
	
	public boolean dce(BasicBlk blk) {
		if(xEarliest[blk.id] && xTransp_addr[blk.id] && !xUse[blk.id]) {
			for(BiLink q=blk.succList().first();!q.atEnd();q=q.next()){
				BasicBlk succ = (BasicBlk)q.elem();
				if(pNDSafe[succ.id]) {
					return false;
				}
			}
			return true;
		}
		return false;
	}
         
    public boolean doIt(Function function,ImList args) {
    	
      //
      long startTime = System.currentTimeMillis();
      //
      f = function;
      env.println("****************** doing GSA to "+
    		  f.symbol.name,SsaEnvironment.MinThr);
      alias=new MemoryAliasAnalyze(env,f);
    
      f = function;
      env.println("****************** doing GSA to "+
    		  f.symbol.name,SsaEnvironment.MinThr);
      alias=new MemoryAliasAnalyze(env,f);

    // 1/3 
      dfst=(DFST)f.require(DFST.analyzer);
      dom=(Dominators)f.require(Dominators.analyzer);
      idBound = f.flowGraph().idBound();
      bVecInOrderOfRPost = dfst.blkVectorByRPost();
      
      localCodeMotion();
      displayBasicBlk();
//      globalCodeMotion();
//      displayBasicBlk();
      testGCM();
      displayBasicBlk();
      
//         		LirNode newStat = createNewStatement(node);
//         		p.addBefore(newStat);
//         	
//         	
//        	 	LirNode pvar = removingLocalRedundancy(p.prev(), node);
//        	 	if(pvar!=null) {
//        			System.out.println(pvar);
//        		 	node.setKid(1, pvar.makeCopy(env.lir));
//        		 	System.out.println(node);
//        	 	}
//    	  }    
//      }

      f.flowGraph().touch();
      return(true);
    }
 }






//class lattice {
//    static int Top = 1;
//    static int Bot = 2;
//    static int True = 3;
//    static int False = 4;
//    lattice(){
//        System.out.println(l_and(True,False));
//        System.out.println(l_or(Top,True));
//    }
//    public static void main(String[] args) {
//        lattice obj = new lattice();
//        obj.l_and(1,2);
//        obj.l_or(1,2);
//    }
//    public int l_and(int op1,int op2){
//        if(op1==Top){
//            if(op2==True){
//                return True;
//            } else if(op2==False){
//                return False;
//            } else if(op2==Bot){
//                return Bot;
//            } else {
//                return Top;
//            }
//        } 
//        else if(op1==Bot){
//            if(op2==True){
//                return Bot;
//            } else if(op2==False) {
//                return Bot;
//            } else if(op2==Top) {
//                return Bot;
//            } else {
//                return Bot;
//            }
//        } 
//        else if(op1==True){
//            if(op2==False){
//                return Bot;
//            } else if(op2==Top){
//                return True;
//            } else if(op2==Bot){
//                return Bot;
//            } else {
//                return True;
//            }
//        } 
//        else if(op1==False){
//            if(op2==True){
//                return Bot;
//            } else if(op2==Top){
//                return False;
//            } else if(op2==Bot){
//                return Bot;
//            } else {
//                return False;
//            }
//        }
//        else{
//            return -1;
//        }
//    }
//    public int l_or(int op1, int op2){
//        if(op1==Top){
//            if(op2==True){
//                return Top;
//            } else if(op2==False) {
//                return Top;
//            } else if(op2==Bot) {
//                return Top;
//            } else {
//                return Top;
//            }
//        } 
//        else if (op1==Bot) {
//            if(op2==True){
//                return True;
//            } else if(op2==False){
//                return False;
//            } else if(op2==Top){
//                return Top;
//            } else {
//                return Bot;
//            }
//        }
//        else if(op1==True){
//            if(op2==False){
//                return Top;
//            } else if(op2==Top){
//                return Top;
//            } else if(op2==Bot){
//                return True;
//            }  else {
//                return True;
//            }
//        }
//        else if(op1==False){
//            if(op2==True){
//                return Top;
//            } else if(op2==Top){
//                return Top;
//            } else if(op2==Bot){
//                return False;
//            } else {
//                return False;
//            }
//        }
//        else {
//            return -1;
//        }
//    }
//}

//complete
