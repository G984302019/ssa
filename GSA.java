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
    boolean[] dce;
	boolean[] nSameAddr;
	boolean[] xSameAddr;
	boolean[] nIsSame;
	boolean[] xIsSame;
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
    
    void dcedisplay() {
 	   System.out.println("-------------------------------------------");
 	   for(BiLink p =f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()) {
 		   BasicBlk v=(BasicBlk)p.elem();
 		   for(BiLink bl=v.instrList().first();!bl.atEnd();bl=bl.next()){
 			   LirNode node=(LirNode)bl.elem();
 			   if(dce[node.id]) {
 				   p.unlink();
 				   break;
 			   }else {
 				   System.out.println(node);
 		   
 			   }
 		   }
 	   }
 	   System.out.println("-------------------------------------------");
 	   System.out.println("-------------------------------------------");
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
    
    //そのノードが削除できる可能性があるものなのかを判断するメソッド
    //a[i]=0の時のi,x=yの時のyなど変数の値を変更する可能性があるノード
    public boolean isKill(LirNode expr, LirNode node, ArrayList vars, BasicBlk blk, BiLink p){
		//TODO 局所配列の場合は詳細な解析をするようにする。
//    	System.out.println("isKill"+node);
		if(node.opCode==Op.CALL)return true;//何らかの関数呼び出しがあった場合に問答無用でtrueにする。
//		if(isStore(node))return true;//TODO 局所配列
//		if(node.opCode==Op.SET && node.kid(0).opCode==Op.MEM && ddalias.checkAlias(expr, node.kid(0), blk, p))return true;
		if(vars.contains(node.kid(0)))return true;// conectvarsメソッドと共に何を確認しているかのチェック
//		System.out.println(false);
		return false;
	}
    
//    public boolean isStatic(LirNode node) {
//    	//命令がStaticな命令なのかを判定。
//    	if(isLoad(node)) {
//    		if(node.kid(1).opCode==Op.STATIC)return true;
//    	}
//    	if(isStore(node)) {
//    		if(node.kid(0).nKids()>0) {
//    			if(node.kid(0).kid(0).opCode==Op.STATIC)return true;
//    			if(node.kid(0).kid(0).opCode==Op.ADD&&node.kid(0).kid(0).nKids()>0) {
//    				if(node.kid(0).kid(0).kid(0).opCode==Op.STATIC)return true;
//    			}
//    		}
//    		if(node.kid(1).nKids()>0) {
//    			if(node.kid(1).kid(0).opCode==Op.STATIC)return true;
//    			if(node.kid(1).kid(0).opCode==Op.ADD&&node.kid(1).kid(0).nKids()>0) {
//    				if(node.kid(1).kid(0).kid(0).opCode==Op.STATIC)return true;
//    			}
//    		}
//    	}
//    	return false;
//    }
    //pointerはstaticなものだからそこで判定する。
    
    //同様の配列参照を行っている場合true;
    LirNode getAddr(LirNode exp){
    	if(exp.nKids()==0) return exp;
		if(exp.kid(0).nKids()==0) return exp.kid(0);
		else return getAddr(exp.kid(0));
	}
    
    //同様の配列参照をするload命令があった場合にtrue;
  	public boolean sameAddr(LirNode node, LirNode addr){
  		if(!isLoad(node))return false;
  		return (addr.equals(getAddr(node.kid(1))));
  	}
    
    //最初にローカルプロパティを全て初期化する。
	void compLocalProperty(LirNode exp, LirNode addr, ArrayList vars){
		dce = new boolean[idBound];
		xSameAddr = new boolean[idBound];
		nSameAddr = new boolean[idBound];
		xIsSame = new boolean[idBound];
		nIsSame = new boolean[idBound];
		Transp_e = new boolean[idBound];
		Transp_addr = new boolean[idBound];
		xTransp_addr = new boolean[idBound];
		Arrays.fill(dce, false);
		Arrays.fill(xSameAddr, false);
		Arrays.fill(nSameAddr, false);
		System.out.println("exp:");
		System.out.println(exp);
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			nIsSame[blk.id] = compNIsSame(exp,vars,blk);//〇
			xIsSame[blk.id] = compXIsSame(exp,vars,blk);//〇
			//変数のkillが内科のチェック
			Transp_e[blk.id] = compTranspe(exp,addr,vars,blk);
			//配列のアクセス順序が崩れていないかのチェック。
			Transp_addr[blk.id] = compTranspAddr(exp,addr,vars,blk);
			//
			xTransp_addr[blk.id] = compXTranspAddr(exp,addr,vars,blk);			
		}
	}
	
	//TODO 行っていることの確認と変更する必要の確認
	private boolean compNIsSame(LirNode exp, ArrayList vars, BasicBlk blk){
//		System.out.println("::NisSame"+blk.id);//
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){//渡された基本ブロックの命令をひとつづつ確認している
			LirNode node = (LirNode)p.elem();
//			System.out.println(node);
//			System.out.println(":isKill");
			if(isKill(exp,node,vars,blk,p))break;//isKillがtrueだったらループ終了
//			System.out.println(":isLoad");//
			if(!isLoad(node))continue;//isLoadがfalseだったら次のループ
//			System.out.println(":equals");
//			if(node.kid(1).equals(exp)) return true;//渡されたノードの配列の一つ目と渡されたexpが同じならtrue
			if(node.kid(1).equals(exp)) { 
//				System.out.println("++TrueTrueTrueTrue++");
//				System.out.println(blk.id);
				return true;
			}
		}
//		System.out.println("--FalseFalseFalseFalse--");
		return false;
	}

	//変数xIsSameを変更するためのメソッド
	//変数xIsSameはcompDSafeで用いられている
	//同じ変数の定義をしている分がその先にあるかの判定。
	private boolean compXIsSame(LirNode exp, ArrayList vars, BasicBlk blk){
//		System.out.println("::XisSame"+blk.id);//
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode node = (LirNode)p.elem();
//			System.out.println(node);//
//			System.out.println("::isKill");//
			if(isKill(exp,node,vars,blk,p))break;//
			//式の右辺を確認しようとしている。
			//ロード命令省かなくてもいい。
//			System.out.println(":isLoad");//
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
		}
//		System.out.println("--FalseFalseFalseFalse--");
		return false;
	}
	
	//TODO EarliestをPDE用に更新
	public void compEarliest() {
		nEarliest = new boolean[idBound];
		xEarliest = new boolean[idBound];
		Arrays.fill(nEarliest, true);
		Arrays.fill(xEarliest, true);
		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
			BasicBlk blk = (BasicBlk)p.elem();
			boolean n = nUSafe[blk.id] || nDSafe[blk.id];
			if(n && blk!=f.flowGraph().entryBlk()){
				n = false;
				for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()){
					BasicBlk pred = (BasicBlk)q.elem();
					if(!(xUSafe[pred.id] || xDSafe[pred.id])){
						n = true;
						break;
					}
				}
			}
			nEarliest[blk.id] = n;
			xEarliest[blk.id] = (xUSafe[blk.id] || xDSafe[blk.id]) && (!Transp_e[blk.id] || !(nUSafe[blk.id] || nDSafe[blk.id]) && !n);
		}
	}
	
	
	//TODO DelayedをPDE用に更新
	public void compDelayed() {
		nDelayed = new boolean[idBound];
		xDelayed = new boolean[idBound];
		Arrays.fill(nDelayed, true);
		Arrays.fill(xDelayed, true);
		boolean change = true;
		while(change){
			change = false;
			for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
				BasicBlk blk = (BasicBlk)p.elem();
				boolean n = false;
				if(nEarliest[blk.id]){
					n = true;
				}else if(blk!=f.flowGraph().entryBlk()){
					n = true;
					for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()){
						BasicBlk pred = (BasicBlk)q.elem();
						if(!xDelayed[pred.id] || !xKeepOrder[pred.id] || xIsSame[pred.id]){
							n = false;
							break;
						}
					}
				}
				boolean x = xEarliest[blk.id] || (n && !nIsSame[blk.id] && nKeepOrder[blk.id]);
				if(nDelayed[blk.id]!=n || xDelayed[blk.id]!=x) change = true;
				nDelayed[blk.id] = n;
				xDelayed[blk.id] = x;
			}
		}
	}
	
	//TODO 行っていることと変える必要の確認
	public void compKeepOrder(){
		nKeepOrder = new boolean[idBound];
		xKeepOrder = new boolean[idBound];
		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
			BasicBlk blk = (BasicBlk)p.elem();
			nKeepOrder[blk.id] = !nUSafe[blk.id] || Transp_addr[blk.id];
			xKeepOrder[blk.id] = !xUSafe[blk.id] || xTransp_addr[blk.id];
		}
	}

	//同様のインスタンスを持つ配列へのストア命令があった場合にfalse,
	//またxsameaddrの更新
	private boolean compTranspe(LirNode exp, LirNode addr, ArrayList vars, BasicBlk blk){
//		System.out.println("::compTranspe");//
		boolean xt = true;
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode node = (LirNode)p.elem();
//			System.out.println(node);//
//			System.out.println(":iskill");//
			if(isKill(exp,node,vars,blk,p)){
//				System.out.println("----false----");
				xt = false;
				break;
			}
//			System.out.println(":isload_isstore");//
			if(!isLoad(node)&&!isStore(node))continue;
//			System.out.println(":sameaddr");//
			if(sameAddr(node,addr)) xSameAddr[blk.id] = true;
		}
//		System.out.println("++++"+xt+"++++");
		return xt;
	}
	
	//同様のストア命令に対する変更も、異なる配列への参照もない場合true
	private boolean compTranspAddr(LirNode exp, LirNode addr, ArrayList vars, BasicBlk blk){
		if(!Transp_e[blk.id])return false;
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
			LirNode node = (LirNode)p.elem();
			if(isKill(exp,node,vars,blk,p))return false;
			if(!isLoad(node)&&!isStore(node))continue;
			if(sameAddr(node,addr)){
				nSameAddr[blk.id] = true;
				if(node.kid(1).equals(exp)) break;
			}else return false;
		}
		return true;
	}
	
	//同様のストア命令に対する変更も、異なる配列への参照もない場合true;
	//ノードは上げないからいらないかも
	private boolean compXTranspAddr(LirNode exp, LirNode addr, ArrayList vars, BasicBlk blk){
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode node = (LirNode)p.elem();
			if(isKill(exp,node,vars,blk,p))return false;
			if(!isLoad(node))continue;
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
		}
	}
    
	//TODO Upsafeが必要なのかの確認とGSA用に更新
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
				boolean x = xSameAddr[blk.id] || n && Transp_e[blk.id];
				if(nUSafe[blk.id]!=n || xUSafe[blk.id]!=x) change = true;
				nUSafe[blk.id] = n;
				xUSafe[blk.id] = x;
			}
		}
	}
	
	//変数nDSafe,xDSafeを変更するためのメソッド
	//変数nDSafeはノード上部のDownSafe
	//変数xDSafeは
	public void compDSafe() {
		System.out.println("compDSafe");
		nDSafe = new boolean[idBound];
		xDSafe = new boolean[idBound];
		Arrays.fill(nDSafe, true);
		Arrays.fill(xDSafe, true);
		boolean change = true;
		while(change){
			change = false;
			for(BiLink p=f.flowGraph().basicBlkList.last();!p.atEnd();p=p.prev()){
				BasicBlk blk = (BasicBlk)p.elem();
				System.out.println(blk.id);//
				boolean x = false;
//				if(xIsSame[blk.id]) x = true;
				if(xIsSame[blk.id]) {//
					System.out.println("___xIsSame___");//
					x = true;//
				}//
				else if(blk!=f.flowGraph().exitBlk()){
					x = true;
					for(BiLink q=blk.succList().first();!q.atEnd();q=q.next()){
						BasicBlk succ = (BasicBlk)q.elem();
						if(!nDSafe[succ.id]){
							x = false;
							break;
						}
					}
				}
				boolean n = nIsSame[blk.id] || x;
				if(nDSafe[blk.id]!=n || xDSafe[blk.id]!=x) change = true;
				if(change) {
					if(nDSafe[blk.id]!=n) System.out.println("^^^nnn^^^"+n);
					if(xDSafe[blk.id]!=x) System.out.println("^^^xxx^^^"+x);
				}
				nDSafe[blk.id] = n;
				xDSafe[blk.id] = x;
			}
		}
	}
	
	//TODO checkTypeメソッドでは何を確認しているの？
	public boolean checkType(LirNode exp){
		char type=Type.toString(exp.type).charAt(0);
		return (type=='I' || type=='F');
	}
	
	//TODO checkLocalメソッドで行っていることの確認
	boolean checkLocal(LirNode node, LirNode addr, ArrayList localLoad, ArrayList localAddr){
		if(localLoad.contains(node.kid(1)))return true;
		if(localAddr.contains(addr)){
			int pos = localAddr.indexOf(addr);
			for(int i=pos+1;i<localAddr.size();i++){
				LirNode la = (LirNode)localAddr.get(i);
				if(!la.equals(addr)){
					return true;
				}
			}
		}
		return false;
	}
	
	//TODO localCMメソッドで行っていることの確認
	boolean localCM(LirNode expr, LirNode addr, ArrayList vars, BasicBlk blk, BiLink p){
		BiLink latest = null;
		for(BiLink q=p.prev();!q.atEnd();q=q.prev()){
			LirNode node = (LirNode)q.elem();
			if(isKill(expr.kid(1),node,vars,blk,p))return false;
			ArrayList nvars = new ArrayList();
			collectVars(nvars,node);
			if(nvars.contains(expr.kid(0)))return false;
			if(!isLoad(node))continue;
			if(node.kid(1).equals(expr.kid(1))){
				replace(expr,node,blk,p);
				return true;
			}
			LirNode node_addr = getAddr(node.kid(1));
			if(node_addr.equals(addr)){
				if(latest!=null){
					latest.addBefore(expr.makeCopy(env.lir));
					p.unlink();
					return true;
				}
			}else{
				latest = q;
			}
		}
		return false;
	}
	
	//TODO compReplaceメソッドの確認
	public void compReplace(){
		nReplace = new boolean[idBound];
		xReplace = new boolean[idBound];
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			//TODO 条件の追加
			nReplace[blk.id] = nIsSame[blk.id];
			xReplace[blk.id] = xIsSame[blk.id];
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
	
	//TODO localCodeMotionメソッドの見直し
	public void localCodeMotion(){
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			ArrayList localLoad = new ArrayList();
			ArrayList localAddr = new ArrayList();
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				if(node.opCode==Op.CALL || node.kid(0).opCode==Op.MEM){
					localLoad = new ArrayList();
					localAddr = new ArrayList();
				}
				if(!isStore(node))continue;
				LirNode addr = getAddr(node.kid(1));
				ArrayList vars = new ArrayList();
				collectVars(vars,node.kid(1));
				if(checkLocal(node,addr,localLoad,localAddr)) localCM(node,addr,vars,blk,p);
				if(!isLoad(node)) continue;
				localLoad.add(node.kid(1).makeCopy(env.lir));
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
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
//			for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()) {
				LirNode node = (LirNode)p.elem();
				//TODO この下の挙動は何なのかを探る。
				if(!isStore(node) || insertNode.contains(node.kid(0)) || !checkType(node))continue;
				insertNode.add(node.kid(0).makeCopy(env.lir));
				//addrは変数名,a[1]=0だったらaが出る感じ
//				LirNode addr = getAddr(node.kid(1));
				LirNode addr = getAddr(node.kid(0));//〇getadd
				//varsは添え字
				ArrayList vars = new ArrayList();
				collectVars(vars,node.kid(0));//〇collectvars
				compLocalProperty(node.kid(0),addr,vars);
				compDSafe();
//				dce(node,addr,vars);
//				printGlobalProp(node);
//				LirNode newNode = insertNewNode(node,addr,vars);
//				if(newNode!=null) replace(newNode);
			}
		}		
	}
	
	//TODO dceメソッドを完成させる
	public void dce(LirNode node, LirNode addr, ArrayList vars) {
        //for文でIsSameを各ノードに適用させながら、compDSafeを適用させ、除去できるかを判定。dceに結果を格納する。
        //exitノードで結果がtrueだったのなら除去可能。
		compLocalProperty(node,addr,vars);
		compDSafe();
		for(BiLink p=f.flowGraph().basicBlkList.last();!p.atEnd();p=p.prev()){
			BasicBlk blk = (BasicBlk)p.elem();
			if(blk==f.flowGraph().exitBlk()) continue; 
			if(!xDSafe[blk.id]) dce[blk.id]=true;
			p.unlink();
			break;
		}
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
      
//      for(BiLink pp=f.flowGraph().basicBlkList.first();!pp.atEnd();pp=pp.next()){
//    	  BasicBlk v=(BasicBlk)pp.elem();        
//    	  for(BiLink p=v.instrList().first();!p.atEnd();p=p.next()){
//    		  LirNode node=(LirNode)p.elem();
//    		  System.out.println(node);
//    	  }
//      }
      
//      localCodeMotion();
//      globalCodeMotion();
      displayBasicBlk();
      testGCM();
      	
//      displayBasicBlk();
      System.out.println("------------------------------");
//      checkDCE();
//      displayBasicBlk();
    
      
       		
        	
        	
        	
        	
//             	if(node.opCode!=Op.SET) continue;
//             	if(node.kid(1).opCode==Op.MEM) continue;
//				System.out.println("== Checking target ==");
//            	System.out.println(node);
//             	System.out.println("== Checking BasicBlk ==");
//             	displayBasicBlk(v);

             
            
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
//      
//      boolean change = true;
//      dce = new boolean[idBound];
//      Arrays.fill(dce, true);
//      while(change) {
//      	change = false;
//      	for(BiLink pp=f.flowGraph().basicBlkList.first();!pp.atEnd();pp=pp.next()){
//      		BasicBlk v=(BasicBlk)pp.elem();        
//      		for(BiLink p=v.instrList().first();!p.atEnd();p=p.next()){
//      			LirNode node=(LirNode)p.elem();
//      			boolean isSame=false;
//      			if(p!=v.instrList().last()) {
//      				for(LirNode n=(LirNode)p.next().elem();!p.atEnd();p=p.next()) {
//      					if(isKill(node,n)) {
//      						isSame = true;
//      					}
//      				}
//      				if(!isSame) {
//      					System.out.println(node);
//      					p.unlink();
//      					change = true;
//      				}
//      			}
//      		}
//      	}
//      }
//      
//      dce = new boolean[idBound];
//      Arrays.fill(dce, false);
//      for(BiLink pp=f.flowGraph().basicBlkList.last();!pp.atEnd();pp=pp.prev()){
//      	BasicBlk v=(BasicBlk)pp.elem();        
//      	for(BiLink p=v.instrList().last();!p.atEnd();p=p.prev()){
//      		LirNode node=(LirNode)p.elem();
//      		boolean isSame=false;
//      		for(LirNode n=(LirNode)p.next().elem();!p.atEnd();p=p.next()) {
//      			if(isKill(node,n)) {
//      				isSame = true;
//      			}
//      		}
//      		if(!isSame) {
//      			dce[node.id]=true;
//      		}
//      	}
//      }
    
      //if(node.kid(0).opCode==Op.MEM && (node.kid(1).opCode==Op.REG || 
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