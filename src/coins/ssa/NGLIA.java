/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import java.util.ArrayList;
import java.util.Arrays;

import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.Type;
import coins.backend.ana.DFST;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;

/**
 * Normal form GLIA.
 **/
public class NGLIA implements LocalTransformer {
	public boolean doIt(Data data, ImList args) {return true;}
	public String name() {return "NGLIA";}
	public String subject() {return "NGLIA";}
	private String tmpSymName = "_nglia";
	public static final int THR = SsaEnvironment.OptThr;
	/** The threshold of debug print **/
	public static final int THR2 = SsaEnvironment.AllThr;
	private SsaEnvironment env;
	private SsaSymTab sstab;
	private Function f;
	public BasicBlk[] bVecInOrderOfRPost;
	private DFST dfst;
	
	DDAliasAnalysis ddalias;
	
	int idBound;
	boolean[] nSameAddr;
	boolean[] xSameAddr;
	boolean[] Transp_e;
	boolean[] xTransp_e;
	boolean[] Transp_addr;
	boolean[] xTransp_addr;
	boolean[] nIsSame;
	boolean[] xIsSame;
	public boolean[] nUSafe;
	public boolean[] xUSafe;
	public boolean[] nDSafe;
	public boolean[] xDSafe;
	public boolean[] pUSafe;
	public boolean[] nEarliest;
	public boolean[] xEarliest;
	public boolean[] nKeepOrder;
	public boolean[] xKeepOrder;
	public boolean[] nDelayed;
	public boolean[] xDelayed;
	public boolean[] nLatest;
	public boolean[] xLatest;
	public boolean[] nIsolated;
	public boolean[] xIsolated;
	public boolean[] nInsert;
	public boolean[] xInsert;
	public boolean[] nReplace;
	public boolean[] xReplace;
	public static final String NSGLIA = "_nglia";

	/**
	 * Constructor.
	 * 
	 * @param env The environment of the SSA module
	 * @param sstab The current symbol table on SSA form
	 **/
	public NGLIA(SsaEnvironment env, SsaSymTab sstab) {
		this.env = env;
		this.sstab = sstab;
	}
	
	
	public NGLIA(SsaEnvironment env, SsaSymTab sstab, Function f) {
		this.env = env;
		this.sstab = sstab;
		this.f = f;
	}
	
	
	/**
	 * Do Normal form GLIA.
	 * 
	 * @param func
	 *            The current function
	 * @param args
	 *            The list of options
	 **/
	public boolean doIt(Function func, ImList args) {
		f = func;
		env.println("****************** doing Normal form GLIA to " + f.symbol.name, SsaEnvironment.MinThr);
		invoke();
		f.flowGraph().touch();
		return (true);
	}
	
	
	public void init(){
		dfst = (DFST) f.require(DFST.analyzer);
		idBound = f.flowGraph().idBound();
		bVecInOrderOfRPost = dfst.blkVectorByRPost();
	}
	
	
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
				if(!isLoad(node))continue;
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
	
	
	private void invoke(){
		init();
		localCodeMotion();
		globalCodeMotion();
	}
	
	
	private void globalCodeMotion(){
		ArrayList insertNode = new ArrayList();
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				if(!isLoad(node) || insertNode.contains(node.kid(1)) || !checkType(node))continue;
				insertNode.add(node.kid(1).makeCopy(env.lir));
				LirNode addr = getAddr(node.kid(1));
				ArrayList vars = new ArrayList();
				collectVars(vars,node.kid(1));
				glia(node,addr,vars);
//				printGlobalProp(node);
				LirNode newNode = insertNewNode(node,addr,vars);
				if(newNode!=null) replace(newNode);
			}
		}
	}
	
	
	public void glia(LirNode node, LirNode addr, ArrayList vars){
		compLocalProperty(node.kid(1),addr,vars);
		compUSafe();
		compDSafe();
		compPartialSafe();
		compEarliest();
		compKeepOrder();
		compDelayed();
		compLatest();
		compIsolated();
		compInsert();
		compReplace();
	}
	
	
	public boolean isKill(LirNode expr, LirNode node, ArrayList vars, BasicBlk blk, BiLink p){
		if(node.opCode==Op.CALL)return true;
		if(node.opCode==Op.SET && node.kid(0).opCode==Op.MEM)return true;
//		if(node.opCode==Op.SET && node.kid(0).opCode==Op.MEM && ddalias.checkAlias(expr, node.kid(0), blk, p))return true;
		if(vars.contains(node.kid(0)))return true;
		return false;
	}
	
	
	public boolean isLoad(LirNode node){
		return (node.opCode==Op.SET && node.kid(0).opCode==Op.REG && node.kid(1).opCode==Op.MEM);
	}
	
	
	public boolean sameAddr(LirNode node, LirNode addr){
		if(!isLoad(node))return false;
		return (addr.equals(getAddr(node.kid(1))));
	}
	
	
	public void compLocalProperty(LirNode exp, LirNode addr, ArrayList vars){
		nSameAddr = new boolean[idBound];
		xSameAddr = new boolean[idBound];
		Transp_e = new boolean[idBound];
		xTransp_e = new boolean[idBound];
		Transp_addr = new boolean[idBound];
		xTransp_addr = new boolean[idBound];
		nIsSame = new boolean[idBound];
		xIsSame = new boolean[idBound];
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			nIsSame[blk.id] = compNIsSame(exp,vars,blk);
			xIsSame[blk.id] = compXIsSame(exp,vars,blk);
			Transp_e[blk.id] = compTranspe(exp,addr,vars,blk);
			Transp_addr[blk.id] = compTranspAddr(exp,addr,vars,blk);
			xTransp_addr[blk.id] = compXTranspAddr(exp,addr,vars,blk);
		}
	}
	
	
	private boolean compNIsSame(LirNode exp, ArrayList vars, BasicBlk blk){
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
			LirNode node = (LirNode)p.elem();
			if(isKill(exp,node,vars,blk,p))break;
			if(!isLoad(node))continue;
			if(node.kid(1).equals(exp))return true;
		}
		return false;
	}
	
	
	private boolean compXIsSame(LirNode exp, ArrayList vars, BasicBlk blk){
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode node = (LirNode)p.elem();
			if(isKill(exp,node,vars,blk,p))break;
			if(!isLoad(node))continue;
			if(node.kid(1).equals(exp))return true;
		}
		return false;
	}
	
	
	private boolean compTranspe(LirNode exp, LirNode addr, ArrayList vars, BasicBlk blk){
		boolean xt = true;
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode node = (LirNode)p.elem();
			if(isKill(exp,node,vars,blk,p)){
				xt = false;
				break;
			}
			if(!isLoad(node))continue;
			if(sameAddr(node,addr)) xSameAddr[blk.id] = true;
		}
		return xt;
	}
	

	private boolean compTranspAddr(LirNode exp, LirNode addr, ArrayList vars, BasicBlk blk){
		if(!Transp_e[blk.id])return false;
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
			LirNode node = (LirNode)p.elem();
			if(isKill(exp,node,vars,blk,p))return false;
			if(!isLoad(node))continue;
			if(sameAddr(node,addr)){
				nSameAddr[blk.id] = true;
				if(node.kid(1).equals(exp)) break;
			}else return false;
		}
		return true;
	}
	
	
	/**
	 * xTransp_addr is used to aggregate if there is a referring different array as exp after referring the same array in same basic block.
	 * e.g., 
	 *    x = a[i];
	 *    y = b[i];
	 *    if(...){
	 *      z = a[j];
	 *    }
	 * The a[j] should be moved immediately before the b[i].
	 */
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
	
	
	public void compDSafe() {
		nDSafe = new boolean[idBound];
		xDSafe = new boolean[idBound];
		Arrays.fill(nDSafe, true);
		Arrays.fill(xDSafe, true);
		boolean change = true;
		while(change){
			change = false;
			for(BiLink p=f.flowGraph().basicBlkList.last();!p.atEnd();p=p.prev()){
				BasicBlk blk = (BasicBlk)p.elem();
				boolean x = false;
				if(xIsSame[blk.id]) x = true;
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
				boolean n = nIsSame[blk.id] || x && Transp_e[blk.id];
				if(nDSafe[blk.id]!=n || xDSafe[blk.id]!=x) change = true;
				nDSafe[blk.id] = n;
				xDSafe[blk.id] = x;
			}
		}
	}
	
	
	public void compUSafe() {
		nUSafe = new boolean[idBound];//基本ブロックの数で初期化
		xUSafe = new boolean[idBound];
		Arrays.fill(nUSafe, true);//trueで埋める
		Arrays.fill(xUSafe, true);
		boolean change = true;
		while(change){//Safeの変更があったときに全部やり直す
			change = false;
			for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){//基本ブロックの最初から最後までひとつづつチェック
				BasicBlk blk = (BasicBlk)p.elem();
				boolean n = false;
				if(blk!=f.flowGraph().entryBlk()){//entryblock以外を探索
					n = true;
					for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()){//
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
	
	
	public void compPartialSafe() {
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

	
	public void compEarliest() {
		nEarliest = new boolean[idBound];//すべての基本ブロックの数で初期化
		xEarliest = new boolean[idBound];
		Arrays.fill(nEarliest, true);//trueで埋める
		Arrays.fill(xEarliest, true);
		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){//目的のブロックから最後のブロックまで繰り返す
			BasicBlk blk = (BasicBlk)p.elem();
			boolean n = nUSafe[blk.id] || nDSafe[blk.id];//
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
	
	
	public void compKeepOrder(){
		nKeepOrder = new boolean[idBound];
		xKeepOrder = new boolean[idBound];
		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
			BasicBlk blk = (BasicBlk)p.elem();
			nKeepOrder[blk.id] = !nUSafe[blk.id] || Transp_addr[blk.id];
			xKeepOrder[blk.id] = !xUSafe[blk.id] || xTransp_addr[blk.id];
		}
	}
	
	
	public void compDelayed() {
		nDelayed = new boolean[idBound];//すべての基本ブロックの数idBoundで初期化
		xDelayed = new boolean[idBound];
		Arrays.fill(nDelayed, true);//初期値trueで埋める
		Arrays.fill(xDelayed, true);
		boolean change = true;
		while(change){//Delayedの値に変更があった場合に全部やり直す。
			change = false;
			for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
				BasicBlk blk = (BasicBlk)p.elem();
				boolean n = false;
				if(nEarliest[blk.id]){//Ealiestかを確認
					n = true;
				}else if(blk!=f.flowGraph().entryBlk()){//entryblockだと命令がないため見る必要がないから
					n = true;
					for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()){//predの命令をひとつづつ見ている
						BasicBlk pred = (BasicBlk)q.elem();
						if(!xDelayed[pred.id] || !xKeepOrder[pred.id] || xIsSame[pred.id]){//nDelayをチェック
							n = false;
							break;
						}
					}
				}
				boolean x = xEarliest[blk.id] || (n && !nIsSame[blk.id] && nKeepOrder[blk.id]);//xDelayをチェック
				if(nDelayed[blk.id]!=n || xDelayed[blk.id]!=x) change = true;//xDelay,nDelayに変更があったかチェック
				nDelayed[blk.id] = n;
				xDelayed[blk.id] = x;
			}
		}
	}
	
	
	public void compLatest() {
		nLatest = new boolean[idBound];//基本ブロックの数配列を用意
		xLatest = new boolean[idBound];
		for(BiLink p=f.flowGraph().basicBlkList.last();!p.atEnd();p=p.prev()){//下から上に見ていく
			BasicBlk blk = (BasicBlk)p.elem();
			boolean x = false;
			if(xDelayed[blk.id]){//delayedがtrueかつ
				if(xIsSame[blk.id]) x = true;//issafeがtrueならxをtrueに
				else if(blk!=f.flowGraph().exitBlk()){//最後ではないなら
					for(BiLink q=blk.succList().first();!q.atEnd();q=q.next()){//succをひとつづつ確認
						BasicBlk succ = (BasicBlk)q.elem();//呼び出し
						if(!nDelayed[succ.id]){//取り出したsuccのndelayedがfalseならば
							x = true;//xをtrueにして終了
							break;
						}
					}
				}
			}
			xLatest[blk.id] = x;
			nLatest[blk.id] = nDelayed[blk.id] && (!xDelayed[blk.id] || nIsSame[blk.id]);
		}
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
	
	
	public void compInsert(){
		nInsert = new boolean[idBound];
		xInsert = new boolean[idBound];
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			nInsert[blk.id] = nLatest[blk.id] && !nIsolated[blk.id];
			xInsert[blk.id] = xLatest[blk.id] && !xIsolated[blk.id];
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
	
	
	public LirNode insertNewNode(LirNode expr, LirNode addr, ArrayList vars){
		expr = expr.makeCopy(env.lir);
		LirNode newNode = null;
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			if(nInsert[blk.id]){
				boolean same_addr = false;
				boolean insert = false;
				for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
					LirNode node = (LirNode)p.elem();
					if(isKill(expr.kid(1),node,vars,blk,p))break;
					if(!isLoad(node))continue;
					if(node.kid(1).equals(expr.kid(1))){
						newNode = getNewNode(newNode,expr);
						p.addBefore(newNode);
						replace(node,newNode,blk,p);
						insert = true;
						break;
					}
					if(sameAddr(node,addr)) same_addr = true;
					else if(same_addr){
						insert = true;
						newNode = getNewNode(newNode,expr);
						p.addBefore(newNode);
						break;
					}
				}
				if(!insert){
					newNode = getNewNode(newNode,expr);
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
						if(isKill(expr.kid(1),node,vars,blk,p))break;
						if(!isLoad(node))continue;
						if(node.equals(newNode)){
							insert = true;
							break;
						}
						if(node.kid(1).equals(expr.kid(1))){
							newNode = getNewNode(newNode,expr);
							p.addBefore(newNode);
							replace(node,newNode,blk,p);
							insert = true;
							break;
						}
						if(sameAddr(node,addr)){
							if(latest!=null){
								newNode = getNewNode(newNode,expr);
								latest.addBefore(newNode);
								insert = true;
								break;
							}
						}else latest = p;
					}
				}
				if(!insert){
					insert = true;
					newNode = getNewNode(newNode,expr);
					blk.instrList().last().addBefore(newNode);
				}
			}
		}
		return newNode;
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
	
	
	public void replace(LirNode node, LirNode newNode, BasicBlk blk, BiLink p){
		node.setKid(1, newNode.kid(0).makeCopy(env.lir));
//		LirNode copy = node.makeCopy(env.lir);
//		ddcpyp.cpyp(blk, copy.kid(0), copy.kid(1), p, 1);
	}
	
	
	public void collectVars(ArrayList vars, LirNode exp){
		for(int i=0;i<exp.nKids();i++){
			if(exp.kid(i).opCode==Op.REG) vars.add(exp.kid(i).makeCopy(env.lir));
			else if(exp.kid(i).nKids()>0) collectVars(vars,exp.kid(i));
		}
	}
	
	
	public void updateAlias(LirNode node, BasicBlk blk){
		ddalias.insertNewEntry(node, blk);
	}
	
	
	LirNode getAddr(LirNode exp){
		if(exp.kid(0).nKids()==0) return exp.kid(0);
		else return getAddr(exp.kid(0));
	}
	
	
	public boolean checkType(LirNode exp){
		char type=Type.toString(exp.type).charAt(0);
		return (type=='I' || type=='F');
	}
	
	
	public void printLocalProp(LirNode expr) {
		System.out.println("----------------------------------------------------");
		for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();
			System.out.println("blk: " + blk.label());
			System.out.println("id: " + blk.id);
			System.out.println("NSameAddr: " + nSameAddr[blk.id] + ", XSameAddr: "+ xSameAddr[blk.id]);
			System.out.println("nIsSame: " + nIsSame[blk.id]+", xIsSame:"+xIsSame[blk.id]);
			System.out.println("Transp_e: " + Transp_e[blk.id]+", xTransp_e:"+xTransp_e[blk.id]);
			System.out.println("Transp_addr: " + Transp_addr[blk.id]+", xTransp_addr:"+xTransp_addr[blk.id]);
			System.out.println("----------------------------------------------------");
		}
		System.out.println("target -- " + expr);
		System.out.println("");
	}
	
	
	public void printGlobalProp(LirNode expr) {
		System.out.println("----------------------------------------------------");
		for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();
			System.out.println("blk: " + blk.label());
			System.out.println("id: " + blk.id);
			System.out.println("NDSafe: " + nDSafe[blk.id] + ", XDSafe: "+ xDSafe[blk.id]);
			System.out.println("NUSafe: " + nUSafe[blk.id] + ", XUSafe: "+ xUSafe[blk.id]);
			System.out.println("NEarliest: " + nEarliest[blk.id]+ ", XEarliest: " + xEarliest[blk.id]);
			System.out.println("NKeepOrder: " + nKeepOrder[blk.id]+" , XKeepOrder:"+xKeepOrder[blk.id]);
			System.out.println("NDelayed: " + nDelayed[blk.id] + ", XDelayed: "+ xDelayed[blk.id]);
			System.out.println("NLatest: " + nLatest[blk.id] + ", XLatest: "+ xLatest[blk.id]);
			System.out.println("NIsolated: " + nIsolated[blk.id] + ", XIsolated: "+ xIsolated[blk.id]);
			System.out.println("NInsert: " + nInsert[blk.id]+", XInsert:"+xInsert[blk.id]);
			System.out.println("NReplace: " + nReplace[blk.id]+", XReplace:"+xReplace[blk.id]);
			System.out.println("----------------------------------------------------");
		}
		System.out.println("target -- " + expr);
		System.out.println("");
	}
}