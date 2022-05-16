/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Vector;

import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.ana.DFST;
import coins.backend.ana.DominanceFrontiers;
import coins.backend.ana.Dominators;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirLabelRef;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.sym.Label;
import coins.backend.sym.Symbol;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;

/**
 * Global Load Instruction Aggregation.
 **/
public class GLIA implements LocalTransformer {
	private String tmpSymName = "_glia";
	private Util util;
	public static final int THR = SsaEnvironment.OptThr;
	/** The threshold of debug print **/
	public static final int THR2 = SsaEnvironment.AllThr;
	private SsaEnvironment env;
	private SsaSymTab sstab;
	private Function f;
	private Dominators dom;
	/** The current dominance frotiers **/
	DominanceFrontiers df;
	private DFST dfst;
	BasicBlk[] bVecInOrderOfRPost;

	private Symbol invalidSym;
	private Symbol bottomSym;

	/** Whether analyze the aliases of the memory object **/
	private boolean withMem;

	/** The target expression **/
	LirNode expr;
	LirNode address;
	HashMap addresses;
	HashMap leftToNode;
	Vector vars;
	Vector targetPcc;
	boolean checkInsOfPhi;
	Vector insertedInstrs;

	HashMap renameBlkTable;
	HashMap repToIns;
	
	/** Entry same address **/
	boolean[] nSameAddr;
	/** Exit same address **/
	boolean[] xSameAddr;

	/** Contain same instrument with target **/
	boolean[] isSame;
	
	boolean[] isDef;
	
	boolean[] isStore;
	
	boolean[] isAmb;

	/** Transparency of BusyCodeMotion **/
	boolean[] transp_e;

	/** Transparency of LazyCodeMotion **/
	boolean[] transp_addr;

	/** Entry down-safety of BusyCodeMotion **/
	boolean[] ndSafe;

	/** Exit down-safety of BusyCodeMotion **/
	boolean[] xdSafe;

	/** Entry up-safety **/
	boolean[] nuSafe;

	/** Exit up-safety **/
	boolean[] xuSafe;

	boolean[] npUpSafe;

	boolean[] xpUpSafe;
	
	boolean[] npDownSafe;
	boolean[] xpDownSafe;

	/** Entry earliestness **/
	boolean[] nEarliest;

	/** Exit earliestness **/
	boolean[] xEarliest;

	/** Entry delayability **/
	boolean[] nDelayed;

	/** Exit delayability **/
	boolean[] xDelayed;

	boolean[] xLatest;

	boolean[] nLatest;

	/** Entry liveness **/
	boolean[] nLive;

	/** Exit liveness **/
	boolean[] xLive;

	boolean[] Insert;

	/** Entry replacement **/
	boolean[] Replace;

	boolean[] Phi;

	LirNode preTmp;

	/** The Phi Congruence Class list **/
	Vector congruenceClassList;
	/** Exit insertion **/

	public static final String GLIA = "_glia";

	/**
	 * Constructor.
	 * 
	 * @param env
	 *            The environment of the SSA module
	 * @param sstab
	 *            The current symbol table on SSA form
	 **/
	public GLIA(SsaEnvironment env, SsaSymTab sstab) {
		this.env = env;
		this.sstab = sstab;
	}

	
	private void printAll(){
		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
			BasicBlk blk = (BasicBlk)p.elem();
			System.out.println("********************");
			System.out.println("blk:"+blk.label());
			for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
				LirNode node = (LirNode)q.elem();
				System.out.println("node:"+node);
			}
		}
		System.out.println("********************");
	}
	
	
	private void printLocalProp() {
		System.out.println("----------------------------------------------------");
		for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();
			System.out.println("blk: " + blk.label());
			System.out.println("NSameAddr: " + nSameAddr[blk.id] + ", XSameAddr: "+ xSameAddr[blk.id]);
			System.out.println("isDef: " + isDef[blk.id]);
			System.out.println("isStore: " + isStore[blk.id]);
			System.out.println("isAmb: " + isAmb[blk.id]);
			System.out.println("isSame: " + isSame[blk.id]);
			System.out.println("transp_e: " + transp_e[blk.id]);
			System.out.println("transp_addr: " + transp_addr[blk.id]);
			System.out.println("----------------------------------------------------");
		}
		System.out.println("target -- " + expr);
	}
	
	
	private void printGlobalProp() {
		System.out.println("----------------------------------------------------");
		for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();
			System.out.println("blk: " + blk.label());
			System.out.println("NDSafe: " + ndSafe[blk.id] + ", XDSafe: "+ xdSafe[blk.id]);
			System.out.println("NUSafe: " + nuSafe[blk.id] + ", XUSafe: "+ xuSafe[blk.id]);
			System.out.println("NpartialUpSafe: " + npUpSafe[blk.id]+ ", XpartialUpSafe: " + xpUpSafe[blk.id]);
			System.out.println("NEarliest: " + nEarliest[blk.id]+ ", XEarliest: " + xEarliest[blk.id]);
			System.out.println("NDelayed: " + nDelayed[blk.id] + ", XDelayed: "+ xDelayed[blk.id]);
			System.out.println("NLatest: " + nLatest[blk.id] + ", XLatest: "+ xLatest[blk.id]);
			System.out.println("NLive: " + nLive[blk.id] + ", XLive: "+ xLive[blk.id]);
			System.out.println("Insert: " + Insert[blk.id]);
			System.out.println("Replace: " + Replace[blk.id]);
			System.out.println("Phi: " + Phi[blk.id]);
			System.out.println("----------------------------------------------------");
		}
		System.out.println("target -- " + expr);
	}
	
	
	/**
	 * Make a phi congruence class list.
	 **/
	private void makeCongruenceClassList() {

		// Begin

		congruenceClassList = new Vector();
		// End

		for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();

			for (BiLink q = blk.instrList().first(); !q.atEnd(); q = q.next()) {
				LirNode node = (LirNode) q.elem();

				if (node.opCode == Op.PHI) {

					Vector newCongruenceClass = new Vector();
					// End
					newCongruenceClass.add((LirSymRef) node.kid(0));
					for (int i = 1; i < node.nKids(); i++) {
						LirNode arg = node.kid(i);
						if(arg.kid(0).opCode!=Op.REG){
							continue;
						}
						newCongruenceClass.add((LirSymRef) arg.kid(0));
					}

					int i = 0;
					while (i < congruenceClassList.size()) {
						boolean find = false;
						// Begin
						Vector congruenceClass = (Vector) congruenceClassList
								.get(i);
						// End
						for (int iNCC = 0; iNCC < newCongruenceClass.size(); iNCC++) {
							LirNode phiVar = (LirNode) newCongruenceClass.get(iNCC);
							for (int iCC = 0; iCC < congruenceClass.size(); iCC++) {
								LirNode var = (LirNode) congruenceClass.get(iCC);
								if (phiVar.equals(var)) {
									for (int iCC2 = 0; iCC2 < congruenceClass.size(); iCC2++) {
										LirNode n = (LirNode) congruenceClass.get(iCC2);
										if (!newCongruenceClass.contains(n)) {
											newCongruenceClass.add(n);
										}
									}
									congruenceClassList.remove(congruenceClass);
									find = true;
									break;
								}
								if (find) {
									break;
								}
							}
						}
						// End
						if (!find) {
							i++;
						}
					}

					congruenceClassList.add(newCongruenceClass);
				}
			}
		}
	}

	
	private Vector returnClass(LirNode var) {
		for (int iCCL = 0; iCCL < congruenceClassList.size(); iCCL++) {
			Vector set = (Vector) congruenceClassList.get(iCCL);
			for (int iS = 0; iS < set.size(); iS++) {
				LirNode nodeInSet = (LirNode) set.get(iS);
				if (var.equals(nodeInSet)) {
					return set;
				}
			}
		}
		Vector newset = new Vector();
		newset.add(var);
		return newset;
	}

	
	/**
	 * Return the pcc which the node belongs to.
	 * 
	 * @param node
	 *            The specified expression.
	 **/
	private Vector belongClass(Vector vars) {

		Vector pcc = new Vector();

		for (int i = 0; i < vars.size(); i++) {
			LirNode var = (LirNode) vars.get(i);
			Vector sameClass = returnClass(var);
			if (sameClass != null) {
				pcc.add(returnClass(var));
			}
		}

		return pcc;
	}

	
	private Vector belongClass(LirNode var) {

		Vector pcc = new Vector();

		Vector sameClass = returnClass(var);
		if (sameClass != null) {
			pcc.add(returnClass(var));
		}

		return pcc;
	}

	
	LirNode getAddress(LirNode rhs) {
		if (rhs.opCode == Op.SET) {
			return getAddress(rhs.kid(1));
		}

		if (rhs.opCode == Op.FRAME || rhs.opCode == Op.STATIC) {
			return rhs;
		} else if (rhs.opCode == Op.REG) {
			if (addresses.containsKey(rhs)) {
				LirNode add = (LirNode) addresses.get(rhs);
				return add;
			} else {
				return rhs;
			}
		} else if (rhs.nKids() == 0) {
			return null;
		} else {
			return getAddress(rhs.kid(0));
		}
		
	}

	
	/**
	 * If instrument and target instrument reference same address,
	 * return true. otherwise return false.
	 * 
	 * @param node
	 * @return
	 */
	boolean sameAddress(LirNode node, LirNode debExp) {
		LirNode addr1 = getAddress(node.kid(1));
		LirNode addr2 = getAddress(debExp.kid(1));

		if (addr1 == addr2 && addr1 != null) {
			return true;
		} else {
			return false;
		}
	}
	

	/**
	 * check whether reference address. If instrument is ambitious
	 * reference,return true.
	 * 
	 * @param mem
	 * @return
	 */
	boolean checkAmbness(LirNode mem) {
		if (mem.opCode == Op.REG) {
			if (addresses.containsKey(mem)) {
				return false;
			}else{
				return true;
			}
		} else if (mem.opCode == Op.FRAME || mem.opCode == Op.STATIC) {
			return false;
		} else {
			return checkAmbness(mem.kid(0));
		}
	}

	
	/**
	 * If instrument is ambitious call,return true.
	 * 
	 * @param call
	 * @return
	 */
	boolean isAmbCall(LirNode call) {
		if (call.opCode != Op.CALL || address==null) {
			return false;
		}else{
			if(address.opCode==Op.STATIC){
				return true;
			}else{
				LirNode args = call.kid(1);
				if (args.nKids() == 0 || expr == null) {
					return false;
				}
				for (int i = 0; i < args.nKids(); i++) {
					LirNode arg = args.kid(i);
					LirNode argAddr = getAddress(arg);
					if (argAddr != null && argAddr.equals(address)) {
						// contain same address.
						return true;
					} else if (vars.contains(arg)) {
						// argument is contained in target expression
						return true;
					}
				}
				return false;
			}
		}
	}

	
	/**
	 * If instrument is ambitious reference , return true.otherwise return
	 * false.
	 * 
	 * @param node
	 * @return
	 */
	boolean isAmb(LirNode node) {
		if (isAmbCall(node)) {
			return true;
		} else if (isLoad(node) && checkAmbness(node.kid(1).kid(0))) {
			return true;
		} else {
			return false;
		}
	}

	private boolean isLoad(LirNode node) {
		if (node.opCode != Op.SET || node.kid(0).opCode != Op.REG
				|| node.kid(1).opCode != Op.MEM) {
			return false;
		} else {
			return true;
		}
	}
	
	
	boolean isStore(LirNode node){
		if(node.opCode==Op.SET && node.kid(0).opCode==Op.MEM){
			if(address==null){
				return true;
			}else{
				LirNode addr = getAddress(node.kid(0));
				if(address.equals(addr)){
					return true;
				}
			}
		}
		
		return false;
		
	}
	

	boolean defNode(LirNode node){
		if(node.opCode==Op.SET || node.opCode==Op.PHI){
			if(vars.contains(node.kid(0)) || samePcc(node.kid(0))){
				return true;
			}else{
				return false;
			}
		}else if(node.opCode==Op.CALL){
			if(node.kid(2).nKids()==0){
				return false;
			}
			LirNode dst = node.kid(2).kid(0);
			if(vars.contains(dst) || samePcc(dst)){
				return true;
			}else{
				return false;
			}
		}else{
			return false;
		}
	}
	
		
	boolean isDef(LirNode node) {
		if(node.opCode==Op.PHI){
			if(defNode(node) && loopPhi(node)){
				return true;
			}else{
				return false;
			}
		}else if(node.opCode==Op.SET){
			if(defNode(node)){
				return true;
			}else{
				return false;
			}
		}else if(node.opCode==Op.CALL){
			if(defNode(node)){
				return true;
			}else{
				return false;
			}
		}else{
			return false;
		}
	}


	/**
	 *  Check this phi node exists at head of loop.
	 */
	boolean loopPhi(LirNode phi) {

		Label label = ((LirLabelRef) phi.kid(1).kid(2)).label;
		BasicBlk thisBlk = label.basicBlk();

		for (int i = 1; i < phi.nKids(); i++) {
			Label arg = ((LirLabelRef) phi.kid(i).kid(1)).label;
			BasicBlk pred = arg.basicBlk();
			if (dom.dominates(thisBlk, pred)) {
				return true;
			}
		}

		return false;

	}

	
	boolean samePcc(LirNode var) {
		Vector instrPcc = new Vector();
		instrPcc = belongClass(var);
		if (!targetPcc.contains(instrPcc.get(0))) {
			return false;
		} else {
			return true;
		}
	}

	
	/**
	 * If node is not ambitious load instrument,then return true. 
	 * @param instr
	 * @return
	 */
	boolean setAddr(LirNode node) {
		if (node.opCode != Op.SET || node.kid(0).opCode != Op.REG) {
			return false;
		} else {
			LirNode addr = getAddress(node.kid(1));
			if (addr != null
					&& (addr.opCode == Op.FRAME || addr.opCode == Op.STATIC)) {
				return true;
			} else {
				return false;
			}
		}
	}

	
	boolean sameForm(LirNode target, LirNode node) {
		if (target.opCode != node.opCode || target.nKids() != node.nKids()) {
			return false;
		} else if (target.opCode != Op.REG && target.nKids() == 0 && !target.equals(node)) {
			return false;
		} else {
			for (int i = 0; i < target.nKids(); i++) {
				if (!sameForm(target.kid(i), node.kid(i))) {
					return false;
				}
			}
			return true;
		}
	}

	
	boolean sames(LirNode target, LirNode node) {
		if (target.opCode != node.opCode || target.type != node.type) {
			return false;
		}

		if (!sameForm(target, node)) {
			return false;
		}

		Vector varInstr = new Vector();
		varInstr = detectVar(node.kid(1), varInstr);

		for (int i = 0; i < varInstr.size(); i++) {
			LirNode var = (LirNode) varInstr.get(i);
			Vector instrPcc = new Vector();
			instrPcc = belongClass(var);
			if (!targetPcc.contains(instrPcc.get(0))) {
				return false;
			}
		}
		
		return true;

	}

	
	/**
	 * Check variable of right hand of expression.
	 * 
	 * @param rhs
	 */
	Vector detectVar(LirNode rhs, Vector vars) {
		if (rhs.opCode == Op.REG) {
			vars.add(rhs);
		} else if (rhs.opCode != Op.STATIC && rhs.opCode != Op.FRAME) {
			for (int i = 0; i < rhs.nKids(); i++) {
				detectVar(rhs.kid(i), vars);
			}
		}
		return vars;
	}

	
	/**
	 * Compute local properties.
	 **/
	private void compLocalProperty() {
		int idBound = f.flowGraph().idBound();
		nSameAddr = new boolean[idBound];
		xSameAddr = new boolean[idBound];
		isDef = new boolean[idBound];
		isStore = new boolean[idBound];
		isAmb = new boolean[idBound];

		isSame = new boolean[idBound];
		transp_e = new boolean[idBound];
		transp_addr = new boolean[idBound];
		
		Arrays.fill(isDef, false);
		Arrays.fill(isStore, false);
		Arrays.fill(isAmb, false);
		Arrays.fill(isSame, false);
		Arrays.fill(transp_e, false);
		Arrays.fill(transp_addr, false);

		for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();
			// compute NSameAdd
			nSameAddr[blk.id] = isNSameAddr(blk);

			// compute XSameAdd
			xSameAddr[blk.id] = isXSameAddr(blk);
			
			// compute isSame , isDef , isStore , isAmb , transp_e , transp_addr
			compOtherLocalProp(blk);
		}
	}
	
	
	void compOtherLocalProp(BasicBlk blk){
		boolean transpAddr = true;
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
			LirNode node = (LirNode)p.elem();

			if(isDef(node)){
				isDef[blk.id] = true;
			}
			
			if(isStore(node)){
				isStore[blk.id] = true;
			}
			
			if(isAmb(node)){
				isAmb[blk.id] = true;
			}
			
			if(isLoad(node)){
				if((expr.kid(1).equals(node.kid(1)) || sames(expr, node))){
					isSame[blk.id] = true;
				}else if(!sameAddress(node, expr)){
					transpAddr = false;
				}
			}

		}
		
		if(isStore[blk.id] || isAmb[blk.id]){
			transp_e[blk.id] = false;
			transp_addr[blk.id] = false;
		}else{
			transp_e[blk.id] = true;
			transp_addr[blk.id] = transpAddr;
		}
		
	}

	
	/**
	 * Check whether the specified block has an entry same reference which not
	 * ambitious.
	 * 
	 * @param blk
	 * @return
	 */
	private boolean isNSameAddr(BasicBlk blk) {
		for (BiLink p = blk.instrList().first(); !p.atEnd(); p = p.next()) {
			LirNode node = (LirNode) p.elem();
			if (isAmb(node) || isStore(node)) {
				return false;
			} else if (isLoad(node) && sameAddress(node,expr)) {
				return true;
			}
		}
		return false;
	}

	
	/**
	 * Check whether the specified block has an exit same reference which not
	 * ambitious.
	 * 
	 * @param blk
	 * @return
	 */
	private boolean isXSameAddr(BasicBlk blk) {
		for (BiLink p = blk.instrList().last(); !p.atEnd(); p = p.prev()) {
			LirNode node = (LirNode) p.elem();
			if (isAmb(node) || isStore(node)) {
				return false;
			} else if (isLoad(node) && sameAddress(node,expr)) {
				return true;
			}
		}
		return false;
	}

	
	/**
	 * Compute global properties.
	 **/
	private void compGlobalProperty() {
		int idBound = f.flowGraph().idBound();

		ndSafe = new boolean[idBound];
		xdSafe = new boolean[idBound];

		nuSafe = new boolean[idBound];
		xuSafe = new boolean[idBound];

		npUpSafe = new boolean[idBound];
		xpUpSafe = new boolean[idBound];

		npDownSafe = new boolean[idBound];
		xpDownSafe = new boolean[idBound];
		
		nEarliest = new boolean[idBound];
		xEarliest = new boolean[idBound];
		nDelayed = new boolean[idBound];
		xDelayed = new boolean[idBound];

		nLatest = new boolean[idBound];
		xLatest = new boolean[idBound];

		nLive = new boolean[idBound];
		xLive = new boolean[idBound];

		Insert = new boolean[idBound];

		Replace = new boolean[idBound];

		Phi = new boolean[f.flowGraph().idBound()];

		Arrays.fill(npDownSafe, true);
		Arrays.fill(xpDownSafe, true);
		Arrays.fill(npUpSafe, true);
		Arrays.fill(xpUpSafe, true);
		Arrays.fill(ndSafe, true);
		Arrays.fill(xdSafe, true);
		Arrays.fill(nuSafe, true);
		Arrays.fill(xuSafe, true);
		Arrays.fill(nEarliest, true);
		Arrays.fill(xEarliest, true);
		Arrays.fill(nDelayed, true);
		Arrays.fill(xDelayed, true);

		Arrays.fill(nLatest, true);
		Arrays.fill(xLatest, true);

		Arrays.fill(nLive, false);
		Arrays.fill(xLive, false);

		Arrays.fill(Replace, false);
		Arrays.fill(Insert, false);
		Arrays.fill(Phi, false);

		// comp dSafe
		compDSafe();

		compPartialDSafe();

		// comp uSafe
		compUSafe();

		compPartialUSafe();

		// comp earliest
		compEarliest();

		// comp delayed
		compDelayed();

		// comp latest
		compLatest();

		// comp live
		compLive();

		// comp insert
		compInsert();

		if(checkInsOfPhi){

			compPhi();

			compRenameArg();
			
		}

		// comp replace
		compReplace();

	}

	
	private void compDSafe() {

		boolean change = true;

		while (change) {
			change = false;
			for (BiLink p = f.flowGraph().basicBlkList.last(); !p.atEnd(); p = p.prev()) {
				BasicBlk blk = (BasicBlk) p.elem();

				boolean x = true;

				if (isSame[blk.id] && xSameAddr[blk.id]) {
					x = true;
				} else {
					if (blk == f.flowGraph().exitBlk()) {
						x = false;
					} else {
						for (BiLink pp = blk.succList().first(); !pp.atEnd(); pp = pp.next()) {
							BasicBlk succ = (BasicBlk) pp.elem();
							if (!ndSafe[succ.id]) {
								x = false;
								break;
							}
						}
					}
				}

				if (x != xdSafe[blk.id]) {
					xdSafe[blk.id] = x;
					change = true;
				}

				boolean n = (nSameAddr[blk.id] && isSame[blk.id]) || (transp_e[blk.id] && xdSafe[blk.id]);

				if (n != ndSafe[blk.id]) {
					ndSafe[blk.id] = n;
					change = true;
				}
			}
		}
	}
	
	
	private void compPartialDSafe(){
		boolean change = true;
		while (change) {
			change = false;

			for(BiLink p=f.flowGraph().basicBlkList.last();!p.atEnd();p=p.prev()){
				BasicBlk blk = (BasicBlk)p.elem();
				boolean np = false;
				
				if(ndSafe[blk.id]){
					np = true;
				}else{
					if(blk == f.flowGraph().exitBlk()){
						np=false;
					}else{
						for(BiLink q=blk.succList().first();!q.atEnd();q=q.next()){
							BasicBlk succ = (BasicBlk)q.elem();
							if(xdSafe[succ.id]){
								np = true;
								break;
							}
						}
					}
				}
				
				if(np!=npDownSafe[blk.id]){
					npDownSafe[blk.id] = np;
					change=true;
				}
				
				boolean xp = xdSafe[blk.id] || (npDownSafe[blk.id] && transp_e[blk.id]);

				if(xp!=xpDownSafe[blk.id]){
					xpDownSafe[blk.id] = xp;
					change = true;
				}
			}
		}
	}


	private void compUSafe() {

		boolean change = true;
		while (change) {
			change = false;
			for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
				BasicBlk blk = (BasicBlk) p.elem();

				// comp NuSafe
				boolean n = true;

				if(nSameAddr[blk.id]){
					n = true;
				}else{
					if (blk == f.flowGraph().entryBlk()) {
						n = false;
					} else {
						for (BiLink q = blk.predList().first(); !q.atEnd(); q = q.next()) {
							BasicBlk pred = (BasicBlk) q.elem();
							if (!(xSameAddr[pred.id] || xuSafe[pred.id])) {
								n = false;
								break;
							}
						}
					}
				}
				
				if (n != nuSafe[blk.id]) {
					nuSafe[blk.id] = n;
					change = true;
				}

				// comp XuSafe
				boolean x = transp_e[blk.id] && (nSameAddr[blk.id] || nuSafe[blk.id]);
				if (x != xuSafe[blk.id]) {
					xuSafe[blk.id] = x;
					change = true;
				}
			}
		}
	}

	
	private void compPartialUSafe() {
		boolean change = true;
		while (change) {
			change = false;

			for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
				BasicBlk blk = (BasicBlk)p.elem();
				boolean np = false;
				
				if(nuSafe[blk.id]){
					np = true;
				}else{
					if(blk == f.flowGraph().entryBlk()){
						np=false;
					}else{
						for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()){
							BasicBlk pred = (BasicBlk)q.elem();
							if(xpUpSafe[pred.id]){
								np = true;
								break;
							}
						}
					}
				}
				
				if(np!=npUpSafe[blk.id]){
					npUpSafe[blk.id] = np;
					change=true;
				}
				
				boolean xp = xuSafe[blk.id] || (npUpSafe[blk.id] && transp_e[blk.id]);

				if(xp!=xpUpSafe[blk.id]){
					xpUpSafe[blk.id] = xp;
					change = true;
				}
			}
		}
	}

	
	private void compEarliest() {

		boolean change = true;
		while (change) {
			change = false;

			for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
				BasicBlk blk = (BasicBlk) p.elem();

				boolean n = false;

				if(ndSafe[blk.id] || nuSafe[blk.id]){
					if(blk == f.flowGraph().entryBlk()){
						n = true;
					}else{
						for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()){
							BasicBlk pred = (BasicBlk)q.elem();
							if((!transp_e[pred.id] || isDef[pred.id])||
									!(xuSafe[pred.id] || xdSafe[pred.id])){
								n = true;
							}
						}
					}
				}

				if (nEarliest[blk.id] != n) {
					nEarliest[blk.id] = n;
					change = true;
				}

				boolean x = xdSafe[blk.id] && !nuSafe[blk.id] && (!transp_e[blk.id] || isDef[blk.id]);
				
				if(xEarliest[blk.id] != x){
					xEarliest[blk.id] = x;
					change = true;
				}
			}
		}
	}

	
	private void compDelayed() {

		boolean change = true;
		while (change) {
			change = false;
			for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
				BasicBlk blk = (BasicBlk) p.elem();

				// comp NDelayed
				boolean n = true;

				if (nEarliest[blk.id]) {
					n = true;
				} else {
					if (blk == f.flowGraph().entryBlk()) {
						n = false;
					} else {
						for (BiLink pp = blk.predList().first(); !pp.atEnd(); pp = pp.next()) {
							BasicBlk pred = (BasicBlk) pp.elem();
							if (!xDelayed[pred.id] || (isSame[pred.id] && xSameAddr[pred.id])) {
								n = false;
								break;
							}
						}
					}
				}

				if (n != nDelayed[blk.id]) {
					nDelayed[blk.id] = n;
					change = true;
				}

				boolean x = true;

				x = xEarliest[blk.id]
						|| (nDelayed[blk.id] && !isSame[blk.id] && keepOrder(blk));

				if (x != xDelayed[blk.id]) {
					xDelayed[blk.id] = x;
					change = true;
				}
			}
		}
	}
	

	boolean keepOrder(BasicBlk blk) {
		if (!npUpSafe[blk.id]) {
			if (nSameAddr[blk.id]) {
				if (transp_addr[blk.id]) {
					return true;
				} else {
					return false;
				}
			}
			return true;
		} else {
			if (transp_addr[blk.id]) {
				return true;
			} else {
				return false;
			}
		}
	}

	
	private void compLatest() {

		boolean change = true;
		while (change) {
			change = false;

			for (BiLink p = f.flowGraph().basicBlkList.last(); !p.atEnd(); p = p.prev()) {
				BasicBlk blk = (BasicBlk) p.elem();

				boolean x = false;
				
				if(!xDelayed[blk.id]){
					x = false;
				}else{
					if(isSame[blk.id] && xSameAddr[blk.id]){
						x = true;
					}else{
						for(BiLink q=blk.succList().first();!q.atEnd();q=q.next()){
							BasicBlk succ = (BasicBlk)q.elem();
							if(!nDelayed[succ.id]){
								x = true;
								break;
							}
						}
					}
				}
				
				if(x!=xLatest[blk.id]){
					xLatest[blk.id] = x;
				}
				
				boolean n = nDelayed[blk.id] && (isSame[blk.id] && nSameAddr[blk.id] || !xDelayed[blk.id]);

				if (n != nLatest[blk.id]) {
					nLatest[blk.id] = n;
					change = true;
				}
			}

		}

	}


	private void compLive() {
		boolean change = true;
		while (change) {
			change = false;
			for (BiLink p = f.flowGraph().basicBlkList.last(); !p.atEnd(); p = p.prev()) {
				BasicBlk blk = (BasicBlk) p.elem();

				boolean x = false;

				if (blk == f.flowGraph().exitBlk()) {
					x = false;
				} else {
					for (BiLink q = blk.succList().first(); !q.atEnd(); q = q.next()) {
						BasicBlk succ = (BasicBlk) q.elem();
						if(!nLatest[succ.id] &&
								(nSameAddr[succ.id] && isSame[succ.id]) ||
								 nLive[succ.id]){
							x = true;
							break;
						}
					}
				}
				
				if (x != xLive[blk.id]) {
					xLive[blk.id] = x;
					change = true;
				}

				boolean n = !nLatest[blk.id] && xLive[blk.id] && transp_e[blk.id] ||
				isSame[blk.id] && nSameAddr[blk.id];

				if (n != nLive[blk.id]) {
					nLive[blk.id] = n;
					change = true;
				}
			}
		}
	}
	

	private void compInsert() {
		
		ArrayList insedblk = new ArrayList();
		
		BasicBlk[] bVecInOrderOfRPost = dfst.blkVectorByRPost();

		for (int i = 1; i < bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];

			boolean ins = xLive[blk.id] && (xLatest[blk.id] || nLatest[blk.id]);
			
			
			if(ins){
				//Check new BasicBlk is dominated by already Insert[blk]=true.
				for(int j=0;j<insedblk.size();j++){
					BasicBlk v = (BasicBlk)insedblk.get(j);
					if(dom.dominates(v, blk)){
						ins = false;
						break;
					}
				}
			}
			
			if(ins){
				insedblk.add(blk);
			}
			
			Insert[blk.id] = ins;

		}
		
		if(insedblk.size()>1){
			checkInsOfPhi = true;
		}
		
	}

	
	private void compPhi() {
		
		BasicBlk[] bVecInOrderOfRPost = dfst.blkVectorByRPost();

		for (int i = 1; i < bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];

			if (!(Insert[blk.id] || Phi[blk.id])) {
				continue;
			}

			for (BiLink p = df.frontiers[blk.id].first(); !p.atEnd(); p = p.next()) {
				BasicBlk domFront = (BasicBlk) p.elem();
				
				Phi[domFront.id] = nLive[domFront.id];

				if(Phi[domFront.id]){
					Insert[domFront.id] = false;
				}
			}
		}
	}
	
	
	private void compRenameArg(){

		BasicBlk[] bVecInOrderOfRPost = dfst.blkVectorByRPost();

		for (int i = 1; i < bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			
			if(Phi[blk.id]){
				for(BiLink p=blk.predList().first();!p.atEnd();p=p.next()){
					BasicBlk pred = (BasicBlk)p.elem();
					
					BasicBlk v = searchBlk(pred);
					
					if(v==null){
						Phi[blk.id] = false;
						break;
					}
					
					renameBlkTable.put(pred, v);

				}
			}
		}
	}
	

	private void compReplace() {

		for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();

			if (!isSame[blk.id]) {
				Replace[blk.id] = false;
				continue;
			}
			
			if(Insert[blk.id]){
				Replace[blk.id] = true;
				repToIns.put(blk, blk);
				continue;
			}
			
			boolean rep = true;
			
			for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
				LirNode node = (LirNode)q.elem();
				if(sameNode(node)){

					BasicBlk insertBlk = searchBlk(blk);

					if(insertBlk==null){
						rep = false;
					}else{
						rep = true;
						repToIns.put(blk, insertBlk);
					}
					
					break;
				}else if(isDef(node)){
					rep = false;
					break;
				}
			}

			Replace[blk.id] = rep;
			
		}
	}
	

	boolean checkTransp(BasicBlk target,BasicBlk visit,boolean[] visited){

		if(target==visit){
			if(nLive[visit.id]){
				return true;
			}else{
				return false;
			}
		}
		
		if(!nLive[visit.id] || !transp_e[visit.id] || isDef[visit.id]){
			return false;
		}
		
		if(visit==f.flowGraph().exitBlk()){
			return true;
		}
		
		visited[visit.id] = true;
		
		for(BiLink p=visit.succList().first();!p.atEnd();p=p.next()){
			BasicBlk succ = (BasicBlk)p.elem();
			if(visited[succ.id]){
				continue;
			}else if(!checkTransp(target,succ,visited)){
				return false;
			}
		}
		
		return true;
		
	}
	
	
	boolean checkTransp(BasicBlk predBlk,BasicBlk succBlk){

		int idBound = f.flowGraph().idBound();
		boolean[] visited = new boolean[idBound];
		Arrays.fill(visited, false);
		visited[predBlk.id] = true;
		for(BiLink p=predBlk.succList().first();!p.atEnd();p=p.next()){
			BasicBlk succ = (BasicBlk)p.elem();
			if(visited[succ.id]){
				continue;
			}else if(!checkTransp(succBlk,succ,visited)){
				return false;
			}
		}
		return true;
		
	}
	

	BasicBlk searchBlk(BasicBlk blk){
		if(Insert[blk.id]){
			return blk;
		}else if(Phi[blk.id]){
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				if(isDef(node) || isStore(node) || isAmb(node)){
					Phi[blk.id] = false;
					return null;
				}else if(sameNode(node)){
					break;
				}
			}
			return blk;
		}

		BasicBlk domBlk = dom.immDominator(blk);
		while(true){
			if(domBlk==f.flowGraph().entryBlk() || domBlk==null){
				break;
			}else if(!xLive[domBlk.id] || !checkTransp(domBlk,blk)){
				return null;
			}else{
				if(Insert[domBlk.id] || Phi[domBlk.id]){
					return domBlk;
				}else{
					domBlk = dom.immDominator(domBlk);
				}
			}
		}

		return null;

	}

	
	LirNode createRightNode(LirNode right, BasicBlk blk) {

		if (vars.contains(right)) {
			LirNode samePcc = getVar(right, blk);
			if (samePcc == null) {
				return right;
			} else {
				return samePcc;
			}
		} else if (right.nKids() > 0) {
			for (int i = 0; i < right.nKids(); i++) {
				LirNode subRight = createRightNode(right.kid(i), blk);
				if (subRight == null) {
					return subRight;
				} else {
					right.setKid(i, subRight);
				}
			}
		}

		return right;
	}

	
	LirNode getVar(LirNode var, BasicBlk blk) {
		Vector wantClass = new Vector();
		Vector leftClass = new Vector();

		wantClass = returnClass(var);

		LirNode samePcc = null;

		for (BasicBlk v = blk;; v = dom.immDominator(v)) {
			if (v == null) {
				return null;
			}
			for (BiLink p = v.instrList().last(); !p.atEnd(); p = p.prev()) {
				LirNode node = (LirNode) p.elem();
				leftClass = returnClass(node.kid(0));
				if (leftClass.equals(wantClass)) {
					samePcc = node.kid(0);
					break;
				}
			}
			if (samePcc != null)
				break;
		}
		return samePcc;
	}
	

	boolean sameNode(LirNode node){
		if(isLoad(node) && (expr.kid(1).equals(node.kid(1)) || sames(expr, node))){
			return true;
		}else{
			return false;
		}
	}
	
	
	/**
	 * Check node contain load instruction.
	 * 
	 * @param node
	 * @return
	 */
	boolean containLoad(LirNode node) {
		if (node.opCode == Op.SET) {
			return containLoad(node.kid(1));
		} else if (node.opCode == Op.MEM) {
			if (node.kid(0).opCode == Op.ADD) {
				return true;
			} else {
				return false;
			}
		} else if (node.nKids() == 0) {
			return false;
		} else {
			for (int i = 0; i < node.nKids(); i++) {
				if (containLoad(node.kid(i))) {
					return true;
				}
			}
		}

		return false;
	}

	
	LirNode createNewSetExp(LirNode node,LirNode typeNode) {
		Symbol dstSym = sstab.newSsaSymbol(GLIA, typeNode.type);
		LirNode nn = env.lir.symRef(Op.REG, typeNode.type, dstSym, ImList.Empty);
		LirNode setExpr = env.lir.operator(Op.SET, typeNode.type, nn, node, ImList.Empty);
		return setExpr;
	}

	
	LirNode div(LirNode kid,LirNode r,BiLink p){
		LirNode newNode = createNewSetExp(kid,r);
		
		if(!containLoad(newNode)){
			return newNode;
		}
		
		LirNode rhs = newNode.kid(1);
		
		if(!(rhs.opCode==Op.ADD || rhs.opCode==Op.SUB ||
				rhs.opCode==Op.MUL || rhs.opCode==Op.DIVS ||
				rhs.opCode==Op.DIVU)){
			return newNode;
		}

		for(int i=0;i<rhs.nKids();i++){
			LirNode kidKid = rhs.kid(i);
			if(!containLoad(kidKid)){
				continue;
			}
			LirNode new_node = div(kidKid,rhs,p);
			p.addBefore(new_node);
			rhs.setKid(i, new_node.kid(0));
		}
		
		return newNode;
	}

	
	private void aliasAnalyze() {
		for (BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()) {
			BasicBlk v = (BasicBlk) p.elem();
			for (BiLink pp = v.instrList().first(); !pp.atEnd(); pp = pp.next()) {
				LirNode node = (LirNode) pp.elem();
				if (notAmbitiousLoad(node)) {
					LirNode addr = getAddress(node.kid(1));
					addresses.put(node.kid(0), addr);
					
					if(node.kid(1).opCode!=Op.MEM){
						leftToNode.put(node.kid(0), node.makeCopy(env.lir));
					}
					continue;
				}
			}
		}
	}
	
	
	/**
	 * If node is not ambitious load instrument,then return true. 
	 * @param node
	 * @return
	 */
	boolean notAmbitiousLoad(LirNode node) {
		if (node.opCode != Op.SET || node.kid(0).opCode != Op.REG) {
			return false;
		} else {
			LirNode addr = getAddress(node.kid(1));
			if (addr != null
					&& (addr.opCode == Op.FRAME || addr.opCode == Op.STATIC)) {
				return true;
			} else {
				return false;
			}
		}
	}

	
	void localCodeMotion(BasicBlk blk,LirNode exp,HashMap addrToInstr,BiLink pp){
		

		boolean up = false;
		boolean valid = false;
		boolean replace = false;
		
		LirNode predNode = (LirNode)addrToInstr.get(address);
		LirNode dif = null;
		LirNode defNode = null;

		valid = false;
		
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode node = (LirNode)p.elem();
			if(!valid){
				if(node.equals(expr)){
					valid = true;
				}
			}else{
				if(isDef(node) || isStore(node) || isAmb(node)){
					defNode = node.makeCopy(env.lir);
					break;
				}else if(isLoad(node)){
					LirNode addr = getAddress(node.kid(1));
					if(address.equals(addr)){
						predNode = node.makeCopy(env.lir);
						if(node.kid(1).equals(expr.kid(1))){
							replace=true;
						}
						break;
					}else{
						dif = node.makeCopy(env.lir);
					}
				}
			}
		}

		if(predNode==null && nSameAddr[blk.id]){
			for(BiLink qq=blk.predList().first();!qq.atEnd();qq=qq.next()){
				BasicBlk pred = (BasicBlk)qq.elem();
				if(xpUpSafe[pred.id]){
					up = true;
					break;
				}
			}
		}else if(predNode!=null && dif==null){
			predNode=null;
		}

		valid = false;
		
		// Start code motion.
		
		
		if(predNode==null){
			if(dif!=null && up){
				if(defNode==null){
					for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
						LirNode node = (LirNode)p.elem();
						if(node.equals(dif)){
							p.addBefore(expr);
							pp.unlink();
							break;
						}
					}
				}else{
					for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
						LirNode node = (LirNode)p.elem();
						if(!valid){
							if(node.equals(defNode)){
								valid = true;
							}
						}else{
							if(node.equals(dif)){
								p.addBefore(expr);
								pp.unlink();
								break;
							}
						}
					}
				}
			}
		}else{
			
			boolean valid2 = true;

			if(defNode!=null){
				valid2 = false;
			}

			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				if(!valid || !valid2){
					if(node.equals(defNode)){
						valid2 = true;
					}else if(node.equals(predNode)){
						valid = true;
					}
				}else{
					if(node.equals(expr)){
						if(replace){
							exp.setKid(1, predNode.kid(0));
						}
						break;
					}else if(dif.equals(node)){
						p.addBefore(expr);
						pp.unlink();
						break;
					}else if(isDef(node)){
						break;
					}
				}
			}
		}

		if(addrToInstr.containsKey(address)){
			addrToInstr.remove(address);
		}
		addrToInstr.put(address, exp.makeCopy(env.lir));
	}
	
	

	/**
	 * Insert new expressions and replace.
	 * 
	 */
	void globalCodeMotion() {
		HashMap blkToins = new HashMap();
		Vector insertExp = new Vector();

		// insert expressions
		insertExpr(blkToins, insertExp);

		if (checkInsOfPhi) {

			insertPhi(blkToins);
			
			rename(blkToins);

		}

		replace(blkToins, insertExp);
		
	}
	
	
	private void replace(HashMap blkToins, Vector insertExp) {
		
		HashMap replaced = new HashMap();
		ArrayList replacedBlks = new ArrayList();
		BasicBlk[] bVecInOrderOfRPost = dfst.blkVectorByRPost();
		
		BasicBlk insedBlk = null;
		LirNode inserted = null;
		
		for (int i = 1; i < bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];

			if (!Replace[blk.id]) {
				continue;
			}
			
			insedBlk = (BasicBlk)repToIns.get(blk);
			
			if(replacedBlks.size()>0){
				for(int j=0;j<replacedBlks.size();j++){
					BasicBlk v = (BasicBlk)replacedBlks.get(j);
					if(v!=null && dom.dominates(insedBlk,v)){
						insedBlk = v;
						inserted = (LirNode)replaced.get(insedBlk);
					}
				}
			}
			
			if(inserted==null && blkToins.containsKey(insedBlk)){
				inserted = (LirNode)blkToins.get(insedBlk);
			}

			boolean val = false;
			
			for (BiLink pp = blk.instrList().first(); !pp.atEnd(); pp = pp.next()) {
				LirNode node = (LirNode) pp.elem();

				if(isStore(node) || isAmb(node) || isDef(node)){
					val = false;
					break;
				}
				
				if (insertExp.contains(node) || !isLoad(node)) {
					continue;
				}

				if(sameNode(node)){
					val = true;
					node.setKid(1, inserted.kid(0).makeCopy(env.lir));
					inserted = node.makeCopy(env.lir);
				}
			}
			
			if(val){
				replacedBlks.add(blk);
				replaced.put(blk, inserted);
			}
			
			inserted = null;

		}
	}
	
	
	private void insert(LirNode newnode,BasicBlk blk){
		if(isSame[blk.id]){
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				if(sameNode(node)){
					p.addBefore(newnode);
					break;
				}
			}
		}else if(xSameAddr[blk.id]){
			for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
				LirNode node = (LirNode)p.elem();
				if(isDef(node) || isStore(node) || isAmb(node) || 
						isLoad(node) && sameAddress(node,expr)){
					p.addAfter(newnode);
					break;
				}
			}
		}else if(npUpSafe[blk.id]){
			if(isDef[blk.id] || isStore[blk.id] || isAmb[blk.id]){
				if(xuSafe[blk.id]){
					for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
						LirNode node = (LirNode)p.elem();
						if(isDef(node) || isStore(node) || isAmb(node)){
							p.addAfter(newnode);
							break;
						}else if(isLoad(node) && sameAddress(node,expr)){
							p.addAfter(newnode);
							break;
						}
					}
				}else{
					blk.instrList().last().addBefore(newnode);
				}
			}else if(!transp_addr[blk.id]){
				for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
					LirNode node = (LirNode)p.elem();
					if(node.opCode!=Op.PHI && node.opCode!=Op.PROLOGUE){
						p.addBefore(newnode);
						break;
					}
				}
			}else{
				blk.instrList().last().addBefore(newnode);
			}
		}else{
			blk.instrList().last().addBefore(newnode);
		}
	}
	
	
	/**
	 * Insert expressions.
	 **/
	void insertExpr(HashMap blkToIns,Vector insertExp) {

		boolean first = true;
		// Create insert instrument.
		LirNode tempExp = expr.makeCopy(env.lir);
		Symbol dstSym = null;
		LirNode nn = null;
		LirNode newNode = null;
		LirNode newRight = null;

		for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();

			if(!Insert[blk.id]){
				continue;
			}

			dstSym = sstab.newSsaSymbol(GLIA, tempExp.type);
			nn = env.lir.symRef(Op.REG, dstSym.type, dstSym, ImList.Empty);
			
			if(first){
				newNode = env.lir.operator(Op.SET, tempExp.type, nn, tempExp,ImList.Empty);
				preTmp = newNode.kid(0).makeCopy(env.lir);
				first = false;
			}else{
				newNode = newNode.makeCopy(env.lir);
				newNode.setKid(0, nn);
			}
			
			newRight = createRightNode(expr.kid(1).makeCopy(env.lir),blk);
			newNode.setKid(1, newRight);

			// Insert new expression.
			insert(newNode,blk);
			
			LirNode copyNode = newNode.makeCopy(env.lir);
			blkToIns.put(blk, copyNode);
			insertedInstrs.add(copyNode.kid(1));
			insertExp.add(copyNode);
		}
	}
	

	void insertPhi(HashMap blkToins) {
		for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {

			BasicBlk blk = (BasicBlk) p.elem();

			if (!Phi[blk.id]) {
				continue;
			}

			LirNode phi = createPhi(blk, expr);
			LirNode node = phi.makeCopy(env.lir);
			blk.instrList().addFirst(node);
			blkToins.put(blk, node);
			
		}
	}

	
	private LirNode createPhi(BasicBlk blk, LirNode e) {
		// Make a new phi instruction
		Symbol sym = sstab.newSsaSymbol(tmpSymName, e.type);
		return util.makePhiInst(sym, blk);
	}

	
	private boolean rename(BasicBlk blk,LirNode phi,HashMap blkToins){
		for (BiLink q = blk.instrList().first(); !q.atEnd(); q = q.next()) {
			LirNode node = (LirNode) q.elem();

			if (node.equals(phi)) {
				for(int i=1;i<node.nKids();i++){
					Label label = ((LirLabelRef) node.kid(i).kid(1)).label;
					BasicBlk predBlk = label.basicBlk();
					BasicBlk insertedBlk = (BasicBlk)renameBlkTable.get(predBlk);
					LirNode insed = (LirNode) blkToins.get(insertedBlk);
					node.kid(i).setKid(0,insed.kid(0).makeCopy(env.lir));
				}
			}
		}

		// renew phi congruence class
		// Begin
		Vector newCongruenceClass = new Vector();
		// End
		newCongruenceClass.add((LirSymRef) phi.kid(0));
		for (int i = 1; i < phi.nKids(); i++) {
			LirNode arg = phi.kid(i);
			newCongruenceClass.add((LirSymRef) arg.kid(0));
		}

		int i = 0;
		while (i < congruenceClassList.size()) {
			boolean find = false;
			// Begin
			Vector congruenceClass = (Vector) congruenceClassList.get(i);
			// End
			// Begin

			for (int iNCC = 0; iNCC < newCongruenceClass.size(); iNCC++) {
				LirNode phiVar = (LirNode) newCongruenceClass.get(iNCC);
				for (int iCC = 0; iCC < congruenceClass.size(); iCC++) {
					LirNode var = (LirNode) congruenceClass.get(iCC);
					if (phiVar.equals(var)) {
						for (int iCC2 = 0; iCC2 < congruenceClass.size(); iCC2++) {
							LirNode node = (LirNode) congruenceClass.get(iCC2);
							if (!newCongruenceClass.contains(node)) {
								newCongruenceClass.add(node);
							}
						}
						congruenceClassList.remove(congruenceClass);
						find = true;
						break;
					}
					if (find) {
						break;
					}
				}
			}
			// End
			if (!find) {
				i++;
			}
		}

		congruenceClassList.add(newCongruenceClass);
		
		return true;
	}
	
	
	private void rename(HashMap blkToins){
		ArrayList lazyRename = new ArrayList();
		for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();

			if (!Phi[blk.id]) {
				continue;
			}
			
			LirNode phi_fake = (LirNode) blkToins.get(blk);
			
			if(!rename(blk,phi_fake,blkToins)){
				lazyRename.add(blk);
			}
		}
		
		for(int i=0;i<lazyRename.size();i++){
			BasicBlk blk = (BasicBlk)lazyRename.get(i);
			LirNode phi = (LirNode)blkToins.get(blk);
			rename(blk,phi,blkToins);
		}
	}
	
	
	/**
	 * If return true,execute global code motion.
	 * Otherwise execute local code motion.
	 * @param blk
	 */
	boolean validOfGCM(){
		int replace = 0;
		int phi = 0;
		int insert = 0;
		int count = 0;
		
		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
			BasicBlk blk = (BasicBlk)p.elem();

			if(Replace[blk.id]){
				replace++;
				if(Insert[blk.id]){
					count++;
					insert++;
				}else if(Phi[blk.id]){
					count++;
					phi++;
				}
			}else if(Insert[blk.id]){
				if(repToIns.containsValue(blk) || renameBlkTable.containsValue(blk)){
					insert++;
				}else{
					// Delete unnecessary insert.
					Insert[blk.id] = false;
				}
			}else if(Phi[blk.id]){
				if(repToIns.containsValue(blk) || renameBlkTable.containsValue(blk)){
					phi++;
				}else{
					// Delete unnecessary phi insert.
					Phi[blk.id] = false;
				}
			}
		}
		
		if(replace>0 && replace > count || phi > 0){
			return true;
		}
		
		return false;
		
	}
	
	
	void dividExp(){
		BasicBlk[] bVecInOrderOfRPost = dfst.blkVectorByRPost();
		for (int i = 1; i < bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				
				if(!containLoad(node)){
					continue;
				}

				LirNode rhs = node.kid(1);
				if(!(rhs.opCode==Op.ADD || rhs.opCode==Op.SUB ||
						rhs.opCode==Op.MUL || rhs.opCode==Op.DIVS ||
						rhs.opCode==Op.DIVU)){
					continue;
				}

				for(int j=0;j<rhs.nKids();j++){
					LirNode kid = rhs.kid(j);
					if(!containLoad(kid)){
						continue;
					}
					LirNode newNode = div(kid,rhs,p);
					p.addBefore(newNode);
					rhs.setKid(j, newNode.kid(0));
				}
			}
		}
	}
	
	
	/**
	 * Do GLIA.
	 * 
	 * @param func
	 *            The current function
	 * @param args
	 *            The list of options
	 **/
	public boolean doIt(Function func, ImList args) {
		f = func;
		util = new Util(env, f);
		
		env.println("****************** doing GLIA to " + f.symbol.name,
				SsaEnvironment.MinThr);
				

		util = new Util(env, f);
		expr = null;
		address = null;
		HashMap addrToInstr;
		insertedInstrs = new Vector();
		addresses = new HashMap();
		vars = new Vector();
		targetPcc = new Vector();
		renameBlkTable = new HashMap();
		leftToNode = new HashMap();
		
		(new EdgeSplit(env)).doIt(f, null);

		dfst = (DFST) f.require(DFST.analyzer);
		dom = (Dominators) f.require(Dominators.analyzer);
		df = (DominanceFrontiers) f.require(DominanceFrontiers.analyzer);

		dividExp();
		aliasAnalyze();

		// make phi congruence classes
		makeCongruenceClassList();

		BasicBlk[] bVecInOrderOfRPost = dfst.blkVectorByRPost();

		for (int i = 1; i < bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			
			addrToInstr = new HashMap();

			for (BiLink pp = blk.instrList().first(); !pp.atEnd(); pp = pp.next()) {
				LirNode node = (LirNode) pp.elem();

				// Check ambitiousness and remove not load instruction.
				if (node.opCode == Op.CALL) {
					LirNode arguments = node.kid(1);
					for(int j=0;j<arguments.nKids();j++){
						LirNode arg = arguments.kid(j);
						if (addresses.containsKey(arg)) {
							LirNode addr = (LirNode) addresses.get(arg);
							if (addrToInstr.containsKey(addr)) {
								addrToInstr.remove(addr);
							}
						}
					}
					continue;
				}
				
				if(isStore(node)){
					LirNode addr = getAddress(node.kid(0));
					if (addrToInstr.containsKey(addr)) {
						addrToInstr.remove(addr);
					}
					continue;
				}
				
				if (!isLoad(node) || insertedInstrs.contains(node.kid(1))) {
					continue;
				}

				expr = node.makeCopy(env.lir);
				address = getAddress(expr.kid(1));
				address = address.makeCopy(env.lir);
				
				if(address.opCode!=Op.STATIC && address.opCode!=Op.FRAME){
					continue;
				}
					
				if (isAmb(expr)) {
					addrToInstr.clear();
					addrToInstr.put(address, expr);
					continue;
				}

				checkInsOfPhi = false;
				repToIns = new HashMap();
				vars.clear();
				vars = detectVar(expr.kid(1), vars);
				targetPcc.clear();
				targetPcc = belongClass(vars);

				// compute local propaties
				compLocalProperty();

				// compute global propaties
				compGlobalProperty();

				if(validOfGCM()){
					globalCodeMotion();
					continue;
				}

				localCodeMotion(blk,node,addrToInstr,pp);

			}
		}

		f.flowGraph().touch();
		return (true);
	}

	/**
	 * @param data
	 *            Data to be processes.
	 * @param args
	 *            List of optional arguments.
	 **/
	public boolean doIt(Data data, ImList args) {
		return true;
	}

	/**
	 * Return the name of this optimizer.
	 **/
	public String name() {
		return "GLIA";
	}

	/**
	 * Return brief descriptions of this optimizer.
	 **/
	public String subject() {
		return "GLIA";
	}

}
