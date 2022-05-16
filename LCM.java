/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import java.util.Arrays;
import java.util.Vector;
// Begin
import java.util.Iterator;
// End

import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.Type;
import coins.backend.ana.DominanceFrontiers;
import coins.backend.ana.Dominators;
import coins.backend.cfg.BasicBlk;
import coins.backend.cfg.FlowGraph;
import coins.backend.lir.LirFactory;
import coins.backend.lir.LirLabelRef;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.sym.Label;
import coins.backend.sym.Symbol;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;
/*  2008.12.9
import coins.yo.Option;
import coins.yo.PrintUtil;
*/

/**
 * Lazy Code Motion
 **/
public class LCM implements LocalTransformer {

  /** The environment of the SSA module **/
	SsaEnvironment env;

  /** The current SSA symbol table **/
	SsaSymTab sstab;

  /** The current function **/
	Function func;

  /** The target expression **/
	LirNode expr;

	LirNode preTmp;

// Begin
//	Vector<Vector> congruenceClassList;
  /** The Phi Congruence Class list **/
	Vector congruenceClassList;
// End

// Begin	
//	Vector<BasicBlk> phiInsertedBlkList;
	Vector phiInsertedBlkList;
// End

/** Entry computation **/
	boolean[] nComp;

/** Exit computation **/
	boolean[] xComp;

/** Transparency **/
	boolean[] transp;

  /** Entry down-safety **/
	boolean[] ndSafe;

  /** Exit down-safety **/
	boolean[] xdSafe;

  /** Entry up-safety **/
	boolean[] nuSafe;

  /** Exit up-safety **/
	boolean[] xuSafe;

  /** Entry earliestness **/
	boolean[] nEarliest;

  /** Exit earliestness **/
	boolean[] xEarliest;

  /** Entry delayability **/
	boolean[] nDelayed;

  /** Exit delayability **/
	boolean[] xDelayed;

  /** Entry Latestness **/
	boolean[] nLatest;

  /** Exit Latestness **/
	boolean[] xLatest;

  /** Entry liveness **/
	boolean[] nLive;

  /** Exit liveness **/
	boolean[] xLive;

  /** Entry insertion **/
	boolean[] nInsert;

  /** Exit insertion **/
	boolean[] xInsert;

  /** Entry replacement **/
	boolean[] nReplace;

  /** Exit insertion **/
	boolean[] xReplace;

  /** The current dominator **/
	Dominators dom;

  /** The current dominance frotiers **/
	DominanceFrontiers df;

	int preNum;
	
// Begin
//	Vector<LirNode> exprList;
	Vector exprList;
// End

  /** The ssa option number **/
	int optNum;

/**
 * Constructor.
 * @param env The environment of the SSA module
 * @param sstab The current symbol table on SSA form
 **/
	public LCM(SsaEnvironment env, SsaSymTab sstab) {
		this.env = env;
		this.sstab = sstab;
		preNum = 0;
		optNum=0;
	}

  /**
   * Set the value of the ssa option number
   * @param n The ssa option number
   **/
  public void setOptNum(int n) {
    optNum=n;
  }

  /**
   * Return the value of the ssa option number
   **/
  public int getOptNum() {
    return optNum;
  }

/**
 * Make a phi congruence class list.
 **/
	void makeCongruenceClassList() {

// Begin
//		congruenceClassList = new Vector<Vector>();
		congruenceClassList = new Vector();
// End

		for (BiLink p = func.flowGraph().basicBlkList.first(); !p.atEnd(); p = p
				.next()) {
			BasicBlk blk = (BasicBlk) p.elem();

			for (BiLink q = blk.instrList().first(); !q.atEnd(); q = q.next()) {
				LirNode instr = (LirNode) q.elem();

				if (instr.opCode == Op.PHI) {

					// make var set in phi
// Begin
//					Vector<LirNode> newCongruenceClass = new Vector<LirNode>();
					Vector newCongruenceClass = new Vector();
// End
					newCongruenceClass.add((LirSymRef) instr.kid(0));
					for (int i = 1; i < instr.nKids(); i++) {
						LirNode arg = instr.kid(i);
						newCongruenceClass.add((LirSymRef) arg.kid(0));
					}

					int i=0;
					while(i<congruenceClassList.size()){
						boolean find=false;
// Begin
//						Vector<LirNode> congruenceClass=congruenceClassList.get(i);
						Vector congruenceClass=(Vector)congruenceClassList.get(i);
// End

						
// Begin
//						for (LirNode phiVar : newCongruenceClass) {
//							for (LirNode var : congruenceClass) {
//								
//								if (phiVar.equals(var)) {
//									for(LirNode node:congruenceClass){
//										if(!newCongruenceClass.contains(node)){
//											newCongruenceClass.add(node);
//										}
//									}
//									congruenceClassList.remove(congruenceClass);
//									find=true;
//									break;
//								}
//							}
//							if(find){
//								break;
//							}
//						}
						for(int iNCC=0;iNCC<newCongruenceClass.size();iNCC++) {
						  LirNode phiVar=(LirNode)newCongruenceClass.get(iNCC);
						  for(int iCC=0;iCC<congruenceClass.size();iCC++) {
						    LirNode var=(LirNode)congruenceClass.get(iCC);
						    if(phiVar.equals(var)) {
						      for(int iCC2=0;iCC2<congruenceClass.size();iCC2++) {
							LirNode node=(LirNode)congruenceClass.get(iCC2);
							if(!newCongruenceClass.contains(node)) {
							  newCongruenceClass.add(node);
							}
						      }
						      congruenceClassList.remove(congruenceClass);
						      find=true;
						      break;
						    }
						    if(find) {
						      break;
						    }
						  }
						}
// End
						if(!find){
							i++;
						}
					}
					
					congruenceClassList.add(newCongruenceClass);
				}
			}
		}
	}

/**
 * Check whether the specified node is pure.
 * @param node The expression.
 **/
	boolean isPure(LirNode node) {
		boolean isPure = (Op.NEG <= node.opCode) && (node.opCode <= Op.PURE);
		return isPure;
	}

// Begin
//	Vector<LirNode> belongClass(LirNode node) {
//		for (Vector<LirNode> set : congruenceClassList) {
//			for (LirNode nodeInSet : set) {
//				if (node.equals(nodeInSet)) {
//					return set;
//				}
//			}
//		}
//		Vector<LirNode> set = new Vector<LirNode>();
//		set.add(node);
//		return set;
//	}
/**
 * Return the pcc which the node belongs to.
 * @param node The specified expression.
 **/
	Vector belongClass(LirNode node) {
	  for(int iCCL=0;iCCL<congruenceClassList.size();iCCL++) {
	    Vector set=(Vector)congruenceClassList.get(iCCL);
	    for(int iS=0;iS<set.size();iS++) {
	      LirNode nodeInSet=(LirNode)set.get(iS);
	      if(node.equals(nodeInSet)) {
		return set;
	      }
	    }
	  }
	  Vector set = new Vector();
	  set.add(node);
	  return set;
	}
// End

/**
 * Check whether two expressions belong to the same pcc.
 * @param expr0 The specified expression 1
 * @param expr1 The specified expression 2
 **/
	private boolean sames(LirNode expr0, LirNode expr1) {
		if (isPure(expr0)) {
			if (expr0.opCode != expr1.opCode ||
					expr0.type != expr1.type){
				return false;
			}

			LirNode op00 = expr0.kid(0);
			LirNode op10 = expr1.kid(0);
			if (belongClass(op00).equals(
					belongClass(op10))) {
				if (expr0.nKids() == 1) {
					return true;
				}
				LirNode op01 = expr0.kid(1);
				LirNode op11 = expr1.kid(1);
				if (belongClass(op01).equals(
						belongClass(op11))) {
					return true;
				}
			}
		} else if (expr0 instanceof LirSymRef) {
// Begin
//			Vector<LirNode> class0=belongClass(expr0);
//			Vector<LirNode> class1=belongClass(expr1);
			Vector class0=belongClass(expr0);
			Vector class1=belongClass(expr1);
// End
			/*
			if(((LirSymRef)expr0).symbol.name.equals("k.56%_8")){
				if(((LirSymRef)expr1).symbol.name.equals("k.56%_7")){
					System.out.println("class0\n"+class0);
					System.out.println("class1\n"+class1);
				}
			}*/
			if (class0.equals(class1)){
				return true;
			}
		} else {
			System.out.println(expr0);
			(new Exception()).printStackTrace();
			System.exit(1);
		}
		return false;
	}

/**
 * Divide each self changing expression into two expressions with a temporary var.
 **/
	void divSelfchange() {
		FlowGraph fg = func.flowGraph();
		LirFactory lir = env.lir;
		for (BiLink p = fg.basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();
			for (BiLink q = blk.instrList().first(); !q.atEnd(); q = q.next()) {
				LirNode node = (LirNode) q.elem();
				if (node.opCode == Op.SET) {
					if (node.kid(0).opCode != Op.MEM) {
						LirSymRef left = (LirSymRef) node.kid(0);
						LirNode right = node.kid(1);
						if (isPure(right)) {
							for (int i = 0; i < right.nKids(); i++) {
								LirNode operand = right.kid(i);
								// if (left.equals(operand)) {
								if (sames(left, operand)) {
									Symbol tmpSym = sstab.newSsaSymbol(
											"_divinc", left.type);

									LirNode tnode1 = lir.symRef(tmpSym);
									LirNode tnode2 = lir.symRef(tmpSym);
									LirNode inode = lir.symRef(left.symbol);
									LirNode copy = lir.node(Op.SET, node.type,
											inode, tnode2);

									node.setKid(0, tnode1);
									q.addAfter(copy);

									break;
								}
							}
						}
					}
				}
			}
		}
	}

// Begin
//	Vector<LirNode> collectExpr() {
/**
 * Collect expressions which occurs in the right handside of an assignment.
 **/
	Vector collectExpr() {
// End
// Begin
//		Vector<LirNode> exprList = new Vector<LirNode>();
		Vector exprList = new Vector();
// End
		FlowGraph fg = func.flowGraph();

		for (BiLink p = fg.basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();

			for (BiLink q = blk.instrList().first(); !q.atEnd(); q = q.next()) {
				LirNode instr = (LirNode) q.elem();

				if (instr.opCode == Op.SET) {
					LirNode right = instr.kid(1);

					if (isPure(right)) {
						boolean found = false;
// Begin
//						for (LirNode node : exprList) {
//							if (sames(right, node)) {
//								found = true;
//								break;
//							}
//						}
// End
						for(int iEL=0;iEL<exprList.size();iEL++) {
						  LirNode node=(LirNode)exprList.get(iEL);
						  if(sames(right, node)) {
						    found = true;
						    break;
						  }
						}
						if (!found) {
							exprList.add(right.makeCopy(env.lir));
						}
					}
				}
			}
		}

		return exprList;
	}

/**
 * Check whether a specified statement has modifications of "expr".
 * @param instr A statement.
 **/
	boolean isChangeInstr(LirNode instr) {
		if (instr.opCode == Op.SET) {
			LirNode left = instr.kid(0);
			if (left.opCode != Op.MEM) {
				for (int i = 0; i < expr.nKids(); i++) {
					LirNode operand = expr.kid(i);
					if (sames(left, operand)) {
						return true;
					}
				}
			}
		} else if (instr.opCode == Op.CALL) {
			LirNode rvalueList = instr.kid(2);
			for (int i = 0; i < rvalueList.nKids(); i++) {
				LirNode rvalue = rvalueList.kid(i);
				if(rvalue instanceof LirSymRef){
				
					for (int j = 0; j < expr.nKids(); j++) {
						LirNode operand = expr.kid(j);
						if (sames(rvalue, operand)) {
							return true;
						}
					}
				}
			}
		} else {
			return false;
		}
		return false;
	}

/**
 * Check whether the specified basic block has an entry computation.
 * @param blk A basic block.
 **/
	boolean isNComp(BasicBlk blk) {
		for (BiLink p = blk.instrList().first(); !p.atEnd(); p = p.next()) {
			LirNode instr = (LirNode) p.elem();
			if (isChangeInstr(instr)) {
				return false;
			} else if (instr.opCode == Op.SET) {
				LirNode right = instr.kid(1);
				if (isPure(right)) {
					if (sames(right, expr)) {
						return true;
					}
				}
			}
		}
		return false;
	}

/**
 * Check wheter the specified block has an exit computation.
 * @param blk A basic block.
 **/	boolean isXComp(BasicBlk blk) {
		boolean foundExpr = false;
		for (BiLink p = blk.instrList().last(); !p.atEnd(); p = p.prev()) {
			LirNode instr = (LirNode) p.elem();

			if (isChangeInstr(instr)) {
				if (foundExpr) {
					return true;
				} else {
					return false;
				}
			} else if (instr.opCode == Op.SET) {
				LirNode right = instr.kid(1);
				if (isPure(right)) {
					if (sames(right, expr)) {
						foundExpr = true;
					}
				}
			}
		}
		return false;
	}

/**
 * Check whether the specified block has transparency.
 * @param blk A basic block.
 **/
	boolean isTransp(BasicBlk blk) {
		for (BiLink p = blk.instrList().last(); !p.atEnd(); p = p.prev()) {
			LirNode instr = (LirNode) p.elem();
			if (isChangeInstr(instr)) {
				return false;
			}
		}
		return true;
	}

/**
 * Compute local properties.
 **/
	void compLocalProperty() {
		int idBound = func.flowGraph().idBound();
		nComp = new boolean[idBound];
		xComp = new boolean[idBound];
		transp = new boolean[idBound];
		for (BiLink p = func.flowGraph().basicBlkList.first(); !p.atEnd(); p = p
				.next()) {
			BasicBlk blk = (BasicBlk) p.elem();

			// compute NComp
			nComp[blk.id] = isNComp(blk);

			// compute XComp
			xComp[blk.id] = isXComp(blk);

			// compute Transp
			transp[blk.id] = isTransp(blk);
		}
	}

/**
 * Compute down-safety.
 **/
	void compDSafe() {
		boolean change = true;
		
		while (change) {
			change = false;
			for (BiLink p = func.flowGraph().basicBlkList.last(); !p.atEnd(); p = p
					.prev()) {
				BasicBlk blk = (BasicBlk) p.elem();

				// comp XdSafe
				boolean x = true;
				if (xComp[blk.id]) {
					x = true;
				} else {
					if (blk == func.flowGraph().exitBlk()) {
						x = false;
					} else {
						for (BiLink q = blk.succList().first(); !q.atEnd(); q = q
								.next()) {
							BasicBlk succ = (BasicBlk) q.elem();
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

				// comp NdSafe
				boolean n = nComp[blk.id] || (transp[blk.id] && xdSafe[blk.id]);
				if (n != ndSafe[blk.id]) {
					ndSafe[blk.id] = n;
					change = true;
				}
			}
		}
	}

/**
 * Compute up-safety.
 **/
	void compUSafe() {
		boolean change = true;
		while (change) {
			change = false;
			for (BiLink p = func.flowGraph().basicBlkList.first(); !p.atEnd(); p = p
					.next()) {
				BasicBlk blk = (BasicBlk) p.elem();

				// comp NuSafe
				boolean n = true;
				if (blk == func.flowGraph().entryBlk()) {
					n = false;
				} else {
					for (BiLink q = blk.predList().first(); !q.atEnd(); q = q
							.next()) {
						BasicBlk pred = (BasicBlk) q.elem();
						if (!(xComp[pred.id] || xuSafe[pred.id])) {
							n = false;
							break;
						}
					}
				}
				if (n != nuSafe[blk.id]) {
					nuSafe[blk.id] = n;
					change = true;
				}

				// comp XuSafe
				boolean x = transp[blk.id] && (nComp[blk.id] || nuSafe[blk.id]);
				if (x != xuSafe[blk.id]) {
					xuSafe[blk.id] = x;
					change = true;
				}
			}
		}
	}

/**
 * Compute earliestness.
 **/
	void compEarliest() {
		boolean change = true;
		while (change) {
			change = false;

			for (BiLink p = func.flowGraph().basicBlkList.first(); !p.atEnd(); p = p
					.next()) {
				BasicBlk blk = (BasicBlk) p.elem();

				boolean n = true;
				if (!ndSafe[blk.id]) {
					n = false;
				} else {
					for (BiLink q = blk.predList().first(); !q.atEnd(); q = q
							.next()) {
						BasicBlk pred = (BasicBlk) q.elem();
						if (xuSafe[pred.id] || xdSafe[pred.id]) {
							n = false;
							break;
						}
					}
					if (blk == func.flowGraph().entryBlk()) {
						n = true;
					}
				}
				if (nEarliest[blk.id] != n) {
					nEarliest[blk.id] = n;
					change = true;
				}

				xEarliest[blk.id] = xdSafe[blk.id] && !transp[blk.id];
			}
		}
	}

/**
 * Compute delayability.
 **/
	void compDelayed() {
		boolean change = true;
		while (change) {
			change = false;
			for (BiLink p = func.flowGraph().basicBlkList.first(); !p.atEnd(); p = p
					.next()) {
				BasicBlk blk = (BasicBlk) p.elem();

				// comp NDelayed
				boolean n = true;
				if (nEarliest[blk.id]) {
					n = true;
				} else {
					if (blk == func.flowGraph().entryBlk()) {
						n = false;
					} else {
						for (BiLink q = blk.predList().first(); !q.atEnd(); q = q
								.next()) {
							BasicBlk pred = (BasicBlk) q.elem();
							if (!(xDelayed[pred.id] && !xComp[pred.id])) {
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

				// comp XDelayed
				boolean x = xEarliest[blk.id]
						|| (nDelayed[blk.id] && !nComp[blk.id]);
				if (x != xDelayed[blk.id]) {
					xDelayed[blk.id] = x;
					change = true;
				}
			}
		}
	}

/**
 * Compute latestness.
 **/
	void compLatest() {
		boolean change = true;
		while (change) {
			change = false;
			for (BiLink p = func.flowGraph().basicBlkList.last(); !p.atEnd(); p = p
					.prev()) {
				BasicBlk blk = (BasicBlk) p.elem();

				// comp XLatest
				boolean x = false;
				if (!xDelayed[blk.id]) {
					x = false;
				} else {
					if (xComp[blk.id]) {
						x = true;
					} else {
						for (BiLink q = blk.succList().first(); !q.atEnd(); q = q
								.next()) {
							BasicBlk succ = (BasicBlk) q.elem();
							if (!nDelayed[succ.id]) {
								x = true;
								break;
							}
						}
					}
				}
				if (x != xLatest[blk.id]) {
					xLatest[blk.id] = x;
					change = true;
				}

				// comp NLatest
				boolean n = nDelayed[blk.id] && nComp[blk.id];
				if (n != nLatest[blk.id]) {
					nLatest[blk.id] = n;
					change = true;
				}
			}
		}
	}

/**
 * Compute liveness.
 **/
	void compLive() {
		boolean change = true;
		while (change) {
			change = false;
			for (BiLink p = func.flowGraph().basicBlkList.last(); !p.atEnd(); p = p
					.prev()) {
				BasicBlk blk = (BasicBlk) p.elem();

				// comp XLive
				boolean x = false;
				if (blk == func.flowGraph().exitBlk()) {
					x = false;
				} else {
					for (BiLink q = blk.succList().first(); !q.atEnd(); q = q
							.next()) {
						BasicBlk succ = (BasicBlk) q.elem();
						if ((nComp[succ.id] || nLive[succ.id])
								&& !nLatest[succ.id]) {
							x = true;
							break;
						}
					}
				}
				if (x != xLive[blk.id]) {
					xLive[blk.id] = x;
					change = true;
				}

				// comp NLive
				boolean n = (xComp[blk.id] || xLive[blk.id])
						&& !xLatest[blk.id];
				if (n != nLive[blk.id]) {
					nLive[blk.id] = n;
					change = true;
				}
			}
		}
	}

/**
 * Compute insertion points.
 **/
	void compInsert() {
		for (BiLink p = func.flowGraph().basicBlkList.first(); !p.atEnd(); p = p
				.next()) {
			BasicBlk blk = (BasicBlk) p.elem();
			nInsert[blk.id] = nLatest[blk.id] && nLive[blk.id];
			xInsert[blk.id] = xLatest[blk.id] && xLive[blk.id];
		}
	}

/**
 * Compute replacement points.
 **/
	void compReplace() {
		for (BiLink p = func.flowGraph().basicBlkList.first(); !p.atEnd(); p = p
				.next()) {
			BasicBlk blk = (BasicBlk) p.elem();
			nReplace[blk.id] = nComp[blk.id]
					&& (nInsert[blk.id] || !nLatest[blk.id]);
			xReplace[blk.id] = xComp[blk.id]
					&& (xInsert[blk.id] || !xLatest[blk.id]);
		}
	}

/**
 * Compute global properties.
 **/
	void compGlobalProperty() {
		int idBound = func.flowGraph().idBound();
		ndSafe = new boolean[idBound];
		xdSafe = new boolean[idBound];
		nuSafe = new boolean[idBound];
		xuSafe = new boolean[idBound];
		nEarliest = new boolean[idBound];
		xEarliest = new boolean[idBound];
		nDelayed = new boolean[idBound];
		xDelayed = new boolean[idBound];
		nLatest = new boolean[idBound];
		xLatest = new boolean[idBound];
		nLive = new boolean[idBound];
		xLive = new boolean[idBound];
		nInsert = new boolean[idBound];
		xInsert = new boolean[idBound];
		nReplace = new boolean[idBound];
		xReplace = new boolean[idBound];
		Arrays.fill(ndSafe, true);
		Arrays.fill(xdSafe, true);
		Arrays.fill(nuSafe, true);
		Arrays.fill(xuSafe, true);
		Arrays.fill(nEarliest, true);
		Arrays.fill(xEarliest, true);
		Arrays.fill(nDelayed, true);
		Arrays.fill(xDelayed, true);
		Arrays.fill(nLatest, false);
		Arrays.fill(xLatest, false);
		Arrays.fill(nLive, false);
		Arrays.fill(xLive, false);

		// comp dSafe
		compDSafe();

		// comp uSafe
		compUSafe();

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

		// comp replace
		compReplace();
	}

/**
 * Return the defined operand of the assignment instr.
 * @param instr The specified expression.
 * @param operand The operand.
 **/
	LirNode defOperand(LirNode instr, LirNode operand) {
		// System.out.println(instr);
		// System.out.println(operand+"\n");

		if (instr.opCode == Op.SET) {
			LirNode leftNode = instr.kid(0);

			if(leftNode instanceof LirSymRef){
				//System.out.println(operand+", "+leftNode+": "+sames(operand,leftNode));
				if (sames(operand, leftNode)) {
					return leftNode;
				}
			}
		} else if (instr.opCode == Op.PROLOGUE) {
			for (int j = 1; j < instr.nKids(); j++) {
				LirNode var = instr.kid(j);
				if (sames(operand, var)) {
					return var;
				}
			}

		} else if (instr.opCode == Op.CALL) {
			LirNode rvalueList = instr.kid(2);
			for (int j = 0; j < rvalueList.nKids(); j++) {
				LirNode var = rvalueList.kid(j);
				if (sames(operand, var)) {
					return var;
				}
			}
		} else if (instr.opCode == Op.PHI) {
			LirNode leftNode = instr.kid(0);

			if(leftNode instanceof LirSymRef){
				if (sames(operand, leftNode)) {
					return leftNode;
				}
			}
		}

		return null;
	}

/**
 * Make defOperand list.
 * @param blk The specified basic block
 * @param place The specified place
 **/
	LirNode[] defOperandList(BasicBlk blk, BiLink place) {
		LirNode[] defOperandList = new LirNode[expr.nKids()];
		for (int i = 0; i < expr.nKids(); i++) {
			LirNode operand = expr.kid(i);

			int opCode = operand.opCode;
			if ((opCode == Op.STATIC) || (opCode == Op.FRAME)
					|| (opCode == Op.INTCONST) || (opCode == Op.FLOATCONST)) {
				defOperandList[i] = operand;
			} else if (operand.opCode == Op.REG) {

				// search in blk
				for (BiLink p = place; !p.atEnd(); p = p.prev()) {
					LirNode instr = (LirNode) p.elem();
					LirNode defOperand = defOperand(instr, operand);
					if (defOperand != null) {
						defOperandList[i] = defOperand;
						break;
					}
				}

				// search dom of blk
				boolean found = false;
				for (BasicBlk b = blk;; b = dom.immDominator(b)) {
					try{
						for (BiLink p = b.instrList().last(); !p.atEnd(); p = p
								.prev()) {
							LirNode instr = (LirNode) p.elem();
							LirNode defOperand = defOperand(instr, operand);
							if (defOperand != null) {
								defOperandList[i] = defOperand;
								found = true;
								break;
							}
						}
					}catch(Exception e){
						//PrintUtil.printf(func);
						/*for(HashSet<LirNode> set:congruenceClassList){
							for(LirNode node:set){
								System.out.print(node+" ");
							}
							System.out.println();
						}*/
						System.out.println(expr);
						System.out.println(blk.id);
						System.out.println(i);
						System.exit(0);
					}
					if (found) {
						break;
					}
				}
			}
		}

		return defOperandList;
	}

/**
 * Insert expressions.
 **/
	void insertExpr() {
		LirFactory lir = env.lir;

		// insert dummy to entry blk
//		Symbol ssaLeftSym = sstab
//				.newSsaSymbol("LCM." + preNum + ".", expr.type);
		Symbol ssaLeftSym = sstab
				.newSsaSymbol("LCM" + optNum + "." + preNum + ".", expr.type);
		preTmp = lir.symRef(ssaLeftSym);
		
		LirNode val=null;
		char type=Type.toString(expr.type).charAt(0);
		if(type=='I'){
			val=lir.iconst(expr.type,0);
		}else if(type=='F'){
			val=lir.fconst(expr.type,0);
		}else{
			(new Exception()).printStackTrace();
			System.exit(0);
		}
		LirNode dummyExpr = lir.node(Op.SET, expr.type, preTmp, val);
		

		for (BiLink p = func.flowGraph().basicBlkList.first(); !p.atEnd(); p = p
				.next()) {

			BasicBlk blk = (BasicBlk) p.elem();

			if (nInsert[blk.id]) {
				LirNode[] defOperandList = defOperandList(blk, blk.instrList()
						.first());
				Symbol leftSym = sstab
						.newSsaSymbol(((LirSymRef) preTmp).symbol);
				LirNode leftNode = lir.symRef(leftSym);
				LirNode ssaExpr = null;
				if (expr.nKids() == 1) {
					ssaExpr = lir.node(expr.opCode, expr.type,
							defOperandList[0]);
				} else {
					ssaExpr = lir.node(expr.opCode, expr.type,
							defOperandList[0], defOperandList[1]);
				}
				LirNode setExpr = lir
						.node(Op.SET, expr.type, leftNode, ssaExpr);
				for (BiLink q = blk.instrList().first(); !q.atEnd(); q = q
						.next()) {
					LirNode instr = (LirNode) q.elem();
					if (instr.opCode != Op.PHI && instr.opCode!=Op.PROLOGUE) {
						q.addBefore(setExpr);
						break;
					}
				}
			}

			if (xInsert[blk.id]) {
				BiLink changeInstrPlace = null;
				for (BiLink q = blk.instrList().last(); !q.atEnd(); q = q
						.prev()) {
					LirNode instr = (LirNode) q.elem();
					if (isChangeInstr(instr)) {
						changeInstrPlace = q;
					}
				}

				LirNode[] defOperandList;
				if (changeInstrPlace == null) {
					defOperandList = defOperandList(blk, blk.instrList().last());
				} else {
					defOperandList = defOperandList(blk, changeInstrPlace);
				}
				Symbol leftSym = sstab
						.newSsaSymbol(((LirSymRef) preTmp).symbol);
				LirNode leftNode = lir.symRef(leftSym);
				LirNode ssaExpr = null;
				if (expr.nKids() == 1) {
					ssaExpr = lir.node(expr.opCode, expr.type,
							defOperandList[0]);
				} else {
					ssaExpr = lir.node(expr.opCode, expr.type,
							defOperandList[0], defOperandList[1]);
				}
				LirNode setExpr = lir
						.node(Op.SET, expr.type, leftNode, ssaExpr);

				if (changeInstrPlace == null) {
					blk.instrList().last().addBefore(setExpr);
				} else {
					changeInstrPlace.addAfter(setExpr);
				}
			}
		}
		func.flowGraph().entryBlk().instrList().first().addAfter(dummyExpr);
	}

/**
 * Print properties.
 **/
	void printProp() {
		System.out.println("\nProperty of: " + expr);
		for (BiLink p = func.flowGraph().basicBlkList.first(); !p.atEnd(); p = p
				.next()) {
			BasicBlk blk = (BasicBlk) p.elem();

			System.out.println("blk: " + blk.id);
			// System.out.println("Local Property: ");
			System.out.println("NComp: " + nComp[blk.id] + ", XComp: "
					+ xComp[blk.id] + ", Transp: " + transp[blk.id]);
			System.out.println("NDSafe: " + ndSafe[blk.id] + ", XDSafe: "
					+ xdSafe[blk.id] + ", NUSafe: " + nuSafe[blk.id]
					+ ", XUSafe: " + xuSafe[blk.id]);
			System.out.println("NEarlist: " + nEarliest[blk.id]
					+ ", XEarliest: " + xEarliest[blk.id] + ", NDelayed: "
					+ nDelayed[blk.id] + ", XDelayed: " + xDelayed[blk.id]
					+ ", NLatest: " + nLatest[blk.id] + ", XLatest: "
					+ xLatest[blk.id]);
			System.out.println("NLive: " + nLive[blk.id] + ", XLive: "
					+ xLive[blk.id]);
			System.out.println("NInsert: " + nInsert[blk.id] + ", XInsert: "
					+ xInsert[blk.id] + ", NReplace; " + nReplace[blk.id]
					+ ", XReplace: " + xReplace[blk.id]);
		}
	}

/**
 * Insert phi functions.
 **/
	void insertPhi() {
		FlowGraph fg = func.flowGraph();
		LirFactory lir = env.lir;

		LirNode[] inserted = new LirNode[fg.idBound()];
		LirNode[] work = new LirNode[fg.idBound()];

		LirNode dummyNode = lir.iconst(0, 0);

		for (BiLink p = fg.basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk x = (BasicBlk) p.elem();
			inserted[x.id] = dummyNode;
			work[x.id] = dummyNode;
		}

// Begin
//		Vector<BasicBlk> w = new Vector<BasicBlk>();
		Vector w = new Vector();
// End
		
		LirNode v=preTmp;

// Begin
//		Vector<BasicBlk> exprInsertedBlkList = new Vector<BasicBlk>();
		Vector exprInsertedBlkList = new Vector();
// End
		for (BiLink p = fg.basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();
			if (nInsert[blk.id] || xInsert[blk.id]) {
				exprInsertedBlkList.add(blk);
			}
		}

//
//		for (BasicBlk x : exprInsertedBlkList) {
//			w.add(x);
//			work[x.id] = v;
//		}
		for(int iEIBL=0;iEIBL<exprInsertedBlkList.size();iEIBL++) {
		  BasicBlk x=(BasicBlk)exprInsertedBlkList.get(iEIBL);
		  w.add(x);
		  work[x.id]=v;
		}
//
		
		Util util = new Util(env, func);
		Symbol vSym = ((LirSymRef) v).symbol;
		
// Begin
//		phiInsertedBlkList=new Vector<BasicBlk>();
		phiInsertedBlkList=new Vector();
// End
		
		while (!(w.size() == 0)) {
			BasicBlk x = (BasicBlk)w.remove(0);
			for (BiLink p = df.frontiers[x.id].first(); !p.atEnd(); p = p
					.next()) {
				BasicBlk y = (BasicBlk) p.elem();
				if (!(inserted[y.id].equals(v))) {
					LirNode phi = util.makePhiInst(vSym, y);

					Symbol ssaSym = sstab.newSsaSymbol(vSym);
					LirNode ssaNode = lir.symRef(ssaSym);
					phi.setKid(0, ssaNode);
					

					y.instrList().addFirst(phi);
					
					phiInsertedBlkList.add(y);

					inserted[y.id] = v;
					if (work[y.id] != v) {
						w.add(y);
						work[y.id] = v;
					}
				}
			}
		}
	}
	
/**
 * Rename arguments in phi functions.
 **/
	void rename(){
		LirFactory lir = env.lir;

// Begin
//		for (BasicBlk blk : phiInsertedBlkList) {
//			LirNode phi = (LirNode) blk.instrList().first().elem();
		for(int iPIBL=0;iPIBL<phiInsertedBlkList.size();iPIBL++) {
		  BasicBlk blk=(BasicBlk)phiInsertedBlkList.get(iPIBL);
		  LirNode phi = (LirNode) blk.instrList().first().elem();
// End
			//rename
			for (int i = 1; i < phi.nKids(); i++) {
				LirNode phiArg = phi.kid(i);
				Symbol phiArgSym = sstab.orgSym(((LirSymRef) phiArg.kid(0)).symbol);
				Label label = ((LirLabelRef) phiArg.kid(1)).label;

				BasicBlk domBlk = label.basicBlk();
				boolean find = false;
				while (!find) {
					for (BiLink q = domBlk.instrList().last(); !q.atEnd(); q = q
							.prev()) {
						LirNode instr = (LirNode) q.elem();
						if ((instr.opCode == Op.SET)
								|| (instr.opCode == Op.PHI)) {
							LirNode leftNode = instr.kid(0);

							if (leftNode instanceof LirSymRef) {
								Symbol leftSym = ((LirSymRef) leftNode).symbol;
								// if(sames(phiArg.kid(0),leftNode)){
								if (phiArgSym.equals(sstab.orgSym(leftSym))) {
									phiArg.setKid(0, leftNode.makeCopy(lir));
									find = true;
									break;
								}
							}
						}
					}
					domBlk = dom.immDominator(domBlk);
				}
			}
			
			//renew phi congruence class
// Begin
//			Vector<LirNode> newCongruenceClass = new Vector<LirNode>();
			Vector newCongruenceClass = new Vector();
// End
			newCongruenceClass.add((LirSymRef) phi.kid(0));
			for (int i = 1; i < phi.nKids(); i++) {
				LirNode arg = phi.kid(i);
				newCongruenceClass.add((LirSymRef) arg.kid(0));
			}
			
			
			int i=0;
			while(i<congruenceClassList.size()){
				boolean find = false;
// Begin
//				Vector<LirNode> congruenceClass=congruenceClassList.get(i);
				Vector congruenceClass=(Vector)congruenceClassList.get(i);
// End
// Begin
//				for (LirNode phiVar : newCongruenceClass) {
//					for (LirNode var : congruenceClass) {
//						if (phiVar.equals(var)) {
//							for(LirNode node:congruenceClass){
//								if(!newCongruenceClass.contains(node)){
//									newCongruenceClass.add(node);
//								}
//							}
//							congruenceClassList.remove(congruenceClass);
//							
//							find = true;
//							break;
//						}
//					}
//					if (find) {
//						break;
//					}
//				}
				for(int iNCC=0;iNCC<newCongruenceClass.size();iNCC++) {
				  LirNode phiVar=(LirNode)newCongruenceClass.get(iNCC);
				  for(int iCC=0;iCC<congruenceClass.size();iCC++) {
				    LirNode var=(LirNode)congruenceClass.get(iCC);
				    if(phiVar.equals(var)) {
				      for(int iCC2=0;iCC2<congruenceClass.size();iCC2++) {
					LirNode node=(LirNode)congruenceClass.get(iCC2);
					if(!newCongruenceClass.contains(node)) {
					  newCongruenceClass.add(node);
					}
				      }
				      congruenceClassList.remove(congruenceClass);
				      find=true;
				      break;
				    }
				    if(find) {
				      break;
				    }
				  }
				}
// End
				if(!find){
					i++;
				}
			}
			
			congruenceClassList.add(newCongruenceClass);
		}
	}
	
	
/**
 * Replace expressions.
 **/
	void replace(){
		FlowGraph fg=func.flowGraph();
		LirFactory lir = env.lir;

		Symbol tmpSym = ((LirSymRef) preTmp).symbol;
		
		for(BiLink p=fg.basicBlkList.first();!p.atEnd();p=p.next()){
			BasicBlk blk=(BasicBlk)p.elem();
		
		//for (int i = 0; i < nodeList.size(); i++) {
			//WgNode node = (WgNode) nodeList.get(i);

			//if (node.comp) {
			if(nReplace[blk.id]){
				//LirNode replaceInstr = node.instr;
				LirNode replaceInstr=null;
				BiLink replacePlace=null;
				
				for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
					LirNode instr=(LirNode)q.elem();
					if(instr.opCode==Op.SET){
						LirNode right=instr.kid(1);
						LirNode left=instr.kid(0);
						if(isPure(right) && sames(right,expr)){
							if(left instanceof LirSymRef){
								if(sstab.orgSym(((LirSymRef)left).symbol).equals(
										sstab.orgSym(tmpSym))){
									continue;
								}
							}
							replaceInstr=instr;
							replacePlace=q;
							break;
						}
					}
				}
				
				boolean find = false;
				//search in blk
				//for (BiLink p = node.link.prev(); !p.atEnd(); p = p.prev()) {
				for(BiLink q=replacePlace;!q.atEnd();q=q.prev()){
					LirNode instr = (LirNode) q.elem();
					if ((instr.opCode == Op.SET) || (instr.opCode == Op.PHI)) {
						LirNode left = instr.kid(0);
						if (left instanceof LirSymRef) {
							Symbol sym = ((LirSymRef) left).symbol;
							if (sstab.orgSym(sym).equals(sstab.orgSym(tmpSym))) {
								LirNode ssaNode = lir.symRef(sym);
								replaceInstr.setKid(1, ssaNode);
								//copyPropagation(replaceInstr);
								find = true;
								break;
							}
						}
					}
				}
				
				//search dom of blk
				BasicBlk domBlk = dom.immDominator(blk);
				while (!find) {
					for (BiLink q = domBlk.instrList().last(); !q.atEnd(); q = q
							.prev()) {
						LirNode instr = (LirNode) q.elem();
						if ((instr.opCode == Op.SET)
								|| (instr.opCode == Op.PHI)) {
							LirNode left = instr.kid(0);
							if (left instanceof LirSymRef) {
								Symbol sym = ((LirSymRef) instr.kid(0)).symbol;
								if (sstab.orgSym(sym).equals(sstab.orgSym(tmpSym))) {
									LirNode ssaNode = lir.symRef(sym);
									replaceInstr.setKid(1, ssaNode);
									//copyPropagation(replaceInstr);
									find = true;
									break;
								}
							}
						}
					}
					domBlk = dom.immDominator(domBlk);
				}
			}
			
			if(xReplace[blk.id]){
				//LirNode replaceInstr = node.instr;
				LirNode replaceInstr=null;
				BiLink replacePlace=null;
				for(BiLink q=blk.instrList().last();!q.atEnd();q=q.prev()){
					LirNode instr=(LirNode)q.elem();
					if(instr.opCode==Op.SET){
						LirNode right=instr.kid(1);
						if(isPure(right) && sames(right,expr)){
							replaceInstr=instr;
							replacePlace=q;
							break;
						}
					}
				}
				
				boolean find = false;
				//search in blk
				//for (BiLink p = node.link.prev(); !p.atEnd(); p = p.prev()) {
				for(BiLink q=replacePlace;!q.atEnd();q=q.prev()){
					LirNode instr = (LirNode) q.elem();
					if ((instr.opCode == Op.SET) || (instr.opCode == Op.PHI)) {
						LirNode left = instr.kid(0);
						if (left instanceof LirSymRef) {
							Symbol sym = ((LirSymRef) left).symbol;
							if (sstab.orgSym(sym).equals(sstab.orgSym(tmpSym))) {
								LirNode ssaNode = lir.symRef(sym);
								replaceInstr.setKid(1, ssaNode);
								//copyPropagation(replaceInstr);
								find = true;
								break;
							}
						}
					}
				}
				
				//search dom of blk
				BasicBlk domBlk = dom.immDominator(blk);
				while (!find) {
					for (BiLink q = domBlk.instrList().last(); !q.atEnd(); q = q
							.prev()) {
						LirNode instr = (LirNode) q.elem();
						if ((instr.opCode == Op.SET)
								|| (instr.opCode == Op.PHI)) {
							LirNode left = instr.kid(0);
							if (left instanceof LirSymRef) {
								Symbol sym = ((LirSymRef) instr.kid(0)).symbol;
								if (sstab.orgSym(sym).equals(sstab.orgSym(tmpSym))) {
									LirNode ssaNode = lir.symRef(sym);
									replaceInstr.setKid(1, ssaNode);
									//copyPropagation(replaceInstr);
									find = true;
									break;
								}
							}
						}
					}
					domBlk = dom.immDominator(domBlk);
				}
			}
		}
	}

/**
 * Do SSA based PRE.
 * @param func The current function
 * @param args The list of options
 **/
	public boolean doIt(Function func, ImList args) {
		//System.out.println(func);
		/*if(!func.symbol.name.equals("main")){
			return false;
		}*/
		
/* 2008.12.9
		long t1=System.currentTimeMillis();
*/
		
		this.func = func;

		// translate from TSSA to CSSA
		(new TssaToCssa(env, sstab, TssaToCssa.METHOD_III, true, true)).doIt(
				func, null);

		// make phi congruence classes
		makeCongruenceClassList();

		// remove cretical edges
		(new EdgeSplit(env)).doIt(func, null);
		
		dom = (Dominators) func.require(Dominators.analyzer);
		df = (DominanceFrontiers) func.require(DominanceFrontiers.analyzer);

		// divide expressions
		(new DivideExpression(env, sstab)).doIt(func, null);

		// divide selfchange expressions
		divSelfchange();

		// collect expressions
		exprList = collectExpr();
		
		//PrintUtil.printf(func);
		
/* 2008.12.9
		long t2=System.currentTimeMillis();
		Option.prepare+=t2-t1;
*/

		// do PRE to each expressions
		for (int i = 0; i < exprList.size(); i++) {
			/*if(i!=6){
				continue;
			}*/
			expr = (LirNode)exprList.get(i);

/* 2008.12.9			
			long t3=System.currentTimeMillis();
*/
			
			// compute local propaties
			compLocalProperty();

			// compute global propaties
			compGlobalProperty();
			
			//printProp();
			
/* 2008.12.9
			long t4=System.currentTimeMillis();
			Option.compProp+=t4-t3;
*/

			// insert expressions
			insertExpr();

			// insert phi functions
			insertPhi();

			// rename arguments in phi functions
			rename();

			// replace expressions
			replace();
			
/* 2008.12.9
			long t5=System.currentTimeMillis();
			Option.insert+=t5-t4;
*/

			preNum++;
			
			//printProp();
			/*if(i==1){
				//System.out.println("###############"+expr);
				//break;
			}*/
		}
		
		//PrintUtil.printf(func);
		//SnapShotUtil u = new SnapShotUtil(func, "init_block");
		//u.generate();

		return true;
	}

/**
 * @param data Data to be processes.
 * @param args List of optional arguments.
 **/
	public boolean doIt(Data data, ImList args) {
		return true;
	}

/**
 * Return the name of this optimizer.
 **/
	public String name() {
		return "LCM";
	}

/**
 * Return brief descriptions of this optimizer.
 **/
	public String subject() {
		return "LCM";
	}
	
/**
 * Do copy propagation.
 * @param copy The copy expression.
 **/
	void copyPropagation(LirNode copy){
		LirNode key=copy.kid(0);
		LirNode value=copy.kid(1);
	
		for(BiLink p=func.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
			BasicBlk blk=(BasicBlk)p.elem();
			for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
				LirNode instr=(LirNode)q.elem();
				if(instr.opCode==Op.SET){
					LirNode right=instr.kid(1);
					if(isPure(right)){
						for(int i=0;i<right.nKids();i++){
							LirNode operand=right.kid(i);
							if(key.equals(operand)){
								right.setKid(i,value);
								
								//add new expr to list
								boolean found=false;
// Begin
//								for(LirNode expr:exprList){
//									if(sames(expr,right)){
//										found=true;
//										break;
//									}
//								}
								for(int iEL=0;iEL<exprList.size();iEL++) {
								  LirNode expr=(LirNode)exprList.get(iEL);
								  if(sames(expr,right)) {
								    found=true;
								    break;
								  }
								}
// End
								if(!found){
									//exprList.add(right.makeCopy(env.lir));
								}
							}
						}
					}
				}
			}
		}
	}

}
