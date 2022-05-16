/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */

package coins.ssa;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.ana.Dominators;
import coins.backend.ana.LoopAnalysis;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirLabelRef;
import coins.backend.lir.LirNode;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;

/**
 * Scalar Replacement Based on Partial Redundancy Elimination (PRESR).
 * This optimizer removes redundant array references over loop iterations.
 * PRESR traverses a control flow graph in topological sort order, in the 
 * process of which for each array reference, it backwardly propagates a query 
 * to check whether it is redundant or not.
 * PRESR uses global value numbering (GVN.java) and effective demand-driven partial redundancy elimination (EQP.java).
 * 
 **/

public class PRESR implements LocalTransformer {
	public boolean doIt(Data data, ImList args) {return true;}
	public String name() {return "PRESR";}
	public String subject() {return "PRESR";}
	private SsaEnvironment env;
	private SsaSymTab sstab;
	private Function f;
	private EMemoryAliasAnalyze alias;
	private EQP eqp;
	private Util util;
	
	/**
	 * Constructor
	 * 
	 * @param e The environment of the SSA module
	 * @param tab The symbol tabel of the SSA module
	 * @param function The current function
	 * @param m The current mode
	 **/
	public PRESR(SsaEnvironment e, SsaSymTab tab) {
		env = e;
		env.println("Scalar Replacement Based on Partial Redundancy Elimination", SsaEnvironment.MsgThr);
		sstab = tab;
	}
	
	private HashMap<LirNode, LirNode> varToDef;
	private boolean[] result;
	private boolean[] isReal;
	private boolean[] isSelf;
	private int visitThreshld;
	private int[] visited;
	private int[] latestVisitVal;
	
	LirNode[] trueList;
	HashMap blkToNewNode;
	HashMap newPhiToPredMap;
	ArrayList newSetNodes;
	HashMap newNodeToBlk;
	ArrayList newPhiNodes;
	ArrayList insertedPhiNodes;
	HashSet valueLog;
	
	/**
	 * Do optimize Partial Redundancy Elimination Scalar Replacement.
	 * 
	 * @param f
	 **/
	public boolean doIt(Function function, ImList args) {
		f = function;
		invoke();
		f.flowGraph().touch();
		return (true);
	}
	
	void collectInformation(){
		for(int i=1;i<eqp.bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = eqp.bVecInOrderOfRPost[i];
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				if(node.opCode==Op.PHI || node.opCode==Op.SET && node.kid(0).opCode==Op.REG)
					varToDef.put(node.kid(0), node);
			}
		}
	}
	
	void invoke(){
		util = new Util(env,f);
		eqp = new EQP(env,f,sstab);
		eqp.set();
		eqp.gvn(3);
		alias=new EMemoryAliasAnalyze(env,f);
		varToDef = new HashMap();
		collectInformation();
		eliminate();
		alias.annul();
	}
	
	public boolean checkKillLocal(LirNode expr, BasicBlk blk, BiLink q, ArrayList vars){
		for(BiLink p=q;!p.atEnd();p=p.prev()){
			LirNode node = (LirNode)p.elem();
			if(isStore(expr,node,blk,p,vars))
				return true;
		}
		return false;
	}
	
	public void collectVars(ArrayList vars, LirNode exp){
		for(int i=0;i<exp.nKids();i++){
			if(exp.kid(i).opCode==Op.REG) vars.add(exp.kid(i).makeCopy(env.lir));
			else if(exp.kid(i).nKids()>0) collectVars(vars,exp.kid(i));
		}
	}
	
	private void eliminate(){
		visitThreshld = 2;
		boolean onlyLoop = false;
		onlyLoop = true;
		HashSet insertNodes = new HashSet();
		LoopAnalysis loop = (LoopAnalysis)f.require(LoopAnalysis.analyzer);
		
		for(int i=1;i<eqp.bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = eqp.bVecInOrderOfRPost[i];
			
			if(onlyLoop && loop.nestLevel[blk.id]==0)continue;
			
			HashMap valueMap = new HashMap();
			HashSet blkValueMap = new HashSet();
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				if(node.opCode==Op.PHI){
					int val = eqp.gvn.getValue(node.kid(0));
					blkValueMap.add(val);
					valueMap.put(val, node.kid(0));
				}
				else if(node.opCode==Op.CALL && node.kid(2).nKids()>0){
					int val = eqp.gvn.getValue(node.kid(2).kid(0));
					blkValueMap.add(val);
					valueMap.put(val, node.kid(2).kid(0));
				}
				else if(node.opCode==Op.PROLOGUE){
					for(int j=0;j<node.nKids();j++){
						if(node.kid(j).opCode!=Op.REG)continue;
						int val = eqp.gvn.getValue(node.kid(j));
						blkValueMap.add(val);
						valueMap.put(val, node.kid(j));
					}
				}
				if(node.opCode!=Op.SET || insertNodes.contains(node))continue;
				
				LirNode ve = eqp.gvn.makeVExp(node,blk);
				int val = eqp.gvn.getValue(ve);
				
				if(val==-1){
					if(node.kid(0).opCode==Op.MEM){
						LirNode mv = eqp.gvn.makeVExp(node.kid(0),blk);
						int old = eqp.gvn.getValue(mv);
						eqp.gvn.removeValue(mv,ve,old,blk);
						val = eqp.gvn.newValue();
						eqp.gvn.setValue(val,mv,blk);
					}
					else{
						int old = eqp.gvn.getValue(node.kid(0));
						eqp.gvn.removeValue(node.kid(0),ve,old,blk);
						val = eqp.gvn.newValue();
						eqp.gvn.setValue(val,ve,blk);
						eqp.gvn.setValue(val,node.kid(0),blk);
					}
				}
				else if(valueMap.containsKey(val)){
					// This expression is redundant.
					if((!onlyLoop || loop.nestLevel[blk.id]!=0) && node.kid(1).opCode==Op.MEM){
						LirNode pred = (LirNode)valueMap.get(val);
						node.setKid(1, pred.makeCopy(env.lir));
					}
					else if(node.kid(0).opCode==Op.REG){
						valueMap.put(val, node.kid(0));
						eqp.gvn.setValue(val, node.kid(0), ve, blk);
					}
					else valueMap.put(val, node.kid(1));
					blkValueMap.add(val);
					continue;
				}
				
				ArrayList vars = new ArrayList();
				collectVars(vars, node.kid(1));
				
				if(node.kid(1).opCode!=Op.MEM || node.kid(0).opCode==Op.MEM || checkKillLocal(node,blk,p,vars)){
					// This expression is not target.
					if(node.kid(0).opCode==Op.REG) valueMap.put(val, node.kid(0));
					else valueMap.put(val, node.kid(1));
					blkValueMap.add(val);
					continue;
				}
				
				isReal = new boolean[eqp.idBound];
				isSelf = new boolean[eqp.idBound];
				result = new boolean[eqp.idBound];
				visited = new int[eqp.idBound];
				latestVisitVal = new int[eqp.idBound];
				valueLog = new HashSet();
				eqp.setVarsToGCM(blk,val);
				
				trueList = new LirNode[eqp.idBound];
				newPhiToPredMap = new HashMap();
				newSetNodes = new ArrayList();
				newNodeToBlk = new HashMap();
				blkToNewNode = new HashMap();
				newPhiNodes = new ArrayList();
				insertedPhiNodes = new ArrayList();
				
				LirNode copy = node.makeCopy(env.lir);
				LirNode vnode = node.makeCopy(env.lir);
				vnode.setKid(1, ve);
				
				// propagating query backwardly
				if((!onlyLoop || loop.nestLevel[blk.id]!=0) && propagate(val,vnode,copy,blk) && isReal[blk.id]){
					if(insertNewExpressions()){
						LirNode pred = null;
						
						// local search
						for(BiLink q=p;!q.atEnd();q=q.prev()){
							LirNode n = (LirNode)q.elem();
							if(n.opCode!=Op.PHI)continue;
							int v = eqp.gvn.getValue(n.kid(0));
							if(v==val){
								pred = n.kid(0);
								break;
							}
						}
						
						if(pred==null){
							// global search
							Dominators dom = (Dominators) f.require(Dominators.analyzer);
							BasicBlk domBlk = dom.immDominator(blk);
							while(domBlk!=null){
								if(blkToNewNode.containsKey(domBlk)){
									pred = (LirNode)blkToNewNode.get(domBlk);
									break;
								}
								else if(trueList[domBlk.id]!=null){
									pred = trueList[domBlk.id];
									break;
								}
								domBlk = dom.immDominator(domBlk);
							}
						}
						if(pred!=null){
							node.setKid(1, pred);
						}
					}
					else{
						// canceling program transfer
						for(int j=0;j<newSetNodes.size();j++){
							LirNode newNode = (LirNode)newSetNodes.get(j);
							BasicBlk b = (BasicBlk)newNodeToBlk.get(newNode);
							
							for(BiLink q=b.instrList().last();!q.atEnd();q=q.prev()){
								LirNode n = (LirNode)q.elem();
								if(n.equals(newNode)){
									q.unlink();
									break;
								}
							}
							
							int v = eqp.gvn.getValue(newNode.kid(0));
							eqp.gvn.removeValue(v,newNode.kid(0),b);
						}
						for(int j=0;j<newPhiNodes.size();j++){
							LirNode phi = (LirNode)newPhiNodes.get(j);
							BasicBlk b = (BasicBlk)newNodeToBlk.get(phi);
							int v = eqp.gvn.getValue(phi.kid(0));
							eqp.gvn.removeValue(v,phi.kid(0),b);
						}
						for(int j=0;j<insertedPhiNodes.size();j++){
							LirNode phi = (LirNode)insertedPhiNodes.get(j);
							BasicBlk b = (BasicBlk)newNodeToBlk.get(phi);
							for(BiLink q=b.instrList().first();!q.atEnd();q=q.next()){
								LirNode n = (LirNode)q.elem();
								if(n.equals(phi)){
									q.unlink();
									break;
								}
							}
						}
					}
				}
				
				eqp.gvn.setValue(val, node.kid(0), ve, blk);
				valueMap.put(val, node.kid(0));
				blkValueMap.add(val);
				
				if(node.kid(1).nKids()==0){
					valueMap.put(val, node.kid(1));
				}
			}
			eqp.gvn.updateBlkVariableMap(blk, valueMap);
			eqp.gvn.updateReachableValues(blk,blkValueMap);
		}
	}
	
	/**
	 * These array references are used in method insertNewExpressions.
	 * @param blk
	 * @param predToNewNode
	 */
	private void recordNewNode(BasicBlk blk, HashMap predToNewNode){
		for(BiLink p=blk.predList().first();!p.atEnd();p=p.next()){
			BasicBlk pred = (BasicBlk)p.elem();
			Object value = predToNewNode.get(pred);
			if(!(value instanceof LirNode)) continue;
			LirNode newNode = (LirNode)value;
			newNode.setKid(0, eqp.createNewVar(newNode.kid(0),eqp.tmpSymName));
			newSetNodes.add(newNode);
			newNodeToBlk.put(newNode, pred);
			predToNewNode.put(pred, newNode);
		}
	}
	
	/**
	 * These array references are used in method insertNewExpressions.
	 * @param val
	 * @param node
	 * @param blk
	 * @param predToNewNode
	 */
	private void recordNewPhi(int val, LirNode node, BasicBlk blk, HashMap predToNewNode){
		LirNode newPhi = (eqp.newPhi(node,blk,eqp.tmpSymName)).makeCopy(env.lir);
		eqp.gvn.setValue(val, newPhi.kid(0), blk);
		newPhiNodes.add(newPhi);
		newNodeToBlk.put(newPhi, blk);
		newPhiToPredMap.put(newPhi, predToNewNode);
	}
	
	/**
	 * New array references and phi functions are inserted.
	 * @return
	 */
	private boolean insertNewExpressions(){
		for(int i=0;i<newSetNodes.size();i++){
			LirNode newNode = (LirNode)newSetNodes.get(i);
			BasicBlk blk = (BasicBlk)newNodeToBlk.get(newNode);
			LirNode ve = eqp.gvn.makeVExp(newNode,blk);
			int val = eqp.gvn.getValue(ve);
			eqp.gvn.setValue(val, newNode.kid(0), blk);
			blk.instrList().last().addBefore(newNode);
			blkToNewNode.put(blk, newNode.kid(0));
		}
		
		Dominators dom = (Dominators) f.require(Dominators.analyzer);
		
		for(int i=0;i<newPhiNodes.size();i++){
			LirNode phi = (LirNode)newPhiNodes.get(i);
			BasicBlk blk = (BasicBlk)newNodeToBlk.get(phi);
			LirNode newPhi = phi.makeCopy(env.lir);
			HashMap predToNewNode = (HashMap)newPhiToPredMap.get(phi);
			
			for(int j=1;j<phi.nKids();j++){
				BasicBlk pred = (((LirLabelRef) phi.kid(j).kid(1)).label).basicBlk();
				Object value = predToNewNode.get(pred);
				
				if(value instanceof LirNode){
					LirNode node = (LirNode)value;
					newPhi.kid(j).setKid(0, node.kid(0));
				}
				else if(value instanceof Integer){
					// changing preferred arguments.
					int predVal = ((Integer) value).intValue();
					BasicBlk domBlk = pred;
					LirNode newArg = null;
					while(domBlk!=null){
						if(blkToNewNode.containsKey(domBlk)){
							newArg = (LirNode)blkToNewNode.get(domBlk);
							break;
						}
						else if(trueList[domBlk.id]!=null){
							newArg = trueList[domBlk.id];
							break;
						}
						else if(eqp.gvn.containValue(predVal,domBlk)){
							newArg = eqp.gvn.getVariable(predVal,domBlk);
							break;
						}
						domBlk = dom.immDominator(domBlk);
					}
					if(newArg==null){
						return false;
					}
					newPhi.kid(j).setKid(0, newArg);
				}
			}
			blk.instrList().first().addBefore(newPhi);
			blkToNewNode.put(blk, newPhi.kid(0));
			insertedPhiNodes.add(newPhi);
			newNodeToBlk.put(newPhi, blk);
			int v = eqp.gvn.getValue(phi.kid(0));
			eqp.gvn.removeValue(v,phi.kid(0),blk);
			eqp.gvn.setValue(v, newPhi.kid(0), blk);
		}
		return true;
	}
	
	/**
	 * Query propagation
	 * @param val
	 * @param vnode
	 * @param node
	 * @param blk
	 * @return
	 */
	private boolean propagate(int val, LirNode vnode, LirNode node, BasicBlk blk){
		int True = 0;
		int Real = 0;
		int Self = 0;
		ArrayList blks = new ArrayList(blk.predList().length());
		HashMap newNodeVal = new HashMap();
		
		HashMap predToNewNode = new HashMap();
		newPhiToPredMap.put(val, predToNewNode);
		
		for(BiLink p=blk.predList().first();!p.atEnd();p=p.next()){
			BasicBlk pred = (BasicBlk)p.elem();
			
			// prepare to propagate new query to pred.
			LirNode newNode = node.makeCopy(env.lir);
			LirNode newVNode = vnode.makeCopy(env.lir);
			LirNode inode = alias.getIndex(pred);
			if(node.kid(1).kid(1).equals(inode)){
				inode = node.kid(1).kid(1);
			}
			LirNode newIndex = eqp.gvn.makeVExp(inode,pred).makeCopy(env.lir);
			newVNode.kid(1).setKid(1, newIndex);
			LirNode newVExp = eqp.gvn.makeNewValueExp(newVNode.kid(1),node.kid(1),blk,pred);
			newVNode.setKid(1, newVExp);
			LirNode newExp = eqp.gvn.valueNumberToVariable(newVExp,node.kid(1),pred,null);
			if(newExp==null) return false;
			
			newExp.setKid(1, inode);
			newNode.setKid(1, newExp);
			int newVal = eqp.gvn.getValue(newVExp);
			
			if(newVal==-1){
				LirNode tempExp = newVExp.makeCopy(env.lir);
				tempExp.setKid(1, vnode.kid(1).kid(1));
				int temp = eqp.gvn.getValue(tempExp);
				if(temp==-1){
					eqp.gvn.setValue(eqp.gvn.newValue(), newVExp, pred);
					newVal = eqp.gvn.getValue(newVExp);
				}else{
					newVNode.kid(1).setKid(1, vnode.kid(1).kid(1));
					newNode.kid(1).setKid(1, node.kid(1).kid(1));
					newVal = temp;
				}
			}
			
			valueLog.add(newVal);
			
			boolean localAnswer;
			
			if(result[pred.id]){
				localAnswer = (eqp.avail[pred.id]==newVal);
			}
			else if(latestVisitVal[pred.id]==newVal){
				localAnswer = true;
			}
			else if(visited[pred.id]==visitThreshld){
				localAnswer = false;
			}
			else{
				newNodeVal.put(pred, newVal);
				ArrayList vars = new ArrayList();
				collectVars(vars, newExp);
				// propagating new query to a predecessor
				localAnswer = local(newVal,newVNode,newNode,pred,vars);
			}
			
			if(localAnswer){
				predToNewNode.put(pred, newVal);
				True++;
				if(isReal[pred.id]) Real++;
				if(isSelf[pred.id]) Self++;
			}
			else{
				predToNewNode.put(pred, newNode);
				blks.add(pred);
			}
			result[pred.id] = true;
		}
		
		recordVisited(val,blk);
		result[blk.id] = true;
		
		if(True>0){
			LirNode copy = node.makeCopy(env.lir);
			if(blks.size()>0){
				if(Real!=True || (Self==0 || Self!=Real) &&
						!checkDSafe(val,vnode.kid(1),copy.kid(1),blk)) return false;
				recordNewNode(blk,predToNewNode);
				recordNewPhi(val,node,blk,predToNewNode);
				Real = blk.predList().length();
			}
			else if(blk.predList().length()>1){
				recordNewPhi(val,node,blk,predToNewNode);
			}
			eqp.avail[blk.id] = val;
			if(Real==blk.predList().length())isReal[blk.id] = true;
			if(Self==blk.predList().length())isSelf[blk.id] = true;
			
			return true;
		}
		return false;
	}
	
	/**
	 * checking local answer of this basic block.
	 * @param val
	 * @param vnode
	 * @param node
	 * @param blk
	 * @param vars
	 * @return
	 */
	private boolean local(int val, LirNode vnode, LirNode node, BasicBlk blk, ArrayList vars){
		recordVisited(val,blk);
		
		if(eqp.gvn.containValue(val,blk)){
			if(!checkLocalAvail(val,node,blk,vars))return false;
			trueList[blk.id] = eqp.gvn.getVariable(val, blk);
			result[blk.id] = true;
			eqp.avail[blk.id] = val;
			isReal[blk.id] = true;
			if(blk==eqp.exprBlk)isSelf[blk.id] = true;
			return true;
		}
		
		if(existDefVal(node,blk,vars) && visited[blk.id]<visitThreshld){
			// changing index. ex. n is i = i+1 and node is a[i] => a[i+1];
			visited[blk.id]--;
			LirNode copy = node.makeCopy(env.lir);
			LirNode changedNode=changeOperand(copy.kid(1),blk);
			LirNode transNode=util.trans(changedNode);
			if(!node.kid(1).equals(transNode)){
				node.setKid(1, transNode);
				vars = new ArrayList();
				collectVars(vars, transNode);
				LirNode newVExp = eqp.gvn.makeVExp(node,blk);
				vnode.setKid(1, newVExp);
				int newVal =eqp.gvn.getValue(newVExp);
				if(newVal==-1){
					eqp.gvn.setValue(eqp.gvn.newValue(), newVExp, blk);
					newVal = eqp.gvn.getValue(newVExp);
				}
				if(val!=newVal){
					val = newVal;
				}
				
				if(local(val,vnode,node,blk,vars)){
					result[blk.id] = true;
					eqp.avail[blk.id] = val;
					isReal[blk.id] = true;
					if(blk==eqp.exprBlk)isSelf[blk.id] = true;
					return true;
				}else{
					return false;
				}
			}
		}
		
		if(!eqp.gvn.reachValue(val, blk) && !eqp.dependPhi(node.kid(1),blk) || existKill(node,blk,vars)){
			return false;
		}
		
		return propagate(val,vnode,node,blk);
	}
	
	/**
	 * If an operand of query is defined in this basic block, it returns true.
	 * @param node
	 * @param blk
	 * @param vars
	 * @return
	 */
	private boolean existDefVal(LirNode node, BasicBlk blk, ArrayList vars){
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode n = (LirNode)p.elem();
			if(n.opCode==Op.SET && n.kid(0).opCode==Op.REG && vars.contains(n.kid(0))){
				return true;
			}
		}
		return false;
	}
	
	/**
	 * This optimizer assumes that every function calls return different value.
	 * @param node
	 * @param blk
	 * @param vars
	 * @return
	 */
	private boolean existKill(LirNode node, BasicBlk blk, ArrayList vars){
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
			LirNode n = (LirNode)p.elem();
			if(n.opCode==Op.CALL) return true;
			if(isStore(node, n, blk, p, vars)) return true;
		}
		return false;
	}
	
	/**
	 * Checking down-safety.
	 * @param val
	 * @param ve
	 * @param expr
	 * @param blk
	 * @return
	 */
	public boolean checkDSafe(int val, LirNode ve, LirNode expr, BasicBlk blk){
		if(eqp.gvn.containValue(val,blk)) return true;
		Object[] vals = valueLog.toArray();
		for(int i=0;i<vals.length;i++){
			int v = ((Integer)vals[i]).intValue();
			if(eqp.gvn.containValue(v,blk)) return true;
		}
		int[] checkBlk = new int[eqp.idBound];
		for(BiLink p=blk.succList().first();!p.atEnd();p=p.next()){
			BasicBlk succ = (BasicBlk)p.elem();
			if(checkBlk[succ.id]<visitThreshld)continue;
			LirNode newVExp = eqp.gvn.makeNewValueExp(ve,expr,succ);
			int newVal = eqp.gvn.getValue(newVExp);
			if(newVal==-1 || !checkAnticipatable(newVal,newVExp,expr,succ,checkBlk)) return false;
		}
		return false;
	}
	
	public boolean checkAnticipatable(int val, LirNode ve, LirNode expr, BasicBlk blk, int[] checkBlk){
		checkBlk[blk.id]++;
		if(eqp.gvn.containValue(val,blk) || isReal[blk.id]) return true;
		Object[] vals = valueLog.toArray();
		for(int i=0;i<vals.length;i++){
			int v = ((Integer)vals[i]).intValue();
			if(eqp.gvn.containValue(v,blk)) return true;
		}
		if(blk==f.flowGraph().exitBlk()) return false;
		for(BiLink p=blk.succList().first();!p.atEnd();p=p.next()){
			BasicBlk succ = (BasicBlk)p.elem();
			if(checkBlk[succ.id]<visitThreshld) continue;
			LirNode newVExp = eqp.gvn.makeNewValueExp(ve,expr,succ);
			int newVal = eqp.gvn.getValue(newVExp);
			if(newVal==-1 || !checkAnticipatable(newVal,newVExp,expr,succ,checkBlk)) return false;
		}
		return false;
	}
	
	/**
	 * Just checking whether there is no any function calls after occurring same value number as query.
	 * @param val
	 * @param node
	 * @param blk
	 * @param vars
	 * @return
	 */
	boolean checkLocalAvail(int val, LirNode node, BasicBlk blk, ArrayList vars){
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode n = (LirNode)p.elem();
			if(n.opCode==Op.SET && (n.kid(0).opCode==Op.MEM && eqp.gvn.getValue(n.kid(1))==val || eqp.gvn.getValue(n.kid(0))==val)) return true;
			if(isStore(node, n, blk, p, vars)) break;
		}
		return false;
	}
	
	public boolean isStore(LirNode expr, LirNode node, BasicBlk blk, BiLink p, ArrayList exprVars){
		if(node.opCode==Op.CALL) return true;
		if(node.opCode!=Op.SET || node.kid(0).opCode!=Op.MEM) return false;
		if(eqp.mayAlias(expr,node) || node.kid(0).kid(0).equals(expr.kid(1).kid(0))) return true;
		if(!sameArray(expr.kid(1),node.kid(0))) return false;
		
		// checking indexes
		ArrayList storeVars = new ArrayList();
		collectVars(storeVars,node.kid(0));
		if(storeVars.size()!=exprVars.size()) return true;
		int num = exprVars.size();
		for(int i=0;i<num;i++){
			LirNode var = (LirNode)exprVars.get(i);
			boolean same = false;
			for(int j=0;j<num;j++){
				LirNode svar = (LirNode)storeVars.get(i);
				if(var.equals(svar)){
					same = true;
					break;
				}
			}
			if(!same) return true;
		}
		return false;
	}
	
	private boolean sameArray(LirNode mem1, LirNode mem2){
		LirNode addr1 = getAddr(mem1);
    	LirNode addr2 = getAddr(mem2);
    	return addr1.equals(addr2);
	}
	
	private LirNode getAddr(LirNode mem){
    	if(mem.nKids()==0) return mem;
    	return getAddr(mem.kid(0));
    }
	
	private void recordVisited(int val, BasicBlk blk){
		visited[blk.id]++;
		latestVisitVal[blk.id] = val;
	}
	
	private LirNode changeOperand(LirNode exp, BasicBlk blk){
		for(int i=0;i<exp.nKids();i++){
			if(exp.kid(i).opCode==Op.REG && varToDef.containsKey(exp.kid(i)) && 
					eqp.gvn.containValue(eqp.gvn.getValue(exp.kid(i)),blk) && eqp.gvn.dependLoopPhi(exp.kid(i))){
				LirNode def = varToDef.get(exp.kid(i));
				if(def.opCode==Op.SET) exp.setKid(i, def.kid(1));
			}else if(exp.kid(i).nKids()>0){
				exp.setKid(i, changeOperand(exp.kid(i),blk));
			}
		}
		return exp;
	}
}