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
	public boolean[] nDelayed;
	public boolean[] xDelayed;
	public boolean[] nEarliest;
	public boolean[] xEarliest;
	public boolean[] nUSafe;
	public boolean[] xUSafe;
	public boolean[] nDSafe;
	public boolean[] xDSafe;
	public boolean[] pUSafe;
	
	
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
    
    
   void displayBasicBlk() {
	   System.out.println("-------------------------------------------");
	   for(BiLink p =f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()) {
		   BasicBlk v=(BasicBlk)p.elem();
		   for(BiLink bl=v.instrList().first();!bl.atEnd();bl=bl.next()){
			   LirNode node=(LirNode)bl.elem();
			   System.out.println(node);
		   }
	   }
	   System.out.println("-------------------------------------------");
    }
   
    /**
     *s1????????????s2?????????????????????????????????????????????????????????
     * @param s1 kill??????????????????????????????
     * @param s2 s1???kill???????????????????????????????????????
     * @return
     */
    boolean isUse(LirNode s1, LirNode s2) {
//    	System.out.println("***********************");
//    	System.out.println("s1:" + s1);
//    	System.out.println("s2:" + s2);
    	if(s1.opCode==Op.SET) {
    		if(s1.nKids()>0) {
    			if(s2.nKids()>0) {
    				if(s2.opCode==Op.SET&&s2.nKids()>1) {
    					switch(s2.kid(1).opCode) {
    						case Op.ADD:
    						case Op.SUB:
    						case Op.MUL:
    						case Op.DIVS:
    							if(s1.kid(0).equals(s2.kid(1).kid(0))||s1.kid(0).equals(s2.kid(1).kid(1))) {
    								System.out.println(true);
    								return true;
    							}
    						case Op.CONVSX:
    							if(s1.kid(0).equals(s2.kid(1).kid(0))) {
    								System.out.println(true);
    								return true;
    							}
    					}
    					if(s1.kid(0).equals(s2.kid(1))) {
    						System.out.println(true);
    						return true;
    					}
    				}
    				if(s2.opCode==Op.CALL&&s2.nKids()>1) {
    					if(s2.kid(1).nKids()>0) {
    						if(s1.kid(0).equals(s2.kid(1).kid(0))) {
    							System.out.println(true);
    							return true;
    						}
    					}
    				}
    			}
    		}
    	}
    	System.out.println(false);
    	return false;
    		
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
    
    public void collectVars(ArrayList vars, LirNode exp){
		for(int i=0;i<exp.nKids();i++){
			if(exp.kid(i).opCode==Op.REG) vars.add(exp.kid(i).makeCopy(env.lir));
			else if(exp.kid(i).nKids()>0) collectVars(vars,exp.kid(i));
		}
	}
    
    //load?????????????????????????????????
    public boolean isLoad(LirNode node){
		return (node.opCode==Op.SET && node.kid(0).opCode==Op.REG && node.kid(1).opCode==Op.MEM);
	}
    
    //store?????????????????????????????????
    public boolean isStore(LirNode node) {
    	return(node.opCode==Op.SET && node.kid(0).opCode==Op.MEM);
    }
    
    //?????????????????????????????????????????????????????????????????????????????????????????????
    public boolean isKill(LirNode expr, LirNode node, ArrayList vars, BasicBlk blk, BiLink p){
		if(node.opCode==Op.CALL)return true;//TODO ??????????????????????????????????????????????????????????????????
		if(node.opCode==Op.SET && node.kid(0).opCode==Op.MEM)return true;//TODO ????????????
//		if(node.opCode==Op.SET && node.kid(0).opCode==Op.MEM && ddalias.checkAlias(expr, node.kid(0), blk, p))return true;
		if(vars.contains(node.kid(0)))return true;
		return false;
	}
    
    //LirNode???nKids?????????????????????????????????????????????????????????????????????
    LirNode getAddr(LirNode exp){
		if(exp.kid(0).nKids()==0) return exp.kid(0);
		else return getAddr(exp.kid(0));
	}
    
    //conmTranspe????????????????????????????????????
  	public boolean sameAddr(LirNode node, LirNode addr){
  		if(!isLoad(node))return false;
  		return (addr.equals(getAddr(node.kid(1))));
  	}
    
    //???????????????????????????????????????????????????????????????
	void compLocalProperty(LirNode exp, LirNode addr, ArrayList vars){
		dce = new boolean[idBound];
		Arrays.fill(dce, false);
		xSameAddr = new boolean[idBound];
		xIsSame = new boolean[idBound];
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			xIsSame[blk.id] = compXIsSame(exp,vars,blk);
		}
	}
	
	//??????xIsSame????????????????????????????????????
	//??????xIsSame???compDSafe????????????????????????
	//???????????????????????????????????????????????????????????????????????????
	private boolean compXIsSame(LirNode exp, ArrayList vars, BasicBlk blk){
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode node = (LirNode)p.elem();
			if(isKill(exp,node,vars,blk,p))break;
			if(!isLoad(node)) {
				if(node.kid(1).equals(exp))return true;
			}else if(isStore(node)){
				if(node.kid(0).equals(exp))return true;
			}
		}
		return false;
	}
	
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
			xEarliest[blk.id] = (xUSafe[blk.id] || xDSafe[blk.id]) && (!(nUSafe[blk.id] || nDSafe[blk.id]) && !n);
		}
	}
    
	//??????nDSafe,xDSafe????????????????????????????????????
	//??????nDSafe???
	//??????xDSafe???
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
				boolean n = nIsSame[blk.id] || x;
				if(nDSafe[blk.id]!=n || xDSafe[blk.id]!=x) change = true;
				nDSafe[blk.id] = n;
				xDSafe[blk.id] = x;
			}
		}
	}
	
	public boolean checkType(LirNode exp){
		char type=Type.toString(exp.type).charAt(0);
		return (type=='I' || type=='F');
	}
	
	private void globalCodeMotion(){
		//vars???????????????????????????
		ArrayList insertNode = new ArrayList();
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				if(!isLoad(node) || insertNode.contains(node.kid(1)) || !checkType(node))continue;
				insertNode.add(node.kid(1).makeCopy(env.lir));
				//addr????????????
				LirNode addr = getAddr(node.kid(1));
				//vars????????????
				ArrayList vars = new ArrayList();
				collectVars(vars,node.kid(1));
				compDCE(node,addr,vars);
//				printGlobalProp(node);
			}
		}
	}
	
	public void compDCE(LirNode node, LirNode addr, ArrayList vars) {
        //for??????IsSame??????????????????????????????????????????compDSafe????????????????????????????????????????????????dce???????????????????????????
        //exit?????????????????????true?????????????????????????????????
		//
        
	}
	
    public void checkDCE() {
    	dce = new boolean[idBound];
        Arrays.fill(dce, false);
        for(BiLink p=f.flowGraph().basicBlkList.last();!p.atEnd();p=p.prev()){
        	boolean isSame=false;
//        	System.out.println("??????");
        	BasicBlk v=(BasicBlk)p.elem();
        	if(v!=f.flowGraph().exitBlk()) {
//    			System.out.println("??????");
        		for(BiLink bl=v.instrList().last();!bl.atEnd();bl=bl.prev()) {
        			LirNode node=(LirNode)bl.elem();
//        			System.out.println("??????");
        			for(BiLink bll=bl.next();!bll.atEnd();bll=bll.next()) {
        				LirNode noden=(LirNode)bll.elem();
//        				System.out.println("??????");
        				if((node.opCode==Op.SET)&&(noden.opCode==Op.CALL||noden.opCode==Op.SET)) {
//        					System.out.println("??????");
        					if(isUse(node,noden)) {
//        						System.out.println("??????");
        						isSame=true;
        					}
        				}
        			}
//                	System.out.println("??????");
        			for(BiLink pp=p.next();!pp.atEnd();pp=pp.next()) {
            			BasicBlk vv=(BasicBlk)pp.elem();
            			if(vv!=f.flowGraph().exitBlk()) {
            				for(BiLink blll=vv.instrList().first();!blll.atEnd();blll=blll.next()) {
            					LirNode nodem=(LirNode)blll.elem();
//            					System.out.println("??????");
//            					System.out.println(node);
//            					System.out.println(noden);
//            					System.out.println("++++++++++++++++");
            					if((node.opCode==Op.SET)&&(nodem.opCode==Op.CALL||nodem.opCode==Op.SET)) {
//            						System.out.println("??????");
            						if(isUse(node,nodem)) {
//            							System.out.println("??????");
            							isSame=true;
            						}
            					}
            				}
            			}
            			if(!isSame&&(node.opCode==Op.SET)&&v!=f.flowGraph().entryBlk()) {
                       		dce[v.id]=true;
                       		System.out.println("------do_dce------");
                       	}
                    	isSame=false;
        			}
       			}
       		}
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
      
      displayBasicBlk();
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