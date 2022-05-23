/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
/*
the case where a query reaches uneffective traces of propagated queries is problem.
*/


package coins.ssa;

//import java.util.Enumeration;
//import java.util.Hashtable;
//import java.util.Stack;
//import java.util.Vector;

import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
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
    		//System.out.println("** Checking nodes **");
    		//System.out.println(ps);
    		//System.out.println(kill(ps,statement));
    		if(kill(ps,statement)) break;
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
    	//System.out.println("Checking newSt");
    	//System.out.println(newSt);
    	Symbol dstSym = sstab.newSsaSymbol(tmpSymName, newSt.type);
    	LirNode nn = env.lir.symRef(Op.REG, dstSym.type, dstSym, ImList.Empty);
    	LirNode newNode = env.lir.operator(Op.SET, newSt.type, nn, newSt.kid(1),ImList.Empty);
    	//System.out.println("new node:"+newNode);
    	return newNode;
    }
    
    void displayBasicBlk(BasicBlk v) {
 	   for(BiLink p=v.instrList().first();!p.atEnd();p=p.next()){
        	LirNode node=(LirNode)p.elem();
        	System.out.println(node);
 	   }
    }
    
    
    /**
     *s1の左辺とs2の右辺を比較して同じのがないか確認する
     * @param s1 killかどうかを見る命令。
     * @param s2 s1をkillかどうかチェックする右辺。
     * @return
     */
    boolean kill(LirNode s1, LirNode s2) {
  	 // System.out.println("s1" + s1);
  	 // System.out.println("s2" + s2);
  	   
  	   
  	   if(s1.opCode==Op.SET) {
  		   if(s2.kid(1).opCode==Op.MEM && s1.kid(0).opCode==Op.MEM) {
  			   return true;
  		   }
  		   if(s2.kid(1).nKids() < 2) {
  			   if(s1.kid(0).equals(s2.kid(1))) {
  				   return true;
  			   } 
  		   } 
  		   else if(s1.kid(0).equals(s2.kid(1).kid(0))) {
  				   return true;
  			   }  
  			   else if(s1.kid(0).equals(s2.kid(1).kid(1))) {
  				   return true;
  			   }
  	     }  
  	     else if(s1.opCode == Op.CALL){
  		   if(s2.opCode == Op.SET && s2.kid(1).opCode==Op.MEM) {
  			  return true;
  		   }
  		   else if(s2.kid(1).nKids()<2){
  			   if(s1.kid(2).nKids()<2) {
  				   if(s1.kid(2).equals(s2.kid(1))) {
  					   return true;
  				   }
  			   }
  			   else if(s1.kid(2).kid(0).equals(s2.kid(1))){
  				  return true;
  		      } 
  		  } 
  		   else if(s1.kid(2).nKids()<2) {
  			  if(s1.kid(2).equals(s2.kid(1).kid(0))) {
  				  return true;
  			  }
  			  else if(s1.kid(2).equals(s2.kid(1).kid(1))) {
  				  return true;
  			  }
  		  }
  		  else if(s1.kid(2).kid(0).equals(s2.kid(1).kid(0))) {
  				  return true;
  			  }
  			  else if(s1.kid(2).kid(0).equals(s2.kid(1).kid(1))) {
  				  return true;
  			  }
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
    
    for(BiLink pp=f.flowGraph().basicBlkList.first();!pp.atEnd();pp=pp.next()){
        BasicBlk v=(BasicBlk)pp.elem();        
        for(BiLink p=v.instrList().first();!p.atEnd();p=p.next()){
        	LirNode node=(LirNode)p.elem();
//        	System.out.println(node.kid(0));
        	if(node.nKids()>1&&node.kid(1).nKids()>0) {
            	if(node.kid(1).kid(0).opCode==Op.STATIC) {
            		System.out.println(node.kid(1).kid(0));
            	}
        	}
//        	if(node.opCode==Op.SET) {
//        		if(node.kid(0).opCode==Op.MEM) {
//        			System.out.println(node.kid(0).kid(0).kid(0));
//        		}
//        	}
//        		if(node.opCode==Op.SET) {
//        			System.out.println(node.kid(0));
//        			if(node.kid(1).nKids()>1) {
//        				System.out.println(node.kid(1).kid(1));
//        			}
//        		}
        		
        		
//             if(node.opCode!=Op.SET) continue;
//             if(node.kid(1).opCode==Op.MEM) continue;
//             System.out.println("== Checking target ==");
//             System.out.println(node);
//             System.out.println("== Checking BasicBlk ==");
//             displayBasicBlk(v);
//
//             
//            
//             LirNode newStat = createNewStatement(node);
//             p.addBefore(newStat);
//         	
//         	
//        	 LirNode pvar = removingLocalRedundancy(p.prev(), node);
//        	 if(pvar!=null) {
//        		 System.out.println(pvar);
//        		 node.setKid(1, pvar.makeCopy(env.lir));
//        		 System.out.println(node);
//        	 }
        }    
    }
    
		//if(node.kid(0).opCode==Op.MEM && (node.kid(1).opCode==Op.REG || 
    f.flowGraph().touch();
    return(true);
  }
 }






/**class lattice {
    static int Top = 1;
    static int Bot = 2;
    static int True = 3;
    static int False = 4;
    lattice(){
        System.out.println(l_and(True,False));
        System.out.println(l_or(Top,True));
    }
    public static void main(String[] args) {
        lattice obj = new lattice();
        obj.l_and(1,2);
        obj.l_or(1,2);
    }
    public int l_and(int op1,int op2){
        if(op1==Top){
            if(op2==True){
                return True;
            } else if(op2==False){
                return False;
            } else if(op2==Bot){
                return Bot;
            } else {
                return Top;
            }
        } 
        else if(op1==Bot){
            if(op2==True){
                return Bot;
            } else if(op2==False) {
                return Bot;
            } else if(op2==Top) {
                return Bot;
            } else {
                return Bot;
            }
        } 
        else if(op1==True){
            if(op2==False){
                return Bot;
            } else if(op2==Top){
                return True;
            } else if(op2==Bot){
                return Bot;
            } else {
                return True;
            }
        } 
        else if(op1==False){
            if(op2==True){
                return Bot;
            } else if(op2==Top){
                return False;
            } else if(op2==Bot){
                return Bot;
            } else {
                return False;
            }
        }
        else{
            return -1;
        }
    }
    public int l_or(int op1, int op2){
        if(op1==Top){
            if(op2==True){
                return Top;
            } else if(op2==False) {
                return Top;
            } else if(op2==Bot) {
                return Top;
            } else {
                return Top;
            }
        } 
        else if (op1==Bot) {
            if(op2==True){
                return True;
            } else if(op2==False){
                return False;
            } else if(op2==Top){
                return Top;
            } else {
                return Bot;
            }
        }
        else if(op1==True){
            if(op2==False){
                return Top;
            } else if(op2==Top){
                return Top;
            } else if(op2==Bot){
                return True;
            }  else {
                return True;
            }
        }
        else if(op1==False){
            if(op2==True){
                return Top;
            } else if(op2==Top){
                return Top;
            } else if(op2==Bot){
                return False;
            } else {
                return False;
            }
        }
        else {
            return -1;
        }
    }
}**/