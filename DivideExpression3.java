/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import java.util.ArrayList;

import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.Type;
import coins.backend.util.BiLink;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.Op;
import coins.backend.util.ImList;
import coins.backend.sym.Symbol;

/**
 * Divide expressions into 3 address expression.
 **/
class DivideExpression3 implements LocalTransformer{ 
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "DivideExpression"; }
  public String subject() {
    return "Divide expression into three adress code on SSA form.";
  }

 /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The current symbol table of the SSA module **/
  private SsaSymTab sstab;
  /** The utility of the SSA module **/
  private Util util;
  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.OptThr;
  /** The name of the symbol which the optimzer uses to make the temporary
      variables **/
  public static final String DIVEX="_divex";
  
//  Print print;
  /**
   * Constructor
   * @param e The environment of the SSA module
   * @param symtab The current symbol table
   **/
  public DivideExpression3(SsaEnvironment e,SsaSymTab symtab){
    env=e;
    sstab=symtab;
    env.println("  Divide Expressions into 3 Address Expression",
                SsaEnvironment.MsgThr);
  }

  /**
   * Divide the expressions into 3 address expression.
   * @param f The current function
   * @param args The list of options
   **/
  public boolean doIt(Function f,ImList args){
    env.println("****************** doing DIVEX to "+f.symbol.name,
                SsaEnvironment.MinThr);

    util = new Util(env, f);
//    print = new Print(f);
    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        q.setElem(divide(node,q,false,false));
      }
    }

    env.println("",THR);

    f.touch();
    return(true);
  }

  
  LirNode divDefUseNode(LirNode node, BiLink link){
	  LirNode newNode = null;
	  Symbol dstSym=sstab.newSsaSymbol(DIVEX,node.type);
      // null if the type is aggregate
      if(dstSym!=null){
        LirNode nn=env.lir.symRef(Op.REG,dstSym.type,dstSym,ImList.Empty);
        newNode=env.lir.operator(Op.SET,node.type,nn,node.kid(1),ImList.Empty);
        link.addBefore(newNode);
      }
      return newNode;
  }
  
  
  boolean defUseNode(LirNode node){
      if(node.opCode!=Op.SET || node.kid(0).opCode!=Op.REG)return false;
      if(node.kid(1).nKids()==0){
    	  return node.kid(1).equals(node.kid(0));
      }else if(node.kid(1).nKids()==1){
    	  return (node.kid(1).kid(0).equals(node.kid(0)));
      }else if(node.kid(1).nKids()==2){
    	  return (node.kid(1).kid(0).equals(node.kid(0)) || node.kid(1).kid(1).equals(node.kid(0)));
      }

      return false;
  }
  
  
  LirNode getNewVar(LirNode exp){
	  Symbol dstSym = sstab.newSsaSymbol(DIVEX, exp.type);
	  LirNode nn = env.lir.symRef(Op.REG, exp.type, dstSym, ImList.Empty);
	  return nn;
  }
  
  
  boolean checkType(LirNode exp){
	  char type=Type.toString(exp.type).charAt(0);
	  return (type=='I' || type=='F');
  }
  
  
  LirNode createNewLoad(LirNode exp) {
	  LirNode newVar = getNewVar(exp);
	  LirNode setExpr = env.lir.operator(Op.SET, exp.type, newVar, exp, ImList.Empty);
	  return setExpr;
  }
  
  
  LirNode createNewStore(LirNode exp) {
	  LirNode newVar = getNewVar(exp);
	  LirNode setExpr = env.lir.operator(Op.SET, exp.type, exp, newVar, ImList.Empty);
	  return setExpr;
  }
  
  
  void collectVars(LirNode exp, ArrayList vars){
	  for(int i=0;i<exp.nKids();i++){
		  if(exp.kid(i).opCode==Op.REG){
			  vars.add(exp.kid(i));
		  }else if(exp.kid(i).nKids()>0){
			  collectVars(exp.kid(i),vars);
		  }
	  }
  }
  
  
  void div(LirNode exp,BiLink p){
	  int num = exp.nKids();
	  if(exp.opCode==Op.CALL)num=num-1;
		for(int i=0;i<num;i++){
			if(exp.kid(i).opCode==Op.MEM && checkType(exp.kid(i))){
				LirNode newNode = createNewLoad(exp.kid(i));
        // Simplify mem address
        if(newNode.nKids() > 1) {
          LirNode n1 = util.trans(newNode.kid(1).makeCopy(env.lir));
          newNode.setKid(1, n1);
        }
        //
				exp.setKid(i, newNode.kid(0).makeCopy(env.lir));
				div(newNode.kid(1),p);
				p.addBefore(newNode.makeCopy(env.lir));
			}
			if(exp.kid(i).nKids()>0){
				div(exp.kid(i),p);
			}
		}
	}
  
  
  /**
   * x=a[x] -> t=a[x];x=t;
   * @param node
   */
  void divLoad(LirNode node, BiLink p){
	  ArrayList vars = new ArrayList();
	  collectVars(node.kid(1),vars);
	  if(vars.contains(node.kid(0))){
		  LirNode newVar = getNewVar(node);
		  LirNode newLoad = node.makeCopy(env.lir);
		  newLoad.setKid(0, newVar);
		  p.addBefore(newLoad.makeCopy(env.lir));
		  node.setKid(1, newVar);
	  }
  }
  
  
  boolean containVar(LirNode var, LirNode exp){
	  for(int i=0;i<exp.nKids();i++){
		  if(exp.kid(i).equals(var)){
			  return true;
		  }else if(exp.kid(i).nKids()>0){
			  if(containVar(var,exp.kid(i)))
				  return true;
		  }
	  }
	  return false;
  }
  
  
  /**
   * Divide the expression into 3 address expression recursively.
   * @param node The current LIR node
   * @param link The place where the new expression attachs to
   * @param setSrc Whether the current LIR node is from the source operands
   *               of the SET operator
   * @param setDst Whether the current LIR node is from the destination
   *               operands of the SET operator
   * @return The divided LIR node
   **/
  LirNode divide(LirNode node,BiLink link,boolean setSrc,boolean setDst){
    LirNode result;

    switch(node.opCode){
      // memory operator
      case Op.MEM:{
        // Simple constant calculation
        LirNode copied;
        if(node.nKids() > 1) {

          copied = node.makeCopy(env.lir);
          copied.setKid(1, util.trans(copied.kid(1)));
        } else {
          copied = node;
        }
        if(checkType(copied)){
        	if(setDst){
        		LirNode newNode = createNewStore(copied);
        		link.addAfter(newNode);
        		result = newNode.kid(1);
        	}
        	else{
        		result = node;
        		div(copied,link);
        		LirNode newNode = createNewLoad(copied);
        		link.addBefore(newNode.makeCopy(env.lir));
        		result = newNode.kid(0);
        	}
        }else{
        	result = copied;
        }
        break;
      }
      // unary operators
      case Op.NEG:
      case Op.BNOT:
      // cast operators
      case Op.CONVSX:
      case Op.CONVZX:
      case Op.CONVIT:
      case Op.CONVFX:
      case Op.CONVFT:
      case Op.CONVFI:
      case Op.CONVFS:
      case Op.CONVFU:
      case Op.CONVSF:
      case Op.CONVUF:{
        LirNode leftNode=divide(node.kid(0),link,false,false);

        LirNode oper=env.lir.operator(node.opCode,node.type,leftNode,
                                      node.opt);
        result=oper;

        if(setSrc){
          result=oper;
        }
        else{
          Symbol dstSym=sstab.newSsaSymbol(DIVEX,node.type);
          // null if the type is aggregate
          if(dstSym!=null){
            result=env.lir.symRef(Op.REG,dstSym.type,dstSym,ImList.Empty);

            LirNode dst=env.lir.operator(Op.SET,node.type,result,oper,
                                         node.opt);
            link.addBefore(dst);
          }
          else
            result=oper;
          //env.output.println(dst);
        }
        break;
      }
      // binary operators
      case Op.BAND:
      case Op.BOR:
      case Op.BXOR:
      case Op.LSHS:
      case Op.LSHU:
      case Op.RSHS:
      case Op.RSHU:
      case Op.SUB:
      case Op.DIVS:
      case Op.DIVU:
      case Op.MODS:
      case Op.MODU:
      case Op.MUL:
      case Op.ADD:{
        LirNode leftNode=divide(node.kid(0),link,false,false);
        LirNode rightNode=divide(node.kid(1),link,false,false);

        LirNode oper=env.lir.operator(node.opCode,node.type,leftNode,
                                      rightNode,node.opt);
        if(setSrc){
          result=oper;
        }
        else{
          Symbol dstSym=sstab.newSsaSymbol(DIVEX,node.type);
          // null if the type is aggregate
          if(dstSym!=null){
            result=env.lir.symRef(Op.REG,dstSym.type,dstSym,ImList.Empty);

            LirNode dst=env.lir.operator(Op.SET,node.type,result,oper,
                                         node.opt);
            link.addBefore(dst);
          }
          else
            result=oper;
          //env.output.println(dst);
        }

        break;
      }
      // The condition operator
      case Op.TSTEQ:
      case Op.TSTNE:
      case Op.TSTLTS:
      case Op.TSTLES:
      case Op.TSTGTS:
      case Op.TSTGES:
      case Op.TSTLTU:
      case Op.TSTLEU:
      case Op.TSTGTU:
      case Op.TSTGEU:{
        result=node.makeCopy(env.lir);
        // left side operand
        result.setKid(0,divide(result.kid(0),link,false,false));
        // right side operand
        result.setKid(1,divide(result.kid(1),link,false,false));

        break;
      }
      case Op.SET:{
    	  result=node.makeCopy(env.lir);
    	  if(checkType(node)){
    		  // source
    		  if(result.kid(0).opCode==Op.MEM){
    			  // newNode is Load instruction.
    			  // (SET (MEM "") (...))  -> (SET (REG t ) (...)); (SET (MEM "") (REG t))
    			  LirNode newNode = createNewLoad(result.kid(1));
    			  result.setKid(1, newNode.kid(0));
    			  div(newNode.kid(1),link);
    			  link.addBefore(newNode.makeCopy(env.lir));
			  
    			  div(result.kid(0),link);
    			  if(result.kid(1).opCode==Op.MEM){
    				  divLoad(result,link);
    			  }
			  
    			  if(result.kid(1).opCode==Op.MEM && containVar(result.kid(0),result.kid(1))){
    				  LirNode newLoad = createNewLoad(result.kid(1));
    				  result.setKid(1, newLoad.kid(0));
    				  link.addBefore(newLoad.makeCopy(env.lir));
    			  }
    			  div(result.kid(1),link);
        		  LirNode n=divide(result.kid(1),link,true,false);
        		  result.setKid(1,n);
        		  // destination
            	  if(defUseNode(result)){
            		  result.setKid(1,(divDefUseNode(result,link)).kid(0));
            	  }
    		  }
    		  else if(result.kid(1).opCode!=Op.MEM){
    			  div(result.kid(1),link);
        		  LirNode n=divide(result.kid(1),link,true,false);
        		  result.setKid(1,n);
        		  // destination
            	  if(defUseNode(result)){
            		  result.setKid(1,(divDefUseNode(result,link)).kid(0));
            	  }
    		  }
    	  }
    	  break;
      }
      case Op.CALL:{
        result=node.makeCopy(env.lir);
        // 1st operand
        result.setKid(0,divide(result.kid(0),link,false,false));
        // 2nd operand
        result.setKid(1,divide(result.kid(1),link,false,false));
        // 3ed operand
        result.setKid(2,divide(result.kid(2),link,false,true));

        break;
      }
      case Op.JUMPC:{
        // 1st operand
        result=node.makeCopy(env.lir);
        result.setKid(0,divide(result.kid(0),link,false,false));

        break;
      }
      case Op.JUMPN:{
        // 1st operand
        result=node.makeCopy(env.lir);
        result.setKid(0,divide(result.kid(0),link,false,false));

        break;
      }
      case Op.LIST:{
        result=node.makeCopy(env.lir);
        for(int i=0;i<result.nKids();i++){
          //result.setKid(i,divide(result.kid(i),link,false,false));
          result.setKid(i,divide(result.kid(i),link,setSrc,setDst));
        }

        break;
      }
      case Op.FRAME:
      case Op.STATIC:{
        if(env.opt.isSet("ssa-extend-divex")){
          Symbol dstSym=sstab.newSsaSymbol(DIVEX,node.type);
          result=env.lir.symRef(Op.REG,dstSym.type,dstSym,ImList.Empty);
          LirNode dst=env.lir.operator(Op.SET,node.type,result,
                                       node.makeCopy(env.lir),node.opt);
          link.addBefore(dst);
          
          break;
        }
      }
      // nothing to do for LIR below
      case Op.PROLOGUE:
      case Op.EPILOGUE:
      case Op.PHI:
      case Op.JUMP:
      // Leaf
      case Op.REG:
      case Op.INTCONST:
      case Op.FLOATCONST:
      default:{
        result=node.makeCopy(env.lir);
      }
    }
    //env.output.println("##### "+result);
    
//    print.print(node);
//    System.out.println("result:"+result);
    return(result.makeCopy(env.lir));
  }
}
