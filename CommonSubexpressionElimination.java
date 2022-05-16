/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.ana.Dominators;
import coins.backend.cfg.BasicBlk;
import coins.backend.util.BiLink;
import coins.backend.util.BiList;
import coins.backend.Op;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.sym.Symbol;
import coins.backend.util.ImList;

import java.util.Hashtable;
import java.util.Stack;

/**
 * SSA based common subexpression elimination.<br>
 * If the common subexpression is valid where in the other expressions,
 * this optimizer replace subexpressions which is used in the other expressions
 * into the temporary variable.
 * Also, the optimizer have Efficient Question Propagation (EQP). So, the 
 * subexpression is not valid clearly, the optimizer propagates the question,
 * "Is it valid subexpression?," to the predecessors.
 **/
class CommonSubexpressionElimination implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "CommonSubexpressionElimination"; }
  public String subject() {
    return "Common subexpression elimination on SSA form.";
  }

  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The threshold of debug print **/
  public static final int THR=SsaEnvironment.OptThr;
  /** Utility **/
  private Util util;
  /** The information about dominators **/
  private Dominators dom;
  /** The list of expressions **/
  private BiList expList;
  /** The list of PHI instructions **/
  private BiList phiList;
  /** The map for the expressions **/
  private Hashtable expMap;
  /** The map for the copy related expressions **/
  private Hashtable copyMap;
  /** The current function **/
  private Function f;
  /** Whether analyze the aliases of the memory object **/
  private boolean withMem;

  /**
   * Constructor.
   * @param e The environment of the SSA module
   **/
  public CommonSubexpressionElimination(SsaEnvironment e){
    env=e;
    withMem=!env.opt.isSet(OptionName.SSA_NO_MEMORY_ANALYSIS);

    if(withMem){
      env.println("  Common Subexpression Elimination With Memory "+
                    "on SSA form",SsaEnvironment.MsgThr);
    }
    else{
      env.println("  Common Subexpression Elimination Without Memory "+
                    "on SSA form",SsaEnvironment.MsgThr);
    }
  }

  /**
   * Do SSA based common subexpression elimination to the current function.
   * @param function The current function
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    MemoryAliasAnalyze alias=null;
    // If CSE with memory alias analysis, do below.
    if(withMem){
      env.println("****************** doing CSE with memory to "+
                  function.symbol.name,SsaEnvironment.MinThr);

      // Analyze about memory aliasing.
      alias=new MemoryAliasAnalyze(env,function);
    }
    // If CSE without memory alias analysis, do below.
    else{
      env.println("****************** doing CSE without memory to "+
                  function.symbol.name,SsaEnvironment.MinThr);
    }

    phiList=new BiList();
    //phiMap=new Hashtable();
    expList=new BiList();
    expMap=new Hashtable();
    copyMap=new Hashtable();
    dom=(Dominators)function.require(Dominators.analyzer);
    f=function;
    util=new Util(env,f);

    cse(f.flowGraph().entryBlk());

    //f.printIt(env.output);

    if(withMem){
      alias.annul();
    }

    env.println("",THR);

    return(true);
  }

  /**
   * Main algorithm of CSE.
   * @param blk The current basic block
   **/
  private void cse(BasicBlk blk){
    BiLink expSplit=expList.last();
    BiLink phiSplit=phiList.last();

    for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
      LirNode node=(LirNode)p.elem();

      switch(node.opCode){
        // If the current instruction is a PHI instruction.
        case Op.PHI:{
          // If the current LIR node is PHI instruction

          // If the map has the PHI instruction same as the current PHI
          // instruction
          boolean contain=false;
          for(BiLink q=phiList.first();!q.atEnd();q=q.next()){
            LirNode phiNode=(LirNode)q.elem();
            if(phiNode.nKids()==node.nKids()){
              contain=true;
              for(int i=1;i<phiNode.nKids();i++){
                if(!node.kid(i).equals(phiNode.kid(i))){
                  contain=false;
                  break;
                }
              }
              if(contain){
                // Register the copy assign expression into the map
                Symbol dst=((LirSymRef)node.kid(0)).symbol;
                Symbol ss=((LirSymRef)phiNode.kid(0)).symbol;
                env.println("CSE : replace phi node into copy assign ---> "+
                            node+" in block "+blk.id,THR);

                setCopyIntoMap(dst,ss,blk,p);
                break;
              }
            }
          }

          // If the map does not have the same PHI instruction as the current 
          // PHI instruction, but the arguments of the current PHI instruction
          // are all same.
          if(!contain){
            contain=true;
            LirNode replesent=null;
            for(int i=1;i<node.nKids();i++){
              if(replesent==null)
                replesent=node.kid(i).kid(0);
              else if(!replesent.equals(node.kid(i).kid(0))){
                contain=false;
                break;
              }
            }
            if(contain){
              if(replesent.opCode==Op.REG){
                // Register the copy assign expression into the map
                //env.output.println(node);
                Symbol dst=((LirSymRef)node.kid(0)).symbol;
                Symbol ss=((LirSymRef)replesent).symbol;
                env.println("CSE : replace phi node into copy assign ---> "+
                            node+" in block "+blk.id,THR);
                
                setCopyIntoMap(dst,ss,blk,p);
                break;
              }
              else if(replesent.opCode==Op.INTCONST ||
                      replesent.opCode==Op.FLOATCONST){
                // If the arguments of the current PHI instruction are the 
                // same and the constant value, then replace the current PHI 
                // instruction into the assign instruction.
                LirNode dst=node.kid(0).makeCopy(env.lir);
                LirNode src=replesent.makeCopy(env.lir);
                LirNode assignOp=env.lir.operator(Op.SET,dst.type,dst,src,
                                                  ImList.Empty);
                for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
                  LirNode n=(LirNode)q.elem();
                  if(n.opCode!=Op.PHI){
                    // Insert the assign instruction into the basic block
                    // which includes the current PHI instruction.
                    // The place to insert is just below all PHI instructions.
                    q.addBefore(assignOp);
                    p.unlink();
                    env.println("CSE : replace phi node into assign constant "+
                                "---> "+node+" in block "+blk.id,THR);
                    break;
                  }
                }
              }
            }
          }

          // If the map does not have the PHI instruction which has the same
          // arguments to the current PHI instruction and the arguments of the
          // current PHI instruction are not the same.
          if(!contain){
            // Put the current PHI instruction into the PHI map
            phiList.add(node);
          }
        

          break;
        }
        // If the current instruction is an assign instruction.
        case Op.SET:{
          // Replace the copy related variables into the original variables.
          replaceCopiedSymbol(node,blk);
          // Replace the subexpressions which are in the map into the variables
          // which are assigned by these subexpressions.
          replaceExpIntoSym(node,blk);

          // If the SET node is a copy assign
          if(node.kid(0).opCode==Op.REG && node.kid(1).opCode==Op.REG){
            Symbol dst=((LirSymRef)node.kid(0)).symbol;
            Symbol src=((LirSymRef)node.kid(1)).symbol;
            setCopyIntoMap(dst,src,blk,p);
          }
          // Put the expression into the map.
          else if(node.kid(0).opCode==Op.REG && 
                  node.kid(1).opCode!=Op.INTCONST &&
                  node.kid(1).opCode!=Op.FLOATCONST &&
                  node.kid(1).opCode!=Op.REG &&
                  node.kid(1).opCode!=Op.USE &&
                  node.kid(1).opCode!=Op.CLOBBER){

            // If the subexpression has MEM node and the SSA module did not
            // analyze the aliases of the memory object, then the optimizer
            // does not put the subexpression into the map or do EQP.
            // If the subexpression includes MEM node and the SSA module
            // analyzed the aliases of the memory object.
            BiList list=util.findTargetLir(node.kid(1),Op.MEM,new BiList());
            if(list.length()==0 || withMem){
              // for volatile
/**
              for(BiLink q=list.first();!q.atEnd();q=q.next()){
                LirNode n=(LirNode)q.elem();

              }
**/

              Symbol dst=((LirSymRef)node.kid(0)).symbol;
              expList.add(node.kid(1));
              expMap.put(node.kid(1),dst);
              env.println("CSE : put "+dst+" = "+node.kid(1)+" into the map",
                          THR);
            }
          }
          break;
        }
        case Op.CALL:{
          // Replace the copy related variables into the original variables.
          replaceCopiedSymbol(node,blk);
          // Replace the subexpressions which are in the map into the variables
          // which are assigned by these subexpressions.
          replaceExpIntoSym(node.kid(1),blk);

          break;
        }
        default:{
          // Replace the copy related variables into the original variables.
          replaceCopiedSymbol(node,blk);
          // Replace the subexpressions which are in the map into the variables
          // which are assigned by these subexpressions.
          replaceExpIntoSym(node,blk);
        }
      }      
    }

    // Replace the arguments of the PHI instructions.
    for(BiLink p=blk.succList().first();!p.atEnd();p=p.next()){
      BasicBlk succ=(BasicBlk)p.elem();
      for(BiLink q=succ.instrList().first();!q.atEnd();q=q.next()){
        LirNode succNode=(LirNode)q.elem();
        if(succNode.opCode==Op.PHI){
          // Replace the arguments of the PHI instructions in the successors.
          replaceCopiedSymbol(succNode,succ);
        }
        else break;
      }
    }

    // Iterate over the dominator tree.
    for(BiLink p=dom.kids[blk.id].first();!p.atEnd();p=p.next()){
      cse((BasicBlk)p.elem());
    }

    // Put off the work variables from the stack.
    if(!expSplit.atEnd())
      expList.split(expSplit.next());
    else
      expList.clear();

    if(!phiSplit.atEnd())
      phiList.split(phiSplit.next());
    else
      phiList.clear();
  }

  /**
   * Put the copy assign instructions into the map.
   * @param dst The destination symbol of the instruction
   * @param src The srouce symbol of the instruction
   * @param blk The basic block which includes the instruction
   * @param p The position of the instruction in the basic block
   **/
  private void setCopyIntoMap(Symbol dst,Symbol src,BasicBlk blk,BiLink p){
    if(dst==src) return;
      
    while(true){
      Symbol s=(Symbol)copyMap.get(src);
      if(s==null)break;
      src=s;
    }
    copyMap.put(dst,src);
    p.unlink();
    f.flowGraph().touch();
    env.println("CSE : remove copy assign ---> "+dst+" = "+src+
                " in block "+blk.id,THR);
  }

  /**
   * If the variables in subexpressions are copy related, then replace them
   * into the original ones.
   * @param node The current subexpressions
   * @param blk The basic block which includes the current subexpression
   **/
  private void replaceCopiedSymbol(LirNode node,BasicBlk blk){
    Stack stack=new Stack();
    stack.push(node);
    
    // If the variables used in the current subexpression are copy related,
    // then replace them into the original ones.
    while(!stack.empty()){
      LirNode n=(LirNode)stack.pop();
      for(int i=0;i<n.nKids();i++){
        if(n.kid(i).opCode==Op.REG){
          Symbol s=(Symbol)copyMap.get(((LirSymRef)n.kid(i)).symbol);
          if(s!=null){
            env.println("CSE : replace symbol "+
                        ((LirSymRef)n.kid(i)).symbol+" --> "+s+
                        " in block "+blk.id,THR);
            LirNode newReg=env.lir.symRef(Op.REG,n.kid(i).type,s,
                                          ImList.Empty);
            n.setKid(i,newReg);
            f.flowGraph().touch();
          }
        }
        else stack.push(n.kid(i));
      }
    }
  }

  /**
   * If the map already has the current subexpression, then replace them
   * into the variables which are assigned by the subexpression.
   * @param node The current subexpression
   * @param blk The basic block which includes the current subexpression
   **/
  private void replaceExpIntoSym(LirNode node,BasicBlk blk){
    Stack stack=new Stack();
    stack.push(node);

    while(!stack.empty()){
      LirNode tempNode=(LirNode)stack.pop();
      for(int i=0;i<tempNode.nKids();i++){
        boolean match=false;
        for(BiLink p=expList.first();!p.atEnd();p=p.next()){
          LirNode listElem=(LirNode)p.elem();
          if(tempNode.kid(i).equals(listElem)){
            Symbol s=(Symbol)expMap.get(listElem);
            env.print("CSE : reconstruct the expression "+node+" ---> ",THR);
            LirNode newReg=env.lir.symRef(Op.REG,listElem.type,s,ImList.Empty);
            tempNode.setKid(i,newReg);
            env.println(node+" in block "+blk.id,THR);

            match=true;
            break;
          }
        }
        if(!match){
          stack.push(tempNode.kid(i));
        }
      }
    }
  }
}
