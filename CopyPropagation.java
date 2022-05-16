/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.Op;
import coins.backend.cfg.FlowGraph;
import coins.backend.cfg.BasicBlk;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.sym.Symbol;

import java.util.Hashtable;
import java.util.Stack;

/**
 * Copy propagation<br>
 * Step1:<br>
 *  Find copy assign expressions and store the right side variable of them
 *  to hash table as a value.
 *  The key which is corresponding to the value is the left side variable
 *  of copy assign expressions.
 *  Then, remove copy assign expressions from LIR list of BBlocks.
 * Step2:<br>
 *  Rename variable names.
 *  This routine renames the variable names which is used in left side of 
 *  copy assign expressions to the variable names which is used in right
 *  side of the same copy assign expression.
 **/
class CopyPropagation implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "CopyPropagation"; }
  public String subject() {
    return "Copy propagation on SSA form.";
  }

  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.OptThr;

  /**
   * Constructor
   * @param e The environment of the SSA module
   **/
  public CopyPropagation(SsaEnvironment e){
    env=e;
    env.println("  Copy Propagation on SSA form",SsaEnvironment.MsgThr);
  }

  /**
   * Do copy propagation.
   * @param function The current function
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    env.println("****************** doing CPYP to "+function.symbol.name,
                SsaEnvironment.MinThr);
    FlowGraph g=function.flowGraph();
    Hashtable variableMap=new Hashtable();

    // Get the information about copy assign expressions.
    for(BiLink p=g.basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        if(node.opCode==Op.SET && 
           node.kid(0).opCode==Op.REG && node.kid(1).opCode==Op.REG){

          Symbol key=((LirSymRef)node.kid(0)).symbol;
          Symbol val=((LirSymRef)node.kid(1)).symbol;

          if(variableMap.containsKey(key)){
            System.err.println("CopyPropagation.java : There is not SSA form");
            System.exit(1);
          }

          Symbol s=val;
          while(true){
            s=(Symbol)variableMap.get(s);
            if(s==null)break;
            val=s;
          }

          variableMap.put(key,val);
          q.unlink();
          g.touch();
          env.println("CPYP : remove "+node+" in block "+blk.id,THR);
        }
      }
    }

    // Replace copied variable
    for(BiLink p=g.basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();

        Stack stack=new Stack();
        stack.push(node);
        while(!stack.empty()){
          LirNode n=(LirNode)stack.pop();
          for(int i=0;i<n.nKids();i++){
            if(n.kid(i).opCode==Op.REG){
              Symbol s=((LirSymRef)n.kid(i)).symbol;
              Symbol newSym=null;
              while(variableMap.get(s)!=null){
                newSym=(Symbol)variableMap.get(s);
                if(newSym==null){
                  newSym=s;
                  break;
                }
                s=newSym;
              }

              if(newSym!=null){
                env.println("CPYP : in "+node+" in block "+blk.id,THR);
                env.print("CPYP : "+n.kid(i)+" ---> ",THR);
                LirNode newNode=env.lir.symRef(n.kid(i).opCode,n.kid(i).type,
                                               newSym,ImList.Empty);
                n.setKid(i,newNode);
                env.println(n.kid(i).toString(),THR);
                g.touch();
              }
            }
            else{
              stack.push(n.kid(i));
            }
          }
        }
      }
    }
    env.println("",THR);

    return(true);
  }
}
