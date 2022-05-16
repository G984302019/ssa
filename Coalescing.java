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
import coins.backend.ana.InterferenceGraph;

import java.util.Stack;

/**
 * Coalescing<br>
 * Perform coalescing proposed by Chaitin after the back translation to 
 * normal form. This coalesces copy-related variables whose live ranges do not
 * interfere each other. In general, after the back translation from SSA form,
 * there are some copy assign statements in the program. Some copy assign 
 * statements only change the names of variables, that is, they are useless. 
 * Coalescing these variables eliminates the useless copy assign statements. 
 * This optimization is done after the back translation from SSA form. 
 **/
class Coalescing implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "Coalescing"; }
  public String subject() {
    return "Coalesce variables.";
  }

  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The threshold of debug print **/
  public static final int THR=SsaEnvironment.OptThr;

  /**
   * Constructor
   * @param e The environment of the SSA module
   **/
  public Coalescing(SsaEnvironment e){
    env=e;
    env.println("  Coalescing by Chaitin",SsaEnvironment.MsgThr);
  }

  /**
   * Do coalescing to the current function.
   * @param function The current fucntion
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    env.println("****************** doing CHAIC to "+function.symbol.name,
                SsaEnvironment.MinThr);
    FlowGraph g=function.flowGraph();
    Symbol dst=null;
    Symbol src=null;
    boolean changed=true;

    while(changed){
      changed=false;
      // Get the information about copy assign expressions.
      for(BiLink p=g.basicBlkList.first();!p.atEnd();p=p.next()){
        BasicBlk blk=(BasicBlk)p.elem();
        boolean flag=false;
        for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
          src=null;
          dst=null;
          
          LirNode node=(LirNode)q.elem();
          if(node.opCode==Op.SET && 
             node.kid(0).opCode==Op.REG && node.kid(1).opCode==Op.REG){
            
            dst=((LirSymRef)node.kid(0)).symbol;
            src=((LirSymRef)node.kid(1)).symbol;
            
            InterferenceGraph ig;
            ig=(InterferenceGraph)function.require(InterferenceGraph.analyzer);
            
            if(!ig.interfere(src,dst)){
              env.println("CHAIC : remove "+node+" in block "+blk.id,THR);
              q.unlink();
              g.touch();
              changed=true;
              flag=true;
              break;
            }
          }
        }
        if(flag) break;
      }
      
      if(dst!=null && src!=null){
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
                  if(s.equals(dst)){
                    env.println("CHAIC : in "+node,THR);
                    env.print("CHAIC : "+n.kid(i)+" ---> ",THR);
                    LirNode newNode=env.lir.symRef(n.kid(i).opCode,
                                                   n.kid(i).type,
                                                   src,ImList.Empty);
                                                   
                    n.setKid(i,newNode);
                    env.println(n.kid(i)+" in block "+blk.id,THR);
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
      }
    }
    env.println("",THR);

    return(true);
  }
}
