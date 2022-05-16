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
import coins.backend.util.BiList;
import coins.backend.util.ImList;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.lir.LirIconst;
import coins.backend.lir.LirFconst;
import coins.backend.sym.Symbol;

import java.util.Hashtable;
import java.util.Stack;

/**
 * Eliminate the redundant PHI instructions.<br><br>
 * The redundant PHI instruction is defined as follows:<br>
 * 1) x=phi(x,x,x) (remove only)<br>
 * 2) x=phi(y,y,y) (regard as `x=y' and do copy propagation)<br>
 * 3) x=phi(y,y,x) (regard as `x=y' and do copy propagation)
 **/
class RedundantPhiElimination implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "RedundantPhiElimination"; }
  public String subject() {
    return "Eliminate redundant phi-instructin.";
  }

  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.OptThr;
  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The map for copy propagation **/
  private Hashtable copyMap;

  /**
   * Constructor
   * @param e The environment of the SSA module
   **/
  public RedundantPhiElimination(SsaEnvironment e){
    env=e;
    env.println("  Redundant Phi Instruction Elimination",
                SsaEnvironment.MsgThr);
  }

  /**
   * Eliminate the redundant PHI instructions.
   * @param function The current funciton
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    env.println("****************** doing RPE to "+function.symbol.name,
                SsaEnvironment.MinThr);
    FlowGraph g=function.flowGraph();

    copyMap=new Hashtable();
    boolean changed=true;
    while(changed){
      changed=false;
      for(BiLink p=g.basicBlkList.first();!p.atEnd();p=p.next()){
        BasicBlk blk=(BasicBlk)p.elem();
        BiList expList=new BiList();
        for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
          LirNode node=(LirNode)q.elem();

          // Refer to the map and replace the copy related variables into the
          // original ones.
          Stack stack=new Stack();
          stack.push(node);
          while(!stack.empty()){
            LirNode n=(LirNode)stack.pop();
            for(int j=0;j<n.nKids();j++){
              if(n.kid(j).opCode==Op.REG){
                LirNode t=(LirNode)copyMap.get(((LirSymRef)n.kid(j)).symbol);
                if(t!=null){
                  env.println("RPE : replace "+n.kid(j)+" to "+t+
                              " of "+node+" in block "+blk.id,THR);
                  n.setKid(j,t.makeCopy(env.lir));
                }
              }
              else{
                stack.push(n.kid(j));
              }
            }
          }
          if(node.opCode==Op.PHI){
            //env.output.println(node);

            // The redundant PHI instructions defined as follows:
            // 1) x=phi(x,x,x) (remove only)
            // 2) x=phi(y,y,y) (regard as `x=y' and copy propagation)
            // 3) x=phi(y,y,x) (regard as `x=y' and copy propagation)

            // Keep the destination variable.
            Symbol dst=((LirSymRef)node.kid(0)).symbol;
            // Check whether the arguments of the current PHI instruction
            // are the same or same as destination variable.
            boolean isOk=true;
            boolean isReg=true;
            Symbol src=null;
            Number value=null;
            for(int i=1;i<node.nKids();i++){
              LirNode srcNode=node.kid(i).kid(0);
              if(isOk){
                if(srcNode.opCode==Op.REG){
                  if(!isReg){
                    isOk=false;
                    break;
                  }
                  isReg=true;
                  Symbol s=((LirSymRef)srcNode).symbol;
                  if(src==null) src=s;
                  else if(!src.equals(s) && !dst.equals(s)){
                    isOk=false;
                    break;
                  }
                }
                else{ // constant
                  if(isReg && src!=null){
                    isOk=false;
                    break;
                  }
                  isReg=false;

                  if(srcNode.opCode==Op.INTCONST){
                    long v=((LirIconst)srcNode).value;
                    if(value==null)
                      value=new Long(v);
                    else if(!value.equals(new Long(v))){
                      isOk=false;
                      break;
                    }
                  }
                  else if(srcNode.opCode==Op.FLOATCONST){
                    double v=((LirFconst)srcNode).value;
                    if(value==null)
                      value=new Double(v);
                    else if(!value.equals(new Double(v))){
                      isOk=false;
                      break;
                    }
                  }
                }
              }
            }
            // The current PHI instruction is redundant.
            if(isOk){
              changed=true;
              // If the arguments are the register variable, the check if it
              // is the same as the destination variable. If it is the same 
              // register variable, then remove only. Otherwise, make a copy
              // assign statement.
              if(isReg){
                // If the argument is the register variable.
                if(dst.equals(src)){
                  env.println("RPE : Just Remove "+node+" in block "+
                              blk.id,THR);
                  q.unlink();
                  g.touch();
                }
                else{
                  env.println("RPE : Remove and replace "+node+" in block "+
                              blk.id,THR);
                  LirNode newReg=env.lir.symRef(Op.REG,src.type,src,
                                                ImList.Empty);
                  copyMap.put(dst,newReg);
                  q.unlink();
                  g.touch();
                }
              }
              // If the argument is a integer constant, then replace the 
              // redundant PHI instruction into assign statement.
              else{
                LirNode cnst=null;

                if(value instanceof Long)
                  cnst=env.lir.iconst(node.type,value.longValue(),
                                      ImList.Empty);
                else if(value instanceof Double)
                  cnst=env.lir.fconst(node.type,value.doubleValue(),
                                      ImList.Empty);

                env.println("RPE : Remove and replace "+node+" in block "+
                            blk.id,THR);

                copyMap.put(dst,cnst);
                q.unlink();
                g.touch();
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
