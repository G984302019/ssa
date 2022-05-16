/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.Function;
import coins.backend.util.BiLink;
import coins.backend.cfg.BasicBlk;
import coins.backend.util.BiList;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirLabelRef;
import coins.backend.Op;
import coins.backend.Data;
import coins.backend.sym.Label;
import coins.backend.util.ImList;
import coins.backend.LocalTransformer;

/**
 * Concatenate basic blocks.
 * This module concatenate block A and B descibed below:
 * The basic block A has only one predecessor B.
 * The basic block B has only one successor A.
 * There are no branches in A and B. Also, there are no junction in
 * A and B.
 **/
class ConcatBlks implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "ConcatBlks"; }
  public String subject() {
    return "Concatenate some basic blocks.";
  }

  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.OptThr;
  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The current function **/
  private Function f;

  /**
   * Constructor
   * @param e The environment of the SSA module
   **/
  ConcatBlks(SsaEnvironment e){
    env=e;
    env.println("  Concatenate Basic Blocks",SsaEnvironment.MsgThr);
    //f.printIt(env.output);
  }

  /**
   * Concatenate basic blocks.
   * @param func The current function
   * @param args The list of options
   **/
  public boolean doIt(Function func,ImList args){
    f=func;
    env.println("****************** doing CBB to "+f.symbol.name,
                SsaEnvironment.MinThr);

    BiList removeList=new BiList();
    boolean changed=true;
    while(changed){
      changed=false;
      removeList.clear();
      for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
        BasicBlk blk=(BasicBlk)p.elem();
        if(!removeList.contains(blk) && blk.succList().length()==1){
          BasicBlk succ=(BasicBlk)blk.succList().first().elem();
          if(!succ.equals(f.flowGraph().exitBlk()) &&
             succ.predList().length()==1){
            changed=true;
            blk.instrList().last().unlink();
            blk.instrList().last().addAllAfter(succ.instrList());
            replaceLabelInPhi(succ.succList(),succ.label(),blk.label());
            succ.clearEdges();
            blk.maintEdges();
            f.touch();
            removeList.add(succ);
          }
        }
      }
      for(BiLink p=removeList.first();!p.atEnd();p=p.next()){
        BasicBlk blk=(BasicBlk)p.elem();
        f.flowGraph().basicBlkList.remove(blk);
        f.touch();
        env.println("CBB : remove blk["+blk.id+"]",THR);
      }
    }

    //f.printIt(env.output);
    env.println("",THR);
    return(true);
  }

  /**
   * Replace the label in the phi instruction.
   * @param list The list of LIR
   * @param org The original label
   * @param rep The target label
   **/
  private void replaceLabelInPhi(BiList list,Label org,Label rep){
    for(BiLink p=list.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        if(node.opCode!=Op.PHI) break;

        for(int i=1;i<node.nKids();i++){
          if(((LirLabelRef)node.kid(i).kid(1)).label.equals(org)){
            //env.output.println("find");
            node.kid(i).setKid(1,env.lir.labelRefVariant(rep));
          }
        }
      }
    }
  }
}
