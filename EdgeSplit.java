/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.util.ImList;
import coins.backend.Function;
import coins.backend.Op;
import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.cfg.BasicBlk;
import coins.backend.util.BiLink;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirLabelRef;
import coins.backend.sym.Label;

/**
 * Split the critical edges. This optimizer treat the PHI instructions safely.
 **/
class EdgeSplit implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "EdgeSplit"; }
  public String subject() {
    return "Split critical edges on SSA form.";
  }

  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The current function **/
  private Function f;
  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.OptThr;

  /**
   * Constructor
   * @param e The environment of the SSA module
   **/
  public EdgeSplit(SsaEnvironment e){
    env=e;

    env.println("  Split Critical Edges",SsaEnvironment.MsgThr);
  }

  /**
   * Split the critical edges in each functions.
   * If find the critical edge between b1 and b2, then make a new basic block
   * b3 and insert onto the edge. If the PHI instruction is in the b2, then
   * maintain the arguments of it.
   * @param function The current function
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    env.println("****************** doing ESPLT to "+function.symbol.name,
                SsaEnvironment.MinThr);
    f=function;

    // Split critical edges.
    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      LirNode lastNode=(LirNode)blk.instrList().last().elem();

      // There are more than one successors.
      if(lastNode.opCode==Op.JUMPC || lastNode.opCode==Op.JUMPN){
        Label[] succ=lastNode.getTargets();
        for(int i=0;i<succ.length;i++){
          // There are more than one predecessors.
          if(succ[i].basicBlk().predList().length()>1){
            env.println("ESPLT : find critical edge "+blk.label()+
                        " --> "+succ[i],THR);
            // Make a new basic block on the critical edge.
            insertNewBlk(blk,succ[i].basicBlk());
            f.touch();
          }
        }
      }
    }
    //f.printIt(env.output);

    env.println("",THR);

//    if(!checkEdge()){
//      System.err.println("ESPLT : fail");
//      System.exit(1);
//    }

    return(true);
  }

/** Debug Method
  private boolean checkEdge(){
    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        if(node.opCode==Op.PHI){
          if(blk.predList().length()!=(node.nKids()-1))
            return(failEsplt(blk,node));
        }
        else break;
      }
    }
    return(true);
  }

  private boolean failEsplt(BasicBlk blk,LirNode node){
    env.output.println(f.symbol.name);
    env.output.println("blk["+blk.id+"]("+blk.label()+")");
    env.output.println("  pred "+blk.predList().length()+" != phi "+
                       (node.nKids()-1));
    env.output.println(node);

    return(false);
  }
**/

  /**
   * Maint all edges on the current CFG.
   * @param newBlk A new basic block
   * @param fromBlk The basic block which the critical edge from
   * @param toBlk The basic block which the critical edge to
   **/
  private void maintEdges(BasicBlk newBlk,BasicBlk fromBlk,BasicBlk toBlk){
    newBlk.maintEdges();
    toBlk.maintEdges();
    fromBlk.maintEdges();
    env.println("ESPLT : insert "+newBlk.label()+
                " and maint edges "+fromBlk.label()+" --> "+
                newBlk.label()+" --> "+toBlk.label(),THR);
  }

  /**
   * Make a new basic block and insert it on the critical edge.
   * @param fromBlk The basic block which the critical edge from
   * @param toBlk The basic block which the critical edge to
   **/
  private void insertNewBlk(BasicBlk fromBlk,BasicBlk toBlk){
    // Make a new block and set it before the toBlk.
    BasicBlk newBlk=f.flowGraph().insertNewBlkBefore(toBlk);
    // Set the edge between the newBlock and toBlk.
    LirNode newJump=(LirNode)newBlk.instrList().last().elem();
    LirLabelRef newLab=(LirLabelRef)env.lir.
      labelRefVariant(((LirLabelRef)newJump.kid(0)).label);
    newJump.setKid(0,newLab);

    // maint the edges between fromBlk and newBlk
    LirNode jumpNode=(LirNode)fromBlk.instrList().last().elem();
    Label lab1=toBlk.label();

    if(jumpNode.opCode==Op.JUMPC){
      for(int j=1;j<jumpNode.nKids();j++){
        LirLabelRef orgLab=(LirLabelRef)jumpNode.kid(j);
        Label lab2=orgLab.label;
                
        // If the successor is the target of the jump node, 
        // then replace it to the new block.
        if(lab1.basicBlk()==lab2.basicBlk()){
          // Make a new label node and set it to jump node.
          LirNode newLabel=env.lir.labelRefVariant(newBlk.label());
          jumpNode.setKid(j,newLabel);
          maintPhiParam(newLab,orgLab,toBlk,newBlk.label());
          maintEdges(newBlk,fromBlk,toBlk);
          break;
        }
      }
    }
    else{ // jumpNode is JUMPN node
      //env.output.println(jumpNode);
      boolean changed=false;
      for(int j=0;j<jumpNode.kid(1).nKids();j++){
        LirLabelRef orgLab=(LirLabelRef)jumpNode.kid(1).kid(j).kid(1);
        Label lab2=orgLab.label;

        // If the successor is the target of the jump node, 
        // then replace it to the new block.
        if(lab1.basicBlk()==lab2.basicBlk()){
          // Make a new label node and set it to jump node.
          LirNode newLabel=env.lir.labelRefVariant(newBlk.label());
          jumpNode.kid(1).kid(j).setKid(1,newLabel);
          maintPhiParam(newLab,orgLab,toBlk,newBlk.label());
          maintEdges(newBlk,fromBlk,toBlk);
          changed=true;
          break;
        }
      }
      if(!changed){
        LirLabelRef orgLab=(LirLabelRef)jumpNode.kid(2);
        Label lab2=orgLab.label;

        // If the successor is the target of the jump node, 
        // then replace it to the new block.
        if(lab1.basicBlk()==lab2.basicBlk()){
          // Make a new label node and set it to jump node.
          LirNode newLabel=env.lir.labelRefVariant(newBlk.label());
          jumpNode.setKid(2,newLabel);
          maintPhiParam(newLab,orgLab,toBlk,newBlk.label());
          maintEdges(newBlk,fromBlk,toBlk);
        }
      }
    }
  }

  /**
   * Maint the arguments of the PHI instructions which are in the basic blocks
   * that are the target of the critical edges.
   * @param newLab The label of a new basic block
   * @param orgLab The label of the original predecessor
   * @param blk The target basic block which will be a successor
   * @param label The label of a new basic block
   **/
  private void maintPhiParam(LirLabelRef newLab,LirLabelRef orgLab,
                             BasicBlk blk,Label label){
    for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
      LirNode node=(LirNode)p.elem();
      
      if(node.opCode==Op.PHI){
        // Iterate all over the argument of the PHI instruction.
        for(int i=1;i<node.nKids();i++){
          LirNode args=node.kid(i);
                
          // Store the edge between the block and the successor.
          LirLabelRef edge=(LirLabelRef)args.kid(2);

          // If the label L1 in the PHI instruction's argument and the 
          // label L2 in the block are the same, then replace L1 to the
          // label L3 which is in the new block.
          LirLabelRef labInPhi=(LirLabelRef)args.kid(2);
          if(labInPhi==orgLab){
            args.setKid(1,env.lir.labelRefVariant(label));
            args.setKid(2,newLab);
          }
        }
      }
    }
  }
}
