/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.cfg.FlowGraph;
import coins.backend.util.BiList;
import coins.backend.util.BiLink;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.Op;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirLabelRef;
import coins.backend.ana.ControlDependences;
import coins.backend.util.ImList;
import coins.backend.sym.Symbol;
import coins.backend.lir.LirIconst;
import coins.backend.lir.LirFconst;
import coins.backend.ana.LoopAnalysis;
import coins.backend.sym.Label;
import coins.backend.opt.JumpOpt;

import java.util.Hashtable;
import java.util.Stack;

/**
 * Dead code elimination:<br>
 * If the expressions which are never used or reached, then these expressions
 * are dead. This optimizer eliminate all dead expressions from the program.
 **/
class DeadCodeElimination implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "DeadCodeElimination"; }
  public String subject() {
    return "Dead code elimination on SSA form.";
  }

  /**
   * The private data for this optimizer.
   **/
  private class Datas{
    /** The basic block which includes the target node **/
    private final BasicBlk blk;
    /** The target LIR node **/
    private final LirNode node;

    /**
     * Constructor
     * @param b The basic block which includes `n'
     * @param n The target LIR node
     **/
    private Datas(BasicBlk b,LirNode n){
      blk=b;
      node=n;
    }
  }

  /** Utility **/
  private Util util;
  /** The map between variables and the expressions which define 
      these variables **/
  private Hashtable defineMap;
  /** The work stack **/
  private Stack Work;
  /** The list of expressions which are not dead **/
  private BiList Live;
  /** The current function **/
  private Function f;
  /** The list of the basic blocks which can be reached 
      from the entry block **/
  private BiList availBlk;
  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.OptThr;

  /**
   * Constructor
   * @param e The environment of the SSA module
   **/
  public DeadCodeElimination(SsaEnvironment e){
    env=e;
    env.println("  Dead Code Elimination on SSA form",SsaEnvironment.MsgThr);
  }

  /**
   * Do dead code elimination.
   * @param function The current function
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    env.println("****************** doing DCE to "+function.symbol.name,
                SsaEnvironment.MinThr);
    f=function;
    //f.printIt(env.output);

    FlowGraph g=f.flowGraph();
    defineMap=new Hashtable();
    Work=new Stack();
    Live=new BiList();
    availBlk=new BiList();
    util=new Util(env,f);

    BiList visited=new BiList();
    BasicBlk entryBlk=g.entryBlk();
    Stack stack=new Stack();
    stack.push(entryBlk);

    LoopAnalysis loop=(LoopAnalysis)f.require(LoopAnalysis.analyzer);
    for (BiLink p=g.basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      if(loop.isLoop[blk.id]){
        if(loop.hasExit[blk.id]){
          // The exit block from the loop is live.
          //env.output.println(blk.id);
          LirNode lastCond=(LirNode)blk.instrList().last().elem();
          Live.add(lastCond);
          availBlk.addNew(blk);
          Work.push(new Datas(blk,lastCond));
        }
        else{
          // The condition expression which is control depended by the header
          // block of the infinite loop is live.
          ControlDependences cdep;
          cdep=(ControlDependences)f.require(ControlDependences.analyzer);
          for(BiLink q=cdep.frontiers[blk.id].first();!q.atEnd();q=q.next()){
            BasicBlk cdepBlk=(BasicBlk)q.elem();
            LirNode jumpExp=(LirNode)cdepBlk.instrList().last().elem();
            if(!Live.contains(jumpExp)){
              Live.add(jumpExp);
              availBlk.addNew(cdepBlk);
              Work.push(new Datas(cdepBlk,jumpExp));
            }
          }
        }
      }
    }

    // Make the expression live when the expression clearly live.
    while(!stack.empty()){
      BasicBlk blk=(BasicBlk)stack.pop();
      if(!visited.contains(blk)){
        visited.add(blk);

        for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
          LirNode node=(LirNode)p.elem();
          switch(node.opCode){
            // The expression clearly live
            case Op.PROLOGUE:
              // set the definition point of the REG to this node and
              // also set the overdefined flag to the REG.
              BiList list=util.findTargetLir(node,Op.REG,new BiList());
              for(BiLink q=list.first();!q.atEnd();q=q.next()){
                LirSymRef regNode=(LirSymRef)q.elem();
                defineMap.put(regNode.symbol,new Datas(blk,node));
              }
              Live.add(node);
              availBlk.addNew(blk);
              Work.push(new Datas(blk,node));
              break;

            case Op.CALL:
              if(node.kid(2).nKids()>0 && node.kid(2).kid(0).opCode==Op.REG){
                defineMap.put(((LirSymRef)node.kid(2).kid(0)).symbol,
                              new Datas(blk,node));
              }

            case Op.EPILOGUE:
              Live.add(node);
              availBlk.addNew(blk);
              Work.push(new Datas(blk,node));
              break;

            // The assign expression and the PHI instruction.
            case Op.SET:
            case Op.PHI:
              if(node.kid(0).opCode==Op.REG){
                defineMap.put(((LirSymRef)node.kid(0)).symbol,
                              new Datas(blk,node));
              }
              // It may be safe if the destination variable is not a register.
              else{
                Live.add(node);
                availBlk.addNew(blk);
                Work.push(new Datas(blk,node));
              }
              break;

            // Iterate over the current CFG.
            case Op.JUMP:
              stack.push(((LirLabelRef)node.kid(0)).label.basicBlk());
              break;
            case Op.JUMPC:
              for(int i=1;i<node.nKids();i++){
                stack.push(((LirLabelRef)node.kid(i)).label.basicBlk());
              }
              break;
            case Op.JUMPN:
              for(int i=0;i<node.kid(1).nKids();i++){
                stack.push(((LirLabelRef)node.kid(1).kid(i).
                            kid(1)).label.basicBlk());
              }
              // default label
              stack.push(((LirLabelRef)node.kid(2)).label.basicBlk());
              break;
              
            // The oteher nodes should be kept
            default:
           	  env.println("[dce] unknown node opcode: " + node.opCode + " (node: " + node + ")", SsaEnvironment.MinThr);
			  Live.add(node);
              break;
          }
        }
      }
    }

    while(!Work.empty()){
      Datas S=(Datas)Work.pop();

      BiList regs=util.findTargetLir(S.node,Op.REG,new BiList());
      for(BiLink p=regs.first();!p.atEnd();p=p.next()){
        LirSymRef reg=(LirSymRef)p.elem();
        Datas defineData=(Datas)defineMap.get(reg.symbol);
        if(defineData!=null && !Live.contains(defineData.node)){
          //env.output.println(reg.symbol+" : "+defineData.node);
          Work.push(defineData);
          Live.add(defineData.node);
          availBlk.addNew(defineData.blk);
        }
      }

      ControlDependences cdep;
      cdep=(ControlDependences)f.require(ControlDependences.analyzer);

      if(S.node.opCode==Op.PHI){

        // Make the condition expression live which the predecessor of the PHI
        // instruction is condition depended.
        for(int i=1;i<S.node.nKids();i++){
          LirNode arg=(LirNode)S.node.kid(i);
          BasicBlk pred=((LirLabelRef)arg.kid(1)).label.basicBlk();

          for(BiLink p=cdep.frontiers[pred.id].first();!p.atEnd();p=p.next()){
            BasicBlk cdepBlk=(BasicBlk)p.elem();
            LirNode jumpExp=(LirNode)cdepBlk.instrList().last().elem();
            if(!Live.contains(jumpExp)){
              Live.add(jumpExp);
              availBlk.addNew(cdepBlk);
              Work.push(new Datas(cdepBlk,jumpExp));
            }
          }
        }

        // If some predecessors of a PHI instruction are the same basic block.
        Hashtable table=new Hashtable();
        for(int i=1;i<S.node.nKids();i++){
          LirNode arg=(LirNode)S.node.kid(i);
          BasicBlk pred=((LirLabelRef)arg.kid(1)).label.basicBlk();

          LirNode lnode=(LirNode)table.get(pred);
          if(lnode==null){
            table.put(pred,arg.kid(0));
          }
          else{
            boolean keepJump=false;
            if(arg.kid(1) instanceof LirSymRef){
              LirSymRef ref1=(LirSymRef)arg.kid(1);
              if(lnode instanceof LirSymRef){
                LirSymRef ref2=(LirSymRef)lnode;
                if(ref1.symbol!=ref2.symbol) keepJump=true;
              }
            }
            else if(arg.kid(1) instanceof LirIconst){
              LirIconst cnst1=(LirIconst)arg.kid(1);
              if(lnode instanceof LirIconst){
                LirIconst cnst2=(LirIconst)lnode;
                if(cnst1.value!=cnst2.value) keepJump=true;
              }
            }
            else if(arg.kid(1) instanceof LirFconst){
              LirFconst cnst1=(LirFconst)arg.kid(1);
              if(lnode instanceof LirFconst){
                LirFconst cnst2=(LirFconst)lnode;
                if(cnst1.value!=cnst2.value) keepJump=true;
              }
            }

            if(keepJump){
              LirNode jumpExp=(LirNode)pred.instrList().last().elem();
              if(!Live.contains(jumpExp)){
                Live.add(jumpExp);
                availBlk.addNew(pred);
                Work.push(new Datas(pred,jumpExp));
              }
            }
          }
        }
      }

      for(BiLink p=cdep.frontiers[S.blk.id].first();!p.atEnd();p=p.next()){
        BasicBlk cdepBlk=(BasicBlk)p.elem();
        LirNode jumpExp=(LirNode)cdepBlk.instrList().last().elem();
        //env.output.println(jumpExp);
        if(!Live.contains(jumpExp)){
          Live.add(jumpExp);
          availBlk.addNew(cdepBlk);
          Work.push(new Datas(cdepBlk,jumpExp));
        }
      }
    }


    // Eliminate the expression from the current CFG if the expression is dead.
    visited=new BiList();
    stack=new Stack();
    stack.push(entryBlk);

    while(!stack.empty()){
      BasicBlk blk=(BasicBlk)stack.pop();
      if(!visited.contains(blk)){
        visited.add(blk);

        for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
          LirNode node=(LirNode)p.elem();
          if(!Live.contains(node)){
            switch(node.opCode){
              // It is safe to keep JUMP node.
              case Op.JUMP:{
                Label lab=((LirLabelRef)node.kid(0)).label;
                if(!reachToAvailBlk(lab.basicBlk(),new BiList())){
                  env.println("DCE : remove "+node+" in block "+blk.id,THR);
                  p.unlink();
                  blk.maintEdges();
                }
                else
                  availBlk.addNew(blk);
                break;
              }
              case Op.JUMPC:{
                // Make JUMPC node to JUMP node which has the valid label.
                boolean changed=false;
                for(int i=1;i<3;i++){
                  LirLabelRef lNode=(LirLabelRef)node.kid(i);
                  if(reachToAvailBlk(lNode.label.basicBlk(),
                                     new BiList())){ // make choice
                    availBlk.addNew(blk);
                    //env.print("DCE : replace "+node+" --> ",THR);
                    LirNode lab=env.lir.labelRefVariant(lNode.label);

                    util.makeNewJump(blk,(LirLabelRef)lab);
                    blk.maintEdges();
                    changed=true;
                    break;
                  }
                }
                if(!changed){
                  System.err.println("DCE : no avail successor of "+node);
                  System.exit(2);
                }
                break;
              }
              case Op.JUMPN:{
                // Make JUMPN node to JUMP node which has the valid label.
                boolean changed=false;

                // First, check the default label.
                Label defaultLabel=((LirLabelRef)node.kid(2)).label;
                if(reachToAvailBlk(defaultLabel.basicBlk(),new BiList())){
                  availBlk.addNew(blk);
                  //env.print("DCE : replace "+node+" --> ",THR);
                  LirNode lab=env.lir.labelRefVariant(defaultLabel);

                  util.makeNewJump(blk,(LirLabelRef)lab);
                  break;
                }
                // If the default label is invalid, then check other labels.
                else{
                  for(int i=0;i<node.kid(1).nKids();i++){
                    LirLabelRef lNode=(LirLabelRef)node.kid(1).kid(i).kid(1);
                    if(reachToAvailBlk(lNode.label.basicBlk(),new BiList())){
                      availBlk.addNew(blk);
                      //env.print("DCE : replace "+node+" --> ",THR);
                      LirNode lab=env.lir.labelRefVariant(lNode.label);

                      util.makeNewJump(blk,(LirLabelRef)lab);
                      changed=true;
                      break;
                    }
                  }
                }
                if(!changed){
                  System.err.println("DCE : no avail successor of "+node);
                  System.exit(2);
                }
                break;
              }
              // The dead statements.
              default:
                env.println("DCE : remove "+node+" in block "+blk.id,THR);
                p.unlink();
            }
            g.touch();
          }

          switch(node.opCode){
            // Iterate over the current CFG.
            case Op.JUMP:
              stack.push(((LirLabelRef)node.kid(0)).label.basicBlk());
              break;
            case Op.JUMPC:
              for(int i=1;i<node.nKids();i++){
                stack.push(((LirLabelRef)node.kid(i)).label.basicBlk());
              }
              break;
            case Op.JUMPN:
              for(int i=0;i<node.kid(1).nKids();i++){
                stack.push(((LirLabelRef)node.kid(1).kid(i).
                            kid(1)).label.basicBlk());
              }
              // default label
              stack.push(((LirLabelRef)node.kid(2)).label.basicBlk());
              break;
          }
        }
      }
    }

    // Remove basic blocks which are not able to reach from the entry block.
    boolean changed=true;
    while(changed){
      changed=false;
      for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
        BasicBlk blk=(BasicBlk)p.elem();
        blk.maintEdges();
        if(blk!=entryBlk && blk.predList().length()==0 &&
           blk.dummyPredList().length()==0){
          env.println("DCE : remove block "+blk.id,THR);
          blk.clearEdges();
          p.unlink();
          f.touch();
          changed=true;
        }
      }
    }

    env.println("",THR);

    return(true);
  }

  /**
   * If the basic block can be reached from the entrance of the current CFG,
   * then return true.
   * @param blk The current basic block
   * @param visited The list of the basic blocks which are already visited
   * @return If the current basic block can be reached, return true
   **/
  boolean reachToAvailBlk(BasicBlk blk,BiList visited){
    // If blk can be reached, return true.
    if(availBlk.contains(blk)) return(true);

    // If blk is already visited, return false.
    if(visited.contains(blk)) return(false);

    // Mark blk is visited.
    visited.addNew(blk);

    // Search the reachable path from the entrance of the current CFG.
    // If find, make the basic blocks on the path reachable and also blk 
    // is reachable.
    for(BiLink p=blk.succList().first();!p.atEnd();p=p.next()){
      BasicBlk succ=(BasicBlk)p.elem();
      if(!visited.contains(succ)){
        if(reachToAvailBlk(succ,visited)){
          availBlk.addNew(succ);
          return(true);
        }
      }
    }
    return(false);
  }
}
