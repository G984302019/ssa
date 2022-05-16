/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.Op;
import coins.backend.util.BiLink;
import coins.backend.util.BiList;
import coins.backend.ana.Dominators;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirLabelRef;
import coins.backend.sym.Label;
import coins.backend.opt.PreHeaders;
import coins.backend.util.ImList;

import java.util.Hashtable;
import java.util.Stack;
import java.util.Enumeration;

/**
 * Change the structure of the loop from `while type' into `do-while' type.
 * Also the optimizer merges some loops which have the same header and insert
 * loop preheaders.
 **/
class ChangeLoopStructure implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "ChangeLoopStructure"; }
  public String subject() {
    return "Change loop structure from while type to do-while type.";
  }

  /**
   * The private data which holds the information about natural loop.
   **/
  private class NaturalLoop{
    /** The loop header **/
    BasicBlk header;
    /** The basic block which has back edge **/
    BasicBlk backEdgeBlk;

    /**
     * Constructor
     * @param h The loop header
     * @param beb The basic block which has back edge
     **/
    NaturalLoop(BasicBlk h,BasicBlk beb){
      header=h;
      backEdgeBlk=beb;
    }

    /**
     * Represent this class as a String value.
     * @return The String value of this class 
     **/
    public String toString(){
      return("(H["+header.id+"] , B["+backEdgeBlk.id+"])");
    }
  }

  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The threshold of debug print **/
  public static final int THR=SsaEnvironment.OptThr;
  /** The list of the loop structures **/
  private BiList loops;
  /** The current function **/
  private Function f;

  /**
   * Constructor
   * @param e The environment of the SSA module
   **/
  public ChangeLoopStructure(SsaEnvironment e){
    env=e;
    env.println("  Change Loop Structure",SsaEnvironment.MsgThr);
  }

  /**
   * Change the structure of the loop and insert preheaders.
   * @param function The current function
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    env.println("****************** doing CLS to "+
                function.symbol.name,
                SsaEnvironment.MinThr);

    f=function;
    loops=new BiList();

    boolean changed=true;

    // repeat until no loop has changed
    while(changed){
      changed=false;
      loops.clear();

      loopDetect();
      mergeLoops();
      changed=changeLoopStructure();
    }

    // Insert preheaders
    f.apply(PreHeaders.trig);

    for(BiLink p=loops.first();!p.atEnd();p=p.next()){
      NaturalLoop l=(NaturalLoop)p.elem();

      if(l.header.predList().length()>1){
        // Find the preheader of the loop.
        BasicBlk preheader=f.flowGraph().insertNewBlkBefore(l.header);
        for(BiLink q=l.header.predList().first();!q.atEnd();q=q.next()){
          BasicBlk blk=(BasicBlk)q.elem();
          if(blk!=preheader){
            LirNode last=(LirNode)blk.instrList().last().elem();
            last.replaceLabel(l.header.label(),preheader.label(),env.lir);
            blk.maintEdges();
          }
        }
        preheader.maintEdges();
      }
    }

    env.println("",THR);

    return(true);
  }

  /**
   * Change the loop structure from `while type' into `do-while type'.
   * @return If any changes, return `true'
   **/
  private boolean changeLoopStructure(){
    boolean changed=false;

    for(BiLink p=loops.first();!p.atEnd();p=p.next()){
      NaturalLoop l=(NaturalLoop)p.elem();

      // If the loop include only one basic block, the optimizer can not
      // change the structure.
      if(l.header==l.backEdgeBlk) continue;

      // Get the body part of the loop.
      BiList body=new BiList();
      Stack stack=new Stack();

      body.add(l.header);
      if(!body.contains(l.backEdgeBlk)){
        body.add(l.backEdgeBlk);
        stack.push(l.backEdgeBlk);
      }

      while(!stack.empty()){
        BasicBlk m=(BasicBlk)stack.pop();
        for(BiLink q=m.predList().first();!q.atEnd();q=q.next()){
          BasicBlk pred=(BasicBlk)q.elem();
          if(!body.contains(pred)){
            body.add(pred);
            stack.push(pred);
          }
        }
      }

      // If the loop include only the basic blocks, all of which have the edge
      // to outside of the loop, then the optimizer can not change the 
      // structure into `do-while' type even if that is a `while' type loop.
      boolean doNotChange=true;
      for(BiLink q=body.first();!q.atEnd();q=q.next()){
        BasicBlk loopBlk=(BasicBlk)q.elem();
        LirNode lastNode=(LirNode)loopBlk.instrList().last().elem();
        switch(lastNode.opCode){
          case Op.JUMP:{
            doNotChange=false;
            break;
          }
          case Op.JUMPC:
          case Op.JUMPN:{
            boolean toOutSide=false;
            Label[] targets=lastNode.getTargets();
            for(int i=0;i<targets.length;i++){
              if(!body.contains(targets[i].basicBlk())){
                toOutSide=true;
                break;
              }
            }
            if(toOutSide) break;

            doNotChange=false;
          }
        }
        if(!doNotChange) break;
      }
      if(doNotChange) continue;
 

      // The optimizer find that it can change the loop structure.
      LirNode node=(LirNode)l.header.instrList().last().elem();
      BasicBlk newBlk=null;

      switch(node.opCode){
        case Op.JUMPC:{
          //env.output.println("JUMPC");

          // Make a new basic block and insert it into the current control
          // flow graph.
          for(int i=1;i<node.nKids();i++){
            BasicBlk blk=((LirLabelRef)node.kid(i)).label.basicBlk();
            if(!body.contains(blk)){
              env.println("CLS : find 'while' type "+l,THR);
              newBlk=f.flowGraph().insertNewBlkBefore(blk);
              //env.output.println("aaaaaaaaaaa "+newBlk.label());

              // Copy the instructions in the header into the new basic block
              BiList newInstrList=newBlk.instrList();
              newInstrList.clear();
              for(BiLink q=l.header.instrList().first();!q.atEnd();q=q.next()){
                LirNode instr=(LirNode)q.elem();
                newInstrList.add(instr.makeCopy(env.lir));
              }
              newBlk.maintEdges();

              break;
            }
          }
          break;
        }
        case Op.JUMPN:{
          // The optimizer can not change the structure of the loop
          // which has JUMPN at the end of the back edge block.
          env.println("CLS : find 'while' type, but not changed "+l,THR);
          break;
        }
      }

      if(newBlk!=null){
        f.flowGraph().touch();
        changed=true;
        // Replace the back edge
        LirNode bebJump=(LirNode)l.backEdgeBlk.instrList().last().elem();
        switch(bebJump.opCode){
          case Op.JUMP:{
            bebJump.setKid(0,env.lir.labelRef(newBlk.label()));
            break;
          }
          case Op.JUMPC:{
            for(int i=1;i<bebJump.nKids();i++){
              if(l.header==((LirLabelRef)bebJump.kid(i)).label.basicBlk()){
                bebJump.setKid(i,env.lir.labelRef(newBlk.label()));
              }
            }
            break;
          }
          case Op.JUMPN:{
            // default label
            if(l.header==((LirLabelRef)bebJump.kid(2)).label.basicBlk()){
              bebJump.setKid(2,env.lir.labelRef(newBlk.label()));
            }
            // normal labels
            for(int i=0;i<bebJump.kid(1).nKids();i++){
              LirLabelRef lab=(LirLabelRef)bebJump.kid(1).kid(i).kid(1);
              if(l.header==lab.label.basicBlk()){
                bebJump.kid(1).kid(i).setKid(1,
                                             env.lir.labelRef(newBlk.label()));
              }
            }
            break;
          }
        }
        l.backEdgeBlk.maintEdges();
      }
    }
    return(changed);
  }

  /**
   * Merge some loops which have the same header.
   **/
  private void mergeLoops(){
    Hashtable table=new Hashtable();
    for(BiLink p=loops.first();!p.atEnd();p=p.next()){
      NaturalLoop l=(NaturalLoop)p.elem();
      BasicBlk header=l.header;
      BiList list=(BiList)table.get(header);
      if(list==null){
        list=new BiList();
        table.put(header,list);
      }
      list.add(l);
    }
    Enumeration keys=table.keys();
    while(keys.hasMoreElements()){
      BasicBlk header=(BasicBlk)keys.nextElement();
      BiList list=(BiList)table.get(header);

      if(list.length()>1){
        BasicBlk newBeb=f.flowGraph().insertNewBlkBefore(header);
        //env.output.println("bbbbbbbbbbbb "+newBeb.label());
        env.print("CLS : merge ",THR);
        for(BiLink p=list.first();!p.atEnd();p=p.next()){
          NaturalLoop l=(NaturalLoop)p.elem();
          loops.remove(l);
          env.print(l.toString(),THR);
          BasicBlk beb=l.backEdgeBlk;
          LirNode jumpNode=(LirNode)beb.instrList().last().elem();
          
          switch(jumpNode.opCode){
            case Op.JUMP:{
              jumpNode.setKid(0,env.lir.labelRef(newBeb.label()));
              break;
            }
            case Op.JUMPC:{
              for(int i=1;i<3;i++){
                if(((LirLabelRef)jumpNode.kid(i)).label==header.label())
                  jumpNode.setKid(i,env.lir.labelRef(newBeb.label()));
              }
              break;
            }
            case Op.JUMPN:{
              for(int i=0;i<jumpNode.kid(1).nKids();i++){
                LirLabelRef labRef=(LirLabelRef)jumpNode.kid(1).kid(i).kid(1);
                if(labRef.label==header.label()){
                  jumpNode.kid(1).kid(i).
                    setKid(1,env.lir.labelRef(newBeb.label()));
                }
              }
              // default label
              if(((LirLabelRef)jumpNode.kid(2)).label==header.label()){
                jumpNode.setKid(2,env.lir.labelRef(newBeb.label()));
              }
              break;
            }
          }
          beb.maintEdges();
        }
        NaturalLoop newLoop=new NaturalLoop(header,newBeb);
        env.println(" to "+newLoop,THR);
        loops.add(newLoop);
      }
    }
  }

  /**
   * Detect the natural loops in the current function.
   **/
  private void loopDetect(){
    Dominators dom;
    dom=(Dominators)f.require(Dominators.analyzer);

    // Find out the header and the back edge block of the loop
    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.succList().first();!q.atEnd();q=q.next()){
        BasicBlk succ=(BasicBlk)q.elem();
        if(dom.dominates(succ,blk)){
          NaturalLoop l=new NaturalLoop(succ,blk);
          env.println("CLS : detect loop "+l,THR);
          loops.add(l);
        }
      }
    }
  }
}
