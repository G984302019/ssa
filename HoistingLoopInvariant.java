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
import coins.backend.sym.Symbol;
import coins.backend.ana.LoopAnalysis;
import coins.backend.ana.Dominators;
import coins.backend.ana.DFST;
import coins.backend.ana.LiveVariableAnalysis;
import coins.backend.ana.LiveVariableSlotwise;
import coins.backend.lir.LirIconst;

import java.util.Hashtable;
import java.util.Stack;

/**
 * Hoisting loop invariant expression to the outside of the loop.
 **/
class HoistingLoopInvariant implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "HoistingLoopInvariant"; }
  public String subject() {
    return "Hoisting loop invariant variables on SSA form.";
  }

  /**
   * The loop information used in this optimizer.
   **/
  private class Loops{
    /** The loop header **/
    BasicBlk header;
    /** The list of the basic blocks which are the loop body **/
    BiList body;
    /** The list of the basic blocks which are the exit of the loop **/
    BiList exits;
    /** The nest level of the loop **/
    final int nestLevel;
    /** The loop preheaders **/
    private BiList preheader;

    /**
     * Constructor
     * @param h The current loop header
     * @param nestLev The nest level of the current loop
     **/
    Loops(BasicBlk h,int nestLev){
      header=h;
      nestLevel=nestLev;
      body=new BiList();
      exits=new BiList();
      preheader=null;
    }

    /**
     * Return the preheader of the current loop.
     * @return The List of the preheaders of the current loop
     **/
    BiList preheader(){
      if(preheader==null){
        preheader=new BiList();
        // Find the preheader of the loop.
        for(BiLink p=header.predList().first();!p.atEnd();p=p.next()){
          BasicBlk blk=(BasicBlk)p.elem();
          if(blk!=header && !body.contains(blk)){
            preheader.addNew(blk);
          }
        }
      }
      return(preheader);
    }

    /**
     * The debug print
     **/    
    void print(){
      env.output.print("[NestLevel: "+nestLevel+"] ");
      env.output.print("[Header: "+header.id+"] ");
      env.output.print("[Body:");
      for(BiLink p=body.first();!p.atEnd();p=p.next()){
        BasicBlk blk=(BasicBlk)p.elem();
        env.output.print(" "+blk.id);
      }
      env.output.print("] ");
      env.output.print("[ExitBlock:");
      for(BiLink p=exits.first();!p.atEnd();p=p.next()){
        BasicBlk blk=(BasicBlk)p.elem();
        env.output.print(" "+blk.id);
      }
      env.output.println("]");
    }
  }
  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.OptThr;
  /** The prefix of the new symbol **/
  private final String hliSymName="_hli";
  /** The current symbol table of the SSA module **/
  private SsaSymTab sstab;
  
  /**
   * Constructor
   * @param e The environment of the SSA module
   * @param symtab The current symbol table 
   **/
  public HoistingLoopInvariant(SsaEnvironment e,SsaSymTab symtab){
    env=e;
    sstab=symtab;
    env.println("  Hoisting Loop Invariant Variables",SsaEnvironment.MsgThr);
  }

  /**
   * Do hoisting the loop invariant variables to outside of the loop.
   * @param f The current function
   * @param args The list of options
   **/
  public boolean doIt(Function f,ImList args){
    env.println("****************** doing HLI to "+f.symbol.name,
                SsaEnvironment.MinThr);
    // Analyze about memory aliasing.
    MemoryAliasAnalyze alias=new MemoryAliasAnalyze(env,f);

    Util util=new Util(env,f);
    LoopAnalysis loop=(LoopAnalysis)f.require(LoopAnalysis.analyzer);
    DFST dfst=(DFST)f.require(DFST.analyzer);
    //loop.printAfterFunction(env.output);

    BasicBlk[] v=dfst.blkVectorByPre();
    int n=dfst.maxDfn;

    Hashtable loopTable=new Hashtable();
    BiList loopList=new BiList();

    // Collect the basic blocks which makes loop.
    for(int i=1;i<=n;i++){
      if(loop.isLoop[v[i].id]){
        // Make a new loop object consist of the basic blocks and nest level.
        Loops l=new Loops(v[i],loop.nestLevel[v[i].id]);
        for(int j=i+1;j<=n;j++){
          if(loop.loopHeader[v[j].id]!=null && 
             loop.loopHeader[v[j].id].id==v[i].id){
            // Put the basic blocks into the list as a part of loop body.
            l.body.addNew(v[j]);
          }
        }

        if(l.nestLevel==1) loopList.addNew(l);
        else{
          for(BiLink p=loopList.first();!p.atEnd();p=p.next()){
            Loops ll=(Loops)p.elem();
            if(l.nestLevel>ll.nestLevel){
              p.addBefore(l);
              break;
            }
          }
        }
        loopTable.put(l.header,l);
      }
    }

    // Check the exit from the loop.
    for(BiLink p=loopList.first();!p.atEnd();p=p.next()){
      Loops l=(Loops)p.elem();

      BiList all=l.body.copy();
      all.add(l.header);
      for(BiLink pp=all.first();!pp.atEnd();pp=pp.next()){
        BasicBlk blk=(BasicBlk)pp.elem();
        BiList succ=blk.succList();
        for(BiLink q=succ.first();!q.atEnd();q=q.next()){
          BasicBlk s=(BasicBlk)q.elem();
          if(!all.contains(s)){
            if(loop.isLoop[blk.id]){
              Loops ll=(Loops)loopTable.get(blk);
              if(!ll.body.contains(s)) l.exits.addNew(blk);
            }
            else l.exits.addNew(blk);
          }
        }
      }
//      l.print();
    }

    // Repeat until no hoistable variable are found
    boolean isChanged=true;
    while(isChanged){
      isChanged=false;
      // Hoisting the loop invariant expressions.
      Hashtable defineVarMap=new Hashtable();
      for(BiLink p=loopList.first();!p.atEnd();p=p.next()){
        Loops l=(Loops)p.elem();
        if(l.preheader().length()>1) continue;

        //l.print();
        BiList all=l.body.copy();
        all.add(l.header);

        // Check whether the variables are defined inside of the loop.
        BiList defined=new BiList();
        for(BiLink q=all.first();!q.atEnd();q=q.next()){
          BasicBlk blk=(BasicBlk)q.elem();
          BiList nestLoopDefs=(BiList)defineVarMap.get(blk);

          // If blk is the header of the loop which is already checked.
          if(nestLoopDefs!=null){
            for(BiLink r=nestLoopDefs.first();!r.atEnd();r=r.next()){
              LirSymRef symRef=(LirSymRef)r.elem();
              defined.addNew(symRef);
            }
          }
          else{
            for(BiLink r=blk.instrList().first();!r.atEnd();r=r.next()){
              LirNode node=(LirNode)r.elem();
              switch(node.opCode){
                case Op.SET:{
                  if(node.kid(0).opCode==Op.REG){
                    //env.output.println(node);
                    defined.addNew(node.kid(0));
                  }
                  break;
                }
                case Op.PHI:{
                  //env.output.println(node.kid(0));
                  defined.addNew(node.kid(0));
                  break;
                }
                case Op.CALL:{
                  if(node.kid(2).nKids()>0 && 
                     node.kid(2).kid(0).opCode==Op.REG){
                    //env.output.println(node);
                    defined.addNew(node.kid(2).kid(0));
                  }
                  break;
                }
              }
            }
          }
        }

        // Search the loop invariant expressions and hoist them 
        // to the preheader.
        for(BiLink q=all.first();!q.atEnd();q=q.next()){
          BasicBlk blk=(BasicBlk)q.elem();

          for(BiLink r=blk.instrList().first();!r.atEnd();r=r.next()){
            LirNode node=(LirNode)r.elem();

            if(node.opCode==Op.SET && node.kid(0).opCode==Op.REG){
              boolean hoistable=true;

              if(node.kid(1).opCode==Op.REG) continue;

              // If the current expression has memory access
              BiList mems=util.findTargetLir(node.kid(1),Op.MEM,new BiList());
              if(mems.length()>0){
                long[] phRank=new long[l.preheader().length()];
                int i=0;
                for(BiLink pp=l.preheader().first();!pp.atEnd();pp=pp.next()){
                  BasicBlk phBlk=(BasicBlk)pp.elem();
                  phRank[i++]=alias.blkRank(phBlk);
                }
                  
                for(BiLink pp=mems.first();!pp.atEnd();pp=pp.next()){
                  LirNode memNode=(LirNode)pp.elem();
                  //env.output.println(memNode);
                  for(i=0;i<phRank.length;i++){
                    if(phRank[i]!=((LirIconst)memNode.kid(1)).value){
                      hoistable=false;
                      break;
                    }
                  }
                  if(!hoistable) break;
                }
              }

              if(hoistable){
                BiList list=util.findTargetLir(node.kid(1),Op.REG,
                                               new BiList());

                // If all the variables are defined outside of the loop in this
                // expression.
                for(BiLink pp=list.first();!pp.atEnd();pp=pp.next()){
                  LirNode n1=(LirNode)pp.elem();
                  for(BiLink qq=defined.first();!qq.atEnd();qq=qq.next()){
                    LirNode n2=(LirNode)qq.elem();
                    if(n1.equals(n2)){
                      hoistable=false;
                      break;
                    }
                  }
                  if(!hoistable) break;
                }
              }

              if(hoistable){
                env.println("HLI : Loop invariant "+node+" in block "+
                            blk.id,THR);

                if (!mayCauseException(node)) { //# 2007/03/16
                LiveVariableAnalysis ana;
                ana=(LiveVariableAnalysis)f.
                  require(LiveVariableSlotwise.analyzer);
                // Find the exit which the destination of the target expression
                // is live out.
                for(BiLink pp=l.exits.first();!pp.atEnd();pp=pp.next()){
                  BasicBlk exitBlk=(BasicBlk)pp.elem();
                  BiList liveOut=ana.liveOut(exitBlk);

                  if(liveOut.contains(((LirSymRef)node.kid(0)).symbol)){
                    // Check whether the exits are dominated by the basic block
                    // which includes the target expression.
                    Dominators dom;
                    dom=(Dominators)f.require(Dominators.analyzer);
                    boolean isOk=false;

                    if(!dom.dominates(blk,exitBlk)){
                      //l.print();
                      //env.output.println(blk.id+" "+exitBlk.id);
                      hoistable=false;
                    }

                  }
                }
                } //# 2007/03/16
                //# add, 2007/03/16
                else {
                  for(BiLink pp=l.exits.first();!pp.atEnd();pp=pp.next()){
                    BasicBlk exitBlk=(BasicBlk)pp.elem();

                    Dominators dom;
                    dom=(Dominators)f.require(Dominators.analyzer);
                    boolean isOk=false;

                    if(!dom.dominates(blk,exitBlk)){
                      //l.print();
                      //env.output.println(blk.id+" "+exitBlk.id);
                      hoistable=false;
                    }
                  } //# end of fix, 2007/03/16
                } 

                // Hoisting the target expression to the preheader.
                if(hoistable){
                  isChanged=true;
                  for(BiLink pp=l.preheader().first();!pp.atEnd();
                      pp=pp.next()){
                    BasicBlk preheader=(BasicBlk)pp.elem();
                    env.println("HLI : Hoisted "+node+" into block "+
                                preheader.id,THR);

                    // make new symbol and assign statement
                    Symbol s=sstab.newSsaSymbol(hliSymName,node.type);
                    LirNode regNode=env.lir.symRef(s);
                    LirNode cpy=env.lir.operator(Op.SET,node.type,
                                                 regNode,
                                                 node.kid(1).makeCopy(env.lir),
                                                 ImList.Empty);

                    BiList instr=preheader.instrList();
                    instr.last().addBefore(cpy);
                    
//                    instr.last().addBefore(node.makeCopy(env.lir));

                    node.setKid(1,regNode.makeCopy(env.lir));
                  }
//                  r.unlink();
                  f.touch();
                }
              }
            }
          }
        }
        defineVarMap.put(l.header,defined);
      }
    }
    env.println("",THR);
    alias.annul();

    return(true);
  }


  //# add, 2007/03/16
  private boolean mayCauseException(LirNode node) {
    java.util.Stack stack = new java.util.Stack();
    stack.push(node);

    while (!stack.empty()) {
      LirNode n = (LirNode) stack.pop();
      switch (n.opCode) {
      case Op.DIVS:
      case Op.DIVU:
      case Op.MODS:
      case Op.MODU: {
        LirNode kid = n.kid(1);

        if (kid.opCode == Op.INTCONST) {
          long i = ((LirIconst) kid).value;
          if (i == 0) {
            return true;
          }

          stack.push(n.kid(0));
          break;
        }
        else if (kid.opCode == Op.FLOATCONST) {
          double f = ((coins.backend.lir.LirFconst) kid).value;
          if (f == 0.0) {
            return true;
          }

          stack.push(n.kid(0));
          break;
        }

        return true;
      }
      default:
        for (int i = 0; i < n.nKids(); i++) {
          stack.push(n.kid(i));
        }
      }
    }

    return false;
  }
}
