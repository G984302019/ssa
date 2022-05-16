/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.Function;
import coins.backend.util.BiList;
import coins.backend.util.BiLink;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.sym.Symbol;
import coins.backend.Op;
import coins.backend.ana.LiveVariableAnalysis;
import coins.backend.ana.LiveVariableSlotwise;

import java.util.Stack;
import java.util.Enumeration;

/**
 * Aggregate LIR trees.<br>
 * There are some optimizations to break LIR trees many pieces.
 * with the temporary variables.
 * Unfortunately it may be disadvantage for good code generation.
 * So, the SSA module aggregates LIR trees again.
 * If the temporary varaibles refers only once, this optimizer fills
 * the expression instead of the temporary variable.
**/
class AggregateInstructions{
  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** Utility **/
  private Util util;
  /** The threshold of debug print **/
  public static final int THR=SsaEnvironment.OptThr;
  /** The current function **/
  private Function f;

  /**
   * Constructor
   * @param e The environment of the SSA module
   * @param func The current function
   **/
  AggregateInstructions(SsaEnvironment e,Function func){
    env=e;
    f=func;
    util=new Util(env,f);

    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      LiveVariableAnalysis liveAna;
      liveAna=(LiveVariableAnalysis)f.require(LiveVariableSlotwise.analyzer);
      BiList removeList=new BiList();

      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        if(node.opCode==Op.SET && node.kid(0).opCode==Op.REG){
          if(!liveAna.isLiveAtExit(((LirSymRef)node.kid(0)).symbol,blk)){
            BiList mem=util.findTargetLir(node.kid(1),Op.MEM,new BiList());
            if(search(q,!(mem.length()==0)))
              removeList.add(q);
          }
        }
      }

      // remove unnecessary expression
      for(BiLink q=removeList.first();!q.atEnd();q=q.next()){
        BiLink link=(BiLink)q.elem();
        env.println("AGGI : remove "+link.elem(),THR);
/**
        if(!check((LirNode)link.elem())){
          Symbol s=((LirSymRef)((LirNode)link.elem()).kid(0)).symbol;
          env.output.println(blk.id+" aaaaaaaaaaaaaaaa "+s);
          env.output.println(liveAna.liveOut(blk));
        }
        else{**/
//env.output.println("-------> "+link.elem()+"\n");
          link.unlink();
//        }
      }
      f.touch();
    }
  }

  /**
   * Check whether the left hand side variable of the target LIR node
   * uses only once or not. If so, return true.
   * @param root The target LIR node
   * @param withMem True if the target node includes MEM node
   * @return True if the target variable uses only once
   **/
  private boolean search(BiLink root,boolean withMem){
    Symbol s=((LirSymRef)((LirNode)root.elem()).kid(0)).symbol;
    BiList candidate=new BiList();

    for(BiLink p=root.next();!p.atEnd();p=p.next()){
      LirNode node=(LirNode)p.elem();

      BiList list=util.findTargetLir(node,Op.REG,new BiList());
      for(BiLink q=list.first();!q.atEnd();q=q.next()){
        LirSymRef reg=(LirSymRef)q.elem();
        if(reg.symbol==s){
          candidate.add(node);
        }
      }
    }

    if(candidate.length()==1){
      LirNode node=(LirNode)candidate.first().elem();

      if(withMem && node.opCode==Op.CALL){
        BiList list=util.findTargetLir(node.kid(2),Op.MEM,new BiList());
        for(BiLink p=list.first();!p.atEnd();p=p.next()){
          LirNode mem=(LirNode)p.elem();
          BiList list2=util.findTargetLir(mem,Op.REG,new BiList());
          for(BiLink q=list2.first();!q.atEnd();q=q.next()){
            LirNode reg=(LirNode)q.elem();
            if(((LirSymRef)reg).symbol==s){
              return(false);
            }
          }
        }
      }

      if(withMem){
        for(BiLink p=root.next();!p.atEnd();p=p.next()){
          LirNode n=(LirNode)p.elem();
          if(n.equals(node)) break;

          switch(n.opCode){
            case Op.CALL: return(false);
            case Op.SET:{
              if(n.kid(0).opCode!=Op.REG) return(false);
            }
          }
        }
      }

      env.println("AGGI : put "+root.elem()+" into "+node,THR);

//env.output.println("------->   "+root.elem());
//env.output.println(node);
      replace((LirNode)root.elem(),node);
//env.output.println(node+"\n");
      return(true);
    }

    return(false);
  }

/**
  private boolean check(LirNode target){
    Symbol s=((LirSymRef)target.kid(0)).symbol;
    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        if(node==target) continue;

        BiList list=util.findTargetLir(node,Op.REG,new BiList());
        for(BiLink pp=list.first();!pp.atEnd();pp=pp.next()){
          LirSymRef reg=(LirSymRef)pp.elem();
          if(s==reg.symbol){
            env.output.println("("+blk.id+")");
            return(false);
          }
        }
      }
    }
    return(true);
  }
**/

  /**
   * Put the LIR node `dst' into the LIR node `src'.
   * @param src The source node
   * @param dst The destination node
   **/
  private void replace(LirNode src,LirNode dst){
    Symbol s=((LirSymRef)src.kid(0)).symbol;
    Stack stack=new Stack();
    stack.push(dst);

    while(!stack.empty()){
      LirNode node=(LirNode)stack.pop();
      for(int i=0;i<node.nKids();i++){
        if(node.kid(i).opCode==Op.REG &&
           ((LirSymRef)node.kid(i)).symbol==s){
          node.setKid(i,src.kid(1).makeCopy(env.lir));
          stack.clear();
          break;
        }
        else
          stack.push((LirNode)node.kid(i));
      }
    }
  }
}

