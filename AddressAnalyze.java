/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.util.BiLink;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.util.ImList;
import coins.backend.cfg.BasicBlk;
import coins.backend.sym.Symbol;
import coins.backend.Function;
import coins.backend.Op;

/**
 * This class is to keep the order of FRAME or STATIC node.
 **/
class AddressAnalyze{
  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The current function **/
  private Function f;
  /** The current symbol table **/
  private SsaSymTab sstab;

  /**
   * Constructor
   * @param e The environment of the SSA module
   * @param func The current function
   * @param tab The current symbol table of the module
   **/
  AddressAnalyze(SsaEnvironment e,Function func,SsaSymTab tab){
    env=e;
    f=func;
    sstab=tab;

    // make ordering FRAME and STATIC node.
    analyze();
  }

  /**
   * Make ordering FRAME and STATIC node.
   * To keep ordering, ths SSA module appends the sequential number to
   * the FRAME and STATIC nodes.
   **/
  void analyze(){
    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        if(node.opCode==Op.CALL){
          replaceAddress(node.kid(0),node,0);
          replaceAddress(node.kid(2),node,2);

          for(int i=0;i<node.kid(1).nKids();i++){
            if(node.kid(1).kid(i).opCode==Op.FRAME ||
               node.kid(1).kid(i).opCode==Op.STATIC){
              LirSymRef curAddress=(LirSymRef)node.kid(1).kid(i);
              Symbol sym=sstab.newAddressSymbol(curAddress.symbol);
              LirNode newAddress=env.lir.symRef(node.kid(1).kid(i).opCode,
                                                curAddress.type,sym,
                                                node.kid(1).kid(i).opt);

              node.kid(1).setKid(i,newAddress);
            }
          }
        }
        else{
          replaceAddress(node,null,0);
        }
      }
    }
  }

  /**
   * Replace original FRAME and STATIC node into the serialized ones.
   * @param root The target LIR node
   * @param parent The parent of the target LIR node
   * @param place The place of the target LIR in the parent
   **/
  private void replaceAddress(LirNode root,LirNode parent,int place){
    if(root!=null) return;

    for(int i=0;i<root.nKids();i++){
      replaceAddress(root.kid(i),root,i);
    }

    if(parent!=null && (root.opCode==Op.FRAME || root.opCode==Op.STATIC)){
      Symbol sym=sstab.currentAddressSymbol(((LirSymRef)root).symbol);
      LirNode newAddress=env.lir.symRef(root.opCode,root.type,
                                        sym,root.opt);
      //env.output.println("FA : replace to "+newAddress);
      parent.setKid(place,newAddress);
    }
  }

  /**
   * Translate back from the ordered nodes into the original nodes.
   **/
  void annul(){
    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        addressAsBefore(node,null,0);
      }
    }
  }

  /**
   * Replace the ordered FRAME and STATIC nodes into the original ones.
   * @param root The target LIR
   * @param parent The parent of the target LIR
   * @param place The place of the target LIR in the parent
   **/
  private void addressAsBefore(LirNode root,LirNode parent,int place){
    if(root!=null){
      if(parent!=null && (root.opCode==Op.FRAME || root.opCode==Op.STATIC)){
        Symbol sym=sstab.orgSym(((LirSymRef)root).symbol);
        LirNode newAddress=env.lir.symRef(root.opCode,root.type,sym,
                                          root.opt);
        //env.output.println("FA : annul "+newAddress);
        parent.setKid(place,newAddress);
        root=newAddress;
      }
      for(int i=0;i<root.nKids();i++){
        addressAsBefore(root.kid(i),root,i);
      }
    }
  }
}
