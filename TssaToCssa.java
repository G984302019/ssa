/* ----------------------------------------------------------
%   Copyright (C) 2004 The Coins Project Group               
%       (Read COPYING for detailed information.)             
----------------------------------------------------------- */
package coins.ssa;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Stack;

import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.ana.InterferenceGraph;
import coins.backend.ana.LiveVariableAnalysis;
import coins.backend.ana.LiveVariableSlotwise;
import coins.backend.cfg.BasicBlk;
import coins.backend.cfg.FlowGraph;
import coins.backend.lir.LirBinOp;
import coins.backend.lir.LirFconst;
import coins.backend.lir.LirIconst;
import coins.backend.lir.LirLabelRef;
import coins.backend.lir.LirNaryOp;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.sym.Symbol;
import coins.backend.util.BiLink;
import coins.backend.util.BiList;
import coins.backend.util.ImList;

/**
 * The back translation from SSA form into normal form.
 * This class has three methods for the back translation.
 * Sreedhar's method I, II and III.
 * This class also has the SSA based coalescing module.
 * Reference:<br>
 * Vugranam C. Sreedhar, Roy Dz-Ching Ju, David M. Gillies, Vatsa Santhanam,
 * "Translating Out of Static Single Assignment Form,"
 * SAS'99, LNCS 1694, pp.194-210, 1999.
 **/
class TssaToCssa implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "TssaToCssa"; }
  public String subject() {
    return "TSSA to CSSA.";
  }

  /**
   * The information about symbols which are used in the Sreedhar's method III.
   **/
  private class m3Datas{
    /** The LIR node which represent Xi in Sreedhar's paper **/
    LirNode nodeXi;
    /** The LIR node which represent Xj in Sreedhar's paper **/
    LirNode nodeXj;
    /** The symbol of Xi **/
    Symbol xi;
    /** The symbol of Xj **/
    Symbol xj;
    /** The basic block related to Xi **/
    BasicBlk Li;
    /** The basic block related to Xj **/
    BasicBlk Lj;
    /** The variables which live into Xi **/
    BiList liveXi;
    /** The variables which live into Xj **/
    BiList liveXj;
    /** Phi congruence class of Xi **/
    BiList pccXi;
    /** Phi congruence class of Xj **/
    BiList pccXj;

    /**
     * Constructor
     **/
    m3Datas(){
      nodeXi=null;
      nodeXj=null;
      xi=null;
      xj=null;
      Li=null;
      Lj=null;
      liveXi=null;
      liveXj=null;
      pccXi=null;
      pccXj=null;
    }

    /**
     * If it has intersection between Live information about Xi (or Xj) and
     * the element of the phi congruence class about Xj (or Xi), then return 
     * true.
     * @param pcc The Phi Congruence Class
     * @param live The Live information
     * @return If it has intersection, return true
     **/
    boolean hasIntersection(BiList pcc,BiList live){
      if(pcc==null) return(true);

      BiList mergedLive=mergePhiCongruenceClass(live);

      for(BiLink p=pcc.first();!p.atEnd();p=p.next()){
        Symbol s=(Symbol)p.elem();
        if(mergedLive.contains(s)) return(true);
      }
      return(false);
    }

    /**
     * Choose the case 1 to 4 using the information about Xi and Xj.
     * @return The case number
     **/
    int whichCase(){
/**
      boolean intersect1=false;
      boolean intersect2=false;

      if(!(nodeXj instanceof LirSymRef) && 
         !(nodeXj.kid(0) instanceof LirSymRef)) intersect1=true;
      else intersect1=hasIntersection(pccXi,liveXj);

      if(!(nodeXi instanceof LirSymRef) &&
         !(nodeXi.kid(0) instanceof LirSymRef)) intersect2=true;
      else intersect2=hasIntersection(pccXj,liveXi);
**/
      boolean intersect1=hasIntersection(pccXi,liveXj);
      boolean intersect2=hasIntersection(pccXj,liveXi);

      if(intersect1&&!intersect2) return(1);
      else if(!intersect1&&intersect2) return(2);
      else if(intersect1&&intersect2) return(3);
      
      return(4);
    }

    /**
     * Set the LIR node as Xi.
     * This is used for the source operands of the PHI instruction.
     * @param node The Xi node
     **/
    void setXi(LirNaryOp node){
      nodeXi=node;
      if(node.kid(0) instanceof LirSymRef)
        xi=((LirSymRef)node.kid(0)).symbol;
      Li=((LirLabelRef)node.kid(1)).label.basicBlk();

      LiveVariableAnalysis liveAna;
      liveAna=(LiveVariableAnalysis)f.require(LiveVariableSlotwise.analyzer);
      liveXi=liveAna.liveOut(Li);

      if(node.kid(0) instanceof LirSymRef)
        pccXi=(BiList)phiCongruenceClasses.get(xi);
    }

    /**
     * Set the LIR node as Xi.
     * This is used for the destination operand of the PHI instruction.
     * @param node The Xi node
     * @param blk The basic block which includes the current PHI instruction
     **/
    void setXi(LirSymRef node,BasicBlk blk){ // for target
      nodeXi=node;
      xi=node.symbol;
      Li=blk;

      LiveVariableAnalysis liveAna;
      liveAna=(LiveVariableAnalysis)f.require(LiveVariableSlotwise.analyzer);
      liveXi=liveAna.liveIn(Li);
      pccXi=(BiList)phiCongruenceClasses.get(xi);
    }

    /**
     * Set the LIR node as Xj.
     * @param node The Xj node
     **/
    void setXj(LirNaryOp node){
      nodeXj=node;
      if(node.kid(0) instanceof LirSymRef)
        xj=((LirSymRef)node.kid(0)).symbol;

      Lj=((LirLabelRef)node.kid(1)).label.basicBlk();
      LiveVariableAnalysis liveAna;
      liveAna=(LiveVariableAnalysis)f.require(LiveVariableSlotwise.analyzer);
      liveXj=liveAna.liveOut(Lj);

      if(node.kid(0) instanceof LirSymRef)
        pccXj=(BiList)phiCongruenceClasses.get(xj);
    }

    void unsetXj(){
      nodeXj=null;
      xj=null;
      Lj=null;
      liveXj=null;
      pccXj=null;
    }

    /**
     * If the elements of PhiCongruenceClass(Xi) and PhiCongruenceClass(Xj)
     * has interfere, then return true. Otherwise return false.
     **/
    boolean hasInterfere(){
      if(pccXi==null || pccXj==null) return(true);

      InterferenceGraph ig;
      ig=(InterferenceGraph)f.require(InterferenceGraph.analyzer);

      for(BiLink p=pccXi.first();!p.atEnd();p=p.next()){
        Symbol yi=(Symbol)p.elem();
        for(BiLink q=pccXj.first();!q.atEnd();q=q.next()){
          Symbol yj=(Symbol)q.elem();
          if(!yi.equals(yj) && ig.interfere(yi,yj))
            return(true);
        }
      }
      return(false);
    }

    /**
     * Debug print
     **/
    void print(){
      env.output.println("xi : "+xi.name);
      env.output.println("xj : "+xj.name);
    }

  }

  /** The threshold of debug print **/
  public static final int THR=SsaEnvironment.SsaThr;
  /** The threshold of debug print **/
  public static final int THR2=SsaEnvironment.OptThr;
  /** The threshold of debug print **/
  public static final int THR3=SsaEnvironment.AllThr;
  /** The name of the symbol which the optimzer uses to make the temporary
      variables **/
  public static final String BACK_TMP="_ssa";
  /** Represent Sreedhar's Method I **/
  public static final int METHOD_I=1;
  /** Represent Sreedhar's Method II **/
  public static final int METHOD_II=2;
  /** Represent Sreedhar's Method III **/
  public static final int METHOD_III=3;

  /** The type of the back translation from SSA form **/
  private final int type;
  /** If the value is set `true', then do SSA based coalescing **/
  private final boolean coalesce;
  /** If the value is set `true', then do SSA aggregate expressions **/
  private final boolean aggregate;
  /** The current function **/
  private Function f;
  /** The symbol table of SSA form **/
  private SsaSymTab sstab;
  /** The relation between resources and their Phi Congruence Class **/
  private Hashtable phiCongruenceClasses;
  /** The environment of the SSA module **/
  private SsaEnvironment env;

  /**
   * Constructor. The back translation from SSA form.
   * @param e The environment of the SSA module
   * @param stab The current symbol table on SSA form
   * @param howToTranslate Specify the translate method
   * @param withCoalesce Whether coalesce or not
   **/
  TssaToCssa(SsaEnvironment e,SsaSymTab stab,
                       int howToTranslate,boolean withCoalesce,boolean aggr){
    sstab=stab;
    env=e;
    type=howToTranslate;
    coalesce=withCoalesce;
    aggregate=aggr;

    int msg=SsaEnvironment.MsgThr;
    env.print("  SSA back translation : ",msg);
    switch(type){
      case METHOD_I: env.print("METHOD I",msg);break;
      case METHOD_II: env.print("METHOD II",msg);break;
      case METHOD_III: env.print("METHOD III",msg);
    }
    if(coalesce) env.println(" with Coalescing.",msg);
    else env.println(" without Coalescing.",msg);

  }

  /**
   * Do Back translation from the SSA form.
   * @param function The current function
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    env.println("****************** TSSA to CSSA "+
                function.symbol.name,SsaEnvironment.MinThr);

    f=function;

    // Aggregate LIR trees again
    if(aggregate){
      new AggregateInstructions(env,f);
    }
    //f.printIt(env.output);

    oustConstant();

    // Step 1: Translating the TSSA form to a CSSA form.
    // Initialize phi congruence class of each resources in phi instruction.
    initPhiCongruenceClass(f.flowGraph());
    tssaToCssa(f.flowGraph());

    return(true);
  }

  private void oustConstant(){
    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        if(node.opCode==Op.PHI){
          for(int i=1;i<node.nKids();i++){
            if(node.kid(i).kid(0).opCode!=Op.REG){
              LirNode src=node.kid(i).kid(0).makeCopy(env.lir);
              LirNode dst=env.lir.symRef(sstab.newSsaSymbol(BACK_TMP,
                                                            src.type));
              LirNode copyAssign=env.lir.operator(Op.SET,src.type,
                                                  dst,src,ImList.Empty);
//              env.output.println(copyAssign);
              BasicBlk b=((LirLabelRef)node.kid(i).kid(1)).label.basicBlk();
              b.instrList().last().addBefore(copyAssign);

              node.kid(i).setKid(0,dst.makeCopy(env.lir));
              f.touch();
            }
          }
        }
      }
    }
  }
 
  /**
   * Translate from TSSA (Transformed SSA) form to CSSA (Conventional SSA)
   * form by using METHOD I, METHOD II or METHOD III.
   * @param g The current control flow graph
   **/
  private void tssaToCssa(FlowGraph g){
    BiList candidateResourceSet=null;

    // 2:
    //  for each phi instruction ( phiInst ) in CFG {
    //    phiInst in the form of x0 = f ( x1:L1, x2:L2, ..., xn:Ln );
    //    L0 is the basic block containing phiInst;
    // 3:
    //  Set candidateResourceSet;
    for(BiLink p=g.basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        if(node.opCode==Op.PHI){
          if(type==METHOD_I){
            candidateResourceSet=methodI((LirNaryOp)node);
          }
          else if(type==METHOD_II){
            candidateResourceSet=methodII((LirNaryOp)node);
          }
          else{ // Metod III
            candidateResourceSet=methodIII((LirNaryOp)node,blk);
          }

          // Insert copy assign expressions.
          insertCopy(candidateResourceSet,(LirNaryOp)node,blk);

          // Merge phiCongruenceClass's for all resources in phiInst
          mergePhiCongruenceClass((LirNaryOp)node);
        }
      }
    }

    // 8: Nullify phi congruence classes that contain only singleton resources.
    Enumeration keys=phiCongruenceClasses.keys();
    while(keys.hasMoreElements()){
      Symbol s=(Symbol)keys.nextElement();
      BiList phiCongruenceClass=(BiList)phiCongruenceClasses.get(s);
      if(phiCongruenceClass.length()==1){
        phiCongruenceClasses.remove(s);
        phiCongruenceClasses.put(s,new BiList());
      }
    }
  }

  /**
   * <pre>
   * ----------------------------------------------------------------------
   * 7: Merge phiCongruenceClass's for all resources in phiInst.
   *    currentphiCongruenceClass = {};
   *    for each resource xi in phiInst, where 0<=i<=n {
   *      currentphiCongruenceClass += phiCongruenceClass[xi];
   *      Let phiCongruenceClass[xi] simply point to currentphiCongruenceClass;
   *    }
   * ----------------------------------------------------------------------
   * </pre>
   * @param phiInst The current PHI instruction.
   **/
  private void mergePhiCongruenceClass(LirNaryOp phiInst){
    //BiList currentphiCongruenceClass=new BiList();
    BiList symbols=new BiList();

    // The symbol which is target of the current phi node.
    symbols.addNew(((LirSymRef)phiInst.kid(0)).symbol);

    // The symbols which are the source resource of the current phi node.
    for(int i=1;i<phiInst.nKids();i++){
      LirNode node=phiInst.kid(i).kid(0);
      if(node instanceof LirSymRef)
        symbols.addNew(((LirSymRef)phiInst.kid(i).kid(0)).symbol);
    }

    BiList merged=mergePhiCongruenceClass(symbols);
    for(BiLink pp=merged.first();!pp.atEnd();pp=pp.next()){
      Symbol s=(Symbol)pp.elem();
      phiCongruenceClasses.remove(s);
      phiCongruenceClasses.put(s,merged);
    }
  }

  /**
   * Merge phi congruence classes which are related the variables
   * in the same phi instruction.
   * @param list The variables which are in the same phi instruction
   * @return A new phi congruence class
   **/
  private BiList mergePhiCongruenceClass(BiList list){
    Stack stack=new Stack();
    for(BiLink p=list.first();!p.atEnd();p=p.next()){
      Symbol s=(Symbol)p.elem();
      stack.push(s);
    }

    BiList merged=new BiList();
    while(!stack.empty()){
      Symbol s=(Symbol)stack.pop();
      if(!merged.contains(s)){
        merged.addNew(s);
        BiList pcc=(BiList)phiCongruenceClasses.get(s);
        if(pcc!=null){
          for(BiLink p=pcc.first();!p.atEnd();p=p.next())
            stack.push(p.elem());
        }
      }
    }

    return(merged);
  }

  /**
   * Back translate from SSA form using Method III by Sreedhar.
   * @param phi The current Phi node
   * @param blk The current basic block
   * @return Candidate Resource Set
   **/
  private BiList methodIII(LirNaryOp phi,BasicBlk blk){
    BiList candidateResourceSet=new BiList();


    // Make `unresolvedNeighborMap' and initial it.
    // for each xi, 0<=i<=n, in phiInst
    //   unresolvedNeighborMap[xi]={}
    Hashtable unresolvedNeighborMap=new Hashtable();
    
    // 4: for each pair of resources xi:Li and xj:Lj in phiInst, 
    //             where 0<=i,j<=n and xi!=xj,
    //             such that there exists yi in phiCongruenceClass[xi],
    //             yj in phiCongruenceClass[xj], 
    //             and yi and yj interfere with each other, {
    //      Determine what copies needed to break the interference between xi
    //      and xj using the four cases as follows:
    //
    //      case 1:
    //        The intersection of phiCongruenceClass[xi] and Liveout[Lj] is not
    //        empty, and the intersection of phiCongruenceClass[xj] and
    //        LiveOut[Li] is empty. A new copy, xi'=xi, is needed in Li to 
    //        ensure that xi and xj are put in different phi congruence classes
    //        So xi is added to candidateResourceSet.
    //      case 2:
    //        The intersection of phiCongruenceClass[xi] and LiveOut[Lj] is 
    //        empty, and the intersection of phiCongruenceClass[xj] and 
    //        LiveOut[Li] is not empty. A new copy, xj'=xj, is needed in Lj to 
    //        ensure that xi and xj are put in different phi congruence 
    //        classes. So xj is added to candidateResourceSet.
    //      case 3:
    //        The intersection of phiCongruenceClass[xi] and LiveOut[Lj] is not
    //        empty, and the intersection of phiCongruenceClass[xj] and 
    //        LiveOut[Li] is not empty. Two new copies, xi'=xi in Li and xj'=xj
    //        in Lj, are needed to ensure that xi and xj are put in different
    //        phi congruence class. So xi and xj are added to 
    //        candidateResourceSet.
    //      case 4:
    //        The intersection of phiCongruenceClass[xi] and LiveOut[Lj] is 
    //        empty, and the intersection of phiCongruenceClass[xj] and
    //        LiveOut[Li] is empty. Either a copy, xi'=xi in Li, or a copy, 
    //        xj'=xj in Lj, is sufficient to eliminate the interference between
    //        xi and xj. However, the final decision of which copy to insert is
    //        deferred until all pairs of interfering resources in the phi 
    //        instruction are processed.
    //    }

    env.println("\n___ in "+phi,THR3);
    BiList unresolvedKeys=new BiList();

    for(int i=0;i<phi.nKids()-1;i++){
      m3Datas data=new m3Datas();
      if(i==0){
        // If xi is the target resource of the current phi node
        data.setXi((LirSymRef)phi.kid(i),blk);
      }
      else{
        // If xi is the source resource of the current phi node
        data.setXi((LirNaryOp)phi.kid(i));
      }

      for(int j=i+1;j<phi.nKids();j++){
        // xj is always the source resource of the current phi node
        data.setXj((LirNaryOp)phi.kid(j));

        //function.printIt(output);
        if(data.hasInterfere()){
          env.print("  Has interfere ("+data.nodeXi+","+data.nodeXj+")",THR3);
          int whichCase=data.whichCase();
          env.println("   --->  Case "+whichCase,THR3);

          if(whichCase==1||whichCase==3){
            candidateResourceSet.addNew(data.nodeXi);
          }
          if(whichCase==2||whichCase==3){
            candidateResourceSet.addNew(data.nodeXj);
          }
          if(whichCase==4){
            BiList unresolved=(BiList)unresolvedNeighborMap.get(data.nodeXi);
            if(unresolved==null){
              unresolved=new BiList();
              unresolvedNeighborMap.put(data.nodeXi,unresolved);
            }
            unresolved.addNew(data.nodeXj);
            unresolvedKeys.addNew(data.nodeXi);

            unresolved=(BiList)unresolvedNeighborMap.get(data.nodeXj);
            if(unresolved==null){
              unresolved=new BiList();
              unresolvedNeighborMap.put(data.nodeXj,unresolved);
            }
            unresolved.addNew(data.nodeXi);
            unresolvedKeys.addNew(data.nodeXj);
          }
        }
        else{
          env.println("  No interfere ("+data.nodeXi+","+data.nodeXj+")",THR3);
        }
        data.unsetXj();
      }
    }

    // sort unresolved naighbor map
    BiList sorted=new BiList();
    for(BiLink p=unresolvedKeys.first();!p.atEnd();p=p.next()){
      LirNode node1=(LirNode)p.elem();
      BiList map1=(BiList)unresolvedNeighborMap.get(node1);

      for(BiLink q=sorted.first();;q=q.next()){
        if(q.atEnd()){
          sorted.add(node1);
          break;
        }

        LirNode node2=(LirNode)q.elem();
        BiList map2=(BiList)unresolvedNeighborMap.get(node2);
        if(map2.length()<map1.length()){
          q.addBefore(node1);
          break;
        }
      }
    }

    // 5: Process the unresolved resources (case 4) as follows:
    //Enumeration e=unresolvedNeighborMap.keys();
    for(BiLink key=sorted.first();!key.atEnd();key=key.next()){
      LirNode node=(LirNode)key.elem();

      // if the node is already in the candidate resource set,
      // then do nothing with the if
      if(candidateResourceSet.contains(node))continue;

      BiList uSyms=(BiList)unresolvedNeighborMap.get(node);
      boolean shouldAdd=false;
      for(BiLink p=uSyms.first();!p.atEnd();p=p.next()){
        LirNode neighbor=(LirNode)p.elem();
        if(!candidateResourceSet.contains(neighbor)){
          //env.output.println("Neighbor "+neighbor);
          shouldAdd=true;
          break;
        }
      }
      if(shouldAdd){
        candidateResourceSet.addNew(node);
        env.println("  Added "+node+" By case 4.",THR3);
      }
    }
    
    return(candidateResourceSet);
  }

  /**
   * Back translate from SSA form using Method II by Sreedhar.
   * @param phi The current Phi node
   * @return Candidate Resource Set
   **/
  private BiList methodII(LirNaryOp phi){

    InterferenceGraph ig;
    ig=(InterferenceGraph)f.require(InterferenceGraph.analyzer);
    BiList candidateResourceSet=new BiList();
    BiList syms=new BiList();

    // Set the target symbol of Phi node into the list of symbols
    syms.add(phi.kid(0));
    
    // Set the source resource symbol of Phi node into the list of symbols
    for(int i=1;i<phi.nKids();i++){
      syms.add(phi.kid(i));
    }

    for(BiLink p=syms.first();!p.atEnd();p=p.next()){
      LirNode inode=(LirNode)p.elem();
      Symbol xi=null;
      if(inode.opCode==Op.LIST && inode.kid(0) instanceof LirSymRef){
          xi=((LirSymRef)inode.kid(0)).symbol;
      }
      else if(inode.opCode==Op.REG){
        xi=((LirSymRef)inode).symbol;
      }

      for(BiLink q=p.next();!q.atEnd();q=q.next()){
        LirNode jnode=(LirNode)q.elem();
        Symbol xj=null;
        if(jnode.opCode==Op.LIST && jnode.kid(0) instanceof LirSymRef){
          xj=((LirSymRef)jnode.kid(0)).symbol;
        }
        else if(jnode.opCode==Op.REG){
          xj=((LirSymRef)jnode).symbol;
        }

        // Check interference not only between xi and xj but also between
        // phi congruence classes which belongs to xi and xj.
        if(xi==null || xj==null){
          candidateResourceSet.addNew(inode);
          candidateResourceSet.addNew(jnode);
        }

        if((xi!=null && xj!=null) && (xi!=xj)){
          BiList pccXi=(BiList)phiCongruenceClasses.get(xi);
          BiList pccXj=(BiList)phiCongruenceClasses.get(xj);

          if(pccXi==pccXj) break;

          BiList xiList=new BiList();
          BiList xjList=new BiList();

          if(pccXi!=null)xiList=pccXi.copy();
          xiList.add(xi);

          if(pccXj!=null)xjList=pccXj.copy();
          xjList.add(xj);

          boolean exit=false;
          for(BiLink pp=xiList.first();!pp.atEnd();pp=pp.next()){
            Symbol si=(Symbol)pp.elem();
            for(BiLink qq=xjList.first();!qq.atEnd();qq=qq.next()){
              Symbol sj=(Symbol)qq.elem();

              if(ig.interfere(si,sj)){
                // There is an interference between xi and xj
                candidateResourceSet.addNew(jnode);
                candidateResourceSet.addNew(inode);
                exit=true;
                break;
              }
            }
            if(exit)break;
          }
        }
      }
    }

    return(candidateResourceSet);
  }

  /**
   * Back translate from SSA form using Method I by Sreedhar.
   * @param phi The current Phi node
   * @return Candidate Resource Set
   **/
  private BiList methodI(LirNaryOp phi){
    BiList candidateResourceSet=new BiList();

    // Set the target symbol of Phi node into the candidate resource set.
    candidateResourceSet.addNew(phi.kid(0));
    
    // Set the source resource symbol of Phi node into the candidate
    // resource set.
    for(int i=1;i<phi.nKids();i++){
      candidateResourceSet.addNew(phi.kid(i));
    }

    return(candidateResourceSet);
  }

  /**
   * <pre>
   * -----------------------------------------------------------------------
   * 1: for each resource, x, participated in a phi
   *    phiCongruenceClass[x] = {x};
   * -----------------------------------------------------------------------
   * </pre>
   * Initialize phi congruence classes of each resources in phi instructions.
   * @param g The current control flow graph
   **/
  private void initPhiCongruenceClass(FlowGraph g){
    phiCongruenceClasses=new Hashtable();
    for(BiLink p=g.basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        if(node.opCode==Op.PHI){
          Util util=new Util(env,f);
          BiList symList=util.findTargetLir(node,Op.REG,new BiList());
          for(BiLink r=symList.first();!r.atEnd();r=r.next()){
            LirSymRef reg=(LirSymRef)r.elem();
            if(phiCongruenceClasses.get(reg.symbol)==null){
              BiList phiCongruenceClass=new BiList();
              phiCongruenceClass.addNew(reg.symbol);
              phiCongruenceClasses.put(reg.symbol,phiCongruenceClass);
            }
          }
        }
      }
    }
  }

  /**
   * <pre>
   * -----------------------------------------------------------------------
   * 6: for each xi in candidateResourceSet
   *      insertCopy(xi,phiInst)
   *   
   *    insertCopy(xi,phiInst){
   *      if(xi is a source resource of phiInst){
   *        for every Lk associated with xi in the source list of phiInst {
   *          Insert a copy inst: xnew_i=xi at the end of Lk;
   *          Replace xi with xnew_i in phiInst;
   *          Add xnew_i in phiCongruenceClass[xnew_i];
   *          LiveOut[Lk]+=xnew_i;
   *          if(for Lj an immediate successor of Lk, xi not in LiveIn[Lj]
   *             and not used in a phi instruction associated with Lk in Lj)
   *            LiveOut[Lk]-=xi;
   *          Build interference edges between xnew_i and LiveOut[Lk];
   *        }
   *      }
   *      else{
   *        // xi is the phi target, x0.
   *        Insert a copy inst: x0=xnew_0 at the beginning of L0;
   *        Replace x0 with xnew_0 as the target in phiInst;
   *        Add xnew_0 in phiCongruenceClass[xnew_0];
   *        LiveIn[L0]-=x0;
   *        LiveIn[L0]+=xnew_0;
   *        Build interference edges between xnew_0 and LiveIn[L0];
   *      }
   *    }
   * -----------------------------------------------------------------------
   * </pre>
   * This method makes and inserts the copy assign expressions of the symbols
   * which are contained in candidate resource set.
   *
   * @param candidateResourceSet The list of symbols which make copy assign exp
   * @param phiInst The current phi node
  **/
  private void insertCopy(BiList candidateResourceSet,LirNaryOp phiInst,
                          BasicBlk L0){
    for(BiLink p=candidateResourceSet.first();!p.atEnd();p=p.next()){
      LirNode node=(LirNode)p.elem();

      if(node.opCode==Op.LIST){ // xi is a source resource
        Symbol xi=null;
        if(node.kid(0) instanceof LirSymRef)
          xi=((LirSymRef)node.kid(0)).symbol;

        BasicBlk Lk=((LirLabelRef)node.kid(1)).label.basicBlk();

        Symbol xnew_i=null;
        if(node.kid(0) instanceof LirSymRef)
          xnew_i=sstab.newSsaSymbol(xi);
        else
          xnew_i=sstab.newSsaSymbol(BACK_TMP,node.kid(0).type);

        // Make copy assign expression "xnew_i = xi"
        LirSymRef dst=(LirSymRef)env.lir.symRef(Op.REG,xnew_i.type,
                                                xnew_i,ImList.Empty);
        LirNode src=null;
        if(node.kid(0) instanceof LirSymRef){
          src=env.lir.symRef(Op.REG,xi.type,xi,ImList.Empty);
        }
        else if(node.kid(0) instanceof LirIconst){
          src=env.lir.iconst(node.kid(0).type,((LirIconst)node.kid(0)).value,
                             ImList.Empty);
        }
        else if(node.kid(0) instanceof LirFconst){
          src=env.lir.fconst(node.kid(0).type,((LirFconst)node.kid(0)).value,
                             ImList.Empty);
        }
        else{
          src=node.kid(0).makeCopy(env.lir);
        }

        LirBinOp copyOp=(LirBinOp)env.lir.operator(Op.SET,dst.type,dst,
                                                   src,ImList.Empty);

        // Insert a copy inst: xnew_i = xi at the end of Lk
        Lk.instrList().last().addBefore(copyOp);
        env.println("Insert Copy : "+copyOp+" in block "+Lk.id,THR);
        f.flowGraph().touch();

        //env.output.println(phiInst);
        
        // Add xnew_i in phiCongruenceClass[xnew_i];
        if(phiCongruenceClasses.get(xnew_i)==null){
          BiList phiCongruenceClass=new BiList();
          phiCongruenceClass.addNew(xnew_i);
          phiCongruenceClasses.put(xnew_i,phiCongruenceClass);
        }
        


        // Replace xi with xnew_i in phiInst;
        LirNode newReg=env.lir.symRef(Op.REG,xnew_i.type,
                                      xnew_i,ImList.Empty);
        node.setKid(0,newReg);

        // Update the information of live range about the variables.
        f.require(InterferenceGraph.analyzer);
      }
      else if(node.opCode==Op.REG){ // xi is the phi target ( xi == x0 )
        Symbol xi=((LirSymRef)node).symbol;
        // Make copy assign expression "x0 = xnew_0"
        Symbol xnew_0=sstab.newSsaSymbol(xi);

        LirSymRef dst=(LirSymRef)env.lir.symRef(Op.REG,xi.type,
                                                xi,ImList.Empty);
        LirSymRef src=(LirSymRef)env.lir.symRef(Op.REG,xnew_0.type,
                                                xnew_0,ImList.Empty);
        LirBinOp copyOp=(LirBinOp)env.lir.operator(Op.SET,dst.type,
                                                   dst,src,ImList.Empty);



        // Insert a copy inst: x0 = xnew_0 at the beginning of L0;
        // where just after the phi nodes.
        for(BiLink q=L0.instrList().first();!q.atEnd();q=q.next()){
          LirNode tempNode=(LirNode)q.elem();
          if(tempNode.opCode!=Op.PHI){
            q.addBefore(copyOp);
            f.flowGraph().touch();
            env.println("Insert Copy : "+copyOp+" in block "+L0.id,THR);
            break;
          }
        }

        // Add xnew_0 in phiCongruenceClass[xnew_0];
        if(phiCongruenceClasses.get(xnew_0)==null){
          BiList phiCongruenceClass=new BiList();
          phiCongruenceClass.addNew(xnew_0);
          phiCongruenceClasses.put(xnew_0,phiCongruenceClass);
        }
        


        // Replace x0 with xnew_0 as the target in phiInst
        LirNode newReg=env.lir.symRef(Op.REG,xnew_0.type,xnew_0,ImList.Empty);
        phiInst.setKid(0,newReg);

        // Update the information of live range about the variables.
        f.require(InterferenceGraph.analyzer);
      }
      else{
        System.err.println("BackTranslateFromSsa.java : unexpected LIR "+node);
        System.exit(1);
      }
    }
  }
}
