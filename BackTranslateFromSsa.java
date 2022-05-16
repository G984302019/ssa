/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.IoRoot;
import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.Op;
import coins.backend.cfg.FlowGraph;
import coins.backend.cfg.BasicBlk;
import coins.backend.util.BiList;
import coins.backend.util.ImList;
import coins.backend.util.BiLink;
import coins.backend.sym.Symbol;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.lir.LirBinOp;
import coins.backend.lir.LirNaryOp;
import coins.backend.lir.LirLabelRef;
import coins.backend.lir.LirIconst;
import coins.backend.lir.LirFconst;
import coins.backend.ana.LiveVariableAnalysis;
import coins.backend.ana.LiveVariableSlotwise;
import coins.backend.ana.InterferenceGraph;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Stack;
import java.util.Set;

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
class BackTranslateFromSsa implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "BackTranslateFromSsa"; }
  public String subject() {
    return "Back translation from SSA form using Sreedhar's method.";
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
  BackTranslateFromSsa(SsaEnvironment e,SsaSymTab stab,
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
    env.println("****************** Back Translate from SSA form to "+
                function.symbol.name,SsaEnvironment.MinThr);

    f=function;

    // Aggregate LIR trees again
    if(aggregate){
      AggregateInstructions aggre=new AggregateInstructions(env,f);
    }
    //f.printIt(env.output);

    oustConstant();

    // Step 1: Translating the TSSA form to a CSSA form.
    // Initialize phi congruence class of each resources in phi instruction.
    initPhiCongruenceClass(f.flowGraph());
    tssaToCssa(f.flowGraph());

    if(env.opt.isSet(OptionName.SSA_DEBUG))
      checkPcc();
    //f.printIt(env.output);

    // Step 2: Eliminating redundant copies.
    if(coalesce){
      coalescing(f.flowGraph());
    }

    //f.printIt(env.output);

    // Step 3: Eliminating phi instructions and leaving the CSSA form.
    leavingCssa(f.flowGraph());

    // Set special LirLabelRef node instead of normal LirLabelRef.
    Util util=new Util(env,f);
    util.changeLabelRef(false);
    f.touch();

    env.println("",THR);
    return(true);
  }

  private void oustConstant(){
	  BiLink first = f.flowGraph().basicBlkList.first();
	  BasicBlk firstBlk = (BasicBlk)first.elem();
	  for(BiLink q=firstBlk.instrList().first();!q.atEnd();q=q.next()){
		  LirNode node=(LirNode)q.elem();
		  if(node.opCode == Op.CALL){
			  LirNode calledFunc = node.kid(0);
			  if(calledFunc instanceof LirSymRef && 
					  ((LirSymRef)calledFunc).symbol.name==sstab.DUMMY_FUNC){
				  q.unlink();
				  f.touch();
			  }
		  }
	  }
	  f.module.globalSymtab.remove(sstab.DUMMY_FUNC);
	  
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

  private void checkPcc(){
    env.output.print("SSA DBG : checking interfere "+f.symbol.name+" ... ");
    for(BiLink pp=f.flowGraph().basicBlkList.first();!pp.atEnd();pp=pp.next()){
      BasicBlk blk=(BasicBlk)pp.elem();
      for(BiLink qq=blk.instrList().first();!qq.atEnd();qq=qq.next()){
        LirNode node=(LirNode)qq.elem();
        if(node.opCode==Op.PHI){
          Symbol s=((LirSymRef)node.kid(0)).symbol;
          BiList pcc=(BiList)phiCongruenceClasses.get(s);
          InterferenceGraph ig;
          ig=(InterferenceGraph)f.require(InterferenceGraph.analyzer);

          for(BiLink p=pcc.first();!p.atEnd();p=p.next()){
            Symbol s1=(Symbol)p.elem();
            for(BiLink q=p.next();!q.atEnd();q=q.next()){
              Symbol s2=(Symbol)q.elem();
              if(ig.interfere(s1,s2)){
                f.printIt(env.output);
                env.output.println("\nSSA DBG : in "+pcc);
                env.output.println("SSA DBG : "+s1+" and "+s2+
                                   " has interfere!!");
                System.exit(1);
              }
            }
          }
        }
      }
    }
    env.output.println("ok");
  }

  /**
   * Invoke SSA based coalescing.
   * @param g The current control flow graph
   **/
  private void coalescing(FlowGraph g){
    for(BiLink p=g.basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        // The target of this coalescing method is only that:
        //     REG = REG
        if(node.opCode==Op.SET && 
           node.kid(0).opCode==Op.REG && node.kid(1).opCode==Op.REG){
          //env.output.println(node);
          Symbol x=((LirSymRef)node.kid(0)).symbol;
          Symbol y=((LirSymRef)node.kid(1)).symbol;

          BiList pccX=(BiList)phiCongruenceClasses.get(x);
          BiList pccY=(BiList)phiCongruenceClasses.get(y);
          //env.output.println(pccX);
          //env.output.println(pccY);

          if(pccX!=null && pccY!=null){
            boolean interfered=false;
            int pccXSize=pccX.length();
            int pccYSize=pccY.length();

            if(pccXSize==0 && pccYSize==0){
              // Case 1:
              //  This means that x and y are not referenced in any phi
              //  instruction.
              //  The copy can be removed even if x and y interfere.
              env.println("SSA based coalescing : Case 1",THR3);
              // do nothing
            }
            else if(pccXSize==0 && pccYSize>0){
              // Case 2-1:
              //  If x interferes with any resource in 
              //  (phiCongruenceClass[y]-y) then the copy cannot be removed,
              //  otherwise it can be removed.
              env.println("SSA based coalescing : Case 2-1",THR3);
              
              InterferenceGraph ig;
              ig=(InterferenceGraph)f.require(InterferenceGraph.analyzer);
              
              for(BiLink pp=pccY.first();!pp.atEnd();pp=pp.next()){
                Symbol s=(Symbol)pp.elem();
                if(!s.equals(y) && ig.interfere(x,s)){
                  env.println(x.name+" and "+s.name+" are interfered",THR3);
                  interfered=true;
                  break;
                }
              }
            }
            else if(pccXSize>0 && pccYSize==0){
              // Case 2-2:
              //  If y interferes with any resource in 
              //  (phiCongruenceClass[x]-x) then the copy cannot be removed,
              //  otherwise it can be removed.
              env.println("SSA based coalescing : Case 2-2",THR3);
              
              InterferenceGraph ig;
              ig=(InterferenceGraph)f.require(InterferenceGraph.analyzer);
              
              for(BiLink pp=pccX.first();!pp.atEnd();pp=pp.next()){
                Symbol s=(Symbol)pp.elem();
                if(!s.equals(x) && ig.interfere(y,s)){
                  env.println(s.name+" and "+y.name+" are interfered",THR3);
                  interfered=true;
                  break;
                }
              }
            }
            else if(pccXSize>0 && pccYSize>0){
              // If the phi congruence class of x and the phi congruence class 
              // of y are the same object, then the copy assign expression can 
              // be eliminated because x and y will became a single name.
              InterferenceGraph ig;
              ig=(InterferenceGraph)f.require(InterferenceGraph.analyzer);
              
              if(pccX.equals(pccY)){
                env.println("SSA based coalescing : "+x.name+" and "+
                            y.name+" have the same phiCongruenceClass",THR3);
                // do nothing
              }
              else{
                // Case 3
                //  The copy cannot be removed if any resource in 
                //  phiCongruenceClass[x] interferes with any resource in
                //  (phiCongruenceClass[y]-y) or if any resource in 
                //  phiCongruenceClass[y] interferes with any resource in 
                //  (phiCongruenceClass[x]-x), othrewise it can be removed.
                env.println("SSA based coalescing : Case 3",THR3);
                for(BiLink pp=pccX.first();!pp.atEnd();pp=pp.next()){
                  Symbol s=(Symbol)pp.elem();
                  if(!s.equals(x)){
                    for(BiLink qq=pccY.first();!qq.atEnd();qq=qq.next()){
                      Symbol ss=(Symbol)qq.elem();
                      if(ig.interfere(s,ss)){
                        env.println(s.name+" and "+ss.name+
                                    " have interference",THR3);
                        interfered=true;
                        break;
                      }
                    }
                    if(interfered)break;
                  }
                }
                if(!interfered){
                  for(BiLink pp=pccY.first();!pp.atEnd();pp=pp.next()){
                    Symbol s=(Symbol)pp.elem();
                    if(!s.equals(y)){
                      for(BiLink qq=pccX.first();!qq.atEnd();qq=qq.next()){
                        Symbol ss=(Symbol)qq.elem();
                        if(ig.interfere(s,ss)){
                          env.println(s.name+" and "+ss.name+
                                      " have interference",THR3);
                          interfered=true;
                          break;
                        }
                      }
                      if(interfered)break;
                    }
                  }
                }
              }
            }
            if(!interfered){
              env.println("SSA based coalescing : remove "+node+
                          " in block "+blk.id,THR2);
              q.unlink();
              f.flowGraph().touch();
              BiList syms=new BiList();

              syms.addNew(x);
              syms.addNew(y);

              for(BiLink pp=pccX.first();!pp.atEnd();pp=pp.next()){
                syms.addNew(pp.elem());
              }
              for(BiLink pp=pccY.first();!pp.atEnd();pp=pp.next()){
                syms.addNew(pp.elem());
              }
              BiList list=mergePhiCongruenceClass(syms);
              list.addNew(x);
              list.addNew(y);
              for(BiLink pp=list.first();!pp.atEnd();pp=pp.next()){
                Symbol s=(Symbol)pp.elem();
                phiCongruenceClasses.remove(s);
                phiCongruenceClasses.put(s,list);
              }

              //env.output.println(list);
            }
          }
        }
      }
    }
  }

  /**
   * Eliminate phi nodes and leave from SSA form.
   * The resources of phi nodes are rewrote into represent symbol.
   * @param g The current control flow graph
   **/
  private void leavingCssa(FlowGraph g){
    Hashtable representName=new Hashtable();
    for(BiLink p=g.basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        if(node.opCode==Op.PHI){
          //env.output.println(node);
          q.unlink();
          g.touch();
        }
        else if(node.nKids()>0){
          Stack stack=new Stack();
          stack.push(node);
          while(!stack.empty()){
            LirNode parent=(LirNode)stack.pop();
            for(int i=0;i<parent.nKids();i++){
              LirNode child=parent.kid(i);
              if(child.nKids()>0){
                // The child node has some children.
                // ( That is not a leaf node )
                stack.push(child);
              }
              else{
                // The child is a leaf node.
                if(child.opCode==Op.REG){
                  Symbol s=((LirSymRef)child).symbol;
                  BiList phiCongruenceClass;
                  phiCongruenceClass=(BiList)phiCongruenceClasses.get(s);

                  if(phiCongruenceClass!=null){
                    if(!representName.containsKey(phiCongruenceClass)){
                      //if(representName.contains(s.shadow())){
                      //  representName.put(phiCongruenceClass,s);
                      //}
                      //else{
                      //  representName.put(phiCongruenceClass,s.shadow());
                      //}
                      representName.put(phiCongruenceClass,s);
                    }
                    
                    Symbol ss=(Symbol)representName.get(phiCongruenceClass);
                    LirSymRef newReg=(LirSymRef)env.lir.symRef(Op.REG,
                                                               ss.type,ss,
                                                               ImList.Empty);
                    parent.setKid(i,newReg);
                    g.touch();
                  }
                }
              }
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
    BiList alreadyInserted=new BiList();
    Symbol s;
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
    BiList alreadyInserted=new BiList();
    Symbol s;

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
      LirNode node=phi.kid(i).kid(0);
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
