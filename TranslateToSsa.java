/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.cfg.BasicBlk;
import coins.backend.cfg.FlowGraph;
import coins.backend.Function;
import coins.backend.Storage;
import coins.backend.Op;
import coins.backend.Type;
import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.util.BiLink;
import coins.backend.util.BiList;
import coins.backend.util.ImList;
import coins.backend.ana.Dominators;
import coins.backend.ana.DominanceFrontiers;
import coins.backend.ana.LiveVariableAnalysis;
import coins.backend.ana.LiveVariableSlotwise;
import coins.backend.sym.Symbol;
import coins.backend.sym.Label;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.lir.LirLabelRef;

/**
 * Translate to the static single assignment form ( SSA form ).
 * There are 3 major forms in SSA form :<br>
 *   1. minimal SSA<br>
 *   2. semi-pruned SSA<br>
 *   3. pruned SSA<br>
 * The difference among these form is the number of PHI instructions.
 * This class can translate to these 3 forms.
 * This class also fold copy expressions during rename phase.
 **/
public class TranslateToSsa implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "TranslateToSsa"; }
  public String subject() {
    return "Translate into SSA form.";
  }

  /**
   * The stack object using BiList.
   **/
  private class BiListAsStack{
    /** Stack body **/
    private BiList list;
    /**
     * Constructor
     **/
    BiListAsStack(){
      list=new BiList();
    }
    /**
     * Pop the object from the stack.
     * @return The top object of the Stack
     **/
    Object pop(){
      return(list.takeFirst());
    }

    /**
     * Push the object into the stack.
     * @param o The object which is put into the stack
     **/
    void push(Object o){
      list.addFirst(o);
    }

    /**
     * Peek the top object of the stack. This method does not remove the 
     * top object of the stack.
     * @return The top object of the stack
     **/
    Object peek(){
      return(list.first().elem());
    }
  }

  /** The minimal SSA form **/
  public static final int MINIMAL=0;
  /** The semi-pruned SSA form **/
  public static final int SEMI_PRUNED=1;
  /** The pruned SSA form **/
  public static final int PRUNED=2;
  /** The type of the translation to SSA form **/
  private final int type;
  /** If the value is set `true', then do copy folding **/
  private final boolean withCopyFold;
  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.SsaThr;
  /** The threshold of the debug print **/
  public static final int THR2=SsaEnvironment.OptThr;
  /** The symbol table of SSA form **/
  private SsaSymTab sstab;
  /** The dominator object **/
  private Dominators dom;
  /** The stack for renaming **/
  private BiListAsStack[] stack;
  /** The current function **/
  private Function f;
  /** The maximam number of the original symbol table **/
  private int orgSymtabMax;
  /** The list of the variables which need to initialize **/
  private BiList initVariables;

  /**
   * Constructor
   * @param e The environment of the SSA form
   * @param stab The current symbol table on SSA form
   * @param howToTranslate Specify the translate method
   * @param withCopyFolding Whether copy fold or not
   **/
  TranslateToSsa(SsaEnvironment e,SsaSymTab stab,int howToTranslate,
                 boolean withCopyFolding){
    sstab=stab;
    env=e;
    type=howToTranslate;
    withCopyFold=withCopyFolding;

    int msg=SsaEnvironment.MsgThr;
    // information
    env.print("  SSA translation : ",msg);
    switch(type){
      case MINIMAL: env.print("MINIMAL",msg);break;
      case SEMI_PRUNED: env.print("SEMI_PRUNED",msg);break;
      case PRUNED: env.print("PRUNED",msg);
    }
    if(withCopyFold) env.println(" with Copy Folding.",msg);
    else env.println(" without Copy Folding.",msg);
  }

  /**
   * Translate to the SSA form.
   * @param function The current function
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    env.println("****************** Translate into SSA form to "+
                function.symbol.name,SsaEnvironment.MinThr);

    f=function;
    orgSymtabMax=f.localSymtab.idBound();

    // Set special LirLabelRef node instead of normal LirLabelRef.
    Util util=new Util(env,f);
    util.changeLabelRef(true);

    // Insert Phi nodes
    insertPhiInstruction();

    // Rename variables name
    dom=(Dominators)f.require(Dominators.analyzer);
    stack=new BiListAsStack[f.localSymtab.idBound()];
    initVariables=new BiList();
    renameVariables(f.flowGraph().entryBlk());
    makeInitStmts();

    //f.printIt(output);
    env.println("",THR);

    return(true);
  }

  /**
   * Make new Phi instructions and insert them to the basic blocks.
   **/
  private void insertPhiInstruction(){
    FlowGraph g=f.flowGraph();
    BiList[] inserted=new BiList[g.idBound()];
    BiList[] defsites=new BiList[f.localSymtab.idBound()];
    BiList nonLocal=null;
    if(type==SEMI_PRUNED)
      nonLocal=findNonLocal(g);

    Symbol[] syms=new Symbol[f.localSymtab.idBound()];

    DominanceFrontiers df;
    df=(DominanceFrontiers)f.require(DominanceFrontiers.analyzer);
 
    // Find the defined register
    for(BiLink p=g.basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink bp=blk.instrList().first();!bp.atEnd();bp=bp.next()){
        LirNode node=(LirNode)bp.elem();

        switch(node.opCode){
          case Op.SET:{
            switch(node.kid(0).opCode){
              case Op.SUBREG:{
                if(node.kid(0).kid(0).opCode!=Op.REG) break;
                Symbol s=((LirSymRef)node.kid(0).kid(0)).symbol;
                if(defsites[s.id]==null){
                  defsites[s.id]=new BiList();
                }
                defsites[s.id].addNew(blk);
                syms[s.id]=s;
                break;
              }
              case Op.REG:{
                Symbol s=((LirSymRef)node.kid(0)).symbol;
                if(defsites[s.id]==null){
                  defsites[s.id]=new BiList();
                }
                defsites[s.id].addNew(blk);
                syms[s.id]=s;
                break;
              }
            }
            break;
          }
          case Op.CALL:{
            for(int i=0;i<node.kid(2).nKids();i++){
              switch(node.kid(2).kid(i).opCode){
                case Op.SUBREG:{
                  if(node.kid(2).kid(i).kid(0).opCode!=Op.REG) break;
                  Symbol s=((LirSymRef)node.kid(2).kid(i).kid(0)).symbol;
                  if(defsites[s.id]==null){
                    defsites[s.id]=new BiList();
                  }
                  defsites[s.id].addNew(blk);
                  syms[s.id]=s;
                  break;
                }
                case Op.REG:{
                  Symbol s=((LirSymRef)node.kid(2).kid(i)).symbol;
                  if(defsites[s.id]==null){
                    defsites[s.id]=new BiList();
                  }
                  defsites[s.id].addNew(blk);
                  syms[s.id]=s;
                  break;
                }
              }
            }
            break;
          }
          case Op.PARALLEL:{
            for(int i=0;i<node.nKids();i++){
              LirNode child=node.kid(i);
              switch(child.opCode){
                case Op.SET:{
                  switch(child.kid(0).opCode){
                    case Op.SUBREG:{
                      if(child.kid(0).kid(0).opCode!=Op.REG) break;
                      Symbol s=((LirSymRef)child.kid(0).kid(0)).symbol;
                      if(defsites[s.id]==null){
                        defsites[s.id]=new BiList();
                      }
                      defsites[s.id].addNew(blk);
                      syms[s.id]=s;
                      break;
                    }
                    case Op.REG:{
                      Symbol s=((LirSymRef)child.kid(0)).symbol;
                      if(defsites[s.id]==null){
                        defsites[s.id]=new BiList();
                      }
                      defsites[s.id].addNew(blk);
                      syms[s.id]=s;
                      break;
                    }
                  }
                  break;
                }
                case Op.CALL:{
                  for(int j=0;j<child.kid(2).nKids();j++){
                    switch(child.kid(2).kid(j).opCode){
                      case Op.SUBREG:{
                        if(child.kid(2).kid(j).kid(0).opCode!=Op.REG) 
                          break;
                        Symbol s;
                        s=((LirSymRef)child.kid(2).kid(j).kid(0)).symbol;
                        if(defsites[s.id]==null){
                          defsites[s.id]=new BiList();
                        }
                        defsites[s.id].addNew(blk);
                        syms[s.id]=s;
                        break;
                      }
                      case Op.REG:{
                        Symbol s=((LirSymRef)child.kid(2).kid(j)).symbol;
                        if(defsites[s.id]==null){
                          defsites[s.id]=new BiList();
                        }
                        defsites[s.id].addNew(blk);
                        syms[s.id]=s;
                        break;
                      }
                    }
                  }
                  break;
                }
                case Op.USE:
                case Op.CLOBBER:{
                  switch(child.kid(0).opCode){
                    case Op.REG:{
                      Symbol s=((LirSymRef)child.kid(0)).symbol;
                      if(defsites[s.id]==null){
                        defsites[s.id]=new BiList();
                      }
                      defsites[s.id].addNew(blk);
                      syms[s.id]=s;
                      break;
                    }
                    case Op.SUBREG:{
                      if(child.kid(0).kid(0).opCode!=Op.REG) break;
                      Symbol s=((LirSymRef)child.kid(0).kid(0)).symbol;
                      if(defsites[s.id]==null){
                        defsites[s.id]=new BiList();
                      }
                      defsites[s.id].addNew(blk);
                      syms[s.id]=s;
                      break;
                    }
                  }
                  break;
                }
              }
            }
          }
        }
      }
    }
    // Insert Phi instructions
    Util util=new Util(env,f);
    for(int i=0;i<f.localSymtab.idBound();i++){
      if(defsites[i]!=null){
        for(BiLink p=defsites[i].first();!p.atEnd();p=p.next()){
          BasicBlk blk=(BasicBlk)p.elem();
          for(BiLink q=df.frontiers[blk.id].first();!q.atEnd();q=q.next()){
            BasicBlk frontier=(BasicBlk)q.elem();

            if(type==PRUNED){ // pruned ssa
              // Insert Phi node only if the "syms[i]" live in the block
              // "frontier".
              LiveVariableAnalysis liveAna;
              liveAna=
                (LiveVariableAnalysis)f.require(LiveVariableSlotwise.analyzer);
              BiList live=liveAna.liveIn(frontier);
              if(live.contains(syms[i])){
                if(inserted[frontier.id]==null){
                  inserted[frontier.id]=new BiList();
                }
                if(!inserted[frontier.id].contains(syms[i])){
                  LirNode phi=util.makePhiInst(syms[i],frontier);
                  frontier.instrList().addFirst(phi);
                  env.println("Insert PHI : "+
                              frontier.instrList().first().elem()+
                              " in block "+frontier.id,THR);
                  g.touch();
                  inserted[frontier.id].addNew(syms[i]);
                  defsites[i].addNew(frontier);
                }
              }
            }
            else if(type==SEMI_PRUNED){ // semi-pruned ssa
              // Insert Phi node only if the "syms[i]" is a non-local variable
              // of the block "blk".
              if(nonLocal.contains(syms[i])){
                if(inserted[frontier.id]==null){
                  inserted[frontier.id]=new BiList();
                }
                if(!inserted[frontier.id].contains(syms[i])){
                  LirNode phi=util.makePhiInst(syms[i],frontier);
                  frontier.instrList().addFirst(phi);
                  env.println("Insert PHI : "+
                              frontier.instrList().first().elem()+
                              " in block "+frontier.id,THR);
                  g.touch();
                  inserted[frontier.id].addNew(syms[i]);
                  defsites[i].addNew(frontier);
                }
              }
            }
            else{ // minimal SSA
              if(inserted[frontier.id]==null){
                inserted[frontier.id]=new BiList();
              }
              if(!inserted[frontier.id].contains(syms[i])){
                LirNode phi=util.makePhiInst(syms[i],frontier);
                frontier.instrList().addFirst(phi);
                env.println("Insert PHI : "+
                            frontier.instrList().first().elem()+
                            " in block "+frontier.id,THR);
                g.touch();
                inserted[frontier.id].addNew(syms[i]);
                defsites[i].addNew(frontier);
              }
            }
          }
        }
      }
    }
  }

  /**
   * Find non-local variables in the current control flow graph.
   * This method is used in translation into semi-pruned SSA form.
   * @param g The current control flow graph
   * @return The list of the variables which are non-local
   **/
  private BiList findNonLocal(FlowGraph g){
    Util util=new Util(env,f);
    BiList nonlocals=new BiList();

    // For each basic block in the current control flow graph.
    for(BiLink p=g.basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      BiList kill=new BiList();

      // For each instruction in the current basic block.
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        BiList localDef=new BiList();
        BiList regs=new BiList();

        switch(node.opCode){
          case Op.SET:{
            // search
            regs=util.findTargetLir(node.kid(1),Op.REG,new BiList());
            switch(node.kid(0).opCode){
              case Op.REG:{
                localDef.addNew(((LirSymRef)node.kid(0)).symbol);
                break;
              }
              case Op.SUBREG:{
                if(node.kid(0).kid(0).opCode==Op.REG){
                  localDef.addNew(((LirSymRef)node.kid(0).kid(0)).symbol);
                  break;
                }
              }
              default:{
                regs=util.findTargetLir(node.kid(0),Op.REG,regs);
              }
            }

            break;
          }
          case Op.CALL:{
            // search
            regs=util.findTargetLir(node.kid(0),Op.REG,new BiList());
            regs=util.findTargetLir(node.kid(1),Op.REG,regs);
            for(int i=0;i<node.kid(2).nKids();i++){
              switch(node.kid(2).kid(i).opCode){
                case Op.REG:{
                  localDef.addNew(((LirSymRef)node.kid(2).kid(i)).symbol);
                  break;
                }
                case Op.SUBREG:{
                  if(node.kid(2).kid(i).kid(0).opCode==Op.REG){
                    Symbol s=((LirSymRef)node.kid(2).kid(i).kid(0)).symbol;
                    localDef.addNew(s);
                    break;
                  }
                }
                default:{
                  regs=util.findTargetLir(node.kid(2).kid(i),Op.REG,regs);
                }
              }
            }

            break;
          }
          case Op.PARALLEL:{
            for(int i=0;i<node.nKids();i++){
              LirNode child=node.kid(i);
              switch(child.opCode){
                case Op.SET:{
                  // search
                  regs=util.findTargetLir(child.kid(1),Op.REG,regs);
                  switch(child.kid(0).opCode){
                    case Op.REG:{
                      localDef.addNew(((LirSymRef)child.kid(0)).symbol);
                      break;
                    }
                    case Op.SUBREG:{
                      if(child.kid(0).kid(0).opCode==Op.REG){
                        Symbol s=((LirSymRef)child.kid(0).kid(0)).symbol;
                        localDef.addNew(s);
                        break;
                      }
                    }
                    default:{
                      regs=util.findTargetLir(child.kid(0),Op.REG,regs);
                    }
                  }

                  break;
                }
                case Op.CALL:{
                  // search
                  regs=util.findTargetLir(child.kid(0),Op.REG,regs);
                  regs=util.findTargetLir(child.kid(1),Op.REG,regs);
                  for(int j=0;j<child.kid(2).nKids();j++){
                    switch(child.kid(2).kid(j).opCode){
                      case Op.REG:{
                        Symbol s=((LirSymRef)child.kid(2).kid(j)).symbol;
                        localDef.addNew(s);
                        break;
                      }
                      case Op.SUBREG:{
                        if(child.kid(2).kid(j).kid(0).opCode==Op.REG){
                          Symbol s=((LirSymRef)child.kid(2).kid(j).kid(0)).symbol;
                          localDef.addNew(s);
                          break;
                        }
                      }
                      default:{
                        regs=util.findTargetLir(child.kid(2).kid(j),Op.REG,regs);
                      }
                    }
                  }
                  break;
                }
                case Op.USE:
                case Op.CLOBBER:{
                  switch(child.kid(0).opCode){
                    case Op.REG:{
                      Symbol s=((LirSymRef)child.kid(0)).symbol;
                      localDef.addNew(s);
                      break;
                    }
                    case Op.SUBREG:{
                      if(child.kid(0).kid(0).opCode==Op.REG){
                        Symbol s=((LirSymRef)child.kid(0).kid(0)).symbol;
                        localDef.addNew(s);
                        break;
                      }
                    }
                    default:{
                      regs=util.findTargetLir(child,Op.REG,regs);
                    }
                  }
                  break;
                }
              }
            }

            break;
          }
          default:{
            regs=util.findTargetLir(node,Op.REG,new BiList());
          }
        }

        // update non-local variable
        for(BiLink r=regs.first();!r.atEnd();r=r.next()){
          LirSymRef regNode=(LirSymRef)r.elem();
          if(!kill.contains(regNode.symbol)){
            nonlocals.addNew(regNode.symbol);
          }
        }

        // update kill
        for(BiLink r=localDef.first();!r.atEnd();r=r.next())
          kill.addNew((Symbol)r.elem());

      }
    }

    return(nonlocals);
  }

  /**
   * Rename the variables name to SSA name.
   * @param blk The current basic block
   **/
  private void renameVariables(BasicBlk blk){

    int count[]=new int[orgSymtabMax];
    for(int i=0;i<orgSymtabMax;i++) count[i]=0;

    for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
      LirNode node=(LirNode)p.elem();
      if(node.opCode!=Op.PHI && node.opCode!=Op.PROLOGUE){
        // If the current node is a assign node, rename the variables which 
        // are only right hand side of the node.
        // If the current node is not a assign node, rename the variables
        // in whole of the statement.
        renameSymbolToStackTop(node);
      }

      // If the definition is found, make a new ssa name and rename the
      // original one.
      if((node.opCode==Op.SET && node.kid(0).opCode==Op.REG) ||
         node.opCode==Op.PHI || node.opCode==Op.PROLOGUE ||
         (node.opCode==Op.CALL && node.kid(2).nKids()>0 &&
          node.kid(2).kid(0).opCode==Op.REG)){

        // If do the copy folding, execute below.
        if(withCopyFold && node.opCode==Op.SET && node.kid(0).opCode==Op.REG &&
           node.kid(1).opCode==Op.REG){
          LirSymRef symRefDst=(LirSymRef)node.kid(0);
          int num=symRefDst.symbol.id;
          if(stack[num]==null)
            makeNewStack(num,symRefDst.symbol);

          stack[num].push(((LirSymRef)node.kid(1)).symbol);
          count[num]++;
          env.println("Copy Folding : remove "+node+" in block "+blk.id,THR2);
          p.unlink();
          f.flowGraph().touch();
        }
        else{
          if((node.opCode==Op.SET && node.kid(0).opCode==Op.REG) ||
             node.opCode==Op.PHI){ // SET or PHI
            LirSymRef symRef=(LirSymRef)node.kid(0);
            node.setKid(0,makeNewReg(symRef,count));
            f.flowGraph().touch();
          } // SET or PHI
          else if(node.opCode==Op.PROLOGUE){ // PROLOGUE
            for(int i=0;i<node.nKids();i++){
              if(node.kid(i).opCode==Op.REG){
                LirSymRef symRef=(LirSymRef)node.kid(i);
                node.setKid(i,makeNewReg(symRef,count));
                f.flowGraph().touch();
              }
            }
          }// PROLOGUE
          else{ // CALL
            LirSymRef symRef=(LirSymRef)node.kid(2).kid(0);
            node.kid(2).setKid(0,makeNewReg(symRef,count));
            f.flowGraph().touch();
          }
        }
      }
    }

    // Rename the arguments of Phi node which is in each successor of the
    // current basic block.
    for(BiLink p=blk.succList().first();!p.atEnd();p=p.next()){
      BasicBlk succ=(BasicBlk)p.elem();
      for(BiLink q=succ.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        if(node.opCode==Op.PHI){
          for(int i=1;i<node.nKids();i++){
            if(blk.label().basicBlk()==
               ((LirLabelRef)node.kid(i).kid(1)).label.basicBlk()){
              LirSymRef symRef=(LirSymRef)node.kid(i).kid(0);
              int num=symRef.symbol.id;
              if(stack[num]==null)
                makeNewStack(num,symRef.symbol);

              Symbol sym=(Symbol)stack[num].peek();
              LirSymRef newSymRef=(LirSymRef)env.lir.symRef(Op.REG,
                                                            sym.type,
                                                            sym,ImList.Empty);
              node.kid(i).setKid(0,newSymRef);
              f.flowGraph().touch();
            }
          }
        }
        else break;
      }
    }

    // Rename recursively.
    for(BiLink p=dom.kids[blk.id].first();!p.atEnd();p=p.next()){
      renameVariables((BasicBlk)p.elem());
    }

    // Pop from stack.
    for(int i=0;i<orgSymtabMax;i++){
      if(count[i]>0){
        for(int j=0;j<count[i];j++) stack[i].pop();
      }
    }
  }

  /**
   * Make a new value stack which is used in renaming process.
   * @param num The unique number of the symbol belonged to this stack
   * @param symbol The symbol belonged to this stack
   **/
  private void makeNewStack(int num,Symbol symbol){
    stack[num]=new BiListAsStack();
    Symbol s=sstab.newSsaSymbol1(symbol);    /////
    stack[num].push(s);
    initVariables.add(s);
  }

  /**
   * Make initial statements for non-initialized variables and set them
   * into the entry block.
   * The initial value is 0 (long) or 0.0 (double) depends on their type.
   **/
  private void makeInitStmts(){
	  if(initVariables.length() == 0)    /////
		  return;
    BasicBlk entryBlk=f.flowGraph().entryBlk();
 //   BiLink lastStmt=entryBlk.instrList().last();
    BiLink firstStmt=entryBlk.instrList().first();
    
    LirNode[] emptyVector = new LirNode[0];   ///// for dummy parameter
    Symbol dummy = sstab.newGlobalSymbol(SsaSymTab.DUMMY_FUNC);    ///// dummy function

    for(BiLink p=initVariables.first();!p.atEnd();p=p.next()){
      Symbol s=(Symbol)p.elem();
      LirNode regNode=env.lir.symRef(s);    /////
/*      LirNode zeroNode=null;
      if(Type.tag(s.type)==Type.INT){
        // This is the integer register
        zeroNode=env.lir.iconst(s.type,0,ImList.Empty);
        //env.output.println(s);
      }
      else if(Type.tag(s.type)==Type.FLOAT){
        // This is the floating register
        zeroNode=env.lir.fconst(s.type,0,ImList.Empty);
        //env.output.println(s);
      }
      LirNode setNode=env.lir.operator(Op.SET,s.type,regNode,zeroNode,
                                       ImList.Empty);
 */
      LirNode callNode=env.lir.operator    ///// dummy function call
      (Op.CALL, Type.UNKNOWN, env.lir.symRef(dummy),    /////
        env.lir.node(Op.LIST, Type.UNKNOWN, emptyVector),
        env.lir.node(Op.LIST, Type.UNKNOWN, regNode),ImList.Empty);
 //     lastStmt.addBefore(setNode);
      firstStmt.addAfter(callNode);    /////
      //env.output.println(setNode);
    }
  }

  /**
   * Renaming method. The name is poped from the top of the stack.
   * This method change the symbol of register node to a new SSA symbol.
   * @param node The root node
   **/
  private void renameSymbolToStackTop(LirNode node){
    int i=0,end=0;
    // No register node on root node.
    if(node.opCode==Op.SET && node.kid(0).opCode==Op.REG) i=1;
    else i=0;

    if(node.opCode==Op.CALL && node.kid(2).nKids()>0 &&
       node.kid(2).kid(0).opCode==Op.REG){
      end=2;
    }
    else end=node.nKids();

    for(;i<end;i++){
      if(node.kid(i).opCode==Op.REG){
        LirSymRef symRef=(LirSymRef)node.kid(i);
        int num=symRef.symbol.id;

        if(stack[num]==null)
          makeNewStack(num,symRef.symbol);

        Symbol sym=(Symbol)stack[num].peek();
        LirSymRef newSymRef=(LirSymRef)env.lir.symRef(Op.REG,
                                                      sym.type,
                                                      sym,ImList.Empty);
        node.setKid(i,newSymRef);
        f.flowGraph().touch();
      }
      else{
        renameSymbolToStackTop(node.kid(i));
      }
    }
  }

  /**
   * Renaming method. This method always makes a new SSA name and push it
   * into the stack.
   * @param symRef The current register node
   * @param count The stack counter
   * @return A new register node which has new SSA name
   **/
  private LirSymRef makeNewReg(LirSymRef symRef,int count[]){
	  if (sstab.isPhyReg(symRef.symbol)){    /////
//		  System.out.println("do not make new reg for "+symRef.symbol);
		  return symRef;
	  }
    int num=symRef.symbol.id;
    if(stack[num]==null)
      makeNewStack(num,symRef.symbol);
    
    stack[num].push(sstab.newSsaSymbol1(symRef.symbol));    /////
    count[num]++;
    Symbol sym=(Symbol)stack[num].peek();
    LirSymRef newSymRef=(LirSymRef)env.lir.symRef(Op.REG,
                                                  sym.type,
                                                  sym,ImList.Empty);
    return(newSymRef);
  }
}
