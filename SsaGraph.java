/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.util.BiLink;
import coins.backend.util.BiList;
import coins.backend.cfg.BasicBlk;
import coins.backend.Op;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.lir.LirLabelRef;
import coins.backend.lir.LirIconst;
import coins.backend.sym.Symbol;
import coins.backend.ana.Dominators;
import coins.backend.Type;
import coins.backend.util.ImList;

import java.util.Stack;
import java.util.Hashtable;
import java.io.IOException;
import java.io.FileNotFoundException;
import java.io.OutputStreamWriter;
import java.io.FileOutputStream;

/**
 * SSA graph<br><br>
 * This class defined the object of the SSA graph.
 * Ths SSA graph has nodes which have the value or operator and labeled by
 * the variable that defined by the value or operation.
 * The edge of the node of the SSA graph is from the node that value is used
 * to the node that value is defined.<br><br>
 * Reference:<br>
 * Bowen Alpern and Mark N. Wegman and F. Kenneth Zadeck,
 * "Detecting Equality of Variables in Programs,"
 * Proceedings of the Fifteenth Annual ACM Symposium on Principles of 
 * Programming Language, pp. 1-11, January, 1988.
 **/
class SsaGraph implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "SsaGraph"; }
  public String subject() {
    return "Make SSA graph.";
  }

  /** The prefix of the new symbol **/
  public static final String symName="_ssag";
  /** The name of the optimizer which uses SSA graph **/
  public final String optName;
  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The current symbol table of the SSA module **/
  private SsaSymTab sstab;
  /** The current function **/
  private Function f;
  /** The map between the node of the SSA graph and the symbol **/
  private Hashtable table;
  /** The list of the node of the SSA graph **/
  private BiList nodeList;
  /** The array of prologue node of the SSA graph **/
  private SsaGraphNode[] prologues;
  /** The prologue node of LIR **/
  private LirNode prologueNode;
  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.OptThr;
  /** The memory alias analysis engine **/
  private MemoryAliasAnalyze alias;
  /** The map for defines of aggregate type **/
  private Hashtable aggrMayDef;

  /**
   * Constructor
   * @param e The environment of the SSA module
   * @param symtab The current symbol table of the SSA module
   * @param opt The name of the optimizer which uses the SSA graph
   **/
  public SsaGraph(SsaEnvironment e,SsaSymTab symtab,String opt){
    env=e;
    sstab=symtab;
    optName=opt;
    alias=null;

    if(opt.equals(OptionName.SSAG))
      env.println("  Make SSA Graph",SsaEnvironment.MsgThr);
    else if(opt.equals(OptionName.OSR))
      env.println("  Operator Strength Reduction",SsaEnvironment.MsgThr);
  }

  /**
   * Make the SSA graph and optimize with the graph.
   * @param function the current function
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    f=function;
    nodeList=new BiList();
    table=new Hashtable();
    aggrMayDef=new Hashtable();

    // Analyze about FRAME
    AddressAnalyze addressAnalyze=new AddressAnalyze(env,f,sstab);
    // Analyze about memory aliasing.
    alias=new MemoryAliasAnalyze(env,f);

    // Make SSA Graph from the current control flow graph.
    make();

    if(env.shouldDo(SsaEnvironment.AllThr))
      printGraph("before_ssa_graph.dot");

    // Optimizers on SSA Graph
    if(optName!=null){
      if(optName.equals(OptionName.SSAG)){
        env.println("****************** doing SSAG to "+function.symbol.name,
                    SsaEnvironment.MinThr);
        env.println("SSAG : make SSA Graph only",THR);
        env.println("",THR);
      }
      else if(optName.equals(OptionName.OSR))
        f.apply(new OperatorStrengthReduction(env,sstab,this));
    }

    if(env.shouldDo(SsaEnvironment.AllThr))
      printGraph("after_ssa_graph.dot");

    // Reconstruct the current control flow graph
    apply();
    alias.annul();
    addressAnalyze.annul();

    return(true);
  }

  /**
   * Append a new node to the SSA graph.
   * @param node The LIR node which append into the graph
   * @param blk The basic block which the LIR node belongs to
   * @param numOfParents The number of references of the node
   * @return A new node of the SSA graph
   **/
  SsaGraphNode appendNode(LirNode node,BasicBlk blk,int numOfParents){
    SsaGraphNode ssaNode=new SsaGraphNode(env,node,blk,numOfParents);
    nodeList.add(ssaNode);
    return(ssaNode);
  }

  /**
   * Return the list of the node of the SSA graph.
   * @return The list of the node of the SSA graph
   **/
  BiList nodeList(){
    return(nodeList);
  }

  /**
   * Translate the SSA graph's node into the node of CFG.
   **/
  private void apply(){
    Hashtable blkMap=new Hashtable();
    Hashtable blkMapLir=new Hashtable();
    boolean checked[]=new boolean[nodeList.length()];
    for(int i=0;i<nodeList.length();i++){
      checked[i]=false;
    }

    // Separate the node by each basic block
    for(BiLink p=nodeList.first();!p.atEnd();p=p.next()){
      SsaGraphNode node=(SsaGraphNode)p.elem();
      BiList instrList=(BiList)blkMap.get(node.belong);
      if(instrList==null){
        instrList=new BiList();
        blkMap.put(node.belong,instrList);
      }
      instrList.add(node);
    }

    // Iterate over the dominator tree from the root and translate the SSA
    // graph into CFG
    Dominators dom=(Dominators)f.require(Dominators.analyzer);
    Stack stack=new Stack();
    stack.push(f.flowGraph().entryBlk());

    //env.println("SSAG : Reconstruct CFG from SSA graph",THR);
    while(!stack.empty()){
      BasicBlk blk=(BasicBlk)stack.pop();
//      env.output.println("\n### in block "+blk.id);
      BiList instrList=(BiList)blkMap.get(blk);
      BiList lirInstrList=new BiList();
      blkMapLir.put(blk,lirInstrList);

      BiList earlyBird=new BiList();
      Hashtable callMap=new Hashtable();
      for(BiLink p=instrList.first();!p.atEnd();p=p.next()){
        SsaGraphNode node=(SsaGraphNode)p.elem();
        if(node.opCode==Op.MEM && node.parents[1]!=null &&
           node.parents[1].opCode==Op.CALL){
          callMap.put(node.parents[1],node);
        }
      }

      // Arrange the list of instructions satisfied the limitation
      BiList sortedList=new BiList();
      SsaGraphNode jumpNode=null;
      boolean again=true;
      while(again){
//        env.output.println("enter loop");
        again=false;
        for(BiLink p=instrList.first();!p.atEnd();p=p.next()){
          SsaGraphNode node=(SsaGraphNode)p.elem();

          if(checked[nodeList.whereIs(node)])
            continue;

          switch(node.opCode){
            case Op.JUMP:
            case Op.JUMPC:
            case Op.JUMPN:
              checked[nodeList.whereIs(node)]=true;
              jumpNode=node;
              continue;
          }
          
          if(node.opCode==Op.FRAME || node.opCode==Op.STATIC){
            boolean isOk=true;
            for(BiLink pp=instrList.first();!pp.atEnd();pp=pp.next()){
              SsaGraphNode addrNode=(SsaGraphNode)pp.elem();
              if(addrNode.opCode==node.opCode && addrNode!=node){
                Symbol sym1=((LirSymRef)node.node).symbol;
                Symbol sym2=((LirSymRef)addrNode.node).symbol;
                if(sstab.orgSym(sym1).name.equals(sstab.orgSym(sym2).name)){
                  int cmp=sstab.compare(sym1,sym2);
                  if(!checked[nodeList.whereIs(addrNode)] && cmp>0){
                    //env.output.println(sym1+" "+sym2);
                    isOk=false;
                    again=true;
//env.output.println("true1");
                    break;
                  }
                  if(checked[nodeList.whereIs(addrNode)] && cmp<=0){
                    SsaGraphNode aggDef=(SsaGraphNode)aggrMayDef.get(addrNode);
                    if(aggDef!=null && aggDef.belong.id==blk.id &&
                       !checked[nodeList.whereIs(aggDef)]){
                      isOk=false;
                      again=true;
//env.output.println("true2");
                      break;
                    }
                  }
                }
              }
            }
            if(isOk){
//              env.output.println(blk.id+" "+node.node);
              checked[nodeList.whereIs(node)]=true;
              sortedList.addNew(node);
            }
          }
          // Copy unconditionally if the current node is the PHI instruction
          // or a leaf node
          else if(node.opCode==Op.PHI || node.parents.length==0){
            checked[nodeList.whereIs(node)]=true;

            if(node.opCode==Op.PHI)
              sortedList.addFirst(node);
            else
              sortedList.addNew(node);
            //env.println("SSAG : Blk "+blk.id+"  "+node.toString(),THR);
          }
          else{
            boolean isOk=true;
            for(int i=0;i<node.parents.length;i++){
              if(node.parents[i]!=null){
                switch(node.parents[i].opCode){
                  case Op.INTCONST:
                  case Op.FLOATCONST:{
//                  case Op.STATIC:
//                  case Op.FRAME:{
                    if(node.parents[i].symbol()==null)break;
                  }
                  default:{
                    //env.output.println(node+" "+node.parents[i]);
                    if(node.belong==node.parents[i].belong && 
                       !checked[nodeList.whereIs(node.parents[i])]){
                      isOk=false;
//env.output.println("true3 "+node+" --> "+node.parents[i]);
                      again=true;
                    }
                  }
                }
              }
              if(!isOk)break;
            }
            if(isOk && node.opCode==Op.MEM){
              for(BiLink pp=instrList.first();!pp.atEnd();pp=pp.next()){
                SsaGraphNode memNode=(SsaGraphNode)pp.elem();
                if(memNode.opCode==Op.CALL &&
                   !checked[nodeList.whereIs(memNode)]){

                  long ssaVal1=((LirIconst)node.node.kid(1)).value;
                  long ssaVal2=alias.callThreshold(memNode.node);

//env.output.println("+++++++++ "+ssaVal1+" "+ssaVal2);
//env.output.println("+++++++++ "+memNode.node);
                  if(ssaVal1>=ssaVal2){
                    isOk=false;
//env.output.println("true4 "+node);
                    again=true;
                    break;
                  }
                }
                if(memNode.opCode==Op.MEM && 
                   memNode!=node &&
                   !checked[nodeList.whereIs(memNode)]){
//                  env.output.println(node.node);

                  long ssaVal1=((LirIconst)node.node.kid(1)).value;
                  long ssaVal2=((LirIconst)memNode.node.kid(1)).value;
                  boolean isLoad=false;
                  if(memNode.parents[1]==null) isLoad=true;

//env.output.println(ssaVal1+" "+ssaVal2);

                  if((isLoad && ssaVal2<ssaVal1) || 
                     (!isLoad && ssaVal2<=ssaVal1)){
//                    env.output.println(memNode.parents[1]);
//                    env.output.println("1 "+node.node+"\n  "+memNode.node);
                    isOk=false;
//env.output.println("true5 "+node+" --> "+memNode);
                    again=true;
                    break;
                  }
                }
              }
            }
            if(isOk && node.opCode==Op.CALL){
              SsaGraphNode memNode=(SsaGraphNode)callMap.get(node);
              if(memNode!=null &&
                 memNode.symbol()==null &&
                 !checked[nodeList.whereIs(memNode.parents[0])]){
                //env.output.println(memNode.parents[0].node);
                isOk=false;
//env.output.println("true6");
                again=true;
              }

              for(BiLink pp=instrList.first();!pp.atEnd();pp=pp.next()){
                SsaGraphNode targetNode=(SsaGraphNode)pp.elem();
                if(targetNode.opCode==Op.CALL &&
                   targetNode!=node &&
                   !checked[nodeList.whereIs(targetNode)]){
//env.output.println(targetNode.node+"   "+node.node);
                  long ssaVal1=alias.callThreshold(node.node);
                  long ssaVal2=alias.callThreshold(targetNode.node);
//env.output.println("############# "+ssaVal1+"  "+ssaVal2);
                  if(ssaVal1>=ssaVal2){
                    isOk=false;
//env.output.println("true7 "+node+" --> "+targetNode);
                    again=true;
                    break;
                  }
                }
                else if(targetNode.opCode==Op.MEM &&
                        !checked[nodeList.whereIs(targetNode)]){
                  long ssaVal1=alias.callThreshold(node.node);
                  long ssaVal2=((LirIconst)targetNode.node.kid(1)).value;

//                  env.output.println(node+" "+targetNode);
//                  env.output.println(ssaVal1+"   "+ssaVal2+"\n");

                  if(ssaVal1>ssaVal2){
                    isOk=false;
//env.output.println("true8 "+node+" --> "+targetNode);
                    again=true;
                    break;
                  }
                }
              }
            }
            if(isOk){
              checked[nodeList.whereIs(node)]=true;
              sortedList.addNew(node);
//              env.output.println("SSAG : Blk "+blk.id+"  "+node.node);

              if(again)break;
            }
          }
        }
      }

      // Copy JUMPx nodes
      if(jumpNode!=null){
        sortedList.add(jumpNode);
        //env.println("SSAG : Blk "+blk.id+"  "+jumpNode.toString(),THR);
      }
      
      for(BiLink p=sortedList.first();!p.atEnd();p=p.next()){
        SsaGraphNode node=(SsaGraphNode)p.elem();
//        env.output.println(node.belong.id+"  "+node.node);

        switch(node.opCode){
          case Op.PROLOGUE:{
            // The PROLOGUE node is a special one
            break;
          }
          // The LIR node below can be L-expression alone.
          case Op.PHI:
          case Op.JUMP:
          case Op.JUMPC:
          case Op.JUMPN:
          case Op.CALL:
          case Op.EPILOGUE:{
            LirNode lir=node.apply(nodeList);
            //env.output.println(lir);
            if(lir!=null){
              env.println("SSAG : "+blk.id+" "+lir,env.AllThr);
              lirInstrList.add(lir);
            }
            else env.output. println("fail : "+node.node);
            break;
          }

          // Other LIR nodes can not be L-expression alone. So, if the
          // SSA graph's node does not have a symbol then it is used as 
          // a part of the LIR node.
          default:{
            if(node.symbol()!=null){
              LirNode lir=node.apply(nodeList);
              //env.output.println(lir);

              if(lir!=null){
                env.println("SSAG : "+blk.id+" "+lir,env.AllThr);
                lirInstrList.add(lir);
              }
              else env.output.println("fail : "+node.node);
            }
          }
        }
      }
      for(BiLink p=dom.kids[blk.id].first();!p.atEnd();p=p.next()){
        stack.push(p.elem());
      }
    }

    // Treat PROLOGUE node. Basically reuse the node. Replace only the
    // arguments.
    for(int i=0;i<prologues.length;i++){
      Symbol s=prologues[i].symbol();
      if(s!=null){
        prologueNode.setKid(i+1,env.lir.symRef(s));
      }
      else{
        // If the symbol is null
        for(BiLink p=nodeList.first();!p.atEnd();p=p.next()){
          SsaGraphNode n=(SsaGraphNode)p.elem();
          for(int j=0;j<n.parents.length;j++){
            if(n.parents[j]==prologues[i]){
              LirNode argNode=n.apply(nodeList);
              if(argNode.opCode==Op.SET)
                argNode=argNode.kid(1);
              prologueNode.setKid(i+1,argNode.makeCopy(env.lir));
            }
          }
        }
      }
    }

    BiList entryBlkList=(BiList)blkMapLir.get(f.flowGraph().entryBlk());
    entryBlkList.addFirst(prologueNode);

    // Arrange the list of instructions.
    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      BiList l=(BiList)blkMapLir.get(blk);
      if(l!=null){
        blk.instrList().clear();
        blk.instrList().concatenate(l);

        // debug print
        /*
        env.output.println("######## block "+blk.id);
        for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
          LirNode node=(LirNode)q.elem();
          env.output.println("\t"+node);
        }
        */
      }
    }
    f.flowGraph().touch();
  }

  /**
   * Make a SSA graph.
   **/
  private void make(){
    // Iterate the dominator tree from the root.
    Dominators dom=(Dominators)f.require(Dominators.analyzer);
    Stack stack=new Stack();
    stack.push(f.flowGraph().entryBlk());

    while(!stack.empty()){
      BasicBlk blk=(BasicBlk)stack.pop();

      for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
        makeGraph(blk,(LirNode)p.elem());
      }

      for(BiLink p=dom.kids[blk.id].first();!p.atEnd();p=p.next()){
        stack.push(p.elem());
      }
    }

    if(optName.equals(OptionName.SSAG) && 
       env.opt.isSet(OptionName.SSA_SSAG_PRUNING))
      pruning();
  }

  /**
   * Prun the SSA graph (experimental)
   **/
  private void pruning(){
    BiList removeList=new BiList();
    boolean again=true;

    while(again){
      again=false;

      for(BiLink p=nodeList.first();!p.atEnd();p=p.next()){
        SsaGraphNode node=(SsaGraphNode)p.elem();

        for(BiLink q=p.next();!q.atEnd();q=q.next()){
          SsaGraphNode target=(SsaGraphNode)q.elem();
          if(removeList.contains(target)) continue;

          if(node.opCode==target.opCode && node.node.type==target.node.type){
            switch(node.opCode){
              // basically nothing to do because there are no nodes which have
              // the same attributes.
              case Op.INTCONST:
              case Op.FLOATCONST:
              case Op.LABEL:
              case Op.STATIC:
              case Op.FRAME:{
                if(node.node.equals(target.node)){
                  SsaGraphNode remove=replace(node,target);
                  if(remove!=null){
                    removeList.add(remove);
                    again=true;
//                    env.output.println("(0) "+node+"  "+target);
                  }
                }
                break;
              }
              case Op.ADD:
              case Op.MUL:
              case Op.BAND:
              case Op.BOR:
              case Op.BXOR:{
                if(Type.tag(node.node.type)==Type.INT){
                  boolean[] targetCheck=new boolean[target.parents.length];
                  for(int i=0;i<target.parents.length;i++) 
                    targetCheck[i]=false;
                  if(node.parents.length==target.parents.length){
                    boolean isOk=true;
                    for(int i=0;i<node.parents.length;i++){
                      boolean nomatch=true;
                      for(int j=0;j<target.parents.length;j++){
                        if(!targetCheck[j] && 
                           node.parents[i]==target.parents[j]){
                          targetCheck[j]=true;
                          nomatch=false;
                          break;
                        }
                      }
                      if(nomatch){
                        isOk=false;
                        break;
                      }
                    }
                    if(isOk){
                      SsaGraphNode remove=replace(node,target);
                      if(remove!=null){
                        removeList.add(remove);
                        again=true;
//                        env.output.println("(1) "+node+"  "+target);
                      }
                    }
                  }
                  break;
                }
              }
              case Op.JUMP:
              case Op.JUMPC:
              case Op.JUMPN:
              case Op.TSTEQ: 
              case Op.TSTNE: 
              case Op.TSTLTS:
              case Op.TSTLES:
              case Op.TSTGTS:
              case Op.TSTGES:
              case Op.TSTLTU:
              case Op.TSTLEU:
              case Op.TSTGTU:
              case Op.TSTGEU:
              case Op.PROLOGUE:
              case Op.EPILOGUE:
              case Op.CALL:
              case Op.PHI:
              case Op.MEM: break;
              default:{
                if(node.parents.length==target.parents.length){
                  boolean isOk=true;
                  for(int i=0;i<node.parents.length;i++){
                    if(node.parents[i]!=target.parents[i]){
                      isOk=false;
                      break;
                    }
                  }
                  if(isOk){
                    SsaGraphNode remove=replace(node,target);
                    if(remove!=null){
                      removeList.add(remove);
                      again=true;
//                      env.output.println("(2) "+node+"  "+target);
                    }
                  }
                }
              }
            }
          }
        }
      }
      for(BiLink p=removeList.first();!p.atEnd();p=p.next()){
        nodeList.remove(p.elem());
      }
      removeList.clear();
    }
  }

  /**
   * Replace the node of the SSA graph. If the replacement is succeeded, then
   * n1 or n2 is removed from the graph.
   * @param n1 The target node 1
   * @param n2 The target node 2
   * @return If the replacement is succeeded, return the remained node.
   *         If not, return null
   **/
  private SsaGraphNode replace(SsaGraphNode n1,SsaGraphNode n2){
    Dominators dom=(Dominators)f.require(Dominators.analyzer);
    BiList list1=new BiList();
    BiList list2=new BiList();

    for(BiLink p=nodeList.first();!p.atEnd();p=p.next()){
      SsaGraphNode node=(SsaGraphNode)p.elem();
      for(int i=0;i<node.parents.length;i++){
        if(node.parents[i]==n1) list1.addNew(node);
        if(node.parents[i]==n2) list2.addNew(node);
      }
    }

    boolean isOk=true;
    for(BiLink p=list1.first();!p.atEnd();p=p.next()){
      SsaGraphNode node=(SsaGraphNode)p.elem();
      if(!dom.dominates(n2.belong,node.belong)){
        isOk=false;
        break;
      }
    }
    if(isOk){
      for(BiLink p=list1.first();!p.atEnd();p=p.next()){
        SsaGraphNode node=(SsaGraphNode)p.elem();
        for(int i=0;i<node.parents.length;i++){
          if(node.parents[i]==n1) node.parents[i]=n2;
        }
      }
      return(n1);
    }

    isOk=true;
    for(BiLink p=list2.first();!p.atEnd();p=p.next()){
      SsaGraphNode node=(SsaGraphNode)p.elem();
      if(!dom.dominates(n1.belong,node.belong)){
        isOk=false;
        break;
      }
    }
    if(isOk){
      for(BiLink p=list2.first();!p.atEnd();p=p.next()){
        SsaGraphNode node=(SsaGraphNode)p.elem();
        for(int i=0;i<node.parents.length;i++){
          if(node.parents[i]==n2) node.parents[i]=n1;
        }
      }
      return(n2);
    }

    return(null);
  }

  /**
   * Translate the LIR node into the node of SSA graph.
   * @param blk The basic block which the current LIR node is in
   * @param node The current LIR node
   * @return A new subgraph of the SSA graph
   **/
  private SsaGraphNode makeGraph(BasicBlk blk,LirNode node){
    SsaGraphNode returnNode=null;

    switch(node.opCode){
      case Op.SET:{
        // Translate the right hand side into a node of SSA graph.
        SsaGraphNode uNode=makeGraph(blk,node.kid(1));

        // Translate the left hand side into a node of SSA graph.
        // The destination variable is a register variable.
        if(node.kid(0).opCode==Op.REG){
          Symbol s=((LirSymRef)node.kid(0)).symbol;
          setSymbol(s,uNode);
        }
        // The destination variable is not a register variable, such as
        // MEM node.
        else{
          // MEM as STORE
          SsaGraphNode mNode=makeGraph(blk,node.kid(0));

          // Make a temporary variable
          Symbol s=sstab.newSsaSymbol(symName,Type.type(Type.INT,32));
          setSymbol(s,mNode);

          mNode.parents[1]=uNode;

          //env.output.println("1 "+mNode);
        }

        //env.output.println("2 "+uNode);
        break;
      }
      case Op.PHI:{
        Symbol s=((LirSymRef)node.kid(0)).symbol;
        SsaGraphNode phiNode=appendNode(node,blk,node.nKids());
        setSymbol(s,phiNode);

        // We don't use the parent[0]
        for(int i=1;i<node.nKids();i++){
          // Make children of the arguments of the PHI instruction.
          BasicBlk target=((LirLabelRef)node.kid(i).kid(1)).label.basicBlk();
          phiNode.parents[i]=makeGraph(target,node.kid(i).kid(0));
        }

        //env.output.println("9 "+phiNode);
        break;
      }
      case Op.MEM:{
        SsaGraphNode addressNode=makeGraph(blk,node.kid(0));

        // The node represent a load instruction or a store instruction.
        // The parents[0] is a node for calculation the effective address.
        // The parents[1] is only used by a store instruction.
        Symbol s=sstab.newSsaSymbol(symName,node.type);
        returnNode=appendNode(node,blk,2);

        if(s!=null)
          setSymbol(s,returnNode);
        //env.output.println(returnNode+" "+node);
        returnNode.parents[0]=addressNode;

        break;
      }

      // The cast operator
      case Op.CONVSX:
      case Op.CONVZX:
      case Op.CONVIT:
      case Op.CONVFX:
      case Op.CONVFT:
      case Op.CONVFI:
      case Op.CONVFU:
      case Op.CONVFS:
      case Op.CONVSF:
      case Op.CONVUF:{
        // The left hand side
        SsaGraphNode lNode=makeGraph(blk,node.kid(0));

        // The cast operator does't use temporary.
        returnNode=appendNode(node,blk,1);

        returnNode.parents[0]=lNode;
        break;
      }

      // The unary operator
      case Op.NEG:
      case Op.BNOT:{
        //env.output.println("+++ "+node);
        // The left hand side
        SsaGraphNode lNode=makeGraph(blk,node.kid(0));

        // The temporary variable
        Symbol s=sstab.newSsaSymbol(symName,node.type);
        returnNode=appendNode(node,blk,1);

        if(s!=null)
          setSymbol(s,returnNode);

        returnNode.parents[0]=lNode;

        //env.output.println("8 "+returnNode);
        //env.output.println("\t"+lNode);

        break;
      }

      // The condition operator
      case Op.TSTEQ:
      case Op.TSTNE:
      case Op.TSTLTS:
      case Op.TSTLES:
      case Op.TSTGTS:
      case Op.TSTGES:
      case Op.TSTLTU:
      case Op.TSTLEU:
      case Op.TSTGTU:
      case Op.TSTGEU:{
        //env.output.println("+++ "+node);
        // The left hand side.
        SsaGraphNode lNode=makeGraph(blk,node.kid(0));
        // The right hand side.
        SsaGraphNode rNode=makeGraph(blk,node.kid(1));

        // The condition operator doesn't use the temporary.
        returnNode=appendNode(node,blk,2);
        returnNode.parents[0]=lNode;
        returnNode.parents[1]=rNode;

        break;
      }

      // The binary operator
      case Op.BAND:
      case Op.BOR:
      case Op.BXOR:
      case Op.LSHS:
      case Op.LSHU:
      case Op.RSHS:
      case Op.RSHU:
      case Op.SUB:
      case Op.DIVS:
      case Op.DIVU:
      case Op.MODS:
      case Op.MODU:
      case Op.MUL:
      case Op.ADD:{
        //env.output.println("+++ "+node);
        // The left hand side.
        SsaGraphNode lNode=makeGraph(blk,node.kid(0));
        // The right hand side.
        SsaGraphNode rNode=makeGraph(blk,node.kid(1));

        // The temporary variable
        Symbol s=sstab.newSsaSymbol(symName,node.type);
        returnNode=appendNode(node,blk,2);

        if(s!=null)
          setSymbol(s,returnNode);

        returnNode.parents[0]=lNode;
        returnNode.parents[1]=rNode;
        if (nodeList.whereIs(lNode) == -1)
        	nodeList.add(lNode);
        if (nodeList.whereIs(rNode) == -1)
        	nodeList.add(rNode);

        //env.output.println("3 "+returnNode);
        //env.output.println("\t"+lNode);
        //env.output.println("\t"+rNode);

        break;
      }

      // Non-conditional JUMP node.
      case Op.JUMP:{
        SsaGraphNode lNode=makeGraph(blk,node.kid(0));
        returnNode=appendNode(node,blk,1);
        returnNode.parents[0]=lNode;

        //env.output.println("7 "+returnNode);
        //env.output.println("\t"+lNode);

        break;
      }

      // JUMPC node
      case Op.JUMPC:{
        // The conditioinal operator.
        SsaGraphNode tstNode=makeGraph(blk,node.kid(0));
        // true label
        SsaGraphNode lab1Node=makeGraph(blk,node.kid(1));
        // false label
        SsaGraphNode lab2Node=makeGraph(blk,node.kid(2));

        returnNode=appendNode(node,blk,3);
        returnNode.parents[0]=tstNode;
        returnNode.parents[1]=lab1Node;
        returnNode.parents[2]=lab2Node;

        //env.output.println("+ "+returnNode);
        //env.output.println("\t"+tstNode);
        //env.output.println("\t"+lab1Node);
        //env.output.println("\t"+lab2Node);
        
        break;
      }

      // JUMPN node
      case Op.JUMPN:{
        int number=node.nKids();
        number=number-1+node.kid(1).nKids();
        returnNode=appendNode(node,blk,number);

        // The register variable which is compared.
        returnNode.parents[0]=makeGraph(blk,node.kid(0));

        // The constant node and the label symbol.
        for(int i=1;i<number-1;i++){
          SsaGraphNode cnstNode=appendNode(node.kid(1).kid(i-1).kid(0),blk,1);
          SsaGraphNode labNode=makeGraph(blk,node.kid(1).kid(i-1).kid(1));
          cnstNode.parents[0]=labNode;

          returnNode.parents[i]=cnstNode;
        }

        // Default label
        returnNode.parents[number-1]=makeGraph(blk,node.kid(2));

        //env.output.println("$ "+returnNode);
        break;
      }

      // CALL node.
      case Op.CALL:{
        int number=node.kid(1).nKids()+1;
        returnNode=appendNode(node,blk,number);

        // The name or address of the function.
        SsaGraphNode nameNode=makeGraph(blk,node.kid(0));

        // The arguments of the function.
        SsaGraphNode[] argNodes=new SsaGraphNode[node.kid(1).nKids()];
        for(int i=0;i<node.kid(1).nKids();i++){
          if(node.kid(1).kid(i).opCode==Op.FRAME ||
             node.kid(1).kid(i).opCode==Op.STATIC){
            aggrMayDef.put(node.kid(1).kid(i),returnNode);
          }
          argNodes[i]=makeGraph(blk,node.kid(1).kid(i));
        }

        returnNode.parents[0]=nameNode;

        for(int i=0;i<node.kid(1).nKids();i++){
          returnNode.parents[i+1]=argNodes[i];
        }

        // The function has return values.
        if(node.kid(2).nKids()>0){
          // The return values of the function are register variables.
          if(node.kid(2).kid(0).opCode==Op.REG){
            Symbol s=((LirSymRef)node.kid(2).kid(0)).symbol;
            setSymbol(s,returnNode);
          }
          // The return value of the function are not register variables, such
          // as MEM node.
          else{
            SsaGraphNode mNode=makeGraph(blk,node.kid(2).kid(0));
            mNode.setSymbol(null);
            mNode.parents[1]=returnNode;
          }
        }

        //env.output.println("? "+returnNode);

        break;
      }

      // The PROLOGUE node
      case Op.PROLOGUE:{
        prologueNode=node;
        prologues=new SsaGraphNode[node.nKids()-1];
        if(node.nKids()>1){
          for(int i=1;i<node.nKids();i++){
            returnNode=appendNode(node,blk,0);
            prologues[i-1]=returnNode;
            /*
            Symbol  s=((LirSymRef)node.kid(i)).symbol;
            setSymbol(s,returnNode);
            */

            // Translate the left hand side into a node of SSA graph.
            // The destination variable is a register variable.
            if(node.kid(i).opCode==Op.REG){
              Symbol  s=((LirSymRef)node.kid(i)).symbol;
              setSymbol(s,returnNode);
            }
            // The destination variable is not a register variable, such as
            // MEM node.
            else{
              // Make a temporary variable
              SsaGraphNode mNode=makeGraph(blk,node.kid(i));
              //mNode.setSymbol(null);
              mNode.parents[1]=returnNode;
            }
          }
        }
        else{
          returnNode=appendNode(node,blk,0);
        }

        //env.output.println("@ "+returnNode);

        break;
      }

      // The EPILOGUE node.
      case Op.EPILOGUE:{
        if(node.nKids()>1){
          SsaGraphNode[] vals=new SsaGraphNode[node.nKids()-1];
          for(int i=1;i<node.nKids();i++){
            vals[i-1]=makeGraph(blk,node.kid(i));
          }
          returnNode=appendNode(node,blk,node.nKids()-1);
          for(int i=0;i<vals.length;i++){
            returnNode.parents[i]=vals[i];
          }
        }
        else{
          returnNode=appendNode(node,blk,0);
        }
        //env.output.println("# "+returnNode);
        break;
      }

      // The REG node
      case Op.REG:{
        Symbol s=((LirSymRef)node).symbol;
        returnNode=(SsaGraphNode)table.get(s);
        if(returnNode==null){
          // Make a temporary variable as a BOTTOM value.
          //System.err.println("No such node "+node);
          returnNode=appendNode(node,blk,0);
          // A temporary registeration
          table.put(s,returnNode);

          //System.exit(99);
        }
        break;
      }

      // The leaf nodes
      case Op.LABEL:
      case Op.FRAME:
      case Op.STATIC:
      case Op.INTCONST:
      case Op.FLOATCONST:{
        if(optName.equals(OptionName.SSAG) &&
           env.opt.isSet(OptionName.SSA_SSAG_PRUNING)){
//          env.output.println(node);
          SsaGraphNode tmp=(SsaGraphNode)table.get(node.toString().intern());
          if(tmp==null){
            returnNode=appendNode(node,blk,0);
            table.put(node.toString().intern(),returnNode);
          }
          else{
//            env.output.println("aaaaaaaaaaaa "+node);
            Dominators dom=(Dominators)f.require(Dominators.analyzer);
            if(dom.dominates(tmp.belong,blk)){
              returnNode=tmp;
            }
            else{
              if(dom.dominates(blk,tmp.belong))
                returnNode=appendNode(node,blk,0);
              else
                returnNode=appendNode(node,f.flowGraph().entryBlk(),0);
              
              for(BiLink p=nodeList.first();!p.atEnd();p=p.next()){
                SsaGraphNode n=(SsaGraphNode)p.elem();
                for(int i=0;i<n.parents.length;i++){
                  if(n.parents[i]==tmp){
                    //System.err.println("Replace the node");
                    n.parents[i]=returnNode;
                  }
                }
              }

              if(tmp.symbol()!=null) setSymbol(tmp.symbol(),returnNode);

              nodeList.remove(tmp);
              table.remove(tmp);
              table.put(node.toString().intern(),returnNode);
            }
          }
        }
        else{
          returnNode=appendNode(node,blk,0);
          //env.output.println("4 "+returnNode);
        }
        break;
      }

      case Op.SUBREG:{
        break;
      }
    }

    return(returnNode);
  }

  /**
   * Register again the symbol `s' as a value of the node and put it to the
   * map. If the map already has `s', then remove the old one and register 
   * again.
   * @param s The symbol to register
   * @param node The node of the SSA graph which has `s'
   **/
  void setSymbol(Symbol s,SsaGraphNode node){
    node.setSymbol(s);
    
    SsaGraphNode tmp=(SsaGraphNode)table.get(s);
    if(tmp!=null){
      // If the map already has the symbol.
      table.remove(tmp);
      nodeList.remove(tmp);
      for(BiLink p=nodeList.first();!p.atEnd();p=p.next()){
        SsaGraphNode n=(SsaGraphNode)p.elem();
        for(int i=0;i<n.parents.length;i++){
          if(n.parents[i]==tmp){
            //System.err.println("Replace the node");
            n.parents[i]=node;
          }
        }
      }
    }
    table.put(s,node);
  }

  /**
   * Print the node as
   * <a href="http://www.research.att.com/sw/tools/graphviz/">graphviz</a>
   * format.
   * @param filename The file name for output
   **/
  void printGraph(String filename){
    OutputStreamWriter output=new OutputStreamWriter(System.out);
    try{
      FileOutputStream outStream=new FileOutputStream(filename);
      output=new OutputStreamWriter(outStream);
    }
    catch(FileNotFoundException e){}
    try{
      output.write("digraph G {\n");
    }
    catch(IOException e){
      System.out.println("digraph G {");
    }

    for(BiLink p=nodeList.first();!p.atEnd();p=p.next()){
      SsaGraphNode node=(SsaGraphNode)p.elem();
      node.printGraph(output,nodeList);
    }

    try{
      output.write("}\n");
      output.close();
    }
    catch(IOException e){
      System.out.println("}");
    }
  }
}
