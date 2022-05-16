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
import coins.backend.ana.DFST;
import coins.backend.ana.Dominators;
import coins.backend.util.ImList;
import coins.backend.sym.Symbol;
import coins.backend.lir.LirIconst;
import coins.backend.lir.LirFconst;
import coins.backend.Type;

import java.util.Stack;
import java.util.Hashtable;

/**
 * Operator Strength Reduction.<br>
 * This optimizer do the operator strength reduction. Operator strength 
 * reduction is a technique that improves compiler-generated code by 
 * reformulating certain costly computations in terms of less expensive ones.
 * This optimizer use the SSA graph.<br><br>
 * Refer:<br><br>
 * Keith D. Cooper, L. Taylor Simpson, Christopher A. Vick,
 * "Operator Strength Reduction,"
 * ACM TOPLAS, Vol. 23, No. 5, pp. 603-625, September 2001.
 **/
class OperatorStrengthReduction implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "OperatorStrengthReduction"; }
  public String subject() {
    return "Operator Strength Reduction for inductin variables.";
  }

  /**
   * The private data for LFTR.
   **/
  private class LftrData{
    /** The operator node of the SSA graph **/
    private final SsaGraphNode op;
    /** The induction varibale node of the SSA graph **/
    private final SsaGraphNode iv;
    /** The region constant node of the SSA graph **/
    private final SsaGraphNode rc;
    /** The result node of the SSA graph **/
    private final SsaGraphNode result;

    /**
     * Constructor
     * @param o The operator node
     * @param i The induction variable node
     * @param r The region constant node 
     * @param res The result node
     **/
    LftrData(SsaGraphNode o,SsaGraphNode i,SsaGraphNode r,SsaGraphNode res){
      op=o;
      iv=i;
      rc=r;
      result=res;
    }
  }

  /**
   * The search table for OSR.
   **/
  private class OsrLookUpTable{
    /** The list of datas using OSR **/
    final BiList tables;
    /** The map between the datas and the SSA graph's node **/
    final Hashtable resultMap;
    /** The map for LFTR **/
    final Hashtable lftrMap;
    /** The list of SSA graph's nodes which is cyclic 
        but have multi entrance **/
//    private final BiList multiEntryList;

    /**
     * Constructor
     **/
    OsrLookUpTable(){
      tables=new BiList();
      resultMap=new Hashtable();
      lftrMap=new Hashtable();
//      multiEntryList=new BiList();
    }

    /**
     * Look up the table if the set of the datas are already registered.
     * @param code The operator node
     * @param op1 The first operand
     * @param op2 The second operand
     * @return If the table has the same data, return it. Otherwise return null
     **/
    SsaGraphNode search(SsaGraphNode code,SsaGraphNode op1,
                                SsaGraphNode op2){
      //env.output.println("aaaaaaaaa  "+code+" "+op1+" "+op2);
      for(BiLink p=tables.first();!p.atEnd();p=p.next()){
        Object[] t=(Object[])p.elem();
        if(code.opCode==((SsaGraphNode)t[0]).opCode && t[1]==op1){
          //env.output.println(code+" "+t[0]);
          //env.output.println("  "+op1+" "+t[1]);
          //if(op2.opCode==Op.PROLOGUE || op2.opCode==Op.PHI){
          if(!isConst(op2)){
            if(op2.symbol()!=null && ((SsaGraphNode)t[2]).symbol()!=null && 
               op2.symbol()==((SsaGraphNode)t[2]).symbol()){
              return((SsaGraphNode)resultMap.get(t));
            }
          }
          else if(((SsaGraphNode)t[2]).node.equals(op2.node)){
            //env.output.println("MATCH : \n  "+t[2]+" "+
            //                   ((SsaGraphNode)t[2]).node+
            //                  "\n  "+op2+" "+op2.node);
            return((SsaGraphNode)resultMap.get(t));
          }
        }
      }
      return(null);
    }

    /**
     * Add the set of the datas into the table.
     * @param code The operator node
     * @param op1 The first operand
     * @param op2 The second operand
     * @param result The node of the SSA graph which represent the datas
     **/
    void add(SsaGraphNode code,SsaGraphNode op1, SsaGraphNode op2,
                     SsaGraphNode result,boolean isOp1IV){
//      env.output.println("bbbbbbbbb  "+code+" "+op1+" "+op2);
      Object[] t=new Object[3];
      t[0]=code;
      t[1]=op1; // if isOp1IV is true then Induction Variable
      t[2]=op2; // Region Constant

      if(isOp1IV){
        LftrData tmp=(LftrData)lftrMap.get(op1);
        
        // Do LFTR only if a induction variable has only one sequence of the
        // reductions.
/**
        if(tmp!=null){
          env.output.println(op1+" has multiple entry");
//          multiEntryList.add(op1);
//          lftrMap.remove(op1);
        }
        else{
**/
//          if(!multiEntryList.contains(op1)){
            LftrData lftrData=new LftrData(code,op1,op2,result);
            lftrMap.put(op1,lftrData);
//          }
//        }
      }

      tables.add(t);
      resultMap.put(t,result);
    }

    /**
     * Calculate to the induction variable.
     * @param iv The induction variable
     * @param rc The region constant
     * @param belong The basic block which the result put in
     * @return A new datas about induction variable
     **/
    SsaGraphNode[] applyEdges(SsaGraphNode iv,SsaGraphNode rc,
                                      BasicBlk belong){
      SsaGraphNode[] result=new SsaGraphNode[2];
      result[0]=null; // new induction variable
      result[1]=null; // new region constant

      LftrData lftrData=(LftrData)lftrMap.get(iv);
      if(lftrData!=null){
//        env.output.println("candidate");
        do{
//          env.output.println(lftrData.op+" "+rc+" "+lftrData.rc);
          result[0]=lftrData.result;
          SsaGraphNode trc=calc(lftrData.op,rc,lftrData.rc,belong);
          if(trc==null) break;

          rc=trc;
          lftrData=(LftrData)lftrMap.get(lftrData.result);
        }while(lftrData!=null);

        result[1]=rc;
      }
      
      return(result);
    }
  }

  /**
   * The private data for OSR
   **/
  private class OsrData{
    /** The depth first number **/
    final int DFSnum;
    /** The header block **/
    BasicBlk header;
    /** Used for depth first search **/
    int low;
    /** True if it is induction variable **/
    boolean iv;

    /**
     * Constructor
     * @param dfsNum The depth first search number
     **/
    OsrData(int dfsNum){
      DFSnum=dfsNum;
      low=DFSnum;
      header=null;
      iv=false;
    }
  }

  /** The prefix of the new symbol **/
  private final String osrSymName="_osr";
  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The current symbol table of the SSA module **/
  private SsaSymTab sstab;
  /** The current SSA graph **/
  private SsaGraph ssaGraph;
  /** The depth first search number **/
  private int nextDFSnum=0;
  /** The stack for the depth first search **/
  private Stack dfsStack;
  /** The map for the node of SSA graph **/
  private Hashtable nodeMap;
  /** The current function **/
  private Function f;
  /** The look up table for OSR **/
  private OsrLookUpTable osrLookUp;
  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.OptThr;

  /**
   * Constructor
   * @param e The environment of the SSA module
   * @param symtab The current symbol table of the SSA module
   * @param graph The current SSA graph
   **/
  public OperatorStrengthReduction(SsaEnvironment e,SsaSymTab symtab,
                                   SsaGraph graph){
    env=e;
    sstab=symtab;
    ssaGraph=graph;
  }

  /**
   * Do Operator Strength Reduction
   * @param function The current function
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    env.println("****************** doing OSR to "+function.symbol.name,
                SsaEnvironment.MinThr);
    f=function;

    dfsStack=new Stack();
    nodeMap=new Hashtable();
    osrLookUp=new OsrLookUpTable();

    for(BiLink p=ssaGraph.nodeList().first();!p.atEnd();p=p.next()){
      SsaGraphNode node=(SsaGraphNode)p.elem();
      
      if(nodeMap.get(node)==null){
        DFS(node);
      }
    }

    // for LFTR
    if(!env.opt.isSet("ssa-no-lftr")) // for debug
//    if(function.symbol.name.equals("CopyCleanup"))
      LFTR();

    env.println("",THR);

    return(true);
  }

  /**
   * Linear Function Test Replacement
   **/
  private void LFTR(){
    env.println("OSR : doing LFTR",THR);
    for(BiLink p=ssaGraph.nodeList().first();!p.atEnd();p=p.next()){
      SsaGraphNode n=(SsaGraphNode)p.elem();
      switch(n.opCode){
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
          env.println("LFTR : candidate "+n.parents[0]+" "+n.parents[1],THR);
          // If the condition node is between the constant node and induction
          // variable, then do LFTR.
          OsrData pareData0=(OsrData)nodeMap.get(n.parents[0]);
          OsrData pareData1=(OsrData)nodeMap.get(n.parents[1]);

          if(pareData0.header!=null && 
             RegionConst(n.parents[1],pareData0.header)){
            SsaGraphNode[] applied=tstReplace(n.parents[0],n.parents[1],n);
            if(applied!=null){
              n.parents[0]=applied[0];
              n.parents[1]=applied[1];

              // debug
              env.println("LFTR : replace "+n,THR);
              for(int i=0;i<n.parents.length;i++){
                env.println("LFTR    "+n.parents[i],THR);
              }
            }
          }
          else if(pareData1.header!=null &&
                  RegionConst(n.parents[0],pareData1.header)){
            SsaGraphNode[] applied=tstReplace(n.parents[1],n.parents[0],n);
            if(applied!=null){
              n.parents[1]=applied[0];
              n.parents[0]=applied[1];

              // debug
              env.println("LFTR : replace "+n,THR);
              for(int i=0;i<n.parents.length;i++){
                env.println("LFTR    "+n.parents[i],THR);
              }
            }
          }
        }
      }
    }
  }

  /**
   * Replace the TSTxx node.
   * @param iv Induction Variable
   * @param rc Region Constant
   * @param org The original TSTxx node
   * @return Applied induction variable and region constant
   **/
  private SsaGraphNode[] tstReplace(SsaGraphNode iv,SsaGraphNode rc,
                                    SsaGraphNode org){
    if(iv!=null && rc!=null){
//      env.output.println("## "+org+" "+iv+" "+rc);
      
      if(iv.opCode==Op.PROLOGUE){
        if(rc.opCode==Op.PROLOGUE){
          if(Type.tag(iv.symbol().type)!=Type.INT ||
             Type.tag(rc.symbol().type)!=Type.INT)
            return(null);
        }
        else{
          if(Type.tag(iv.symbol().type)!=Type.INT || 
             Type.tag(rc.node.type)!=Type.INT)
            return(null);
        }
      }
      else{
        if(rc.opCode==Op.PROLOGUE){
          if(Type.tag(iv.node.type)!=Type.INT || 
             Type.tag(rc.symbol().type)!=Type.INT)
            return(null);
        }
        else{
          if(Type.tag(iv.node.type)!=Type.INT || 
             Type.tag(rc.node.type)!=Type.INT)
            return(null);
        }
      }
      SsaGraphNode[] applied=osrLookUp.applyEdges(iv,rc,org.belong);
      if(applied[0]!=null && applied[1]!=null) return(applied);
    }

    return(null);
  }

  /**
   * Depth first search and get the Strongly Connected Component (SCC).
   * @param node The current node of the SSA graph
   **/
  private void DFS(SsaGraphNode node){
    OsrData nodeData=new OsrData(nextDFSnum++);
    nodeMap.put(node,nodeData);
    dfsStack.push(node);

    for(int i=0;i<node.parents.length;i++){
      SsaGraphNode o=node.parents[i];
      if(o!=null){
        OsrData oData=(OsrData)nodeMap.get(o);
        if(oData==null){
          DFS(o);
          oData=(OsrData)nodeMap.get(o);
          if(nodeData.low>oData.low) nodeData.low=oData.low;
        }
        if(oData.DFSnum<nodeData.DFSnum && dfsStack.contains(o))
          if(oData.DFSnum<nodeData.low) nodeData.low=oData.DFSnum;
      }
    }
    if(nodeData.low==nodeData.DFSnum){
      BiList SCC=new BiList();
      SsaGraphNode x=null;
      do{
        x=(SsaGraphNode)dfsStack.pop();
        SCC.add(x);
      }while(x!=node);
      ProcessSCC(SCC);
    }
  }

  /**
   * If the SCC has a single member, then tries to reduce it.
   * Else, do `classifyIV' method.
   * @param SCC The strongly connected component
   **/
  private void ProcessSCC(BiList SCC){
    if(SCC.length()==1){
      SsaGraphNode n=(SsaGraphNode)SCC.first().elem();
      reduction(n);
    }
    else{
      //env.output.println("candidate");
      ClassifyIV(SCC);
    }
  }

  /**
   * If the node of SSA graph represent the allow form:<br><br>
   * x = iv * rc,<br>
   * x = rc * iv, <br>
   * x = iv << rc,<br>
   * x = iv + rc,<br>
   * x = rc + iv, <br>
   * x = iv - rc<br><br>
   * then the compiler tries to reduce the operation.
   * @param n The node of the SSA graph
   **/
  private void reduction(SsaGraphNode n){
    //env.output.println("\t"+n);
    OsrData nData=(OsrData)nodeMap.get(n);
    switch(n.opCode){
/**
      case Op.CONVSX:
      case Op.CONVIT:{
        OsrData data=(OsrData)nodeMap.get(n.parents[0]);
        if(data.iv){
          env.output.println("OSR : "+n.parents[0]+" is IV (OP "+n+")");
          Replace(n,n.parents[0],null);
        }
        else{
          nData.header=null;
        }
        break;
      }
**/
      case Op.ADD:
      case Op.MUL:{
        OsrData lData=(OsrData)nodeMap.get(n.parents[0]);
        OsrData rData=(OsrData)nodeMap.get(n.parents[1]);

        if(lData.iv && RegionConst(n.parents[1],lData.header)){
          env.println("OSR : "+n.parents[0]+" is IV and "+n.parents[1]+
                      " is RC (OP "+n+")",THR);
          Replace(n,n.parents[0],n.parents[1]);
        }
        else if(rData.iv && RegionConst(n.parents[0],rData.header)){
          env.println("OSR : "+n.parents[1]+" is IV and "+n.parents[0]+
                      " is RC (OP "+n+")",THR);
          Replace(n,n.parents[1],n.parents[0]);
        }
        else{
          nData.header=null;
        }
        break;
      }
      case Op.LSHS:
      case Op.LSHU: // Shift operation
      case Op.SUB:{
        OsrData lData=(OsrData)nodeMap.get(n.parents[0]);
        OsrData rData=(OsrData)nodeMap.get(n.parents[1]);
        
        if(lData.iv && RegionConst(n.parents[1],lData.header)){
          env.println("OSR : "+n.parents[0]+" is IV and "+n.parents[1]+
                      " is RC (OP "+n+")",THR);
          Replace(n,n.parents[0],n.parents[1]);
        }
        else{
          nData.header=null;
        }
        break;
      }
      default:
        nData.header=null;
    }
  }

  /**
   * Check whether the SCC is a induction variables. If the SCC is induction 
   * variables, then the compiler tries to reduce the operation uses them.
   * @param SCC The strongly connected component
   **/
  private void ClassifyIV(BiList SCC){
    boolean inductionVariable=true;
    DFST dfst=(DFST)f.require(DFST.analyzer);

    BasicBlk header=null;
    for(BiLink p=SCC.first();!p.atEnd();p=p.next()){
      SsaGraphNode n=(SsaGraphNode)p.elem();
      OsrData nData=(OsrData)nodeMap.get(n);
      if(header==null || dfst.dfn[header.id]>dfst.dfn[n.belong.id])
        header=n.belong;
    }

    for(BiLink p=SCC.first();!p.atEnd();p=p.next()){
      SsaGraphNode n=(SsaGraphNode)p.elem();

      switch(n.opCode){/**
        case Op.CONVIT:
        case Op.CONVSX:
        case Op.CONVZX:
        case Op.CONVFX:
        case Op.CONVFT:
        case Op.CONVFI:
        case Op.CONVFS:
        case Op.CONVFU:
        case Op.CONVSF:
        case Op.CONVUF:**/
        case Op.PHI:
        case Op.ADD:
        case Op.SUB: break;
        default: inductionVariable=false;
      }

      for(int i=0;i<n.parents.length;i++){
        SsaGraphNode o=n.parents[i];
        if(o!=null){
          if(!SCC.contains(o) && !RegionConst(o,header)){
            inductionVariable=false;
            break;
          }
        }
      }
      if(!inductionVariable)break;
    }

    if(inductionVariable){
      for(BiLink p=SCC.first();!p.atEnd();p=p.next()){
        SsaGraphNode n=(SsaGraphNode)p.elem();
        OsrData nData=(OsrData)nodeMap.get(n);
        nData.header=header;
        nData.iv=true;
        env.println("OSR : "+n+" is induction variable",THR);
      }
    }
    else{
      for(BiLink p=SCC.first();!p.atEnd();p=p.next()){
        SsaGraphNode n=(SsaGraphNode)p.elem();
        reduction(n);
      }
    }
  }

  /**
   * Return `true' if the node is constant in the current program.
   * @param node The current node of the SSA graph
   * @return `true' if the node is constant
   **/
  private boolean isConst(SsaGraphNode node){
    switch(node.opCode){
      case Op.INTCONST:
      case Op.FLOATCONST:
      case Op.FRAME:
      case Op.STATIC:{
        //env.println("OSR : "+node+" is constant",THR);
        return(true);
      }
    }

    return(false);
  }

  /**
   * Check whether the value in the node of the SSA graph is a region constant.
   * @param name The target node of the SSA graph
   * @param header The loop header block
   * @return If the value in the node is a constant or the block of 
   *         the node is strictly dominated by the header, return `true'.
   **/
  private boolean RegionConst(SsaGraphNode name,BasicBlk header){
    //env.output.print(" is const? : "+name+" header : blk"+header.id);

    if(isConst(name)){
      env.println("OSR : "+name+" is region constant",THR);
      //env.output.println(" true 1");
      return(true);
    }

    switch(name.opCode){
/**
      case Op.CALL:
      case Op.MEM:{
        //env.output.println(" false because load or store");
        return(false);
      }
**/
      case Op.JUMP:
      case Op.JUMPC:
      case Op.JUMPN:{
        //env.output.println(" false because JUMPx");
        return(false);
      }
    }

    // `name' is defined at outside of the loop
    if(header==null){
      //env.output.println(" false1");
      return(false);
    }

    if(name.belong==header){
      //env.output.println(" false2");
      return(false);
    }

    Dominators dom=(Dominators)f.require(Dominators.analyzer);
    if(!dom.dominates(name.belong,header)){
      //env.output.println(" false3");
      return(false);
    }

    env.println("OSR : "+name+" is region constant("+header.id+")",THR);
    //env.output.println(" true 3");
    return(true);
  }

  /**
   * Rewrite the current operation with a copy from its reduced counterpart.
   * @param node The current operation
   * @param iv The induction variable
   * @param rc The region constant
   **/
  private void Replace(SsaGraphNode node,SsaGraphNode iv,SsaGraphNode rc){
    //env.output.println("Replace : "+node+" "+iv+" "+rc);
    SsaGraphNode result=Reduce(node,iv,rc,iv.belong);
    if(result!=null){
      //env.output.println(result.symbol());

      OsrData nodeData=(OsrData)nodeMap.get(node);
      OsrData ivData=(OsrData)nodeMap.get(iv);
      OsrData resultData=(OsrData)nodeMap.get(result);

      nodeData.header=ivData.header;
      resultData.header=ivData.header;
      ssaGraph.setSymbol(node.symbol(),result);
      env.println("OSR : replace "+node+" to "+result,THR);
      env.println("OSR : "+result+" is new IV as a result",THR);
      //env.output.println("--- "+node+" "+iv+" "+rc+" "+result+"\n");
    }
  }

  /**
   * Insert code to strength reduce an induction variable and returns the 
   * node of the SSA graph as a result.
   * @param node The current operation
   * @param iv The induction variable
   * @param rc The region constant
   * @param belong The basic block which the node belongs to
   * @return The node of SSA graph which is a result of strength reduction
   **/
  private SsaGraphNode Reduce(SsaGraphNode node,SsaGraphNode iv,
                              SsaGraphNode rc,BasicBlk belong){

    if(node.node.type!=iv.node.type) return(null);
    if(rc!=null){
      if(rc.opCode==Op.PROLOGUE){
        if(node.node.type!=rc.symbol().type) return(null);
      }
      else{
        if(node.node.type!=rc.node.type) return(null);
      }
    }

    SsaGraphNode result=osrLookUp.search(node,iv,rc);

    if(result==null){
      Symbol s=sstab.newSsaSymbol(osrSymName,node.node.type);

      SsaGraphNode newDef=new SsaGraphNode(env,iv.node.makeCopy(env.lir),
                                           iv.belong,iv.parents.length);
      for(int i=0;i<newDef.parents.length;i++){
        newDef.parents[i]=iv.parents[i];
      }
      ssaGraph.setSymbol(s,newDef);

      BiLink pos=ssaGraph.nodeList().locate(iv);
      pos.addAfter(newDef);

      OsrData ivData=(OsrData)nodeMap.get(iv);
      OsrData newDefData=new OsrData(nextDFSnum++);
      newDefData.header=ivData.header;
      newDefData.iv=ivData.iv;
      nodeMap.put(newDef,newDefData);

      env.println("OSR : Make "+newDef+" to new IV(original "+iv+")",THR);

      result=newDef;
      osrLookUp.add(node,iv,rc,result,true);

      for(int i=0;i<newDef.parents.length;i++){
        SsaGraphNode o=(SsaGraphNode)newDef.parents[i];
        if(o!=null){
          OsrData oData=(OsrData)nodeMap.get(o);
          if(oData.header==ivData.header){
            SsaGraphNode reduced=Reduce(node,o,rc,o.belong);
            newDef.parents[i]=reduced;
          }
          else if(node.opCode==Op.MUL || node.opCode==Op.LSHS ||
                  node.opCode==Op.LSHU || newDef.opCode==Op.PHI){
            SsaGraphNode applied=Apply(node,o,rc,newDefData.header);
            if(applied!=null){
              //env.output.println(applied);
              newDef.parents[i]=applied;
            }
//            else{
//              env.output.println("aaaaaaaaaaaaaaaaaaaaaaaaa NULL\n\t"+
//                                 node+"\n\t"+o+"\n\t"+rc);
//            }
          }
        }
      }
      //env.output.println(node+" "+iv+" "+rc+" "+result);
    }
    //env.output.println("   "+result);
    return(result);
  }

  /**
   * Insert an instruction to apply an opecode to two operands and return the
   * node of the SSA graph as a result. 
   * This method also performs constant folding, if possible.
   * @param opcode The operator
   * @param op1 The first operand
   * @param op2 The second operand
   * @param belong The basic block which the node belongs to
   * @return The new node of SSA graph which applied the operation
   **/
  private SsaGraphNode Apply(SsaGraphNode opcode,SsaGraphNode op1,
                             SsaGraphNode op2,BasicBlk belong){
    int opcodeType=opcode.node.type;
    if(op1.opCode==Op.PROLOGUE || op1.opCode==Op.CALL){
      if(op2.opCode==Op.PROLOGUE || op2.opCode==Op.CALL){
        if(op1.symbol().type!=opcodeType || op2.symbol().type!=opcodeType){
          return(null);
        }
      }
      else{
        if(op1.symbol().type!=opcodeType || op2.node.type!=opcodeType){
          return(null);
        }
      }
    }
    else{
      if(op2.opCode==Op.PROLOGUE || op2.opCode==Op.CALL){
        if(op1.node.type!=opcodeType || op2.symbol().type!=opcodeType){
          return(null);
        }
      }
      else{
        if(op1.node.type!=opcodeType || op2.node.type!=opcodeType){
          return(null);
        }
      }
    }

    SsaGraphNode result=osrLookUp.search(opcode,op1,op2);
    if(result==null){
      //env.output.println("  "+opcode+" "+op1+" "+op2);
      OsrData op1Data=(OsrData)nodeMap.get(op1);
      OsrData op2Data=(OsrData)nodeMap.get(op2);
      if(op1Data.header!=null && RegionConst(op2,op1Data.header)){
//        result=Reduce(opcode,op1,op2,belong);
        result=Reduce(opcode,op1,op2,op1.belong);
        //env.output.println("n "+result);
      }
      else if(op2Data.header!=null && RegionConst(op1,op2Data.header)){
//        result=Reduce(opcode,op2,op1,belong);
        result=Reduce(opcode,op2,op1,op1.belong);
        //env.output.println("r "+result);
      }
      else{
//        env.output.println(opcode+" "+op1+" "+op2);

        result=calc(opcode,op1,op2,belong);
        if(result==null){
//          env.output.println("pos 2");
          return(null);
        }

        osrLookUp.add(opcode,op1,op2,result,false);
        
        //env.output.println(result);

        OsrData resultData=(OsrData)nodeMap.get(result);
        resultData.header=null;
        resultData.iv=false;
      }
    }
    //env.output.println("  "+result);
    return(result);
  }

  /**
   * Calculate the operation and return the result.
   * @param opcode The operation node
   * @param op1 The first operand
   * @param op2 the second operand
   * @param belong The basic block which the node belongs to
   * @return The new node of SSA graph which the result of the calculation
   **/
  private SsaGraphNode calc(SsaGraphNode opcode,SsaGraphNode op1,
                            SsaGraphNode op2,BasicBlk belong){
    SsaGraphNode result=null;



    // If it can be, Do constant folding.
    LirNode newNode=null;
    if(op1.opCode==Op.INTCONST && op2.opCode==Op.INTCONST){
      newNode=env.lir.operator(opcode.opCode,opcode.node.type,
                               op1.node.makeCopy(env.lir),
                               op2.node.makeCopy(env.lir),ImList.Empty);
      newNode=env.lir.foldConstant(newNode);

      //env.output.println(o1+" "+o2+" "+newNode);

      // Put the new node into the entry node of the CFG.
      // Because the new node is a assignment constant into a new variable.
      result=new SsaGraphNode(env,newNode,f.flowGraph().entryBlk(),0);
      //result=new SsaGraphNode(env,newNode,belong,0);

/**
      if(op1.symbol()!=null){
        Symbol s=sstab.newSsaSymbol(osrSymName,opcode.node.type);
        ssaGraph.setSymbol(s,result);
      }
**/
    }
    else if(opcode.opCode!=Op.LSHS && opcode.opCode!=Op.LSHU && 
            op1.opCode==Op.FLOATCONST && op2.opCode==Op.FLOATCONST){
      newNode=env.lir.operator(opcode.opCode,opcode.node.type,
                               op1.node.makeCopy(env.lir),
                               op2.node.makeCopy(env.lir),ImList.Empty);
      newNode=env.lir.foldConstant(newNode);
      // Put the new node into the entry node of the CFG.
      // Because the new node is a assignment constant into a new variable.
      result=new SsaGraphNode(env,newNode,f.flowGraph().entryBlk(),0);
      //result=new SsaGraphNode(env,newNode,belong,0);

/**
      if(op1.symbol()!=null){
        Symbol s=sstab.newSsaSymbol(osrSymName,opcode.node.type);
        ssaGraph.setSymbol(s,result);
      }
**/
    }
    else{
      LirNode newOp1=null;
      LirNode newOp2=null;

      boolean isNewOp1=false;
      boolean isNewOp2=false;

      Symbol ss=op1.symbol();
      if(ss==null || op1.opCode==Op.INTCONST || op1.opCode==Op.FLOATCONST){
        newOp1=op1.node.makeCopy(env.lir);
        // Make a new constant node
        //op1=ssaGraph.appendNode(newOp1,f.flowGraph().entryBlk(),0);
        op1=new SsaGraphNode(env,newOp1,f.flowGraph().entryBlk(),0);
        isNewOp1=true;
      }
      else newOp1=env.lir.symRef(ss);
      
      ss=op2.symbol();
      if(ss==null || op2.opCode==Op.INTCONST || op2.opCode==Op.FLOATCONST){
        newOp2=op2.node.makeCopy(env.lir);
        // Make a new constant node
        //op2=ssaGraph.appendNode(newOp2,f.flowGraph().entryBlk(),0);
        op2=new SsaGraphNode(env,newOp2,f.flowGraph().entryBlk(),0);
        isNewOp2=true;
      }
      else newOp2=env.lir.symRef(ss);
      
      // The basic block which the new expression is inserted must be
      // domninated by the both operands.
      BasicBlk blk=whichBlk(op1,op2,belong);

      // If no block to insert a new expression, then give up insertion.
      if(blk==null) return(null);

      newNode=env.lir.operator(opcode.opCode,opcode.node.type,
                               newOp1,newOp2,ImList.Empty);

      if(isNewOp1) ssaGraph.nodeList().add(op1);
      if(isNewOp2) ssaGraph.nodeList().add(op2);

      result=new SsaGraphNode(env,newNode,blk,2);

      Symbol s=sstab.newSsaSymbol(osrSymName,opcode.node.type);

      //env.output.println(opcode+" "+op1+" "+op2);
      //env.output.println("aaa "+s+" "+belong.id+" "+blk.id+"\n");

      ssaGraph.setSymbol(s,result);
      result.parents[0]=op1;
      result.parents[1]=op2;

      //env.output.println(result);
    }
    //env.output.println("aa "+result);
    //env.output.println("bb "+newNode);

    env.println("OSR : Insert "+result,THR);
    BiLink pos=ssaGraph.nodeList().locate(op1);
    pos.addAfter(result);

    OsrData resultData=new OsrData(nextDFSnum++);
    nodeMap.put(result,resultData);

    return(result);
  }

  /**
   * Choose the basic block which the operator is inserted in.
   * @param op1 The first operand
   * @param op2 The second operand
   * @param belong The basic block which the operator originally is in
   * @return The basic block which the operator is inserted in
   **/
  private BasicBlk whichBlk(SsaGraphNode op1,SsaGraphNode op2,BasicBlk belong){
    BasicBlk blk=null;
    Symbol os1=op1.symbol();
    Symbol os2=op2.symbol();
    int opc1=op1.opCode;
    int opc2=op2.opCode;

    // The both operands are the constant nodes.
    if((os1==null || opc1==Op.INTCONST || opc1==Op.FLOATCONST) &&
       (os2==null || opc2==Op.INTCONST || opc2==Op.FLOATCONST)){
      // The operator is inserted in the entry block of the CFG.
      //env.output.println("########## check 1");
      blk=f.flowGraph().entryBlk();
      //blk=belong;
    }
    // The second operand is the constant node.
    //else if(os1!=null && os2==null){
    else if((os1!=null && opc1!=Op.INTCONST && opc1!=Op.FLOATCONST) &&
            (os2==null || opc2==Op.INTCONST || opc2==Op.FLOATCONST)){
      // The basic block which the operator is inserted in must be dominated
      // by `op1'.
      //env.output.println("########## check 2");
//      Dominators dom=(Dominators)f.require(Dominators.analyzer);
//      if(dom.dominates(op1.belong,belong))
//        blk=belong;
//      else
        blk=op1.belong;
    }
    // The first operand is the constant node.
    //else if(os1==null && os2!=null){
    else if((os1==null || opc1==Op.INTCONST || opc1==Op.FLOATCONST) &&
            (os2!=null && opc2!=Op.INTCONST && opc2!=Op.FLOATCONST)){
      // The basic block which the operator is inserted in must be dominated
      // by `op2'.
      //env.output.println("########## check 3");
      //env.output.println("    "+op1+" "+op2);
//      Dominators dom=(Dominators)f.require(Dominators.analyzer);
//      if(dom.dominates(op2.belong,belong))
//        blk=belong;
//      else
        blk=op2.belong;
    }
    // The both operands are the variables.
    else{
      // The basic block which the operator is inserted in must be dominated
      // by both operands.
//      env.output.println("aaaaaaaaa "+op1+" "+op2+" "+belong.id);

      // Both operands must be region constant
      if(!RegionConst(op1,belong) || !RegionConst(op2,belong)){
        env.output.println("no place to insert a new expression 1");
        blk=null;
//        System.exit(1);
      }
      else{
        Dominators dom=(Dominators)f.require(Dominators.analyzer);
        if(dom.dominates(op1.belong,op2.belong)){
          blk=op2.belong;
        }
        else if(dom.dominates(op2.belong,op1.belong)){
          blk=op1.belong;
        }
        else{
          // If one of the operands doesn't dominate `belong', then the 
          // operator can not insert into `belong'.
          blk=null;
          env.output.println("no place to insert a new expression 2");
//          System.exit(1);
        }
      }
    }

    return(blk);
  }
}
