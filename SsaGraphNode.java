/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.Function;
import coins.backend.util.BiList;
import coins.backend.util.BiLink;
import coins.backend.Op;
import coins.backend.Type;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.lir.LirLabelRef;
import coins.backend.lir.LirIconst;
import coins.backend.lir.LirFconst;
import coins.backend.util.ImList;
import coins.backend.sym.Symbol;

import java.io.IOException;
import java.io.OutputStreamWriter;

/** 
 * The node of the SSA graph
 **/
class SsaGraphNode{
  /** The basic block which the LIR node of this node is in **/
  public final BasicBlk belong;
  /** The operator code of this node **/
  public final int opCode;
  /** The LIR node of this node **/
  public final LirNode node;
  /** The parents of this node **/
  public final SsaGraphNode[] parents;
  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The symbol of this node **/
  private Symbol symbol;

  /**
   * Constructor
   * @param e The environment of the SSA module
   * @param n The LIR node of this node
   * @param blk The basic block which the LIR node of this node is in
   * @param numOfParents The number of parents of this node
   **/
  public SsaGraphNode(SsaEnvironment e,LirNode n,BasicBlk blk,
                      int numOfParents){
    env=e;
    belong=blk;
    node=n;
    opCode=n.opCode;
    parents=new SsaGraphNode[numOfParents];
    symbol=null;
  }

  /** 
   * Return the symbol of this node.
   * @return The symbol of this node
   **/
  Symbol symbol(){
    return(symbol);
  }

  /**
   * Set the symbol of this node.
   * @param s The symbol of this node
   **/
  void setSymbol(Symbol s){
    symbol=s;
  }

  /** 
   * The String representation of this node.
   **/
  public String toString(){
    String str="("+Op.toName(opCode)+" "+Type.toString(node.type);
    if(symbol!=null){
      str=str+" ("+symbol.name+")";
    }
    switch(node.opCode){
      case Op.INTCONST:{
        str=str+" ("+((LirIconst)node).value+")";
        break;
      }
      case Op.FLOATCONST:{
        str=str+" ("+((LirFconst)node).value+")";
        break;
      }
    }
    str=str+" (block "+belong.id+"))";

    return(str);
  }

  /**
   * Translate this node into LIR node.
   * @return LIR node from this SSA graph's node
   **/
  LirNode apply(BiList nodeList){
    //env.output.println("call SsaGraphNode's apply");
    LirNode returnNode=null;
    LirNode[] args=new LirNode[parents.length];
    //env.output.println(node);
    for(int i=0;i<parents.length;i++){
      //env.output.println("  "+parents[i]);
      if(parents[i]!=null){
        Symbol s=parents[i].symbol();
        if(s==null){
          //env.output.println("fffffffffffffffff "+parents[i].apply());
          args[i]=parents[i].apply(nodeList);
        }
        else{
          //env.output.println("fffffffffffffffff "+s);
          args[i]=env.lir.symRef(s);
        }
      }
    }

    switch(opCode){
      case Op.PROLOGUE:{
        // The PROLOGUE node does not treat here.
        break;
      }
      case Op.CALL:{
        // Change the arguments, the return values and the address of the
        // function.

        // The address of the current function.
        node.setKid(0,args[0]);

        // The arguments.
        LirNode argList[]=new LirNode[args.length-1];
        for(int i=0;i<argList.length;i++){
          argList[i]=args[i+1].makeCopy(env.lir);
        }
        LirNode arg=env.lir.operator(Op.LIST,Type.UNKNOWN,argList,
                                     ImList.Empty);
        node.setKid(1,arg);

        // The return values.
        // This module can not treat multiple return value.
        LirNode[] retValList;
        if(symbol!=null){
          retValList=new LirNode[1];
          retValList[0]=env.lir.symRef(symbol);
        }
        else{
          // Return value may be MEM node
          // If the symbol is null
          BiList bList=new BiList();
          boolean hasArg=false;
          for(BiLink p=nodeList.first();!p.atEnd();p=p.next()){
            SsaGraphNode n=(SsaGraphNode)p.elem();
            for(int j=0;j<n.parents.length;j++){
              if(n.parents[j]==this){
                hasArg=true;
                // be careful!
                n.parents[j]=null;
                bList.add(n.apply(nodeList));
              }
            }
          }
          if(hasArg){
            retValList=new LirNode[bList.length()];
            BiLink p=bList.first();
            for(int i=0;i<retValList.length;i++){
              retValList[i]=((LirNode)p.elem()).makeCopy(env.lir);
              p=p.next();
            }
          }
          else{
            retValList=new LirNode[0];
          }
        }
        LirNode retVal=env.lir.operator(Op.LIST,Type.UNKNOWN,
                                        retValList,ImList.Empty);
        node.setKid(2,retVal);
        returnNode=node;

        break;
      }
      case Op.EPILOGUE:{
        // Change the register variable which is the argument of the EPILOGUE
        // node
        for(int i=0;i<args.length;i++){
          node.setKid(i+1,args[i].makeCopy(env.lir));
        }
        returnNode=node;
        break;
      }
      case Op.PHI:{
        // Basically, reuse the registered LIR node.
        args[0]=env.lir.symRef(symbol);
        if(!node.kid(0).equals(args[0])) 
          node.setKid(0,args[0].makeCopy(env.lir));

        for(int i=1;i<args.length;i++){
          //env.output.println(i+" ************* "+args[i]);
          //env.output.println("+++++++++++++ "+node.kid(i));
          if(!args[i].equals(node.kid(i).kid(0)))
            node.kid(i).setKid(0,args[i].makeCopy(env.lir));
        }
        returnNode=node;
        break;
      }
      case Op.MEM:{
        LirNode self=env.lir.operator(opCode,node.type,
                                      args[0].makeCopy(env.lir),node.opt);
        if(symbol==null){
          returnNode=self;
          if(args[1]!=null){
            env.output.println(args[1]);
          }
        }
        else{
          // This is MEM node as load operation.
          if(args[1]==null){
            LirNode definedNode=env.lir.symRef(symbol);
            returnNode=env.lir.operator(Op.SET,node.type,definedNode,
                                        self,node.opt);
          }
          // This is MEM node as store operation.
          else{
            // Temporary, adjest to the type of the source operand.
            returnNode=env.lir.operator(Op.SET,args[1].type,self,
                                        args[1].makeCopy(env.lir),
                                        node.opt);
          }
        }

        break;
      }
      case Op.JUMP:{
        // Reuse the registered LIR node.
        returnNode=node;
        break;
      }
      case Op.JUMPC:{
        switch(args[0].opCode){
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
            // Replace only the conditional part.
            node.setKid(0,args[0].makeCopy(env.lir));
            break;
          }
          default:{
            LirNode zeroNode=env.lir.iconst(args[0].type,0,ImList.Empty);
            LirNode tstNode=env.lir.operator(Op.TSTNE,args[0].type,args[0],
                                             zeroNode,node.opt);
            node.setKid(0,tstNode);
          }
        }

        returnNode=node;
        break;
      }
      case Op.JUMPN:{
        // Replace only the register variable which is compared.
        node.setKid(0,args[0].makeCopy(env.lir));
        returnNode=node;
        break;
      }
      // Cast Operator
      case Op.CONVSX:
      case Op.CONVZX:
      case Op.CONVIT:
      case Op.CONVFX:
      case Op.CONVFT:
      case Op.CONVFI:
      case Op.CONVFS:
      case Op.CONVFU:
      case Op.CONVSF:
      case Op.CONVUF:{
        // If the original type and the casted type are the same type, 
        // then remove cast operator.
        if(args[0].type==node.type){
          if(symbol==null) returnNode=args[0];
          else{
            LirNode definedNode=env.lir.symRef(symbol);
            returnNode=env.lir.operator(Op.SET,node.type,definedNode,
                                        args[0].makeCopy(env.lir),
                                        node.opt);
          }
          break;
        }
        // Otherwise treat as a unary operator.
      }
      // Unary Operator
      case Op.NEG:
      case Op.BNOT:{
        LirNode self=env.lir.operator(opCode,node.type,
                                      args[0].makeCopy(env.lir),node.opt);
        if(symbol==null) returnNode=self;
        else{
          LirNode definedNode=env.lir.symRef(symbol);
          returnNode=env.lir.operator(Op.SET,node.type,definedNode,
                                      self,ImList.Empty);
        }
        break;
      }
      // Binary Operator
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
        LirNode self=env.lir.operator(opCode,node.type,
                                      args[0].makeCopy(env.lir),
                                      args[1].makeCopy(env.lir),
                                      node.opt);
        if(symbol==null) returnNode=self;
        else{
          LirNode definedNode=env.lir.symRef(symbol);
          returnNode=env.lir.operator(Op.SET,node.type,definedNode,
                                      self,ImList.Empty);
        }
        break;
      }
      // Leaf Nodes
      case Op.LABEL:
      case Op.FRAME:
      case Op.STATIC:
      case Op.INTCONST:
      case Op.FLOATCONST:{
        //returnNode=node;

        if(symbol==null) returnNode=node;
        else{
          LirNode definedNode=env.lir.symRef(symbol);
          returnNode=env.lir.operator(Op.SET,node.type,definedNode,
                                      node.makeCopy(env.lir),ImList.Empty);
        }

        break;
      }
      case Op.LINE:
      	{
      		returnNode = env.lir.operator(Op.LINE, Type.UNKNOWN, node.kid(0).makeCopy(env.lir), ImList.Empty);
      	}
      	break;
    }
    //env.output.println("exit from SsaGraphNode's apply");
    return(returnNode);
  }

  /**
   * Print the node as
   * <a href="http://www.research.att.com/sw/tools/graphviz/">graphviz</a>
   * format.
   * @param output The output stream
   * @param list The list of the node of the SSA graph
   **/
  void printGraph(OutputStreamWriter output,BiList list){
    try{
      output.write(list.whereIs(this)+" [fontsize=10,label=\"\\l ");
    }
    catch(IOException e){
      System.out.print(list.whereIs(this)+" [fontsize=10,label=\"\\l ");
    }

    // print labels
    if(symbol!=null){
      try{
        output.write("def : "+symbol.name+"\\l ");
      }
      catch(IOException e){
        System.out.print("def : "+symbol.name+" \\l");
      }
    }

    // print values
    switch(opCode){
      case Op.INTCONST:{
        try{
          output.write("value : "+((LirIconst)node).value+" \\l");
        }
        catch(IOException e){
          System.out.print("value : "+((LirIconst)node).value+" \\l");
        }
        break;
      }
      case Op.FLOATCONST:{
        try{
          output.write("value : "+((LirFconst)node).value+" \\l");
        }
        catch(IOException e){
          System.out.print("value : "+((LirFconst)node).value+" \\l");
        }
        break;
      }
      case Op.STATIC:
      case Op.FRAME:{
        try{
          output.write("value : "+((LirSymRef)node).symbol.name+" \\l");
        }
        catch(IOException e){
          System.out.print("value : "+((LirSymRef)node).symbol.name+" \\l");
        }
        break;
      }
      case Op.LABEL:{
        try{
          output.write("value : "+((LirLabelRef)node).label.name()+" \\l");
        }
        catch(IOException e){
          System.out.print("value : "+((LirLabelRef)node).label.name()+" \\l");
        }
        break;
      }
      default:{
        try{
          output.write("value : "+Op.toName(opCode)+" \\l");
        }
        catch(IOException e){
          System.out.print("value : "+Op.toName(opCode)+" \\l");
        }
      }
    }

    // print basic blk
    try{
      output.write("block : "+belong.id+" \\l");
    }
    catch(IOException e){
      System.out.print("block : "+belong.id+" \\l");
    }

    try{
      output.write("\"]\n");
    }
    catch(IOException e){
      System.out.print("\"]\n");
    }

    // print successors
    for(int i=0;i<parents.length;i++){
      if(list.whereIs(parents[i])!=-1){
        try{
          output.write(list.whereIs(this)+" -> "+
                       list.whereIs(parents[i])+"\n");
        }
        catch(IOException e){
          System.out.println(list.whereIs(this)+" -> "+
                             list.whereIs(parents[i]));
        }
      }
    }
  }
}
