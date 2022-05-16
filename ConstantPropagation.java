/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.Function;
import coins.backend.Op;
import coins.backend.Data;
import coins.backend.LocalTransformer;
import coins.backend.cfg.FlowGraph;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.lir.LirIconst;
import coins.backend.lir.LirFconst;
import coins.backend.lir.LirLabelRef;
import coins.backend.sym.Symbol;
import coins.backend.util.BiList;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;
import coins.backend.Type;

import java.util.Stack;
import java.util.Hashtable;

/**
 * Constant Propagation<br>
 * This constant propagator considers the condition jumps.
 * Only reachable edges and basic blocks  are target on.<br><br>
 * Reference:<br>
 * I. Nakata, "The Structure and Optimization of the Compiler," 
 * Asakura Shoten, 1999(In Japanese). 
**/
class ConstantPropagation implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "ConstantPropagation"; }
  public String subject() {
    return "Constant propagation on SSA form.";
  }

  /**
   * The private date for this optimizer.
   **/
  private class VariableData{
    /** The symbol of the current variable **/
    private Symbol s;
    /** True if the variable is undefined **/
    private boolean undefine;
    /** True if the variable can remove **/
    private boolean canReplace;
    /** True if the variable is overdefined **/
    private boolean overdefine;
    /** The list of the LIR nodes which use the current variable **/
    private BiList useList;
    /** The list of the LIR nodes which define the current variable **/
    private LirNode defineNode;
    /** The constant value if the current variable is constant **/
    //private Number value;
    private LirNode value;

    /**
     * Constructor
     * @param sym The symbol of the current variable
     **/
    VariableData(Symbol sym){
      s=sym;
      undefine=true;
      overdefine=false;
      canReplace=false;
      useList=new BiList();
      defineNode=null;
      value=null;
    }

    /**
     * Debug print
     **/
    void print(){
      env.output.println(" +++++++ about "+s);
      env.output.println("    undefined : "+undefine);
      env.output.println("  overdefined : "+overdefine);
      env.output.println("  can replace : "+canReplace);
      if(!undefine && !overdefine){
        env.output.println("        value : "+value);
      }
      env.output.println("  define node : "+defineNode);
      for(BiLink p=useList.first();!p.atEnd();p=p.next()){
        env.output.print("     use node : ");
        Object[] obj=(Object [])p.elem();
        env.output.println(((BasicBlk)obj[0]).label()+" -- "+obj[1]);
      }
      env.output.println();
    }
  }

  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The threshold of debug print **/
  public static final int THR=SsaEnvironment.OptThr;
  /** The current function **/
  private Function f;
  /** The map between symbols and their datas **/
  private Hashtable symbols;
  /** The work stack **/
  private Stack FlowWork;
  /** The work stack **/
  private Stack SSAWork;
  /** The list of the adges which can reach **/
  private BiList availEdge;
  /** Utility **/
  private Util util;

  /**
   * Constructor
   * @param e The environment of the SSA module
   **/
  public ConstantPropagation(SsaEnvironment e){
    env=e;
    env.println("  Constant Propagation",SsaEnvironment.MsgThr);
  }

  /**
   * Do constant propagation
   * @param function The current function
   **/
  public boolean doIt(Function function,ImList args){
    env.println("****************** doing CSTP to "+function.symbol.name,
                SsaEnvironment.MinThr);
    f=function;
    util=new Util(env,f);
    FlowGraph g=function.flowGraph();

    boolean phiChanged=true;
    while(phiChanged){
      phiChanged=false;

      // initialize the expression lists of the use each variables.
      symbols=new Hashtable();
      for(BiLink p=f.localSymtab.symbols().first();!p.atEnd();p=p.next()){
        Symbol s=(Symbol)p.elem();
        if(!symbols.containsKey(s)){
          symbols.put(s,new VariableData(s));
        }
      }

      BiList visited=new BiList();
      BasicBlk entryBlk=g.entryBlk();
      Stack stack=new Stack();
      stack.push(entryBlk);

      while(!stack.empty()){
        BasicBlk blk=(BasicBlk)stack.pop();
        if(!visited.contains(blk)){
          visited.add(blk);
          //env.output.println(blk.label());

          for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
            LirNode node=(LirNode)p.elem();
            if(node.opCode==Op.PROLOGUE){
              // set the definition point of the REG to this node and
              // also set the overdefined flag to the REG.
              BiList list=util.findTargetLir(node,Op.REG,new BiList());
              for(BiLink q=list.first();!q.atEnd();q=q.next()){
                LirSymRef regNode=(LirSymRef)q.elem();
                //env.output.println(regNode);
                VariableData data=getVariableData(regNode);

                data.overdefine=true;
                data.defineNode=node;
                //data.print();
              }
            }
            else if(node.opCode==Op.SET || node.opCode==Op.PHI){
              if(node.kid(0).opCode!=Op.REG){
                // find REG in the both sides of SET.
                BiList list=util.findTargetLir(node,Op.REG,new BiList());
                setUse(blk,node,list);
              }
              else{
                // The REG in the left hand side of the SET node is defined.
                // The REGs in the right hand side of the SET node are used.
                LirSymRef regNode=(LirSymRef)node.kid(0);
                VariableData data=getVariableData(regNode);

                //data.undefine=false;
                data.defineNode=node;
                //data.print();

                // find REG in the right hand side of SET.
                for(int i=1;i<node.nKids();i++){
                  BiList list=util.findTargetLir(node.kid(i),Op.REG,
                                                 new BiList());
                  setUse(blk,node,list);
                }
              }
            }
            else if(node.opCode==Op.CALL){
              // The REGs in the third argument of CALL node are returned 
              // value.
              if(node.kid(2).nKids()>0 && node.kid(2).kid(0).opCode==Op.REG){
                //env.output.println(node.kid(2));
                LirSymRef regNode=(LirSymRef)node.kid(2).kid(0);
                VariableData data=getVariableData(regNode);

                data.undefine=false;
                data.overdefine=true;
                data.defineNode=node;
                //data.print();
              }
              else{
                BiList rvals=util.findTargetLir(node.kid(2),
                                                Op.REG,new BiList());
                for(BiLink pp=rvals.first();!pp.atEnd();pp=pp.next()){
                  LirNode arg3=(LirNode)pp.elem();
                  BiList list=util.findTargetLir(arg3,Op.REG,new BiList());
                  setUse(blk,node,list);
                }
              }

              // The REGs in other arguments of CALL are used.            
              // find REGs in other arguments of CALL
              for(int i=0;i<2;i++){
                BiList list=util.findTargetLir(node.kid(i),Op.REG,
                                               new BiList());
                setUse(blk,node,list);
              }
            }
            else{
              // All REG nodes which belong to the other nodes are used.
              BiList list=util.findTargetLir(node,Op.REG,new BiList());
              setUse(blk,node,list);

              // Iterate nodes in the control flow graph.
              if(node.opCode==Op.JUMP){
                stack.push(((LirLabelRef)node.kid(0)).label.basicBlk());
              }
              else if(node.opCode==Op.JUMPC){
                for(int i=1;i<node.nKids();i++){
                  stack.push(((LirLabelRef)node.kid(i)).label.basicBlk());
                }
              }
              else if(node.opCode==Op.JUMPN){
                for(int i=0;i<node.kid(1).nKids();i++){
                  stack.push(((LirLabelRef)node.kid(1).kid(i).
                              kid(1)).label.basicBlk());
                }
                // default label
                stack.push(((LirLabelRef)node.kid(2)).label.basicBlk());
              }
            }
          }
        }
      }

      FlowWork=new Stack();
      SSAWork=new Stack();
      availEdge=new BiList();
      BiList availBlk=new BiList();

      LirLabelRef entry=(LirLabelRef)env.lir.labelRefVariant(entryBlk.label());
      FlowWork.push(entry);

      // The main algorithm of the constant propagation
      while(!(FlowWork.empty() && SSAWork.empty())){
        // If the FlowWork is not empty.
        while(!FlowWork.empty()){
          // then, pop an edge from FlowWork.
          LirLabelRef lab=(LirLabelRef)FlowWork.pop();

          // If the edge has been set available, do nothing.
          if(!availEdge.contains(lab)){
            //env.output.println("aaaaaaaaaaaaaaaa "+lab.label.basicBlk().id);
            // If not, then the edge is set available.
            availEdge.add(lab);
            BasicBlk blk=lab.label.basicBlk();

            // Do "Evaluate Phi instruction" to the PHI instructions in the
            // target block of the edge.
            for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
              LirNode node=(LirNode)p.elem();
              if(node.opCode!=Op.PHI)break;

              evalPhiExp(node);
            }

            // If the target block of the edge has been set available,
            // do nothing.
            if(!availBlk.contains(blk)){
              // If not, then the block is set available.
              availBlk.add(blk);
              env.println("CSTP : block "+blk.id+" is available",THR);

              // Do "Evaluate instruction" to every instructions in the block.
              // (except PHI instructions)
              for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
                LirNode node=(LirNode)p.elem();
                if(node.opCode!=Op.PHI){
                  evalExp(node);
                }
              }
            }
            // If the number of the successor of the block is only one,
            // put the edge between the block and the successor into the
            // FlowWork.
            if(((LirNode)blk.instrList().last().elem()).opCode==Op.JUMP){
              LirNode node=(LirNode)blk.instrList().last().elem();
              FlowWork.push(node.kid(0));
            }
          }
        }

        // If the SSAWork is not empty
        while(!SSAWork.empty()){
          // then, pop a definition from SSAWork.
          Symbol s=(Symbol)SSAWork.pop();

          // For every instructions which use the definition
          VariableData data=getVariableData(s);

          for(BiLink p=data.useList.first();!p.atEnd();p=p.next()){
            Object[] obj=(Object [])p.elem();
            // If the instruction is in the available block.
            if(availBlk.contains(obj[0])){
              if(((LirNode)obj[1]).opCode==Op.PHI){
                // If the instruction is kind of PHI instruction, then do
                // "Evaluate PHI instruction" to it.
                evalPhiExp((LirNode)obj[1]);
              }
              else{
                // If not, then do "Evaluate instruction" to it.
                evalExp((LirNode)obj[1]);
              }
            }
          }
        }
      }

      // Replace from variable to constant
      stack=new Stack();
      stack.push(entryBlk);
      visited=new BiList();
    
      while(!stack.empty()){
        BasicBlk blk=(BasicBlk)stack.pop();
        if(!visited.contains(blk)){
          visited.add(blk);
          for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
            LirNode node=(LirNode)p.elem();

            // If the current node is the assign to the register, PHI 
            // instructions or the function call which has return value.
            if(((node.opCode==Op.SET || node.opCode==Op.PHI) &&
                node.kid(0).opCode==Op.REG) ||
               (node.opCode==Op.CALL && node.kid(2).nKids()>0 &&
                node.kid(2).kid(0).opCode==Op.REG)){

              VariableData data=null;
              switch(node.opCode){
                case Op.CALL:{
                  data=getVariableData((LirSymRef)node.kid(2).kid(0));
                  break;
                }
                default:
                  data=getVariableData((LirSymRef)node.kid(0));
              }

              if(data!=null && !data.overdefine){ // not overdefined
                if(data.undefine){ // undefined
                  //data.print();
                  env.println("CSTP : remove because unavailable "+node+
                              " in block "+blk.id,THR);
                  p.unlink();
                  g.touch();
                  //env.output.println("a :"+node);
                }
                else{ // not undefined
                  data.canReplace=true;
                
                  for(BiLink q=data.useList.first();!q.atEnd();q=q.next()){
                    Object[] o=(Object[])q.elem();
                    if(availBlk.contains(o[0])){
                      simplePropagate((LirNode)o[1]);
                      //env.output.println("aaaaaaaaaaaaaaaa");
                      //env.output.println(o[1]);
                      //data.print();
                    }
                  }
                
                  //data.print();
                  env.println("CSTP : remove because constant "+node+
                              " in block "+blk.id,THR);
                  p.unlink();
                  g.touch();
                  //env.output.print(data.value+" = ");
                  //env.output.println("b :"+node);
                }
              }
              else{ // overdefined
                simplePropagate(node);
                folding(node);
                //data.print();
              }
            }
            else{
              simplePropagate(node);
              folding(node);
            }
            // Iterate nodes in the control flow graph.
            if(node.opCode==Op.JUMP){
              LirLabelRef lab=(LirLabelRef)node.kid(0);
              stack.push(lab.label.basicBlk());
            }
            else if(node.opCode==Op.JUMPC){
              for(int i=1;i<node.nKids();i++){
                LirLabelRef lab=(LirLabelRef)node.kid(i);
                stack.push(lab.label.basicBlk());
              }
            }
            else if(node.opCode==Op.JUMPN){
              for(int i=0;i<node.kid(1).nKids();i++){
                LirLabelRef lab=(LirLabelRef)node.kid(1).
                  kid(i).kid(1);
                stack.push(lab.label.basicBlk());
              }
              // default label
              LirLabelRef lab=(LirLabelRef)node.kid(2);
              stack.push(lab.label.basicBlk());
            }
          }
        }
      }

      // Reconstruct JUMP, JUMPC and JUMPN
      for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
        BasicBlk blk=(BasicBlk)p.elem();
        LirNode node=(LirNode)blk.instrList().last().elem();
        //env.output.println(node);
        switch(node.opCode){
          case Op.JUMP:{
            if(!availBlk.contains(blk)){
              LirLabelRef lRef=(LirLabelRef)node.kid(0);
              //env.output.println(lRef);

              BasicBlk succ=lRef.label.basicBlk();
              if(availBlk.contains(succ)){
                boolean chk=eliminateLabelFromSuccPhi(succ,lRef);
                if(!phiChanged && chk) phiChanged=true;
              }
            }
            break;
          }
          case Op.JUMPC:{
            if(!availBlk.contains(blk)){
              //env.output.println("aaaaaaaaaaaaa REMOVE "+blk.id);
              LirLabelRef lRef=(LirLabelRef)node.kid(1);
              BasicBlk succ=lRef.label.basicBlk();
              if(availBlk.contains(succ)){
                boolean chk=eliminateLabelFromSuccPhi(succ,lRef);
                if(!phiChanged && chk) phiChanged=true;
              }

              lRef=(LirLabelRef)node.kid(2);
              succ=lRef.label.basicBlk();
              if(availBlk.contains(succ)){
                boolean chk=eliminateLabelFromSuccPhi(succ,lRef);
                if(!phiChanged && chk) phiChanged=true;
              }
            }
            else{
              LirNode n=evaluate(node.kid(0));
              if(n!=null){
                long v=((LirIconst)n).value;
                util.makeNewJump(blk,(LirLabelRef)node.kid((int)(2-v)));
              
                // Maint successor's PHI node
                // The edge can be removed.
                LirLabelRef lRef=null;
                switch((int)v){
                  case 0:{ // false
                    lRef=(LirLabelRef)node.kid(1); // true edge
                    break;
                  }
                  default: // true
                    lRef=(LirLabelRef)node.kid(2); // false edge
                }
              
                BasicBlk succ=lRef.label.basicBlk();
                if(availBlk.contains(succ)){
                  boolean chk=eliminateLabelFromSuccPhi(succ,lRef);
                  if(!phiChanged && chk) phiChanged=true;
                }
              }
            }
            break;
          }
          case Op.JUMPN:{
            if(!availBlk.contains(blk)){
              //env.output.println("aaaaaaaaaaaaa REMOVE "+blk.id);
              for(int i=0;i<node.kid(1).nKids();i++){
                LirNode n=(LirNode)node.kid(1).kid(i);
              
                LirLabelRef lRef=(LirLabelRef)n.kid(1);
                BasicBlk succ=lRef.label.basicBlk();
                if(availBlk.contains(succ)){
                  boolean chk=eliminateLabelFromSuccPhi(succ,lRef);
                  if(!phiChanged && chk) phiChanged=true;
                }
              }
              BasicBlk succ=((LirLabelRef)node.kid(2)).label.basicBlk();
              if(availBlk.contains(succ)){
                boolean chk=eliminateLabelFromSuccPhi(succ,
                                                      (LirLabelRef)node.kid(2));
                if(!phiChanged && chk) phiChanged=true;
              }
            }
            else{
              if(node.kid(0).opCode==Op.INTCONST){
                long arg0=((LirIconst)node.kid(0)).value;
                boolean changed=false;
                //env.output.println(arg0);
                for(int i=0;i<node.kid(1).nKids();i++){
                  LirNode n=(LirNode)node.kid(1).kid(i);
                  long arg=((LirIconst)n.kid(0)).value;
                
                  if(arg0==arg && !changed){
                    util.makeNewJump(blk,(LirLabelRef)n.kid(1));
                    changed=true;
                  }
                  else{
                    BasicBlk succ=((LirLabelRef)n.kid(1)).label.basicBlk();
                    if(availBlk.contains(succ)){
                      boolean chk=eliminateLabelFromSuccPhi(succ,
                                                            (LirLabelRef)n.kid(1));
                      if(!phiChanged && chk) phiChanged=true;
                    }
                  }
                }
                // Go to default label
                if(!changed){
                  util.makeNewJump(blk,(LirLabelRef)node.kid(2));
                }
                else{
                  BasicBlk succ=((LirLabelRef)node.kid(2)).label.basicBlk();
                  if(availBlk.contains(succ)){
                    boolean chk=eliminateLabelFromSuccPhi(succ,
                                                          (LirLabelRef)node.kid(2));
                    if(!phiChanged && chk) phiChanged=true;
                  }
                }
              }
            }
          }
        }
      }

      // Eliminate unavailable basic blocks
      for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
        BasicBlk blk=(BasicBlk)p.elem();
        if(!availBlk.contains(blk) &&
           ((LirNode)blk.instrList().last().elem()).opCode!=Op.EPILOGUE){
          // remove the target basic block.
          env.println("CSTP : remove block "+blk.id+"("+blk.label()+")",THR);

          blk.clearEdges();
          blk.clearDummyEdges();
          p.unlink();
          f.flowGraph().touch();

        }
      }
    }
    //f.printIt(env.output);
    env.println("",THR);

    return(true);
  }

  /**
   * Eliminate labels from the PHI instructions.
   * @param succ The basic block which include the PHI instruction
   * @param lRef The label which should be removed
   * @return True if eliminate
   **/
  private boolean eliminateLabelFromSuccPhi(BasicBlk succ,LirLabelRef lRef){
    boolean changed=false;
    for(BiLink p=succ.instrList().first();!p.atEnd();p=p.next()){
      LirNode node=(LirNode)p.elem();
      if(node.opCode==Op.PHI){
        // Copy the arguments except invalid edges
        BiList newPhiParam=new BiList();
        for(int i=1;i<node.nKids();i++){
          if(!lRef.equals(node.kid(i).kid(2))){
            newPhiParam.add(node.kid(i));
          }
        }

        if(newPhiParam.length()+1!=node.nKids()){
          // Make a new PHI instruction which has a new arguments.
          LirNode[] args=new LirNode[newPhiParam.length()+1];
          args[0]=node.kid(0);
          BiLink qq=newPhiParam.first();
          for(int i=1;i<args.length;i++){
            args[i]=(LirNode)qq.elem();
            qq=qq.next();
          }
          // Replace the PHI instruction into a new one.
          LirNode newPhi=env.lir.operator(Op.PHI,node.type,args,
                                          ImList.Empty);
          //env.output.println(newPhi);
          p.addBefore(newPhi);
          p.unlink();
          f.flowGraph().touch();

          changed=true;
        }
      }
      else break;
    }

    return(changed);
  }

  /**
   * Evaluate the PHI instruction.
   * @param phiInst The current PHI instruction
   **/
  private void evalPhiExp(LirNode phiInst){
    // Replace the variables which are constant into the constant nodes.
    simplePropagate(phiInst);

    VariableData data=getVariableData((LirSymRef)phiInst.kid(0));

    // Do nothing if the destination variable is overdefined
    if(!data.overdefine){
      for(int i=1;i<phiInst.nKids();i++){
        LirLabelRef edge=(LirLabelRef)phiInst.kid(i).kid(2);
        // The valid arguments of the current PHI instruction.
        if(availEdge.contains(edge)){
          //env.output.println("AVAILALBE EDGE : "+edge);
          LirNode node=phiInst.kid(i).kid(0);

          // The argument is a register.
          if(node instanceof LirSymRef){
            VariableData arg=getVariableData((LirSymRef)node);
            if(arg.overdefine){
              data.overdefine=true;
              SSAWork.push(((LirSymRef)phiInst.kid(0)).symbol);
              break;
            }
            else if(!arg.undefine){
              if(data.undefine){
                data.value=arg.value;
                data.undefine=false;
                SSAWork.push(((LirSymRef)phiInst.kid(0)).symbol);
              }
              //else if(data.value!=arg.value){
              else if(!data.value.equals(arg.value)){
                data.overdefine=true;
                SSAWork.push(((LirSymRef)phiInst.kid(0)).symbol);
                break;
              }
            }
          }
          // The argument is a integer constant.
          else if(node instanceof LirIconst){
            long value=((LirIconst)node).value;
            LirNode newValue=env.lir.iconst(node.type,value,ImList.Empty);
            if(data.undefine){
              //data.value=new Long(value);
              data.value=newValue;
              data.undefine=false;
              SSAWork.push(((LirSymRef)phiInst.kid(0)).symbol);
            }
            //else if(!data.value.equals(new Long(value))){
            else if(!data.value.equals(newValue)){
              data.overdefine=true;
              SSAWork.push(((LirSymRef)phiInst.kid(0)).symbol);
              break;
            }
          }
          // The argument is a floating constant.
          else if(node instanceof LirFconst){
            double value=((LirFconst)node).value;
            LirNode newValue=env.lir.fconst(node.type,value,ImList.Empty);
            if(data.undefine){
              //data.value=new Double(value);
              data.value=newValue;
              data.undefine=false;
              SSAWork.push(((LirSymRef)phiInst.kid(0)).symbol);
            }
            //else if(!data.value.equals(new Double(value))){
            else if(!data.value.equals(newValue)){
              data.overdefine=true;
              SSAWork.push(((LirSymRef)phiInst.kid(0)).symbol);
              break;
            }
          }
        }
      }
    }
    /*
      if(data.overdefine)
      env.println("CSTP : overdefined <== "+phiInst,THR);
      else if(data.undefine)
      env.println("CSTP : undefined <== "+phiInst,THR);
      else
      env.println("CSTP : "+data.value+" <== "+phiInst,THR);
    */
  }

  /**
   * Evaluate the expression except the PHI instruction.
   * @param exp The current expression
   **/
  private void evalExp(LirNode exp){
    // Replace the variables which are constant into the constant nodes.
    simplePropagate(exp);
    // If the expression has the operation whose operand are all constant,
    // then fold it.
    folding(exp);

    // If the expression is an assign expression and the destination of it
    // is a register.
    if(exp.opCode==Op.SET && exp.kid(0).opCode==Op.REG){
      VariableData data=getVariableData((LirSymRef)exp.kid(0));

      // Do nothing if the destination variable is overdefined
      if(!data.overdefine){
        // If the source value is a constant, then the optimizer makes the data
        // of the destination variable to a constant and put the variable into
        // SSAWork.
        int targetCode=exp.kid(1).opCode;
        if(targetCode==Op.INTCONST){
          data.undefine=false;
          //data.value=new Long(((LirIconst)exp.kid(1)).value);
          data.value=exp.kid(1).makeCopy(env.lir);
          data.canReplace=true;
          SSAWork.push(((LirSymRef)exp.kid(0)).symbol);
        }
        else if(targetCode==Op.FLOATCONST){
          //data.print();
          data.undefine=false;
          //data.value=new Double(((LirFconst)exp.kid(1)).value);
          data.value=exp.kid(1).makeCopy(env.lir);
          data.canReplace=true;
          SSAWork.push(((LirSymRef)exp.kid(0)).symbol);
        }
        else{
          // Set overdefined if the MEM node is in the right hand side.
          boolean ov=setOverdefine(Op.MEM,data,exp);
          // Set overdefined if the CALL node is in the right hand side.
          if(!ov) ov=setOverdefine(Op.CALL,data,exp);
          // Set overdefined if the CLOBBER node is in the right hand side.
          if(!ov) ov=setOverdefine(Op.CLOBBER,data,exp);
          // Set overdefined if the STATIC node is in the right hand side.
          if(!ov) ov=setOverdefine(Op.STATIC,data,exp);
          // Set overdefined if the FRAME node is in the right hand side.
          if(!ov) ov=setOverdefine(Op.FRAME,data,exp);

          if(!ov){
            boolean isUndefine=false;
            // The destination variable is set overdefined when the source
            // value is a result of calculation, and the variables which are
            // used in the caluculation is set undefined.
            for(int i=1;i<exp.nKids();i++){
              BiList list=util.findTargetLir(exp.kid(i),Op.REG,new BiList());
              for(BiLink p=list.first();!p.atEnd();p=p.next()){
                LirSymRef regNode=(LirSymRef)p.elem();
                VariableData temp=getVariableData(regNode);
              
                if(temp.overdefine){
                  data.overdefine=true;
                  SSAWork.push(((LirSymRef)exp.kid(0)).symbol);
                  break;
                }
                if(temp.undefine){
                  // If the undefined variable is in the calculation, then
                  // the source variable keep undefined.
                  isUndefine=true;
                  break;
                }
              }
            }

            if(!isUndefine && !data.overdefine){
              // If it is neither undefined nor overdefined, then
              // calculate the source expression.
              LirNode value=evaluate(exp.kid(1));
              if(value!=null){
                data.value=value;
                data.undefine=false;
                //env.output.println(value+" : "+exp);
              }
              else{
                data.overdefine=true;
              }
            }
          }
        }
      }
    }
    else if(exp.opCode==Op.JUMPC){
      // Get the result of evaluation about TST expression and put the edge
      // related to the result into FlowWork. If the result is null, then 
      // put both edges into FlowWork.
      LirNode tstResult=evaluate(exp.kid(0));
      if(tstResult==null){
        FlowWork.push(exp.kid(1));
        FlowWork.push(exp.kid(2));
      }
      else{
        long v=((LirIconst)tstResult).value;
        FlowWork.push(exp.kid((int)(2-v)));
      }
    }
    else if(exp.opCode==Op.JUMPN){
      //Number value=null;
      LirNode value=null;
      switch(exp.kid(0).opCode){
        case Op.REG:
          VariableData tst=getVariableData((LirSymRef)exp.kid(0));
          if(!tst.undefine && !tst.overdefine){
            value=tst.value;
          }
          break;
        case Op.INTCONST:{
          //value=new Long(((LirIconst)exp.kid(0)).value);
          value=env.lir.iconst(exp.type,((LirIconst)exp.kid(0)).value,
                               ImList.Empty);
          break;
        }
      }

      if(value!=null){
        //long v=value.longValue();
        long v=((LirIconst)value).value;
        boolean isFind=false;
        for(int i=0;i<exp.kid(1).nKids();i++){
          //env.output.println(exp.kid(1).kid(i)+"  "+v);
          long nodeVal=((LirIconst)exp.kid(1).kid(i).kid(0)).value;
          if(v==nodeVal){
            FlowWork.push(exp.kid(1).kid(i).kid(1));
            isFind=true;
            break;
          }
        }
        if(!isFind){
          FlowWork.push(exp.kid(2));
        }
      }
      else{
        for(int i=0;i<exp.kid(1).nKids();i++){
          FlowWork.push(exp.kid(1).kid(i).kid(1));
        }
        FlowWork.push(exp.kid(2));
      }
    }

    //env.output.println(exp);
  }

  /**
   * Evaluate the expression.
   * @param node The current expression
   * @return The result of calculation
   **/
  private LirNode evaluate(LirNode node){
    LirNode value=env.lir.evalTree(node);
    LirNode args[]=new LirNode[node.nKids()];

    for(int i=0;i<node.nKids();i++){
      args[i]=evaluate(node.kid(i));
      if(args[i]==null) return(null);
    }

    switch(node.opCode){
      //public static final int INTCONST = 1;
      //public static final int FLOATCONST = 2;
      case Op.INTCONST:
      case Op.FLOATCONST:{
        value=node.makeCopy(env.lir);
        break;
      }
      //public static final int REG = 5;
      case Op.REG:{
        VariableData data=getVariableData((LirSymRef)node);
        if(!data.undefine && !data.overdefine){
          value=data.value.makeCopy(env.lir);
        }
        break;
      }
      //public static final int NEG = 8;
      //public static final int CONVSX = 16;
      //public static final int CONVZX = 17;
      //public static final int CONVIT = 18;
      //public static final int CONVFX = 19;
      //public static final int CONVFT = 20;
      //public static final int CONVFI = 21;
      //public static final int CONVSF = 22;
      //public static final int CONVUF = 23;
      //public static final int BNOT = 27;
      case Op.NEG:
      case Op.CONVSX:
      case Op.CONVZX:
      case Op.CONVIT:
      case Op.CONVFX:
      case Op.CONVFT:
      case Op.CONVFI:
      case Op.CONVFS:
      case Op.CONVFU:
      case Op.CONVSF:
      case Op.CONVUF:
      case Op.BNOT:{
        if(args[0]!=null){
          value=env.lir.operator(node.opCode,node.type,args[0],ImList.Empty);
          value=env.lir.foldConstant(value);
        }
        break;
      }
      //public static final int DIVS = 12;
      //public static final int DIVU = 13;
      //public static final int MODS = 14;
      //public static final int MODU = 15;
      case Op.DIVS:
      case Op.DIVU:
      case Op.MODS:
      case Op.MODU:{
        if(args[0]!=null && args[1]!=null && args[1].opCode==Op.INTCONST &&
           ((LirIconst)args[1]).value!=0){
          value=env.lir.operator(node.opCode,node.type,args[0],args[1],
                                 ImList.Empty);
          value=env.lir.foldConstant(value);
        }
        break;
      }
      //public static final int ADD = 9;
      //public static final int SUB = 10;
      //public static final int MUL = 11;
      //public static final int BAND = 24;
      //public static final int BOR = 25;
      //public static final int BXOR = 26;
      //public static final int LSHS = 28;
      //public static final int LSHU = 29;
      //public static final int RSHS = 30;
      //public static final int RSHU = 31;
      //public static final int TSTEQ = 32;
      //public static final int TSTNE = 33;
      //public static final int TSTLTS = 34;
      //public static final int TSTLTU = 38;
      //public static final int TSTLES = 35;
      //public static final int TSTLEU = 39;
      //public static final int TSTGTS = 36;
      //public static final int TSTGTU = 40;
      //public static final int TSTGES = 37;
      //public static final int TSTGEU = 41;
      case Op.ADD:
      case Op.SUB:
      case Op.MUL:
      case Op.BAND:
      case Op.BOR:
      case Op.BXOR:
      case Op.LSHS:
      case Op.LSHU:
      case Op.RSHS:
      case Op.RSHU:
      case Op.TSTEQ:
      case Op.TSTNE:
      case Op.TSTLTS:
      case Op.TSTLTU:
      case Op.TSTLES:
      case Op.TSTLEU:
      case Op.TSTGTS:
      case Op.TSTGTU:
      case Op.TSTGES:
      case Op.TSTGEU:{
        if(args[0]!=null && args[1]!=null){
          value=env.lir.operator(node.opCode,node.type,args[0],args[1],
                                 ImList.Empty);
          value=env.lir.foldConstant(value);
        }
        break;
      }
      //public static final int STATIC = 3;
      //public static final int FRAME = 4;
      //public static final int SUBREG = 6;
      //public static final int LABEL = 7;
      //public static final int ASMCONST = 42;
      //public static final int PURE = 43;
      //public static final int MEM = 44;
      //public static final int SET = 45;
      //public static final int JUMP = 46;
      //public static final int JUMPC = 47;
      //public static final int JUMPN = 48;
      //public static final int DEFLABEL = 49;
      //public static final int CALL = 50;
      //public static final int PROLOGUE = 51;
      //public static final int EPILOGUE = 52;
      //public static final int PARALLEL = 53;
      //public static final int USE = 54;
      //public static final int CLOBBER = 55;
      //public static final int PHI = 56;
      //public static final int LIST = 57;
      //public static final int UNDEFINED = 58;
      default: value=null;
    }

    if(value!=null && 
       (value.opCode!=Op.INTCONST && value.opCode!=Op.FLOATCONST))
      value=null;

    return(value);
  }

  /**
   * Set overdefine bit into the data which related to the variable if the
   * expression includes the LIR node which has the specified opCode.
   * @param opCode The specified operator code
   * @param data The data of the variable
   * @param exp The current expression
   * @param If the current expression is set overdefined, return true
   **/
  private boolean setOverdefine(int opCode,VariableData data,LirNode exp){
    for(int i=1;i<exp.nKids();i++){
      BiList list=util.findTargetLir(exp.kid(i),opCode,new BiList());
      if(list.length()>0){
        data.overdefine=true;
        SSAWork.push(((LirSymRef)exp.kid(0)).symbol);
        return(true);
      }
    }
    return(false);
  }

  /**
   * Simple constant propagator. If the current LIR node has the variable
   * which value is constant, then replace the variable into the constant.
   * @param n The current LIR node
   **/
  private void simplePropagate(LirNode n){
    //env.output.println("AAAAAAAAAAAAAA "+n);

    Stack stack=new Stack();
    stack.push(n);

    while(!stack.empty()){
      LirNode node=(LirNode)stack.pop();

      for(int i=0;i<node.nKids();i++){
        if(i==0 && (node.opCode==Op.PHI || node.opCode==Op.SET) && 
           node.kid(i).opCode==Op.REG)
          continue;

        if(node.kid(i).opCode==Op.REG){
          //env.output.println(node+"  :  "+n);
          VariableData data=getVariableData((LirSymRef)node.kid(i));
          //data.print();

          if(!data.undefine && !data.overdefine && data.canReplace){
            //env.output.println("AAAAAAAAAAAAAAAAAAAAAA");
            //if(data.value instanceof Long){
            if(data.value.opCode==Op.INTCONST){
              LirNode cnst=data.value.makeCopy(env.lir);
              //LirNode cnst=env.lir.iconst(node.kid(i).type,
              //                            data.value.longValue(),
              //                            ImList.Empty);
              node.setKid(i,cnst);
            }
            //else if(data.value instanceof Double){
            else if(data.value.opCode==Op.FLOATCONST){
              LirNode cnst=data.value.makeCopy(env.lir);
              //LirNode cnst=env.lir.fconst(node.kid(i).type,
              //                            data.value.doubleValue(),
              //                            ImList.Empty);
              node.setKid(i,cnst);
            }
          }
        }
        else{
          stack.push(node.kid(i));
        }
      }
    }
  }

  /**
   * Simple constant folding on LIR.
   * @param node The current LIR node
   **/
  private void folding(LirNode node){
    // It is impossible to fold the values in the PHI instruction.
    if(node.opCode!=Op.PHI){
      //env.output.println(node);
      env.lir.evalTree(node);
      //env.output.println(" -->  "+node);
    }
  }

  /**
   * Get the data related the LIR node `reg'.
   * @param reg The current LIR node
   * @return The data related `reg'
   **/
  private VariableData getVariableData(LirSymRef reg){
    Symbol s=reg.symbol;
    return(getVariableData(s));
  }

  /**
   * Get the data related the Symbol `s'.
   * @param s The current symbol
   * @return The data related `s'
   **/
  private VariableData getVariableData(Symbol s){
    VariableData data=(VariableData)symbols.get(s);
    if(data==null){
      data=new VariableData(s);
      symbols.put(s,data);
    }
    return(data);
  }

  /**
   * Set the information about the use of the variables into the data of the
   * variables.
   * @param blk The basic block which includes the useNode
   * @param useNode The LIR node which uses a certain variable
   * @param list The list of variables which is in the useNode
   **/
  private void setUse(BasicBlk blk,LirNode useNode,BiList list){
    for(BiLink p=list.first();!p.atEnd();p=p.next()){
      LirSymRef regNode=(LirSymRef)p.elem();
      VariableData data=getVariableData(regNode);

      //data.undefine=false;
      Object[] obj=new Object[2];
      obj[0]=blk;
      obj[1]=useNode;
      data.useList.addNew(obj);
      //data.print();
    }
  }
}
