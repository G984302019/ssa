/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.util.ImList;
import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.ana.DFST;
import coins.backend.cfg.BasicBlk;
import coins.backend.util.BiLink;
import coins.backend.util.BiList;
import coins.backend.lir.LirNode;
import coins.backend.Op;
import coins.backend.Type;

import java.util.Hashtable;

/**
 * Global Reassociation.<br>
 * The technique to address the code shape probrems.
 * Originaly, global reassociation has 3 steps, but this module
 * has only 2 steps becouse of keeping SSA form.
 * (Forward Propagation is excluded)<br><br>
 * Refer:<br><br>
 * Preston Briggs and Keith D. Cooper,
 * "Effective Partial Redundancy Elimination,"
 * ACM PLDI, pp. 159-170, June 1994.
 **/
class GlobalReassociation implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "GlobalReassociation"; }
  public String subject() {
    return "Global Reassociation for the expressions.";
  }

  /**
   * Private data for global reassociation.
   **/
  class SortData{
    /** The rank of the data **/
    final int rank;
    /** The operator code of the data **/
    final int opCode;
    /** The type of the data **/
    final int type;
    /** The list of operations **/
    final BiList list;

    /**
     * Constructor
     * @param r The rank of the data
     * @param c The operator code of the data
     * @param t The type of the data
     **/
    SortData(int r,int c,int t){
      rank=r;
      opCode=c;
      type=t;
      list=new BiList();
    }

    /**
     * Constructor
     * @param r The rank of the data
     * @param c The operator code of the data
     * @param t The type of the data
     * @param node The initial node of the data
     **/
    SortData(int r,int c,int t,LirNode node){
      rank=r;
      opCode=c;
      type=t;
      list=new BiList();
      list.add(node);
    }

    /**
     * Generate LIR node from the current data
     * @return The generated LIR node
     **/
    LirNode makeLirNode(){
      LirNode result=null;

      for(BiLink p=list.first();!p.atEnd();p=p.next()){
        Object obj=p.elem();
        if(obj instanceof SortData){
          LirNode node=((SortData)obj).makeLirNode();
          p.setElem(node);
        }
      }

      switch(opCode){
        // Unary Operators
        case Op.MEM:
        case Op.CONVSX:
        case Op.CONVZX:
        case Op.CONVIT:
        case Op.CONVFX:
        case Op.CONVFT:
        case Op.CONVFI:
        case Op.CONVFU:
        case Op.CONVFS:
        case Op.CONVSF:
        case Op.CONVUF:
        case Op.NEG:
        case Op.BNOT:{
          if(list.length()!=1){
            System.err.println("ERROR 1");
            System.exit(1);
          }
          LirNode elem=(LirNode)list.first().elem();
          result=env.lir.operator(opCode,type,elem.makeCopy(env.lir),
                                  ImList.Empty);
          break;
        }
        // Special Binary Operators
        case Op.BAND:
        case Op.BOR:
        case Op.BXOR:
        case Op.MUL:
        case Op.ADD:{
          LirNode[] elem=new LirNode[list.length()];
          int i=0;
          for(BiLink p=list.first();!p.atEnd();p=p.next()){
            elem[i++]=(LirNode)p.elem();
          }
          result=env.lir.operator(opCode,type,
                                  elem[0].makeCopy(env.lir),
                                  elem[1].makeCopy(env.lir),
                                  ImList.Empty);
          for(i=2;i<elem.length;i++){
            result=env.lir.operator(opCode,type,result,
                                    elem[i].makeCopy(env.lir),
                                    ImList.Empty);
          }
          break;
        }
        // Ordinary Binary Operators
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
        case Op.LSHS:
        case Op.LSHU:
        case Op.RSHS:
        case Op.RSHU:
        case Op.SUB:
        case Op.DIVS:
        case Op.DIVU:
        case Op.MODS:
        case Op.MODU:{
          if(list.length()!=2){
            System.err.println("ERROR 2");
            System.exit(1);
          }
          LirNode[] elem=new LirNode[2];
          int i=0;
          for(BiLink p=list.first();!p.atEnd();p=p.next()){
            elem[i++]=(LirNode)p.elem();
          }
          result=env.lir.operator(opCode,type,
                                  elem[0].makeCopy(env.lir),
                                  elem[1].makeCopy(env.lir),
                                  ImList.Empty);
          break;
        }
        // Leaf Nodes
        case Op.REG:
        case Op.LABEL:
        case Op.FRAME:
        case Op.STATIC:
        case Op.INTCONST:
        case Op.FLOATCONST:{
          result=((LirNode)list.first().elem()).makeCopy(env.lir);
          break;
        }
        // List Operator
        case Op.LIST:{
//          env.output.println(this);
          LirNode[] elem=new LirNode[list.length()];
          int i=0;
          for(BiLink p=list.first();!p.atEnd();p=p.next()){
            elem[i]=(LirNode)p.elem();
//            env.output.println(Op.toName(elem[i].opCode));
            i++;
          }
          result=env.lir.operator(opCode,type,elem,ImList.Empty);
          
          break;
        }
        // Doesn't treat here
        case Op.PROLOGUE:
        case Op.EPILOGUE:
        case Op.CALL:
        case Op.PHI:
        case Op.JUMPC:
        case Op.JUMPN:
        case Op.JUMP:{
          break;
        }
      }

      return(result);
    }

    /**
     * Make String to show the current data.
     * @return The String to show the current data
     **/
    public String toString(){
      String result="[";
      result=result+Op.toName(opCode)+",{";

      for(BiLink p=list.first();!p.atEnd();p=p.next()){
        Object obj=p.elem();
        result=result+obj.toString();
      }
      result=result+"},("+rank+")] ";
      return(result);
    }
  }


  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.OptThr;
  /** The map between the LIR node and the rank **/
  private Hashtable rankMap;
  /** The current function **/
  private Function f;
  /** Utility **/
  private Util util;

  /**
   * Constructor
   * @param e The environment of the SSA module
   **/
  public GlobalReassociation(SsaEnvironment e){
    env=e;
    env.println("  Global Reassociation for the expressions",
                SsaEnvironment.MsgThr);
  }

  /**
   * Do global reassociation.
   * @param function The current function
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    env.println("****************** doing GRA to "+function.symbol.name,
                SsaEnvironment.MinThr);
    f=function;
    util=new Util(env,f);
    rankMap=new Hashtable();

    computeRank();
    sortExpression();

    return(true);
  }

  /**
   * Compute the rank for each LIR node in the current function.
   **/
  private void computeRank(){
    DFST dfst=(DFST)f.require(DFST.analyzer);
    BasicBlk[] blks=dfst.blkVectorByRPost();
    for(int blkRank=1;blkRank<blks.length;blkRank++){
      for(BiLink p=blks[blkRank].instrList().first();!p.atEnd();p=p.next()){
        LirNode node=(LirNode)p.elem();
        switch(node.opCode){
          case Op.SET:{
            if(node.kid(0).opCode==Op.REG){
              BiList list=util.findTargetLir(node.kid(1),Op.MEM,new BiList());
              int rank=0;
              if(list.length()>0) rank=blkRank;

              list=util.findTargetLir(node.kid(1),Op.REG,new BiList());
              
              for(BiLink q=list.first();!q.atEnd();q=q.next()){
                LirNode n=(LirNode)q.elem();
                Integer i=(Integer)rankMap.get(n);
                if(i!=null && i.intValue()>rank) rank=i.intValue();
              }
                
              LirNode reg=node.kid(0);
              rankMap.put(reg,new Integer(rank));
              env.println("GRA : "+reg+" --> rank["+rank+"]",THR);
            }
            break;
          }
          case Op.PROLOGUE:{
            BiList list=util.findTargetLir(node,Op.REG,new BiList());
            for(BiLink q=list.first();!q.atEnd();q=q.next()){
              LirNode reg=(LirNode)q.elem();
              rankMap.put(reg,new Integer(blkRank));
              env.println("GRA : "+reg+" --> rank["+blkRank+"]",THR);
            }
            break;
          }
          case Op.PHI:{
            LirNode reg=node.kid(0);
            rankMap.put(reg,new Integer(blkRank));
            env.println("GRA : "+reg+" --> rank["+blkRank+"]",THR);
            break;
          }
          case Op.CALL:{
            if(node.kid(2).nKids()>0 && node.kid(2).kid(0).opCode==Op.REG){
              LirNode reg=node.kid(2).kid(0);
              rankMap.put(reg,new Integer(blkRank));
              env.println("GRA : "+reg+" --> rank["+blkRank+"]",THR);
            }
            break;
          }
        }
      }
    }
  }

  /**
   * Sort the LIR node in the current function.
   * There are 2 kind of sorting.
   * (1) Sorting by rank.
   * (2) Sorting by alphabetic.
   **/
  private void sortExpression(){
    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();

      boolean again=true;
      while(again){
        again=false;
        // rewrite expressions
        for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
          LirNode node=(LirNode)q.elem();
          rewriteExp(null,node,-1);
        }
        
        // sort
        for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
          LirNode node=(LirNode)q.elem();
          env.lir.evalTree(node);
          
          switch(node.opCode){
            case Op.SET:
            case Op.CALL:{
              for(int i=0;i<node.nKids();i++){
                SortData data=getInfo(node.kid(i));
                
                // sort by using rank
                sortByRank(data);
                // sort by alphabetic
                sortByAlphabetic(data);
                
                node.setKid(i,data.makeLirNode());
                f.touch();
              }
              break;
            }
            case Op.JUMPC:
            case Op.JUMPN:{
              SortData data=getInfo(node.kid(0));
              
              // sort by using rank
              sortByRank(data);
              // sort by alphabetic
              sortByAlphabetic(data);
              
              node.setKid(0,data.makeLirNode());
              f.touch();
              break;
            }
          }
        }
        // distribution
        for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
          LirNode node=(LirNode)q.elem();
          String cmp=node.toString();
          LirNode reconst=distribute(node);
          if(!cmp.equals(reconst.toString())){
            q.setElem(reconst);
            again=true;
          }
        }
        f.touch();
      }
    }
//    f.printIt(env.output);
  }

  /**
   * Distribute multiplication over addition.
   * @param node The current LIR node
   * @return LIR node after distribution
   **/
  private LirNode distribute(LirNode node){
    if(Type.tag(node.type)!=Type.INT) return(node);

    LirNode result=node;
    if((node.opCode==Op.MUL) &&
       (node.kid(0).opCode==Op.ADD || node.kid(1).opCode==Op.ADD)){
      SortData data0=getInfo(node.kid(0));
      SortData data1=getInfo(node.kid(1));

      if((data0.rank>data1.rank) && node.kid(0).opCode==Op.ADD){
        env.println("GRA : distribute "+node,THR);
        LirNode kid0=node.makeCopy(env.lir);
        LirNode kid1=node.makeCopy(env.lir);

        kid0.setKid(0,node.kid(0).kid(0).makeCopy(env.lir));
        kid1.setKid(0,node.kid(0).kid(1).makeCopy(env.lir));

        result=env.lir.operator(node.kid(0).opCode,node.kid(0).type,
                                kid0.makeCopy(env.lir),
                                kid1.makeCopy(env.lir),
                                ImList.Empty);
        env.println("GRA : ---> "+result,THR);
      }
      else if((data0.rank<data1.rank) && node.kid(1).opCode==Op.ADD){
        env.println("GRA : distribute "+node,THR);
        LirNode kid0=node.makeCopy(env.lir);
        LirNode kid1=node.makeCopy(env.lir);

        kid0.setKid(1,node.kid(1).kid(0).makeCopy(env.lir));
        kid1.setKid(1,node.kid(1).kid(1).makeCopy(env.lir));

        result=env.lir.operator(node.kid(1).opCode,node.kid(1).type,
                                kid0.makeCopy(env.lir),
                                kid1.makeCopy(env.lir),
                                ImList.Empty);
        env.println("GRA : ---> "+result,THR);
      }
    }

    for(int i=0;i<result.nKids();i++){
      result.setKid(i,distribute(result.kid(i)));
    }

    return(result);
  }

  /**
   * Sorting by using rank.
   * @param data The current data
   **/
  private void sortByRank(SortData data){
    switch(data.opCode){
      case Op.ADD:
      case Op.MUL:
      case Op.BAND:
      case Op.BOR:
      case Op.BXOR:{
//        env.output.println(data);
        BiList sorted=new BiList();
        SortData min=null;

        // recursive call
        for(BiLink p=data.list.first();!p.atEnd();p=p.next()){
          Object obj=p.elem();
          if(obj instanceof SortData)
            sortByRank((SortData)obj);
        }

        if(Type.tag(data.type)!=Type.INT) return;

        // find minimum rank
        for(BiLink p=data.list.first();!p.atEnd();p=p.next()){
          SortData sd=(SortData)p.elem();
          sortByRank(sd);
          if(min==null) min=sd;
          else if(min.rank>sd.rank) min=sd;
        }
        sorted.add(min);

        // sorting
        for(BiLink p=data.list.first();!p.atEnd();p=p.next()){
          SortData sd=(SortData)p.elem();
          if(min!=sd){
            boolean ins=false;
            for(BiLink q=sorted.first();!q.atEnd();q=q.next()){
              SortData target=(SortData)q.elem();
              if(target.rank>sd.rank){
                q.addBefore(sd);
                ins=true;
                break;
              }
            }
            if(!ins) sorted.add(sd);
          }
        }

        // copy the data
        data.list.clear();
        for(BiLink p=sorted.first();!p.atEnd();p=p.next()){
          data.list.add(p.elem());
        }

        break;
//        env.output.println(data);
      }
      default:{
        for(BiLink p=data.list.first();!p.atEnd();p=p.next()){
          Object obj=p.elem();
          if(obj instanceof SortData) sortByRank((SortData)obj);
        }
      }
    }
  }

  /**
   * Sorting alphabetic.
   * @param data The current data
   **/
  private void sortByAlphabetic(SortData data){
    switch(data.opCode){
      case Op.ADD:
      case Op.MUL:
      case Op.BAND:
      case Op.BOR:
      case Op.BXOR:{
//        env.output.println(data);
        BiList sorted=new BiList();
        BiList subList=new BiList();

        // recursive call
        for(BiLink p=data.list.first();!p.atEnd();p=p.next()){
          Object obj=p.elem();
          if(obj instanceof SortData)
            sortByAlphabetic((SortData)obj);
        }
        
        if(Type.tag(data.type)!=Type.INT) return;

        int currentRank=-1;
        for(BiLink p=data.list.first();!p.atEnd();p=p.next()){
          SortData sd=(SortData)p.elem();

          if(sd.rank==currentRank) subList.add(sd);
          else{
            sortSubList(subList,sorted);

            subList=new BiList();
            subList.add(sd);
            currentRank=sd.rank;
          }
        }
        sortSubList(subList,sorted);

        // copy the data
        data.list.clear();
        for(BiLink p=sorted.first();!p.atEnd();p=p.next()){
          data.list.add(p.elem());
        }

//        env.output.println(data);
        break;
      }
      default:{
        for(BiLink p=data.list.first();!p.atEnd();p=p.next()){
          Object obj=p.elem();
          if(obj instanceof SortData) sortByAlphabetic((SortData)obj);
        }
      }
    }    
  }

  /**
   * Sort the list in the current data.
   * @param subList The sub list in the current data
   * @param sorted The list which contains the sorted sub lists
   **/
  private void sortSubList(BiList subList,BiList sorted){
    // find minimum
    SortData min=null;
    for(BiLink p=subList.first();!p.atEnd();p=p.next()){
      SortData sd=(SortData)p.elem();
      if(min==null) min=sd;
      else if(min.toString().compareTo(sd.toString())<0) min=sd;
    }
    if(min==null) return;

    sorted.add(min);

    // sorting
    for(BiLink p=subList.first();!p.atEnd();p=p.next()){
      SortData sd=(SortData)p.elem();
      if(min!=sd){
        boolean ins=false;
        for(BiLink q=sorted.first();!q.atEnd();q=q.next()){
          SortData target=(SortData)q.elem();
          if(target.rank==sd.rank &&
             target.toString().compareTo(sd.toString())>0){
            q.addBefore(sd);
            ins=true;
            break;
          }
        }
        if(!ins) sorted.add(sd);
      }
    }
  }

  /**
   * Get the data corresponded to the current LIR node.
   * @param root The current LIR node
   * @return The current data
   **/
  private SortData getInfo(LirNode root){
    if(root.nKids()==0){
      Integer integer=(Integer)rankMap.get(root);
      int rank=Integer.MAX_VALUE;
      if(integer!=null) rank=integer.intValue();
      else{
        switch(root.opCode){
          case Op.LIST:{
            return(new SortData(rank,root.opCode,root.type));
          }
          case Op.INTCONST:
          case Op.FLOATCONST:
          case Op.FRAME:
          case Op.STATIC: rank=0;
        }
      }
      return(new SortData(rank,root.opCode,root.type,root));
    }
    else{
      SortData[] children=new SortData[root.nKids()];
      for(int i=0;i<root.nKids();i++){
        children[i]=getInfo(root.kid(i));
//        env.output.println(children[i]);
      }

      int maxRank=-1;
      for(int i=0;i<children.length;i++){
        if(children[i].rank>maxRank) maxRank=children[i].rank;
      }
      SortData data=new SortData(maxRank,root.opCode,root.type);
      
      switch(root.opCode){
        case Op.ADD:
        case Op.MUL:
        case Op.BAND:
        case Op.BOR:
        case Op.BXOR:{
          for(int i=0;i<children.length;i++){
            if(root.opCode==children[i].opCode){
              for(BiLink p=children[i].list.first();!p.atEnd();p=p.next()){
                data.list.add(p.elem());
              }
            }
            else{
              data.list.add(children[i]);
            }
          }

          return(data);
        }
        default:{
          for(int i=0;i<children.length;i++){
            data.list.add(children[i]);
          }

          return(data);
        }
      }
    }
  }

  /**
   * Rewrite subtraction to addition for more oppotunities of the 
   * reassociation.
   * @param parent The parent LIR node of the current node
   * @param node The current LIR node
   * @param place The place of the current node in the parent node
   **/
  private void rewriteExp(LirNode parent,LirNode node,int place){
    for(int i=0;i<node.nKids();i++)
      rewriteExp(node,node.kid(i),i);

    switch(node.opCode){
      case Op.SUB:{
        LirNode neg=env.lir.operator(Op.NEG,node.kid(1).type,
                                     node.kid(1).makeCopy(env.lir),
                                     ImList.Empty);
        LirNode add=env.lir.operator(Op.ADD,node.type,
                                     node.kid(0).makeCopy(env.lir),
                                     neg,ImList.Empty);
        parent.setKid(place,add);
        f.touch();
        break;
      }
    }
  }
}
