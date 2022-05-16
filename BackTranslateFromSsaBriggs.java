/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.ana.Dominators;
import coins.backend.ana.LiveVariableAnalysis;
import coins.backend.ana.LiveVariableSlotwise;
import coins.backend.Data;
import coins.backend.LocalTransformer;
import coins.backend.Function;
import coins.backend.Module;
import coins.backend.cfg.FlowGraph;
import coins.backend.cfg.BasicBlk;
import coins.backend.sym.Symbol;
import coins.backend.util.BiList;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirFconst;
import coins.backend.lir.LirIconst;
import coins.backend.lir.LirSymRef;
import coins.backend.lir.LirLabelRef;
import coins.backend.lir.LirUnaOp;
import coins.backend.lir.LirBinOp;
import coins.backend.lir.LirNaryOp;
import coins.backend.lir.LirVisitor;
import coins.backend.Op;

import coins.backend.Storage;

import java.util.Iterator;
import java.util.Hashtable;
import java.util.Stack;
import java.io.PrintWriter;
import java.util.Enumeration;

class BackTranslateFromSsaBriggs implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "BackTranslateFromSsaBriggs"; }
  public String subject() {
    return "Back translation from SSA form using Briggs' method.";
  }

  /** The threshold of debug print **/
  public static final int THR=SsaEnvironment.AllThr;

  /**
     If "extended" is true, do extention extended version.
  **/
  private final boolean extended;

  /**
     The SsaEnvironment.
  **/
  private SsaEnvironment env;

  /**
     The output stream of the compiler.
  **/
  private PrintWriter output;

  /**
     The current function func.
  **/
  private Function func;

  /**
     The symbol table of SSA form.
  **/
  private SsaSymTab ssatab;
    
  public BackTranslateFromSsaBriggs( SsaEnvironment enviroment, SsaSymTab ssasymtab , boolean ex){
    env = enviroment;
    output = env.output;
    ssatab = ssasymtab;
    extended = ex;
    /*
      Print which translation is invoked.
    */
    env.println("  SSA back translation : BRIGGS",env.MsgThr);
  }
    
  public boolean doIt(Function function,ImList args){
    env.println("****************** Back Translate from SSA form to "+
                function.symbol.name,SsaEnvironment.MinThr);

    func = function;
    
    removeDummyCall();    /////

    if(extended){
      checkWeak(func);
    }
    //VCGFileGen.printer(func.flowGraph(),"with_phi_"+func.symbol.name+".vcg");

    replace_phi_nodes(func);

    //VCGFileGen.printer(func.flowGraph(),"no_phi_"+func.symbol.name+".vcg");	

    Util util = new Util(env,func);
    util.changeLabelRef(false);

    func.flowGraph().touch();
    //env.output.println("END BRIGSS");
    //func.flowGraph().printIt(output);

    return(true);
  }

  ////////////////////////////////////////////////
  // title:
  // Practical Improvements to the Construction 
  //   and Destruction of Static Single Assignment Form
  //
  // author:
  // Preston Briggs and Keith D. Cooper and Timothy J. Harvey 
  //   and L. Taylor Simpson
  //
  // journal:
  // Software -- Practice and Experience 1998
  //
  ////////////////////////////////////////////////

  private Hashtable arrayOfStack = new Hashtable();
  private Hashtable used_by_another = new Hashtable();
  private Hashtable map = new Hashtable();

  private Hashtable exmap = new Hashtable();

  // key  : LirNode "dest" which is destination of phi-function.
  // elem : BasicBlk "block" which contains phi-function that define "dest".
  private Hashtable phi_define_dest = new Hashtable();

  // For live range cutting.
  // key  : BasicBlk "block".
  // elem : BiList "copies" which is list of copy1-type copies.
  private Hashtable cut = new Hashtable();

  private BiList registers = new BiList();
  private FlowGraph cfg;
  private Dominators dominators;
  private LiveVariableAnalysis liveness;

  ////////////////////////////////////////////////
  // EPLACE_PHI_NODES()
  ////////////////////////////////////////////////

  private void replace_phi_nodes(Function function){
    func = function;

    //Control flow graph.
    cfg = func.flowGraph();

    //Dominator information.
    dominators = (Dominators)func.require(Dominators.analyzer);
	
    //Liveness analysis.
    liveness = (LiveVariableAnalysis)func.require(LiveVariableSlotwise.analyzer);
	

    ////////////////////////////////////////////////
    // For each variable v
    //     Stacks[v] <-- emptystack()
    ////////////////////////////////////////////////

	
    // Get all variables.
    //setRegisters();
    setRegisters2();
    // Initialize data of Hashtable.
    initializeTables();

    ////////////////////////////////////////////////
    // insert_copies( start )
    ////////////////////////////////////////////////

    //cfg.printIt( output );

    //VCGFileGen.printer(cfg, "ssa.vcg");
	
    insert_copies( cfg.entryBlk() );
    removePhiNodes();

    //VCGFileGen.printer(cfg, "normal.vcg");
    //cfg.printIt( output );
	    
  }
    
  private void insert_copies( BasicBlk block ){

    ////////////////////////////////////////////////
    // pushed <-- null
    ////////////////////////////////////////////////

    BiList pushed = new BiList();

    ////////////////////////////////////////////////
    // For all instructions i in block
    //     Replace all uses u with Stacks[u]
    ////////////////////////////////////////////////

    Iterator regiterator = registers.iterator();
    while( regiterator.hasNext() ){
      LirNode u = (LirNode)regiterator.next();
	    
      if( !(arrayOfStack.containsKey( u ) ) ){
        env.println("error1: insert_copies",THR);
      }

      Stack stack = (Stack)arrayOfStack.get( u );
      if( !( stack.empty() ) ){
        LirNode stacks_u = (LirNode)stack.peek();

        searchReplace( u, stacks_u, block );
      }
    }

    ////////////////////////////////////////////////
    // schedule_copies( block )
    ////////////////////////////////////////////////

    schedule_copies( block, pushed );

    ////////////////////////////////////////////////
    // For each child c of block in the dominator tree
    //     insert_copies( c )
    ////////////////////////////////////////////////

    Iterator childiterator = dominators.children( block );
    while( childiterator.hasNext() ){
      BasicBlk child = (BasicBlk)childiterator.next();
      insert_copies( child );
    }

    pushed.toString();

    ////////////////////////////////////////////////
    // For each name n in pushed
    //     pop( Stack[n] )
    ////////////////////////////////////////////////
	
    stackClean( pushed );
  }
    
  private void schedule_copies(BasicBlk block, BiList pushed){

    LirNode jumpInst = (LirNode)block.instrList().last().elem();

    /**********************************************/
    /** Pass One: Initialize the data structures **/
    /**********************************************/

    ////////////////////////////////////////////////
    // copy_set <-- null
    ////////////////////////////////////////////////

    CoupleSet copy_set = new CoupleSet();
    CoupleSet worklist = new CoupleSet();

    ////////////////////////////////////////////////
    // For all successors s of block
    //     j <-- whichPred( s, block )
    ////////////////////////////////////////////////

    BiList succlist = block.succList();
    Iterator succiterator = succlist.iterator();
    while(succiterator.hasNext()){
      BasicBlk s = (BasicBlk)succiterator.next();

      ////////////////////////////////////////////////	
      //     For each phi-function dest <-- phi(...) in s
      //         src    <-- j_th operand of phi-function
      //         copy_set  <-- copy_set U {< src, dest >}
      //         map[src]  <-- src
      //         map[dest] <-- dest
      //         used_by_another[src] <-- TRUE
      ////////////////////////////////////////////////

      BiList phinodes = getPhiNodes( s );
      Iterator phiiterator = phinodes.iterator();
      while(phiiterator.hasNext()){
        LirNode phinode = (LirNode)phiiterator.next();
        LirNode dest = getPhiDest(phinode);
        LirNode src = getJthOperand( block, phinode );
        Couple couple = new Couple( src, dest );
        copy_set.addNewCouple( couple );
        updateHash( map, src, src );
        updateHash( map, dest, dest );
        updateHash( used_by_another, src, new Boolean(true) );
      }
    }

    /*****************************************************/
    /** Pass Two: Set up the worklist of initial copies **/
    /*****************************************************/

    ////////////////////////////////////////////////
    // For each copy < src, dest> in copy_set
    //     If !used_by_another[dest]
    //        worklist <-- worklist U {< src, dest >}
    //        copy_set <-- copy_set - {< src, dest >}
    ////////////////////////////////////////////////

    // dummy of copy_set for iterate.
    BiList dummy1 = copy_set.getCoupleSet().copy();
    Iterator dumIter1 = dummy1.iterator();

    while( dumIter1.hasNext() ){
      Couple current = (Couple)dumIter1.next();
      LirNode dest = current.getDest();

      if(!used_by_another.containsKey(dest)){
        env.println("error: insert_copies",THR);
      }

      if(!((Boolean)used_by_another.get( dest )).booleanValue()){
        worklist.addNewCouple( current );
        BiLink l = copy_set.removeCouple( current );
        if( l == null ){
          env.println("error2: insert_copies",THR);
        }
      }
    }

    /*************************************************************/
    /** Pass Three: Iterate over the worklist, inserting copies **/
    /*************************************************************/

    ////////////////////////////////////////////////
    // While worklist != null or copy_set != null
    ////////////////////////////////////////////////

    while( ( !worklist.isEmpty() ) || ( !copy_set.isEmpty() ) ){

      ////////////////////////////////////////////////
      //    While worklist != null
      //       Pick a < src, dest > from worklist
      //       worklist <-- worklist - {< src, dest >}
      ////////////////////////////////////////////////

      while( !worklist.isEmpty() ){
        Couple picked = worklist.pickRemove();

        ////////////////////////////////////////////////
        //  If dest in live_out_b
        //     Insert a copy from dest to a new temp t 
        //                    at phi-node defining dest
        //     push( t, Stack[dest] )
        ////////////////////////////////////////////////

        LirSymRef dest = (LirSymRef)picked.getDest();

        Symbol destsym = dest.symbol;
        if(extended){
          if( liveness.isLiveAtExit( destsym, block ) && dest.id != ((LirSymRef)picked.getSrc()).id){
            // make symbol of temp t.
            Symbol tsym = ssatab.newSsaSymbol( destsym );
            // make LirNode of temp t.
            LirSymRef t = (LirSymRef)env.lir.symRef( tsym );
            // map[t] <-- t
            updateHash(map,t,t);
            // make copy from dest to t( note: destination of this copy is t). 
            LirBinOp copy1 = (LirBinOp)env.lir.operator( Op.SET, t.type, t, dest, ImList.Empty);
			
            if( !phi_define_dest.containsKey( (LirNode)dest ) ){
              env.println("error1 : schedule_copies",THR);
            }
			
            BasicBlk defining = (BasicBlk)phi_define_dest.get( (LirNode)dest );
            insertCopyAtHead( defining, copy1 );
            env.println("copy1",THR);
			
            //For live range cutting.
            //((BiList)cut.get( defining )).addFirst(new TempCopy(copy1,block));
			
            pushStack( (LirNode)t, (LirNode)dest, pushed );
          }
        }else{
          if( liveness.isLiveAtExit( destsym, block ) ){
            // make symbol of temp t.
            Symbol tsym = ssatab.newSsaSymbol( destsym );
            // make LirNode of temp t.
            LirSymRef t = (LirSymRef)env.lir.symRef( tsym );
            // map[t] <-- t
            updateHash(map,t,t);
            // make copy from dest to t( note: destination of this copy is t). 
            LirBinOp copy1 = (LirBinOp)env.lir.operator( Op.SET, t.type, t, dest, ImList.Empty);
			
            if( !phi_define_dest.containsKey( (LirNode)dest ) ){
              env.println("error1 : schedule_copies",THR);
            }
			
            BasicBlk defining = (BasicBlk)phi_define_dest.get( (LirNode)dest );
            insertCopyAtHead( defining, copy1 );
            env.println("copy1",THR);
			
            //For live range cutting.
            //((BiList)cut.get( defining )).addFirst(new TempCopy(copy1,block));
			
            pushStack( (LirNode)t, (LirNode)dest, pushed );

            // kohama: for bug.
            if(asUse( (LirNode)dest, jumpInst ) ){
              replaceNode((LirNode)dest,(LirNode)t, jumpInst );
              cfg.touch();
            }

            // kohama: for bug.
          }else if(asUse((LirNode)dest, jumpInst)){
            // make symbol of temp t.
            Symbol tsym = ssatab.newSsaSymbol( destsym );
            // make LirNode of temp t.
            LirSymRef t = (LirSymRef)env.lir.symRef( tsym );
            // map[t] <-- t
            updateHash(map,t,t);
            // make copy from dest to t( note: destination of this copy is t). 
            LirBinOp copy4 = (LirBinOp)env.lir.operator( Op.SET, t.type, t, dest, ImList.Empty);
			
            if( !phi_define_dest.containsKey( (LirNode)dest ) ){
              env.println("error1 : schedule_copies",THR);
            }
			
            BasicBlk defining = (BasicBlk)phi_define_dest.get( (LirNode)dest );
            insertCopyAtHead( defining, copy4 );
            env.println("copy4",THR);
            replaceNode((LirNode)dest,(LirNode)t, jumpInst );
            cfg.touch();
          }
        }

	////////////////////////////////////////////////
	//       Insert a copy operation from map[ src ] to dest
	//                                at the end of b
	//       map[ src ] <-- dest
	////////////////////////////////////////////////

        LirNode src = picked.getSrc();

        if( !map.containsKey ( src ) ){
          env.println( "error2 : schedule_copies",THR);
        }

        // modified by FUKUOKA Takeaki (2004.8.30)		    
        //LirSymRef map_src = (LirSymRef)map.get( src );
        LirNode map_src=(LirNode)map.get(src);


        //make copy from map[src] to dest.
        LirBinOp copy2 = (LirBinOp)env.lir.operator( Op.SET, map_src.type, dest, map_src, ImList.Empty);
        insertCopyAtTail( block, copy2 );
        //env.println("copy2",THR);

        updateHash( map, src, dest );
        updateHash(exmap, src, dest);

	////////////////////////////////////////////////
	//       If src is the name of a destination in copy_set
	//          Add that copy to worklist
	////////////////////////////////////////////////

        BiList dummy2 = copy_set.getCoupleSet();
        Iterator dumIterator2 = dummy2.iterator();
		
        while( dumIterator2.hasNext() ){
          Couple current = (Couple)dumIterator2.next();
          LirNode destination = current.getDest();
		    
          if( src.equals( destination ) ){
            BiLink l = copy_set.removeCouple( current );
            if( l == null ){
              env.println("error2: schedule_copies",THR);
            }
            Couple couple = (Couple)l.elem();
            worklist.addNewCouple( couple );
          }
        }
      }

      ////////////////////////////////////////////////
      //    If copy_set != null
      //       Pick a < src, dest > from copy_set
      //       copy_set <-- copy_set - {< src, dest >}
      ////////////////////////////////////////////////

      if( !copy_set.isEmpty() ){
        Couple current = copy_set.pickRemove();

	////////////////////////////////////////////////
	//       Insert a copy from dest to a new temp t at the end of b
	////////////////////////////////////////////////

        LirSymRef dest = (LirSymRef)current.getDest();
        Symbol destsym = dest.symbol;
        // make symbol of temp t.
        Symbol tsym = ssatab.newSsaSymbol( destsym );
        // make LirNode of temp t.
        LirSymRef t = (LirSymRef)env.lir.symRef( tsym );
        // map[t] <-- t //for jump repair
        updateHash(map,t,t);
        updateHash(exmap,t,t);
        // make copy from dest to t( note: destination of this copy is t).
        LirBinOp copy3 = (LirBinOp)env.lir.operator( Op.SET, t.type, t, dest, ImList.Empty);
        insertCopyAtTail( block, copy3 );
        //env.println("copy3",THR);

	////////////////////////////////////////////////
	//       map[ dest ] <-- t
	//       worklist <-- worklist U {< src, dest >}
	////////////////////////////////////////////////
		
        updateHash( map, dest, t );
        updateHash(exmap,dest,t);
        worklist.addNewCouple( current );
      }
    }

    //For jump Repair.
    if(extended){
      //if(false){
      //if(true){
      jumpRepair(block);
    }
    exmap.clear();

  }


  /**
     Set BiList registers.
  **/
  private void setRegisters2(){
    PickingRegister visitor = new PickingRegister();
    Iterator blockiterator = cfg.basicBlkIterator();
    while( blockiterator.hasNext() ){
      BasicBlk block = (BasicBlk)blockiterator.next();
      Iterator nodelistiterator = block.instrList().iterator();
	    
      while( nodelistiterator.hasNext() ){
        LirNode node = (LirNode)nodelistiterator.next();
        walkPreorder( visitor , node );
      }
    }
    registers = visitor.getRegisterlist();
  }
    
  /**
     initialize as bellow for each variable.
     1. Stacks[v]  <-- emptystack()
     2. used_by_another[v] <-- false
     3. phi_define_dest[destination of phi] <-- block which contains the phi.
  **/
  private void initializeTables(){
    Iterator regiterator = registers.iterator();
    while( regiterator.hasNext() ){
      LirNode node = (LirNode)regiterator.next();

      // 1.
      arrayOfStack.put( node, new Stack() );
      // 2.
      used_by_another.put( node, new Boolean(false) );
    }

    Iterator blockiterator = cfg.basicBlkIterator();
    while( blockiterator.hasNext() ){
      BasicBlk block = (BasicBlk)blockiterator.next();

      //For live range cutting.
      cut.put( block, new BiList() );

      Iterator instriterator = block.instrList().iterator();
      while( instriterator.hasNext() ){
        LirNode instr = (LirNode)instriterator.next();

        if( instr.opCode == Op.PHI ){
          LirNode dest = getPhiDest( instr );
          // 3.
          phi_define_dest.put( dest, block );
        }
      }
    }
  }

  /**
     search "old" in "block" and it replaces with "node".
  **/
  private void searchReplace(LirNode old, LirNode node, BasicBlk block){
    Iterator nodeIterator = block.instrList().iterator();
    ReplaceVisitor visitor = new ReplaceVisitor(old, new Hashtable());
    while(nodeIterator.hasNext()){
      LirNode current = (LirNode)nodeIterator.next();
      walkPreorder( visitor, current );
    }
	
    Hashtable children = visitor.children;
    Enumeration e = children.keys();
    while( e.hasMoreElements() ){
      LirNode current = (LirNode)e.nextElement();
      BiList srclist = (BiList)children.get( current );
	    
      Iterator srciterator = srclist.iterator();
      while(srciterator.hasNext()){
        int i = ((Integer)srciterator.next()).intValue();
        current.setKid( i, node );
        cfg.touch();
      }
    }
  }
    

  /**
     return "list" of phi-nodes in "block".
  **/
  BiList getPhiNodes(BasicBlk block){
    BiList phinodes = new BiList();
	
    Iterator instriterator = block.instrList().iterator();
    while(instriterator.hasNext()){
      LirNode current = (LirNode)instriterator.next();
      if(current.opCode == Op.PHI){
        phinodes.addNew(current);
      }
    }
	
    return phinodes;
  }

  /**
     retun "dest" of "phinode".
  **/
  LirNode getPhiDest(LirNode phinode){
    if( !(phinode.opCode == Op.PHI) ){
      env.println(" error1: getPhiDest",THR);
    }

    if( !isReg(phinode.kid(0)) ) env.println("error2: getPhiDest",THR);

    return phinode.kid(0);
  }


  /**
     return J-th operand (corresponding to "block") 
     from "phinode".
  **/
  LirNode getJthOperand(BasicBlk block, LirNode phinode){
    if( !(phinode.opCode == Op.PHI) ){
      env.println(" error1: getJthOperand",THR);
    }
	
    for(int i = 0; i < phinode.nKids(); i++){
      if(i == 0){
        if(!isReg(phinode.kid(i))) env.println("error2: getJthOperand",THR);
        continue;//This param is destination.
      }
	    
      LirNode param = phinode.kid(i);

      LirNode labelnode = param.kid(1);
      if (!(labelnode instanceof LirLabelRef)) 
        env.println("error4: getJthOperand",THR);
	    
      if(((LirLabelRef)labelnode).label.basicBlk() == block){
        if( !isReg( param.kid(0) ) ){
          env.println("error5: getJthOperand",THR);
          env.println( param.kid(0).toString(),THR);
        }
        return param.kid(0);
      }
    }

    env.println("error6: getJthOperand",THR);
    env.println(phinode.toString(),THR);
    env.println(block.label().toString(),THR);
    return null;
  }

  /**
     retun true if "node" is register.
     retun false if "node" is not register.
  **/
  boolean isReg(LirNode node){
    if (node.opCode == Op.REG
        || node.opCode == Op.SUBREG && node.kid(0).opCode == Op.REG){
      return true;
    }
    return false;
  }

  /**
     Update "elem" of "hashtable" at "key".
  **/
  void updateHash( Hashtable hashtable, Object key, Object elem ){
    if( !hashtable.containsKey( key ) ){
      hashtable.put( key, elem );
    }else{
      hashtable.remove( key );
      hashtable.put( key, elem );	    
    }
  }

  /**
     Insert "node" at block'head.
     If there are some phi-functions, "node" is inserted behind thoes.
  **/
  void insertCopyAtHead( BasicBlk block, LirNode node ){
    BiList instrlist = block.instrList();

    for( BiLink l = instrlist.first(); !l.atEnd(); l = l.next() ){
      LirNode instr = (LirNode)l.elem();

      if( instr.opCode == Op.PHI ) continue;

      l.addBefore( node );
      break;
    }

    //if block is empty, print out error.
    if( instrlist.isEmpty() ){
      env.println("error1 : insertHead",THR);
    }

    //if block has only phi functions, print out error.
    if( instrlist.length() == getPhiNodes( block ).length() 
        && instrlist.length() != 0 ){
      env.println("error2 : insertHead",THR);
    }
    cfg.touch();
  }

  void insertCopyAtTail( BasicBlk block, LirNode node ){
    BiList instrlist = block.instrList();
    if( instrlist.isEmpty() ){
      env.println("error1 : insertAtTail",THR);
    }
	
    BiLink tail = instrlist.last();
    LirNode instr = (LirNode)tail.elem();
	
    if( instr.opCode != Op.JUMP &&
        instr.opCode != Op.JUMPC &&
        instr.opCode != Op.JUMPN ){
      env.println("error2 : insertAtTail",THR);
      env.println( instr.toString(),THR);
    }

    tail.addBefore( node );
	
    cfg.touch();
  }

  /**
     Push temp on stack[dest],
     and add dest in pushed.
  **/
  private void pushStack( LirNode temp, LirNode dest, BiList pushed){
    if( !arrayOfStack.containsKey( dest )){
      env.println("error1: pushStack",THR);
    }
    Stack stack = (Stack)arrayOfStack.get( dest );
    stack.push( temp );
    pushed.addNew( dest );
  }

  /**
     Pop the stack[elem],
     and clear pushed.
  **/
  private void stackClean( BiList pushed ){
    Iterator pushediterator = pushed.iterator();
    while( pushediterator.hasNext() ){
      LirNode elem = (LirNode)pushediterator.next();

      if( !arrayOfStack.containsKey( elem )){
        env.println("error1: stackClean",THR);
      }

      Stack stack = (Stack)arrayOfStack.get(elem);

      if( !stack.empty() ){
        LirNode on_stack = (LirNode)stack.pop();
      }else{
        env.println("error2: stackClean",THR);
      }
    }

    pushed.clear();

  }

  void removePhiNodes(){
    Iterator blockiterator = cfg.basicBlkIterator();
    while( blockiterator.hasNext() ){
      BasicBlk block = (BasicBlk)blockiterator.next();

      BiList instrlist = block.instrList();
      BiList dummy =instrlist.copy();

      Iterator dumIter = dummy.iterator();
      while( dumIter.hasNext() ){
        LirNode instr = (LirNode)dumIter.next();

        if( instr.opCode == Op.PHI){
          BiLink l = instrlist.remove( instr );
		    
          if( l == null ){
            env.println("error1: removePhiNodes",THR);
          }
        }
      }
    }
  }

  // Check weak case, and change the case.
  void checkWeak(Function func){

    cfg = func.flowGraph();

    for(BiLink p=cfg.basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        liveness = (LiveVariableAnalysis)func.require(LiveVariableSlotwise.analyzer);
        LirNode node=(LirNode)q.elem();
        if(node.opCode==Op.PHI){
          if(isNeedCopy(node,blk)){
            phiNodeModify(node,blk);
            cfg.touch();
            continue;
          }
        }
      }
    }
  }

  // if dest is liveout at pred, return true.
  boolean isNeedCopy(LirNode node,BasicBlk block){
    if(!(node.opCode==Op.PHI)){
      env.println("error: isNeedCopy",THR);
    }

    Symbol destsym = ((LirSymRef)node.kid(0)).symbol;
    Iterator pIter = block.predList().iterator();
    while(pIter.hasNext()){
      BasicBlk pred = (BasicBlk)pIter.next();
      if(liveness.isLiveAtExit(destsym,pred)){
        return true;
      }
    }
    return false;
  }

  // Modify phinode to "temp=phi(...)" and make copy "temp=dest" and insert the copy.
  void phiNodeModify(LirNode node, BasicBlk block){
    LirSymRef dest = (LirSymRef)node.kid(0);

    Symbol destsym = dest.symbol;
    // make symbol of temp t.
    Symbol tsym = ssatab.newSsaSymbol( destsym );
    // make LirNode of temp t.
    LirSymRef t = (LirSymRef)env.lir.symRef( tsym );
    // make copy "dest=t"
    LirBinOp copy = (LirBinOp)env.lir.operator( Op.SET, t.type, dest, t, ImList.Empty);

    node.setKid(0,(LirNode)t);
    insertCopyAtHead(block,(LirNode)copy);
    System.out.println("copy5");
  }


  // target is list of LirNode.
  void printList(BiList target){
    Iterator tIter = target.iterator();
    while(tIter.hasNext()){
      LirNode t = (LirNode)tIter.next();
      env.println(t.toString(),THR);
    }
  }

  void travel(BasicBlk block, LirNode dest, BiList candidates){
    //--
    env.println("trabel at --- " + block.id,THR);
    env.println("candidates:",THR);
    printList(candidates);

    boolean transp = false;//if src is changed, return true.
    Iterator insIter = block.instrList().iterator();
    while(insIter.hasNext()){
      env.println("",THR);

      LirNode instr = (LirNode)insIter.next();

      //--
      env.println("For " + instr.toString(),THR);

      //--
      env.println("before --",THR);
      printList(candidates);
      //--

      if(isCopy(instr)){

        //--
        env.println("invoke cuttingCopy()",THR);

        BiList templist = candidates.copy();
        Iterator temIter = templist.iterator();
        while(temIter.hasNext()){
          LirNode current = (LirNode)temIter.next();
          LirNode source = cuttingCopy(current,dest,instr);
          if(source != null){
            if(source.id != current.id){
			    
              //--
              env.println("candidates++ " + source.toString(),THR);
			    
              candidates.add(source);
              break;
            }else{
			    
              //++
              BiLink q = candidates.removeEqual(instr.kid(0));
              //++
            }
          }
        }
      }else{
        Iterator canIter = candidates.iterator();
        while(canIter.hasNext()){
          LirNode current = (LirNode)canIter.next();
          cutting(current, dest, instr);
        }
        //++
        BiList templist = candidates.copy();
        Iterator temIter = templist.iterator();
        while(temIter.hasNext()){
          LirNode temp = (LirNode)temIter.next();
          if(asDest(temp,instr)){
            BiLink p = candidates.removeEqual(temp);
		    
            if(p == null){
              env.println("error3: liveRangeCutting",THR);
            }
          }
        }
        //++
      }

      //--
      env.println("after --",THR);
      printList(candidates);
      //--

      if(candidates.isEmpty()){
        transp = true;
        break;
      }
    }
    if(!transp){
      if(candidates.isEmpty()){
        env.println("error4: liveRangeCutting",THR);
      }

      Iterator childIter = dominators.children(block);
      while(childIter.hasNext()){

        BasicBlk child = (BasicBlk)childIter.next();
        BiList templist = candidates.copy();
        if(inSucc(block,child)){
          travel(child,dest,templist);
        }
      }
    }
  }

  // If node is copy-instruction, return true.
  boolean isCopy(LirNode node){
    if(node.opCode == Op.SET
       && node.kid(0).opCode == Op.REG
       && node.kid(1).opCode == Op.REG){
      return true;
    }
    return false;
  }

  // If child is in block's successor, return true.
  boolean inSucc(BasicBlk block, BasicBlk child){
    Iterator sucIter = block.succList().iterator();
    while(sucIter.hasNext()){
      BasicBlk succ = (BasicBlk)sucIter.next();
      if(succ.id == child.id){
        return true;
      }
    }
    return false;
  }

  // replace node1 to node2, in instr.
  void replaceNode(LirNode node1, LirNode node2, LirNode instr){
    switch(instr.opCode){
      case Op.SET:
        for(int i = 1; i < instr.nKids(); i++){
          if(instr.kid(i).opCode == Op.REG){
            if(instr.kid(i).id == node1.id){
              instr.setKid(i,node2);
            }
          }
        }
        break;

      case Op.CALL:
        for(int i = 0; i < instr.kid(1).nKids(); i++){
          if(instr.kid(1).kid(i).opCode == Op.REG){
            if(node1.id == instr.kid(1).kid(i).id){
              instr.kid(1).setKid(i,node2);
            }
          }
        }
        break;

      default:
        for(int i = 0; i < instr.nKids(); i++){
          if(instr.kid(i).opCode == Op.REG){
            if(instr.kid(i).id == node1.id){
              instr.setKid(i,node2);
            }
          }else{
            replaceNode(node1, node2, instr.kid(i));
          }
        }
        break;
    }
  }

  // If node is use at instr, return true.
  boolean asUse(LirNode node, LirNode instr){
    switch(instr.opCode){
      case Op.SET:
        for(int i = 1; i < instr.nKids(); i++){
          if(instr.kid(i).opCode == Op.REG){
            if(instr.kid(i).id == node.id){
              return true;
            }
          }
        }
        break;

      case Op.CALL:
        for(int i = 0; i < instr.kid(1).nKids(); i++){
          if(instr.kid(1).kid(i).opCode == Op.REG){
            if(node.id == instr.kid(1).kid(i).id){
              return true;
            }
          }
        }
        break;

      default:
        for(int i = 0; i < instr.nKids(); i++){
          if(instr.kid(i).opCode == Op.REG){
            if(instr.kid(i).id == node.id){
              return true;
            }
          }else{
            if(asUse(node,instr.kid(i))){
              return true;
            }
          }
        }
        break;
    }
    return false;
  }

  // If src is defined at instr, return true.
  boolean asDest(LirNode src, LirNode instr){
    switch( instr.opCode ){

      case Op.SET:
        if( instr.kid(0).opCode == Op.REG ){
          //if(src.equals(instr.kid(0))){
          if(src.id == instr.kid(0).id){
            return true;
          }
        }
        break;
	    
      case Op.CALL:
        for(int i = 0; i < instr.kid(2).nKids(); i++){
          if(instr.kid(2).kid(i).opCode == Op.REG){
            if(src.id == instr.kid(2).kid(i).id){
              return true;
            }
          }
        }
        break;

      default: break;
    }

    return false;
  }
    
  // If src is use in instr, replace src to dest.
  void cutting(LirNode src, LirNode dest, LirNode instr){
    switch( instr.opCode ){
      case Op.SET:
        for(int i = 1; i < instr.nKids(); i++){
          if(instr.kid(i).opCode == Op.REG){
            //if(instr.kid(i).equals(src)){
            if(instr.kid(i).id == src.id){
              //System.out.println("reach hear");
              instr.setKid(i,dest);
              cfg.touch();
            }
          }else{
            cutting(src,dest,instr.kid(i));
          }
        }
        break;

      case Op.CALL:
        for(int i = 0; i < instr.kid(1).nKids(); i++){
          if(instr.kid(1).kid(i).opCode == Op.REG){
            if(src.id == instr.kid(1).kid(i).id){
              instr.kid(1).setKid(i,dest);
              cfg.touch();
            }
          }
        }
        break;
	    
      default:
        for(int i = 0; i < instr.nKids(); i++){
          if(instr.kid(i).opCode == Op.REG){
            //if(instr.kid(i).equals(src)){
            if(instr.kid(i).id == src.id){
              instr.setKid(i,dest);
              cfg.touch();
            }
          }else{
            cutting(src,dest,instr.kid(i));
          }
        }
        break;
    }
  }

  // If src is use in copy, replace src to dest and return destination of copy.
  // Else, return null.
  LirNode cuttingCopy(LirNode src, LirNode dest, LirNode copy){
    if(!isCopy(copy)){
      env.println("error1: cuttingCopy",THR);
    }
    LirNode destination = copy.kid(0);
    LirNode source = copy.kid(1);

    if(src.id == source.id){
      copy.setKid(1,dest);
      cfg.touch();
      return destination;
    }

    return null;
  }
  //####
  // For Live Range Cutting -- END
  //###

  //###
  // For Jump Repair -- START
  //###
    
  void jumpRepair(BasicBlk block){
    LirNode instr = (LirNode)block.instrList().last().elem();

    if( instr.opCode == Op.JUMPC ||
        instr.opCode == Op.JUMPN ){
      repair(instr,block);
    }
  }

  void repair(LirNode instr, BasicBlk block){
    for(int i = 0; i < instr.nKids(); i++){
      switch( instr.kid(i).opCode ){
        case Op.REG:
          if(!(instr.kid(i) instanceof LirSymRef)){
            env.println("error1: repair",THR);
          }
          LirSymRef s1 = (LirSymRef)instr.kid(i);
          if(exmap.containsKey(s1)){
            LirSymRef s2 = (LirSymRef)exmap.get(s1);
            if(!( s1.equals(s2) )){
              if((LirNode)exmap.get(s1) == null){
                env.println("error2: repair",THR);
              }
              //if(!isLiveAtSuccEntry(s1.symbol,block)){//change
              if(true){
                instr.setKid(i,(LirNode)s2);
                cfg.touch();
              }
            }
          }
          break;

        default:
          repair(instr.kid(i),block);
          break;
      }
    }
  }

  // If s is liveAtEntry at any succ, return true.
  boolean isLiveAtSuccEntry(Symbol s, BasicBlk block){
    Iterator sIter = block.succList().iterator();
    while(sIter.hasNext()){
      BasicBlk succ = (BasicBlk)sIter.next();
      if(liveness.isLiveAtEntry(s,succ)){
        return true;
      }
    }
    return false;
  }

  //###
  // For Jump Repair -- END
  //###

  //###
  // For remove useless copy -- START
  //###

  boolean removeUselessCopy(){

    Iterator bIter = cfg.basicBlkIterator();
    while(bIter.hasNext()){
      BiList rmlist = new BiList();
      liveness = (LiveVariableAnalysis)func.require(LiveVariableSlotwise.analyzer);
      BasicBlk block = (BasicBlk)bIter.next();

      //env.println("Trace at " + block.id,THR);
      //env.println("Live Out +++",THR);
      Iterator oiter = liveness.liveOut(block).iterator();
      while(oiter.hasNext()){
        Symbol s = (Symbol)oiter.next();
        //env.println(s.name,THR);
      }
      //env.println("+++",THR);


      Iterator iIter = block.instrList().iterator();
      while(iIter.hasNext()){
        LirNode instr = (LirNode)iIter.next();
        //env.print("rmlist - ",THR);
        //env.println(instr.toString(),THR);
        //printList(rmlist);
        //env.println("",THR);

        if(isCopy(instr)){
          LirSymRef dest = (LirSymRef)instr.kid(0);
          if(!(liveness.isLiveAtExit(dest.symbol,block))){
            //env.println("add rmlist " + dest.toString(),THR);
            rmlist.addNew(instr);
          }
        }
		
        for(BiLink q=rmlist.first(); !q.atEnd(); q=q.next()){
          LirNode rm = (LirNode)q.elem();
          if(asUse(rm.kid(0),instr)){
            //env.println("rem rmlist " + rm.toString(),THR);
            q.unlink();
          }
        }
		
        /*		
          BiList temp = rmlist.copy();
          Iterator temIter = temp.iterator();
          while(temIter.hasNext()){
          LirNode current = (LirNode)temIter.next();
          LirNode d = current.kid(0);
          LirNode s = current.kid(1);
          if(asUse(d,instr)){
          for(BiLink q=rmlist.first(); !q.atEnd(); q=q.next()){
          LirNode rm = (LirNode)q.elem();
          if(d.id == rm.kid(0).id && s.id == rm.kid(1).id){
          q.unlink();
          break;
          }
          }
          }
          }
        */
        //--
      }

      Iterator rmIter = rmlist.iterator();
      while(rmIter.hasNext()){
        LirNode rm = (LirNode)rmIter.next();
        //env.println("Trace2",THR);
        for(BiLink q=block.instrList().first(); !q.atEnd(); q=q.next()){
          LirNode instr = (LirNode)q.elem();
          //env.println("=== " + instr.toString(),THR);
          if(isCopy(instr)){
            if(rm.kid(0).id == instr.kid(0).id &&
               rm.kid(1).id == instr.kid(1).id ){
              //if(rm.kid(0).equals(instr.kid(0)) &&
              //   rm.kid(1).equals(instr.kid(0))){

              q.unlink();
              cfg.touch();

              return true;
            }
          }
        }
      }
    }
    return false;
  }

  // temp method. If cfg is canonicalize, this may not use.
  boolean removeUselessCopyBEFORE(){

    Iterator bIter = cfg.basicBlkIterator();
    while(bIter.hasNext()){
      BiList rmlist = new BiList();
      liveness = (LiveVariableAnalysis)func.require(LiveVariableSlotwise.analyzer);
      BasicBlk block = (BasicBlk)bIter.next();

      env.println("Trace at " + block.id,THR);
      env.println("Live Out +++",THR);
      Iterator oiter = liveness.liveOut(block).iterator();
      while(oiter.hasNext()){
        Symbol s = (Symbol)oiter.next();
        env.println(s.name,THR);
      }
      env.println("+++",THR);


      Iterator iIter = block.instrList().iterator();
      while(iIter.hasNext()){
        LirNode instr = (LirNode)iIter.next();
        env.print("rmlist - ",THR);
        env.println(instr.toString(),THR);
        printList(rmlist);
        env.println("",THR);

        if(isCopy(instr)){
          LirSymRef dest = (LirSymRef)instr.kid(0);
          if(!(liveness.isLiveAtExit(dest.symbol,block))){
            env.println("add rmlist " + dest.toString(),THR);
            rmlist.addNew(instr);
          }
        }
		
        for(BiLink q=rmlist.first(); !q.atEnd(); q=q.next()){
          LirNode rm = (LirNode)q.elem();
          if(asUse(rm.kid(0),instr)){
            env.println("rem rmlist " + rm.toString(),THR);
            q.unlink();
          }
        }

      }

      // check about cut.
      if(true){
        Iterator rmIter = rmlist.iterator();
        while(rmIter.hasNext()){
          LirBinOp rm = (LirBinOp)rmIter.next();
          BiList c = (BiList)cut.get(block);
          for(BiLink q=c.first(); !q.atEnd();q=q.next()){
            LirBinOp current = (LirBinOp)q.elem();
            if(rm.equals(current)){
              env.println("kohama",THR);
              q.unlink();
            }
          }
        }
      }

      Iterator rmIter = rmlist.iterator();
      while(rmIter.hasNext()){
        LirNode rm = (LirNode)rmIter.next();
        env.println("Trace2",THR);
        for(BiLink q=block.instrList().first(); !q.atEnd(); q=q.next()){
          LirNode instr = (LirNode)q.elem();
          env.println("=== " + instr.toString(),THR);
          if(isCopy(instr)){
            if(rm.kid(0).id == instr.kid(0).id &&
               rm.kid(1).id == instr.kid(1).id ){
              //if(rm.kid(0).equals(instr.kid(0)) &&
              //   rm.kid(1).equals(instr.kid(0))){

              q.unlink();
              cfg.touch();

              return true;
            }
          }
        }
      }
    }
    return false;
  }

  //###
  // For remove Unuseless copy -- END
  //###

  void walkPreorder( LirVisitor v, LirNode node ){
    node.accept( v );
    int n = node.nKids();
    for ( int i = 0; i < n; i++ ){
      walkPreorder( v, node.kid(i) );
    }
  }

  class ReplaceVisitor implements LirVisitor{
    public LirNode old;
    public Hashtable children;

    public ReplaceVisitor(LirNode node, Hashtable table){
      old = node;
      children = table;
    }

    public void visit(LirFconst node){
      // Do nothing , becouse it has no child of register.
    }
    public void visit(LirIconst node){
      // Do nothing , becouse it has no child of register.
    }
    public void visit(LirSymRef node){
      // Do nothing , becouse it has no child of register.
    }
    public void visit(LirLabelRef node){
      // Do nothing , becouse it has no child of register.
    }
    public void visit(LirUnaOp node){
      for ( int i = 0; i < node.nKids(); i++){
        LirNode child = node.kid(i);
	    
        if ( old.equals( child ) ){

          if ( !children.containsKey(node) ){
            BiList numbers = new BiList();
            numbers.addNew(new Integer(i));
            children.put(node, numbers);
          } else {
            BiList numbers = (BiList)children.get(node);
            numbers.addNew(new Integer(i));
          }
        }
      }
    }
    public void visit(LirBinOp node){
      for ( int i = 0; i < node.nKids(); i++){
        LirNode child = node.kid(i);
	    
        if ( old.equals( child ) ){

          if ( !children.containsKey(node) ){
            BiList numbers = new BiList();
            numbers.addNew(new Integer(i));
            children.put(node, numbers);
          } else {
            BiList numbers = (BiList)children.get(node);
            numbers.addNew(new Integer(i));
          }
        }
      }
    }
    public void visit(LirNaryOp node){
      for ( int i = 0; i < node.nKids(); i++){
        LirNode child = node.kid(i);
	    
        if ( old.equals( child ) ){

          if ( !children.containsKey(node) ){
            BiList numbers = new BiList();
            numbers.addNew(new Integer(i));
            children.put(node, numbers);
          } else {
            BiList numbers = (BiList)children.get(node);
            numbers.addNew(new Integer(i));
          }
        }
      }
    }
  }

  class PickingRegister implements LirVisitor{
    private BiList reglist = new BiList();

    public BiList getRegisterlist(){
      return reglist;
    }
    public void visit(LirFconst node){
    }
    public void visit(LirIconst node){
    }
    public void visit(LirSymRef node){
      if (node.opCode == Op.REG
          || node.opCode == Op.SUBREG && node.kid(0).opCode == Op.REG){
        reglist.addNew(node);
      }
    }
    public void visit(LirLabelRef node){
    }
    public void visit(LirUnaOp node){
    }
    public void visit(LirBinOp node){
    }
    public void visit(LirNaryOp node){
    }
  }

  class Couple{
    private LirNode src;
    private LirNode dest;
    
    public Couple(LirNode src, LirNode dest){
      this.src = src;
      this.dest = dest;
    }
    
    public LirNode getSrc(){
      return src;
    }

    public LirNode getDest(){
      return dest;
    }
  }

  class CoupleSet{
    private BiList couplelist;
    
    public CoupleSet(){
      couplelist = new BiList();
    }

    public BiList getCoupleSet(){
      return couplelist;
    }

    public void addNewCouple(Couple couple){
      couplelist.addNew(couple);
    }

    /*
      Remove couple from Couple,
      and return l.
      If Couple has not the couple,
      return null.
    */
    public BiLink removeCouple(Couple couple){
      BiLink l = couplelist.remove(couple);
      return l;
    }

    public Couple pickRemove(){
      // this need to check couplelist is not empty.
      BiLink picked = couplelist.first();
      picked.unlink();
      return (Couple)picked.elem();
    }
    
    public boolean isEmpty(){
      return couplelist.isEmpty();
    }

    public Iterator iterator(){
      return couplelist.iterator();
    }

    
  }
  private void removeDummyCall(){    /////
	  BiLink first = func.flowGraph().basicBlkList.first();
	  BasicBlk firstBlk = (BasicBlk)first.elem();
	  for(BiLink q=firstBlk.instrList().first();!q.atEnd();q=q.next()){
		  LirNode node=(LirNode)q.elem();
		  if(node.opCode == Op.CALL){
			  LirNode calledFunc = node.kid(0);
			  if(calledFunc instanceof LirSymRef && 
					  ((LirSymRef)calledFunc).symbol.name==ssatab.DUMMY_FUNC){
				  q.unlink();
				  func.touch();
			  }
		  }
	  }
	  func.module.globalSymtab.remove(ssatab.DUMMY_FUNC);
  }
}
