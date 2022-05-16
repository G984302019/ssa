/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import java.io.File;

import coins.IoRoot;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Module;
import coins.backend.Op;
import coins.backend.ana.LiveVariableAnalysis;
import coins.backend.ana.LiveVariableSlotwise;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.opt.If2Jumpc;
import coins.backend.opt.JumpOpt;
import coins.backend.util.BiLink;
import coins.backend.util.BiList;
import coins.backend.util.ImList;
import coins.driver.CompileSpecification;

/**
 * The SSA Optimization.
 **/
public class SsaDriver implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "SsaDriver"; }
  public String subject() {
    return "SSA optimizations";
  }

  /** The symbol table of the SSA module **/
  private SsaSymTab sstab;
  /** The environment of the SSA module **/
  private final SsaEnvironment env;
  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.MsgThr;
  /** The suffix of the file name for LIR to C **/
  private int suffix;
  /** The current function **/
  private Function f;
  /** The counter of SSA options **/
  private int optNum;

  // Begin(2010.3.2)
  /** The flag is true if SSA_OPT contains "num" **/
  private boolean lineNumbering;
  // End(2010.3.2)

  // Begin(2010.3.1)
  /** LirNumbering instance **/
  private LirNumbering lirnum;
  // End(2010.3.1)
  
  // Begin(2010.3.31)
  /** The int size of the counter int CountingInstructionsOfBB (bytes) **/
  private int size=8;
  // End(2010.3.31)
  
  /**
   * Constructor
   * @param m The current module
   * @param io IoRoot 
   * @param coinsSpec The compiler driver's specification
  **/
  public SsaDriver(Module m,IoRoot io,CompileSpecification coinsSpec){
    env=new SsaEnvironment(m,coinsSpec,io);

    // Do JUMP opt
    m.apply(JumpOpt.trig);

    // Begin(2010.3.25)
    (new CountingInstructionsOfBB(env,0,size)).chkProfOpt(m, coinsSpec, io, env);
    //CountingInstructionsOfBB cntbb=new CountingInstructionsOfBB(env,0,size);
    //cntbb.chkProfOpt(m, coinsSpec, io, env);
    // End(2010.3.25)
  }

  /**
   * Invoke the SSA Optimization.
   * @param function The current function
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    // Initialize the ssa option counter
    optNum=0;

    if(!isNoParallelAndSubreg(function)) return(true);

    env.println("Optimization on SSA form",1);

    f=function;
    // Initialize the suffix of the lir2c code
    suffix=1;

    // Get the current time
    long start=0;
    if(env.shouldDo(THR)){
      start=System.currentTimeMillis();
    }
    
    // Initialize all register symbols
    sstab=new SsaSymTab(env,f);

    // eliminate IF node
    f.apply(If2Jumpc.trig);
        
    BiList opt=decodeOptions();

    // Begin(2010.3.2)
    // If SSA_OPT contains "num", do numbering at first.
    // Later insert LirNodes of (LINE number) at insertLineNum().
    if(lineNumbering) {
    	lirnum=new LirNumbering(f);
    	lirnum.numbering();
    }
    // End(2010.3.2)

    for(BiLink p=opt.first();!p.atEnd();p=p.next()){
      long s=0;
      if(env.shouldDo(SsaEnvironment.MinThr)){
        s=System.currentTimeMillis();
      }
      f.apply((LocalTransformer)p.elem());
      if(env.shouldDo(SsaEnvironment.MinThr)){
        long e=System.currentTimeMillis();
        long t=e-s;
        env.println("-------  "+t+"[ms]\n",SsaEnvironment.MinThr);
      }
    }

    // Begin(2010.2.25)
    if(lineNumbering){
    	lirnum.insertLineNum();
    }
    // End(2010.2.25)
    // for debug 2010.3.1
    //PrintBasicBlocks pbb=new PrintBasicBlocks(env, sstab);
    //pbb.doIt(f, ImList.Empty);
    //
    
    // Get the current time
    if(env.shouldDo(THR)){
      long end=System.currentTimeMillis();
      long t=end-start;
      env.println("[ Total Time of SSA : "+t+"ms ]",THR);
    }

    if(env.opt.isSet(OptionName.SSA_DEBUG))
      checkLir();

    return(true);
  }

  /**
   * Check whether the live in variables into the entry basic block of the
   * current CFG are nothing.
   * THIS IS THE DEBUG METHOD.
   **/
  private void checkLir(){
    env.output.print("SSA DBG : checking live-in "+f.symbol.name+" ... ");
    LiveVariableAnalysis liveAna;
    liveAna=(LiveVariableAnalysis)f.apply(LiveVariableSlotwise.analyzer);

    BiList liveIn=liveAna.liveIn(f.flowGraph().entryBlk());
    if(liveIn.length()>0){
      env.output.print("fail --> ");
      for(BiLink p=liveIn.first();!p.atEnd();p=p.next()){
        env.output.print(p.elem()+" ");
      }
      env.output.println();
      env.output.println("SSA DBG : Some variables LiveIn at the entrance!");
      //f.printIt(env.output);
    }
    else env.output.println("ok");
  }

  /**
   * Decode the options specified in the COINS compiler driver.
   * @return The list of the name of the optimizers
   **/
  private BiList decodeOptions(){
    final int delimiter='/';
    BiList optionString=new BiList();

    int beginIndex=0;
    int endIndex=0;

    String options=env.opt.getArg(OptionName.SSA_OPT);
    int length=options.length();
    while(endIndex<=length){
      beginIndex=endIndex;
      endIndex=options.indexOf(delimiter,beginIndex);
      if(endIndex==-1)
        endIndex=length;

      if(endIndex>beginIndex){
        String opt=options.substring(beginIndex,endIndex);
        opt=opt.trim();
        optionString.add(opt);
      }
      endIndex++;
    }

    // Begin(2010.3.2)
    BiLink blink=optionString.locateEqual(OptionName.NUMBERING);
    if(blink==null) {
    	// for debug 2010.3.4
    	//System.out.println("optionString doesn't have num");
    	//
    	lineNumbering=false;
    }
    else {
    	//System.out.println("optionString has num");
    	lineNumbering=true;
    }
    if(lineNumbering) 	optionString.removeEqual(OptionName.NUMBERING);
    // End(2010.3.2)

    boolean isOk=syntaxCheck(optionString);
    if(!isOk){
      System.err.println("WARNING : illegal syntax in the SSA option.");
      return(new BiList());
    }

    isOk=checkMultipleOccurrences(optionString);
    if(!isOk) {
    	System.err.println("WARNING : cnt/cntbb has multiple occurrences.");
    	return(new BiList());
    }

    env.println("------------",THR);
    env.println("agenda",THR);
    env.println("------------",THR);

    BiList optimizers=new BiList();
    // change loop structure
    if(!env.opt.isSet(OptionName.SSA_NO_CHANGE_LOOP)){
      optimizers.add(new ChangeLoopStructure(env));
    }
    for(BiLink p=optionString.first();!p.atEnd();p=p.next()){
      String name=(String)p.elem();
      LocalTransformer lt=lookUpOptimizer(name);
      if(lt!=null){
        if(name.equals(OptionName.CSEQP) || name.equals(OptionName.PREQP)){
          optimizers.add(new EdgeSplit(env));
          optimizers.add(new DivideExpression(env,sstab));
	  optNum++;
	  optNum++;
        }
        optimizers.add(lt);
	optNum++;
        if(!env.opt.isSet(OptionName.SSA_NO_PHI_ELIMINATE) &&
           (name.equals(OptionName.MINI) ||
            name.equals(OptionName.SEMI) ||
            name.equals(OptionName.PRUN))){
          optimizers.add(new RedundantPhiElimination(env));
	  optNum++;
        }
      }
    }
    if(env.opt.isSet(OptionName.SSA_WITH_CHAITIN_COALESCING)){
      optimizers.add(new Coalescing(env));
      optNum++;
    }

    env.println("------------\n",THR);

    return(optimizers);
  }

  /**
   * Make the object of the optimizer which is specified in the COINS
   * compiler driver.
   * @param name The name of the optimizer
   * @return The object of the optimizer
   **/
  private LocalTransformer lookUpOptimizer(String name){
    LocalTransformer lt=null;
    if(name.equals(OptionName.MINI)){ // minimal
      boolean folding=!env.opt.isSet(OptionName.SSA_NO_COPY_FOLDING);
      lt=new TranslateToSsa(env,sstab,TranslateToSsa.MINIMAL,folding);
    }
    else if(name.equals(OptionName.SEMI)){ // semi-pruned
      boolean folding=!env.opt.isSet(OptionName.SSA_NO_COPY_FOLDING);
      lt=new TranslateToSsa(env,sstab,TranslateToSsa.SEMI_PRUNED,folding);
    }
    else if(name.equals(OptionName.PRUN)){ // pruned
      boolean folding=!env.opt.isSet(OptionName.SSA_NO_COPY_FOLDING);
      lt=new TranslateToSsa(env,sstab,TranslateToSsa.PRUNED,folding);
    }
    else if(name.equals(OptionName.SRD1)){ // method I
      boolean coalesce=!env.opt.isSet(OptionName.SSA_NO_SREEDHAR_COALESCING);
      boolean aggregate=!env.opt.isSet(OptionName.SSA_NO_REPLACE_BY_EXP);
      lt=new BackTranslateFromSsa(env,sstab,BackTranslateFromSsa.METHOD_I,
                                  coalesce,aggregate);
    }
    else if(name.equals(OptionName.SRD2)){ // method II
      boolean coalesce=!env.opt.isSet(OptionName.SSA_NO_SREEDHAR_COALESCING);
      boolean aggregate=!env.opt.isSet(OptionName.SSA_NO_REPLACE_BY_EXP);
      lt=new BackTranslateFromSsa(env,sstab,BackTranslateFromSsa.METHOD_II,
                                  coalesce,aggregate);
    }
    else if(name.equals(OptionName.SRD3)){ // method III
      boolean coalesce=!env.opt.isSet(OptionName.SSA_NO_SREEDHAR_COALESCING);
      boolean aggregate=!env.opt.isSet(OptionName.SSA_NO_REPLACE_BY_EXP);
      lt=new BackTranslateFromSsa(env,sstab,BackTranslateFromSsa.METHOD_III,
                                  coalesce,aggregate);
    }
    else if(name.equals(OptionName.BRIG)){ // Briggs
      //boolean extend=!env.opt.isSet(OptionName.SSA_NO_SREEDHAR_COALESCING);
      boolean extend=false;
      lt=new BackTranslateFromSsaBriggs(env,sstab,extend);
    }
    else if(name.equals(OptionName.CPYP)){ // copy propagation
      lt=new CopyPropagation(env);
    }
    else if(name.equals(OptionName.CSTP)){ // constant propagation
      lt=new ConstantPropagation(env);
    }
    else if(name.equals(OptionName.DCE)){ // dead code elimination
      lt=new DeadCodeElimination(env);
    }
    else if(name.equals(OptionName.CSE)){ // common subexpression elimination
      lt=new CommonSubexpressionElimination(env);
    }
    else if(name.equals(OptionName.CSEQP)){ // efficient question propagation
      lt=new PREQP(env,sstab,7);
    }
    else if(name.equals(OptionName.PREQP)){ // efficient question propagation
      lt=new PREQP(env,sstab,0);
    }
    else if(name.equals(OptionName.RPE)){ // redundant phi elimination
      lt=new RedundantPhiElimination(env);
    }
    else if(name.equals(OptionName.ESPLT)){ // edge split
      lt=new EdgeSplit(env);
    }
    else if(name.equals(OptionName.HLI)){ // hoisting loop invariant variables
      lt=new HoistingLoopInvariant(env,sstab);
    }
    else if(name.equals(OptionName.DUMP)){ // dump the current module
      lt=new Dump(env);
    }
    else if(name.equals(OptionName.LIR2C)){ // make C source from LIR
      lt=new LirToC(env,makeCName());
    }
    else if(name.equals(OptionName.EBE)){ // empty block elimination
      lt=new EmptyBlockElimination(env);
    }
    else if(name.equals(OptionName.OSR)){ // operator strength reduction
      lt=new SsaGraph(env,sstab,name);
    }
    else if(name.equals(OptionName.SSAG)){ // make ssa graph only
      lt=new SsaGraph(env,sstab,name);     // it is for debug
    }
    else if(name.equals(OptionName.DIVEX)){ // divide expressions
      lt=new DivideExpression(env,sstab);
    }
    else if(name.equals(OptionName.CBB)){ // concatenate basic blocks
      lt=new ConcatBlks(env);
    }
    else if(name.equals(OptionName.GRA)){ // global reassociation
      lt=new GlobalReassociation(env);
    }
    else if(name.equals(OptionName.LCM)) { // lazy code motion on SSA form
      lt=new LCM(env,sstab);
      LCM lcm=(LCM)lt;
      lcm.setOptNum(optNum);
    }
    else if(name.equals(OptionName.DIVEX2)) {
      lt=new DivideExpression2(env, sstab);
    }
    else if(name.equals(OptionName.PDEQP)) {
      lt=new PDEQP(env,sstab);
    }
  // ******************** Begin 2012.3
    else if(name.equals(OptionName.DDPDE)) {
      lt=new DDPDE(env,sstab);
    }
    else if(name.equals(OptionName.CS)) {
      lt=new CS(env,sstab);
    }
    else if(name.equals(OptionName.DC)) {
      lt=new DCE(env,sstab);
    }
    else if(name.equals(OptionName.EXPDE)) {
      lt=new ExhaustivePDE(env,sstab);
    }
    else if(name.equals(OptionName.GLIA)){ // global load instrument aggregation
    	lt=new GLIA(env,sstab);
    }
  // ******************** End
    else if(name.equals(OptionName.LDPRE)){ // global load instrument aggregation
    	lt=new LDPRE(env,sstab);
    }
    else if(name.equals(OptionName.GSA)){ // global load instrument aggregation
    	lt=new GSA(env,sstab);
    }
    else if(name.equals(OptionName.CNT)) {
    	lt=new CountingInstructions(env, sstab, 0, 4);
    }
    else if(name.equals(OptionName.CNTBB)) {
    	lt=new CountingInstructionsOfBB(env, sstab, 0, size);
    }
    else if(name.equals(OptionName.PBB)) { // print basic blocks
    	lt=new PrintBasicBlocks(env, sstab);
    }
    else if(name.equals(OptionName.EQP)) {// Effective Demand-driven Partial Redundancy Elimination
	lt=new EQP(env,sstab,0);
    }
    else if(name.equals(OptionName.PRESR)) {// Scalar Replacement Based on Partial Redundancy Elimination
      lt=new PRESR(env,sstab);
    }
    else if(name.equals(OptionName.DIVEX3)) {
      lt=new DivideExpression3(env, sstab);
    }
    else if(name.equals(OptionName.SET_LINE_NUM)) {
    	lt=new LirNumbering(f,LirNumbering.SET_LINE_NUMBER);
    }
    else if(name.equals(OptionName.INS_LINE_NUM)) {
    	lt=new LirNumbering(f,LirNumbering.INSERT_LINE_NUMBER);
    }
    else if(name.equals(OptionName.REMOVE_LINE_NUM)) {
    	lt=new LirNumbering(f,LirNumbering.REMOVE_LINE_NUMBER);
    }
    else if(name.equals(OptionName.SHOW_LINE_NUM)) {
    	lt=new LirNumbering(f,LirNumbering.SHOW_LINE_NUMBER);
    }
    else if(name.equals(OptionName.CLEAR_LINE_NUM)) {
    	lt=new LirNumbering(f,LirNumbering.CLEAR_LINE_NUMBER);
    }
   else{
      System.err.println("SsaDriver.java : unexpected optimizer name "+name);
    }
    return(lt);
  }

  /**
   * Make a file name for LIR to C.
   **/
  private String makeCName(){
    File source = env.ioRoot.getSourceFile();
    String sourcePath = source.getName();
    String root = sourcePath.substring(0, sourcePath.lastIndexOf('.'));
    String dest = root.concat("-"+f.symbol.name+"-" +suffix+ ".lir2c");
    suffix++;

    return(dest);
  }

  /**
   * Check the syntax of the options which are specified in the COINS 
   * compiler driver. Return true if the syntax of the option correct.
   * @param optionString The list of options
   * @return True if the syntax of the option correct
   **/
  private boolean syntaxCheck(BiList optionString){
    boolean isOK=true;
    boolean onSSA=false;

    for(BiLink p=optionString.first();!p.atEnd();p=p.next()){
      String name=(String)p.elem();
      if(onSSA){ // in SSA form
        if(name.equals(OptionName.SRD1) || // method I
           name.equals(OptionName.SRD2) || // method II
           name.equals(OptionName.SRD3) || // method III
           name.equals(OptionName.BRIG)){ // briggs
          onSSA=!onSSA;
        }
        else if(!(name.equals(OptionName.ESPLT) || // edge split
                  // common subexression elimination
                  name.equals(OptionName.CSE) || 
                  // efficient question propagation
                  name.equals(OptionName.CSEQP) || 
                  // efficient question propagation
                  name.equals(OptionName.PREQP) || 
                  name.equals(OptionName.GRA) || // global reassociation
  // ******************** Begin 2012.3
                  name.equals(OptionName.GLIA)||
  // ******************** End
                  name.equals(OptionName.DIVEX) || // divide expressions
                  name.equals(OptionName.DIVEX3) || // divide expressions
                  name.equals(OptionName.CBB) || // concatenate basic blocks
                  name.equals(OptionName.SSAG) || // make ssa graph
                  name.equals(OptionName.OSR) || // operator strength reduction
                  name.equals(OptionName.EBE) || // empty block elimination
                  name.equals(OptionName.DUMP) || // dump the current module
                  name.equals(OptionName.LIR2C) || // make C source
                  name.equals(OptionName.HLI) || // hoisting loop invariant
                  name.equals(OptionName.RPE) || // redundant phi elimination
                  name.equals(OptionName.DCE) || // dead code elimination
                  name.equals(OptionName.CPYP) || // copy propagation
                  name.equals(OptionName.CSTP) || // constant propagation
                  name.equals(OptionName.LCM) || // lazy code motion on SSA form
                  name.equals(OptionName.DIVEX3)||
                  name.equals(OptionName.EQP)||
                  name.equals(OptionName.PRESR)||

                  name.equals(OptionName.PBB) || // print basic blocks
                  name.equals(OptionName.SET_LINE_NUM) || // set line number
                  name.equals(OptionName.INS_LINE_NUM) || // insert line number
                  name.equals(OptionName.REMOVE_LINE_NUM) || // remove line number
                  name.equals(OptionName.SHOW_LINE_NUM) || // remove line number
                  name.equals(OptionName.CLEAR_LINE_NUM) || // remove line number
                  name.equals(OptionName.CNTBB) || // counting instructions of basic blocks
                  name.equals(OptionName.NUMBERING) || // line numbering
                  name.equals(OptionName.CNT))) { // counting instructions

           System.err.println("SsaDriver.java : Option syntax error \""+
                             name+"\".");
          isOK=false;
        }
      }
      else{ // in normal form
        if(name.equals(OptionName.MINI) || // minimal
           name.equals(OptionName.SEMI) || // semi-pruned
           name.equals(OptionName.PRUN)){ // pruned
          onSSA=!onSSA;
        }
        else if(!(name.equals(OptionName.LIR2C) || // make C source
                  name.equals(OptionName.DIVEX) || // divide expressions

                  name.equals(OptionName.DIVEX2) || // divide expressions
                  name.equals(OptionName.ESPLT) || 
                  name.equals(OptionName.LDPRE) ||
                  name.equals(OptionName.GSA) || 
                  name.equals(OptionName.PDEQP) || 
                  name.equals(OptionName.GSA) || 

  // ******************** Begin 2012.3
                  name.equals(OptionName.DDPDE) || 
                  name.equals(OptionName.CS) || 
  //###               name.equals(OptionName.CS2) || 
                  name.equals(OptionName.DC) || 
                  name.equals(OptionName.EXPDE) || 
  // ******************** End
                  name.equals(OptionName.DIVEX3)||
                  name.equals(OptionName.PBB) || // print basic blocks
                  name.equals(OptionName.SET_LINE_NUM) || // set line number
                  name.equals(OptionName.INS_LINE_NUM) || // insert line number
                  name.equals(OptionName.REMOVE_LINE_NUM) || // remove line number
                  name.equals(OptionName.SHOW_LINE_NUM) || // remove line number
                  name.equals(OptionName.CLEAR_LINE_NUM) || // remove line number
                  name.equals(OptionName.NUMBERING) || // line numbering
                  name.equals(OptionName.CNT) || // counting instructions 

                  name.equals(OptionName.CBB) || // concatenate basic blocks
                  name.equals(OptionName.DUMP))){ // dump the current module
          System.err.println("SsaDriver.java : Option syntax error \""+
                             name+"\".");
          isOK=false;
        }
      }
    }
    if(onSSA){
      System.err.println("SsaDriver.java : "+
                         "You must translate back into normal form.");
      isOK=false;
    }
    return(isOK);
  }
  
  /**
   * Check whether cnt/cntbb has multiple occurrences.
   * @param optionString
   * @return True if cnt/cntbb has multiple occurrences.
   */
  private boolean checkMultipleOccurrences(BiList optionString) {
	  boolean isOk=true;
	  boolean cntflag=false;
	  for(BiLink p=optionString.first();!p.atEnd();p=p.next()) {
		  String name=((String)p.elem());
		  if(name==OptionName.CNT || name==OptionName.CNTBB) {
			  if(cntflag) {
				  isOk=false;
				  break;
			  }
			  cntflag=true;
		  }
	  }
	  return isOk;
  }

  /**
   * Check whether some PARALLEL nodes or SUBREG nodes are in the
   * current function. If there are, return true.
   * @param func The current function
   * @return True if there are some PARALLEL or SUBREG nodes in the
   *         current function
   **/
  private boolean isNoParallelAndSubreg(Function func){
    Util util=new Util(env,func);
    for(BiLink p=func.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        BiList list=util.findTargetLir(node,Op.PARALLEL,new BiList());
        list=util.findTargetLir(node,Op.SUBREG,list);

        if(list.length()>0) return(false);
      }
    }
    return(true);
  }
}
