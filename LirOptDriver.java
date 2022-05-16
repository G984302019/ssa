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

public class LirOptDriver  implements LocalTransformer{
	  public boolean doIt(Data data, ImList args) { return true; }
	  public String name() { return "LirOptDriver"; }
	  public String subject() {
	    return "LIR optimizations";
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
	  /** The counter of SSA/Lir options **/
	  private int optNum;
      private String optionName;
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
	  public LirOptDriver(Module m,IoRoot io,CompileSpecification coinsSpec, String optName){
	    env=new SsaEnvironment(m,coinsSpec,io);
        optionName = optName;
	    // Do JUMP opt
	    m.apply(JumpOpt.trig);

	    // Begin(2010.3.25)
	    (new CountingInstructionsOfBB(env,0,size)).chkProfOpt(m, coinsSpec, io, env);
	    //CountingInstructionsOfBB cntbb=new CountingInstructionsOfBB(env,0,size);
	    //cntbb.chkProfOpt(m, coinsSpec, io, env);
	    // End(2010.3.25)
	  }
	  
	  public boolean doIt(Function function,ImList args){
		    // Initialize the lir-opt option counter
		    optNum=0;

		    if(!isNoParallelAndSubreg(function)) return(true);

		    env.println("Optimization on LIR form",1);

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

		    // Get the current time
		    if(env.shouldDo(THR)){
		      long end=System.currentTimeMillis();
		      long t=end-start;
		      env.println("[ Total Time of LIR_OPT : "+t+"ms ]",THR);
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

	    String options;
	    options = env.opt.getArg(optionName);
	    int length=options.length();
	    while(endIndex<=length){
	      beginIndex=endIndex;
	      endIndex=options.indexOf(delimiter,beginIndex);
	      if(endIndex==-1)
	        endIndex=length;

	      if(endIndex>beginIndex){
	        String opt=options.substring(beginIndex,endIndex);
	        opt=opt.trim().intern(); //## intern()
	        optionString.add(opt);
	      }
	      endIndex++;
	    }


	    boolean isOk=syntaxCheck(optionString);
	    if(!isOk){
	      System.err.println("WARNING : illegal syntax in the LIR-OPT option.");
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
	        if(name == OptionName.CSEQP || name == OptionName.PREQP){
	          optimizers.add(new EdgeSplit(env));
	          optimizers.add(new DivideExpression(env,sstab));
		  optNum++;
		  optNum++;
	        }
	        optimizers.add(lt);
		optNum++;
	        if(!env.opt.isSet(OptionName.SSA_NO_PHI_ELIMINATE) &&
	           (name == OptionName.MINI ||
	            name == OptionName.SEMI ||
	            name == OptionName.PRUN)){
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
	    if(name == OptionName.MINI){ // minimal
	      boolean folding=!env.opt.isSet(OptionName.SSA_NO_COPY_FOLDING);
	      lt=new TranslateToSsa(env,sstab,TranslateToSsa.MINIMAL,folding);
	    }
	    else if(name == OptionName.SEMI){ // semi-pruned
	      boolean folding=!env.opt.isSet(OptionName.SSA_NO_COPY_FOLDING);
	      lt=new TranslateToSsa(env,sstab,TranslateToSsa.SEMI_PRUNED,folding);
	    }
	    else if(name == OptionName.PRUN){ // pruned
	      boolean folding=!env.opt.isSet(OptionName.SSA_NO_COPY_FOLDING);
	      lt=new TranslateToSsa(env,sstab,TranslateToSsa.PRUNED,folding);
	    }
	    else if(name == OptionName.SRD1){ // method I
	      boolean coalesce=!env.opt.isSet(OptionName.SSA_NO_SREEDHAR_COALESCING);
	      boolean aggregate=!env.opt.isSet(OptionName.SSA_NO_REPLACE_BY_EXP);
	      lt=new BackTranslateFromSsa(env,sstab,BackTranslateFromSsa.METHOD_I,
	                                  coalesce,aggregate);
	    }
	    else if(name == OptionName.SRD2){ // method II
	      boolean coalesce=!env.opt.isSet(OptionName.SSA_NO_SREEDHAR_COALESCING);
	      boolean aggregate=!env.opt.isSet(OptionName.SSA_NO_REPLACE_BY_EXP);
	      lt=new BackTranslateFromSsa(env,sstab,BackTranslateFromSsa.METHOD_II,
	                                  coalesce,aggregate);
	    }
	    else if(name == OptionName.SRD3){ // method III
	      boolean coalesce=!env.opt.isSet(OptionName.SSA_NO_SREEDHAR_COALESCING);
	      boolean aggregate=!env.opt.isSet(OptionName.SSA_NO_REPLACE_BY_EXP);
	      lt=new BackTranslateFromSsa(env,sstab,BackTranslateFromSsa.METHOD_III,
	                                  coalesce,aggregate);
	    }
	    else if(name == OptionName.BRIG){ // Briggs
	      //boolean extend=!env.opt.isSet(OptionName.SSA_NO_SREEDHAR_COALESCING);
	      boolean extend=false;
	      lt=new BackTranslateFromSsaBriggs(env,sstab,extend);
	    }
	    else if(name == OptionName.CPYP){ // copy propagation
	      lt=new CopyPropagation(env);
	    }
	    else if(name == OptionName.CSTP){ // constant propagation
	      lt=new ConstantPropagation(env);
	    }
	    else if(name == OptionName.DCE){ // dead code elimination
	      lt=new DeadCodeElimination(env);
	    }
	    else if(name == OptionName.CSE){ // common subexpression elimination
	      lt=new CommonSubexpressionElimination(env);
	    }
	    else if(name == OptionName.CSEQP){ // efficient question propagation
	      lt=new PREQP(env,sstab,7);
	    }
	    else if(name == OptionName.PREQP){ // efficient question propagation
	      lt=new PREQP(env,sstab,0);
	    }
	    else if(name == OptionName.RPE){ // redundant phi elimination
	      lt=new RedundantPhiElimination(env);
	    }
	    else if(name == OptionName.ESPLT){ // edge split
	      lt=new EdgeSplit(env);
	    }
	    else if(name == OptionName.HLI){ // hoisting loop invariant variables
	      lt=new HoistingLoopInvariant(env,sstab);
	    }
	    else if(name == OptionName.DUMP){ // dump the current module
	      lt=new Dump(env);
	    }
	    else if(name == OptionName.LIR2C){ // make C source from LIR
	      lt=new LirToC(env,makeCName());
	    }
	    else if(name == OptionName.EBE){ // empty block elimination
	      lt=new EmptyBlockElimination(env);
	    }
	    else if(name == OptionName.OSR){ // operator strength reduction
	      lt=new SsaGraph(env,sstab,name);
	    }
	    else if(name == OptionName.SSAG){ // make ssa graph only
	      lt=new SsaGraph(env,sstab,name);     // it is for debug
	    }
	    else if(name == OptionName.DIVEX){ // divide expressions
	      lt=new DivideExpression(env,sstab);
	    }
	    else if(name == OptionName.DIVEX3){ // divide expressions
		  lt=new DivideExpression3(env,sstab);
	    }
	    else if(name == OptionName.CBB){ // concatenate basic blocks
	      lt=new ConcatBlks(env);
	    }
	    else if(name == OptionName.GRA){ // global reassociation
	      lt=new GlobalReassociation(env);
	    }
	    else if(name == OptionName.LDPRE){ // global load instruction aggregation
			lt=new LDPRE(env,sstab);
		}
	    else if(name == OptionName.GSA){ // global load instruction aggregation
			lt=new GSA(env,sstab);
		}
  // ******************** Begin 2012.3
        else if(name == OptionName.GLIA){ // global load instruction aggregation
			lt=new GLIA(env,sstab);
		}
        else if(name == OptionName.DDPDE){ // demand driven partial dead code elimination
			lt=new DDPDE(env,sstab);
		}
        else if(name == OptionName.CS){ // 
			lt=new CS(env,sstab);
		}
        else if(name == OptionName.DC){ // dead code elimination
			lt=new DCE(env,sstab);
		}
        else if(name == OptionName.EXPDE){ // exhaustive pde
			lt=new ExhaustivePDE(env,sstab);
		}
  // ******************** End

	    else if(name == OptionName.LCM) { // lazy code motion on SSA form
	      lt=new LCM(env,sstab);
	      LCM lcm=(LCM)lt;
	      lcm.setOptNum(optNum);
	    }
	    else if(name == OptionName.DIVEX2) {
	      lt=new DivideExpression2(env, sstab);
	    }
	    else if(name == OptionName.PDEQP) {
	      lt=new PDEQP(env,sstab);
	    }
	    else if(name.equals(OptionName.CNT)) {
	      lt=new CountingInstructions(env, sstab, 0, 4);
	    }
	    // Begin(2010.3.12)
	    else if(name.equals(OptionName.CNTBB)) {
	      lt=new CountingInstructionsOfBB(env, sstab, 0, size);
	    }
	    // End(2010.3.12)
	    else if(name.equals(OptionName.PBB)) { // print basic blocks
	      lt=new PrintBasicBlocks(env, sstab);
	    }
	    // Begin(2010.3.5)
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
	    // End(2010.3.5)
	    // Begin(2010.3.25)
	    else if(name.equals(OptionName.CLEAR_LINE_NUM)) {
	      lt=new LirNumbering(f,LirNumbering.CLEAR_LINE_NUMBER);
	    }
	    // End(2010.3.25)
	    else{
	      System.err.println("LirOptDriver.java : unexpected optimizer name "+name);
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
	      String name=((String)p.elem()); //## name is interned.
	      int optionType = OptionName.typeOf(name);
	      if(onSSA){ // in SSA form
	    	  if (optionType == OptionName.FROM_SSA){
	    		  onSSA=!onSSA;
	    	  }
	    	  else if (optionType == OptionName.NON_SSA){
	    		  p.addBefore(OptionName.DEFAULT_FROM_SSA);
	    		  onSSA=!onSSA;
	    		  System.err.println("LirOpt Warning : \"" + name + 
                          "\" can not be applied to SSA-form");
                /* isOK=false;*/
	    	  }
	      }
	      else{ // in normal form
	    	  if (optionType == OptionName.TO_SSA){
	    		  onSSA=!onSSA;
	    	  }
	    	  else if (optionType == OptionName.ON_SSA){
	    		  p.addBefore(OptionName.DEFAULT_TO_SSA);
	    		  onSSA=!onSSA;
	    		  System.err.println("LirOpt Warning : \"" + name + 
                  "\" can not be applied to nonSSA-form");
                 /* isOK=false;*/
	    	  }
	      }
	    }
	    if(onSSA){
	    	optionString.last().addAfter(OptionName.DEFAULT_FROM_SSA);
	       System.err.println("LirOpt Warning : "+
	                         "You must translate back into normal form.");
	      /* isOK=false;*/
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
