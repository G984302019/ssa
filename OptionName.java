/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

/**
 * The String name of optimizers used in the SSA module.
 * These name are used in the options for the COINS compiler driver.
 **/
public class OptionName{
  /** The name of the option for SSA **/
  public static final String SSA_OPT="ssa-opt";
  
  /** The name of the option for LIR optimization **/
  public static final String LIR_OPT="lir-opt";
  public static final String LIR_OPT2="lirOpt";

  // The names of the methods translating into SSA form.
  /** Minimal SSA **/
  public static final String MINI="mini";
  /** Semi-pruned SSA **/
  public static final String SEMI="semi";
  /** Pruned SSA **/
  public static final String PRUN="prun";
  
  // The names of the methods back translating from SSA form.
  /** Method I **/
  public static final String SRD1="srd1";
  /** Method II **/
  public static final String SRD2="srd2";
  /** Method III **/
  public static final String SRD3="srd3";
  /** Briggs **/
  public static final String BRIG="brig";

  // The names of the optimizers.
  /** Copy Propagation **/
  public static final String CPYP="cpyp";
  /** Constant Propagation **/
  public static final String CSTP="cstp";
  /** Dead Code Elimination **/
  public static final String DCE="dce";
  /** Common Subexpression Elimination **/
  public static final String CSE="cse";
  /** Redundant Phi Elimination **/
  public static final String RPE="rpe";
  /** Hoisting Loop Invariant variables **/
  public static final String HLI="hli";
  /** Operator Strength Reduction **/
  public static final String OSR="osr";
  /** Common Subexpression Elimination With Efficient Question Propagation **/
  public static final String CSEQP="cseqp";
  /** Partial Redundancy Elimination With Efficient Question Propagation **/
  public static final String PREQP="preqp";
  // ******************** Begin 2012.3
  /** Demand Driven Partial Dead Code Elimination **/
  public static final String DDPDE="ddpde";
  /** Dead Code Elimination **/
  public static final String DC = "dc";
  /** **/
  public static final String CS = "cs";
  /** Exhaustive PDE **/
  public static final String EXPDE="expde";
  /** Global Load Instruction Aggregation Based on Code Motion **/
  public static final String GLIA="glia";
  // ******************** End
  public static final String LDPRE="ldpre";

  public static final String GSA="gsa";

  /** Effective Demand-driven Partial Redundancy Elimination **/
  public static final String EQP="eqp";
  /** Scalar Replacement Based on Partial Redundancy Elimination **/
  public static final String PRESR="presr";
  public static final String DIVEX3="divex3";


// by R.O.
	/** Lazy Code Motion on SSA form **/
  public static final String LCM="lcm";
  /**  **/
  public static final String DIVEX2="divex2";
  /**  **/
  public static final String PDEQP="pdeqp";
  /** Counting instructions **/
  public static final String CNT="cnt";
  /** Counting instructions of Basic blocks **/
  public static final String CNTBB="cntbb";
  // The names of utilities.
  /** Concatenate Basic Blocks**/
  public static final String CBB="cbb";
  /** Edge Split **/
  public static final String ESPLT="esplt";
  /** Empty Block Elimination **/
  public static final String EBE="ebe";
  /** Making SSA graph **/
  public static final String SSAG="ssag";
  /** Divide Expressions **/
  public static final String DIVEX="divex";
  /** Global Reassociation for the Expressions **/
  public static final String GRA="gra";

  /** Print Basic blocks **/
  public static final String PBB="pbb";
  public static final String NUMBERING="num";
  public static final String SET_LINE_NUM="stlin";
  public static final String INS_LINE_NUM="inslin";
  public static final String REMOVE_LINE_NUM="rmlin";
  public static final String SHOW_LINE_NUM="shlin";
  public static final String CLEAR_LINE_NUM="clrlin";
 
  //The name of the default method translating into SSA form.
  public static final String DEFAULT_TO_SSA = PRUN;
  //The name of the default method back translating from SSA form.
  public static final String DEFAULT_FROM_SSA = SRD3;
  
  // The type of options
  /** options applied to SSA form **/
  public static final int ON_SSA = 1;
  /** options applied to non SSA form **/
  public static final int NON_SSA = 2;
  /** options to translate to SSA form **/
  public static final int TO_SSA = 3;
  /** options to back-translate from SSA form **/
  public static final int FROM_SSA = 4;
  /** options applied to both SSA and non SSA form **/
  public static final int BOTH = 5;
  
  public static int typeOf(String name){
	  if (name == MINI) return TO_SSA;
	  if (name == SEMI) return TO_SSA;
	  if (name == PRUN) return TO_SSA;
	  if (name == MINI) return TO_SSA;
	  if (name == SRD1) return FROM_SSA;
	  if (name == SRD2) return FROM_SSA;
	  if (name == SRD3) return FROM_SSA;
	  if (name == BRIG) return FROM_SSA;
	  if (name == ESPLT) return BOTH;
	  if (name == DIVEX) return BOTH;
	  if (name == CBB) return BOTH;
	  if (name == LIR2C) return BOTH;
	  if (name == DUMP) return BOTH;
	  if (name == DIVEX2) return NON_SSA;
	  if (name == PDEQP) return NON_SSA;
  // ******************** Begin 2012.3
	  if (name == DDPDE) return NON_SSA;
	  if (name == EXPDE) return NON_SSA;
  // ******************** End
	  if(name == CNT) return BOTH;
	  if(name == CNTBB) return BOTH;
	  if(name == PBB) return BOTH;
	  if(name==NUMBERING) return BOTH;
	  if(name==SET_LINE_NUM) return BOTH;
	  if(name==INS_LINE_NUM) return BOTH;
	  if(name==REMOVE_LINE_NUM) return BOTH;
	  if(name==SHOW_LINE_NUM) return BOTH;
	  if(name==CLEAR_LINE_NUM) return BOTH;
	  return ON_SSA;
  }
  
  // The names of debug utilities
  /** Dump Module **/
  public static final String DUMP="dump";
  /** Make C source from the current module **/
  public static final String LIR2C="lir2c";

  // The other information.
  /** No copy folding when translate to SSA form **/
  public static final String SSA_NO_COPY_FOLDING="ssa-no-copy-folding";
  /** No SSA based coalescing in back translation from SSA form **/
  public static final String SSA_NO_SREEDHAR_COALESCING="ssa-no-sreedhar-coalescing";
  /** No aggregation expression before back translation **/
//  public static final String SSA_NO_AGGREGATE_EXP="ssa-no-aggregate-exp";
  public static final String SSA_NO_REPLACE_BY_EXP="ssa-no-replace-by-exp";
  /** No changing loop structure **/
  public static final String SSA_NO_CHANGE_LOOP="ssa-no-change-loop";
  /** With coalescing by Chaitin after back translation from SSA form **/
  public static final String SSA_WITH_CHAITIN_COALESCING="ssa-with-chaitin-coalescing";
  /** No analysis about the aliases of memory object **/
  public static final String SSA_NO_MEMORY_ANALYSIS="ssa-no-memory-analysis";
  /** No redundant phi elimination after translating into SSA form **/
  public static final String SSA_NO_PHI_ELIMINATE="ssa-no-redundant-phi-elimination";
  /** Pruning redundant nodes in SSA graph <<experimental>> **/
  public static final String SSA_SSAG_PRUNING="ssa-ssag-pruning";
  /** Debugging mode **/
  public static final String SSA_DEBUG="ssa-debug";
}
