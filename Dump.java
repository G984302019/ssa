/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.util.ImList;
import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalAnalyzer;
import coins.backend.ana.LiveVariableSlotwise;
import coins.backend.ana.Dominators;
import coins.backend.ana.DominanceFrontiers;
import coins.backend.ana.Postdominators;
import coins.backend.ana.ControlDependences;
import coins.backend.ana.LoopAnalysis;
import coins.backend.ana.ReverseDFST;

/**
 * Dump the current LIR nodes.
 * This is used for debugging.
 **/
class Dump implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "Dump"; }
  public String subject() {
    return "Dump LIR.";
  }

  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.OptThr;

  /**
   * Constructor
   * @param e The environment of the SSA module
   **/
  public Dump(SsaEnvironment e){
    env=e;
    env.println("  Dump the current module",SsaEnvironment.MsgThr);
  }

  /**
   * Print out the current LIR nodes and debug information.
   * @param function The current function
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    env.println("****************** doing DUMP to "+function.symbol.name,
                SsaEnvironment.MinThr);

    function.printIt(env.output,
                     new LocalAnalyzer[]{Dominators.analyzer,
                                         DominanceFrontiers.analyzer,
                                         Postdominators.analyzer,
                                         ControlDependences.analyzer,
                                         LoopAnalysis.analyzer,
                                         ReverseDFST.analyzer,
                                         LiveVariableSlotwise.analyzer});
    env.println("",THR);

    return(true);
  }
}
