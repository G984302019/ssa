/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.util.ImList;
import coins.backend.Function;
import coins.backend.Data;
import coins.backend.LocalTransformer;

/**
 * The wrapper class of LIR to C.
 **/
class LirToC implements LocalTransformer{
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "LirToC"; }
  public String subject() {
    return "Translate from LIR into C code on SSA form (Wrapper).";
  }

  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.OptThr;
  /** LIR to C module **/
  private coins.lir2c.LirToC lir2c;

  /**
   * Constructor
   * @param e The environment of the SSA module
   * @param filename The name of the output file
   **/
  public LirToC(SsaEnvironment e,String filename){
    env=e;
    env.println("  Make C source from LIR into "+filename,
                SsaEnvironment.MsgThr);

    try{
      lir2c=new coins.lir2c.LirToC(env.module,filename);
    }
    catch(Exception exception){
      System.err.println(exception);
    }
  }

  /**
   * Print out the current LIR nodes and debug information.
   * @param function The current function
   * @param args The list of options
   **/
  public boolean doIt(Function function,ImList args){
    env.println("****************** doing LIR to C to "+function.symbol.name,
                SsaEnvironment.MinThr);

    // Call LIR to C
    lir2c.invoke2(function);
    env.println("",THR);

    return(true);
  }
}
