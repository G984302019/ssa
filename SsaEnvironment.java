/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.Module;
import coins.backend.lir.LirFactory;
import coins.driver.CompileSpecification;
import coins.driver.CoinsOptions;
import coins.driver.Trace;
import coins.IoRoot;

import java.io.PrintWriter;

/**
 * The environment of the SSA module.
 **/
class SsaEnvironment{
  /** The threshold of the debug print **/
  public static final int MsgThr=100;
  /** The threshold of the debug print **/
  public static final int MinThr=1000;
  /** The threshold of the debug print **/
  public static final int SsaThr=1500;
  /** The threshold of the debug print **/
  public static final int OptThr=2000;
  /** The threshold of the debug print **/
  public static final int AllThr=10000;
  /** The output stream of the compiler **/
  public final PrintWriter output;
  /** The specification of the COINS compiler driver **/
  public final CompileSpecification spec;
  /** The options to the COINS compiler driver **/
  public final CoinsOptions opt;
  /** The trace object of the compiler **/
  public final Trace trace;
  /** The name of this module **/
  public final String MODULENAME="SSA";
  /** The current compile module **/
  public final Module module;
  /** The factory of LIR **/
  public final LirFactory lir;
  /** The root of IO in COINS **/
  public final IoRoot ioRoot;

  /**
   * Constructor
   * @param m The current compile module
   * @param coinsSpec The specification of the COINS compiler driver
   * @param io The input/output of the compiler
   **/
  SsaEnvironment(Module m,CompileSpecification coinsSpec,IoRoot io){
    ioRoot=io;
    module=m;
    lir=m.newLir;
    output=new PrintWriter(ioRoot.printOut,true);
    spec=coinsSpec;
    opt=spec.getCoinsOptions();
    trace=spec.getTrace();
  }

  /**
   * If the value of threshold is lower than specified by the options to
   * the COINS compiler driver, return TRUE.
   * @param threshold The value which is checked if it is lower than threshold
   * @return True if the value `threshold' is lower than threshold
   **/
  boolean shouldDo(int threshold){
    return(trace.shouldTrace(MODULENAME,threshold));
  }

  /**
   * Debug print out. If the value of `threshold' is lower than the threshold
   * print out `str' as a debug message. This method prints the carriage return
   * at the end of the message.
   * @param str The debug message
   * @param threshold The threshold of the debug message
   **/
  void println(String str,int threshold){
    if(shouldDo(threshold)){
      output.println(str);
    }
  }

  /**
   * Debug print out. If the value of `threshold' is lower than the threshold
   * print out `str' as a debug message.
   * @param str The debug message
   * @param threshold The threshold of the debug message
   **/
  void print(String str,int threshold){
    if(shouldDo(threshold)){
      output.print(str);
    }
  }
}
