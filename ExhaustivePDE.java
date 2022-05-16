/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */

package coins.ssa;

import coins.backend.lir.LirIconst;
import coins.backend.lir.LirFconst;
import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.Type;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.cfg.BasicBlk;
import coins.backend.util.BiList;
import coins.backend.util.BiLink;
import coins.backend.Op;
import coins.backend.lir.LirLabelRef;
import coins.backend.sym.Symbol;
import coins.backend.util.ImList;
import java.util.Hashtable;
import java.util.Stack;
import java.util.Vector;
import java.util.Enumeration;
import coins.backend.lir.LirIconst;
import coins.ssa.BitVector;

/**
 * Exhaustive PDE
 **/
public class ExhaustivePDE implements LocalTransformer {
  /** Debug flag **/
    private boolean debugFlag;

    public boolean doIt(Data data, ImList args) { return true; }
  // Begin(2009.1.23)
//    public String name() { return "PREQP"; }
    public String name() { return "ExhaustivePDE"; }
// End(2009.1.2)
    public String subject() {
	return "It repeats PDE exhaustively .";
    }

  /** The utility class **/
    private Util util;
  /** The temporary SSA symbol name **/
    private String tmpSymName="_pdeqp";
    public static final int THR=SsaEnvironment.OptThr;
    /** The threshold of debug print **/
    public static final int THR2=SsaEnvironment.AllThr;
  /** The current SSA environment **/
    private SsaEnvironment env;
  /** The current SSA symbol table **/
    private SsaSymTab sstab;
  /** The current function **/
    private Function f;

  /**
   * Constructor.
   * @param e The environment of the SSA module
   * @param tab The current SSA symbol table
   **/
    public ExhaustivePDE (SsaEnvironment e, SsaSymTab tab){
      env=e;
      sstab=tab;
    }


    /**
     * Do Demand driven partial dead code elimination.
     * @param function The current function
     * @param args The list of options
     **/
    public boolean doIt(Function function,ImList args) {

	f = function;

	util=new Util(env,f);
	env.println("****************** doing CS to "+
//
		    f.symbol.name,SsaEnvironment.MinThr);

	boolean modified = true;
	int i = 1;
	for (; modified; i++){
	    modified = false;
	    CS cs = new CS(env, sstab, "executed exhaustively");
	    if (cs.doIt(f, args)) modified = true;
	    DCE dc = new DCE(env, sstab, "executed exhaustively");
	    if (dc.doIt(f, args)) modified = true;
	}
	//### System.out.println("times: "+i);

	return true;
    }
}

