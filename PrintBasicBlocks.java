/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import java.io.PrintWriter;

import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.util.ImList;

public class PrintBasicBlocks implements LocalTransformer {

	public boolean doIt(Data data, ImList args) { return true;	}
	public String name() { return "Print Basic Blocks"; }
	public String subject() { return "Print Basic Blocks"; }

	private SsaEnvironment env;
	private SsaSymTab sstab;
	private PrintWriter out;
	public PrintBasicBlocks(SsaEnvironment e,SsaSymTab tab) {
		env=e;
		sstab=tab;
		out=env.output;
	}

	public boolean doIt(Function func, ImList args) {
//		func.module.printIt(out);
		func.printIt(out);
		return true;
	}
}
