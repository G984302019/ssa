/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.Function;
import coins.IoRoot;
import coins.backend.util.ImList;

/**
 * This class is to use SSA module from other optimizers.
 **/
public class PublicSsa{
  /** The environment of the SSA module **/
  SsaEnvironment env;
  /** The symbol table of the SSA module **/
  SsaSymTab sstab;
  /** The current function **/
  Function f;
  /** The memory alias analysis engine **/
  MemoryAliasAnalyze mem;

  /**
   * Constructor
   * @param func The current function
   * @param io The IoRoot of the COINS compiler
   **/
  public PublicSsa(Function func,IoRoot io){
    f=func;
    env=new SsaEnvironment(f.module,f.root.spec,io);
    sstab=new SsaSymTab(env,f);
  }

  /**
   * Translate into SSA form.
   * Pruned SSA is generated. Also, memory alias analysis are done.
   **/
  public void translate(){
    int method=TranslateToSsa.PRUNED;
    TranslateToSsa trans=new TranslateToSsa(env,sstab,method,false);
                                            
    trans.doIt(f,ImList.Empty);
    mem=new MemoryAliasAnalyze(env,f);
  }

  /**
   * Back translate from SSA form.
   * Sreedhar Method III is used.
   **/
  public void backTranslate(){
    int method=BackTranslateFromSsa.METHOD_III;
    mem.annul();

    BackTranslateFromSsa back=new BackTranslateFromSsa(env,sstab,method,true,
                                                       false);
    back.doIt(f,ImList.Empty);
  }
}
