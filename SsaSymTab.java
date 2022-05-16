/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.sym.Symbol;
import coins.backend.ana.EnumRegVars;
import coins.backend.cfg.FlowGraph;
import coins.backend.Function;
import coins.backend.Storage;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;
import coins.backend.Type;

import java.util.Hashtable;

/**
 * The symbol table of SSA variables.
 **/
class SsaSymTab{
  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The map for symbols **/
  private Hashtable symbols;
  /** The current function **/
  private Function function;
  
    //EnumRegVars rn;    /////
    //int nPhyRegs;    /////
  public static final String DUMMY_FUNC = "__dummy_function";    ///// 

  /**
   * The SSA variables. This class has the original symbol and the current
   * suffix of the SSA variable.
   **/
  private class SsaSymbol{
    /** The original symbol of the SSA symbol **/
    final Symbol original;
    /** The latest SSA symbol of it **/
    Symbol latest;
    /** The latest suffix of it **/
    private int suffix;

    /**
     * Constructor
     * @param s The original symbol
     **/
    SsaSymbol(Symbol s){
      original=s;
      suffix=0;
      latest=null;
      //newSymbol();
    }

    /**
     * Return a new SSA variable.
     * @return A new symbol of the SSA variable
     **/
    Symbol newSymbol(){
      String symName=original.name+"_"+suffix;
      symName=symName.intern();
      latest=function.addSymbol(symName,original.storage,original.type,
                                original.boundary,0,ImList.Empty);
      function.flowGraph().touch();
      //latest.setShadow(original);
      //System.out.println("+++++++++++++ "+latest.id+"    "+latest.name);
      suffix++;
      symbols.put(latest,this);
      return(latest);
    }

    /**
     * Return the suffix number of the symbol
     * @param s The target symbol
     * @return The suffix number of the symbol. If there are no such specified
     *         symbol in the table, return -1
     **/
    int rank(Symbol s){
      for(int i=0;i<suffix;i++){
        String symName=original.name+"_"+i;
        symName=symName.intern();

        if(symName.equals(s.name.intern()))
          return(i);
      }
      return(-1);
    }
  }

  /**
   * Constructor<br>
   * Create a new symbol table in the SSA form. Initialize all local variables
   * in the current function.
   * @param e The environment of the SSA module
   * @param f The current function
   **/

  SsaSymTab(SsaEnvironment e,Function f){
    env=e;
    FlowGraph g=f.flowGraph();
    symbols=new Hashtable();
    function=f;

    for(BiLink p=f.localSymtab.symbols().last();!p.atEnd();p=p.prev()){
      Symbol s=(Symbol)p.elem();
        SsaSymbol ssym=(SsaSymbol)symbols.get(s);
        if(ssym==null){
          ssym=new SsaSymbol(s);
          symbols.put(s,ssym);
        }
        //env.output.println(ssym.latest.name+" ---> "+ssym.original.name);
    }
  }

  /**
   * Compare the specified two symbols.
   * @param s1 The first specified symbol
   * @param s2 The second specified symbol
   * @return If s1 and s2 are the same, return 0. If s1 has the large suffix
   *         number, then return 1. Otherwise return -1.
   **/
  int compare(Symbol s1,Symbol s2){
    SsaSymbol ssym1=(SsaSymbol)symbols.get(s1);
    int rank1=-1;
    if(ssym1!=null) rank1=ssym1.rank(s1);

    SsaSymbol ssym2=(SsaSymbol)symbols.get(s2);
    int rank2=-1;
    if(ssym2!=null) rank2=ssym2.rank(s2);

    if(rank1==rank2) return(0);
    else if(rank1>rank2) return(1);

    return(-1);
  }

  /**
   * Get the original symbol of the specified symbol.
   * @param s The specified symbol
   * @return Original symbol of the specified one
   **/
  Symbol orgSym(Symbol s){
    SsaSymbol ssym=(SsaSymbol)symbols.get(s);
    if(ssym!=null) return(ssym.original);

    return(s);
  }

  /**
   * Get a new symbol of the FRAME node or the STATIC node.
   * @param s The old symbol
   * @return A new symbol
   **/
  Symbol newAddressSymbol(Symbol s){
    SsaSymbol ssym=(SsaSymbol)symbols.get(s);
    if(ssym!=null) return(ssym.newSymbol());

    ssym=new SsaSymbol(s);
    symbols.put(s,ssym);
    return(ssym.newSymbol());
  }

  /**
   * Get the current symbol of the FRAME or the STATIC node.
   * @param s The specified symbol
   * @return The current symbol for the specified symbol
   **/
  Symbol currentAddressSymbol(Symbol s){
    SsaSymbol ssym=(SsaSymbol)symbols.get(s);
    if(ssym!=null) return(ssym.latest);

    ssym=new SsaSymbol(s);
    symbols.put(s,ssym);
    return(ssym.newSymbol());
  }

  /**
   * Get a new symbol of the SSA variable.
   * @param s The old symbol
   * @return A new symbol of the SSA variable
   **/
  Symbol newSsaSymbol(Symbol s){
    SsaSymbol ssym=(SsaSymbol)symbols.get(s);
    if(ssym!=null){
      //env.output.println(s+"   "+ssym.latest);
      return(ssym.newSymbol());
    }
    // If no SsaSymbols related on the symbol `s',
    // Make a new SSA symbol related on `s'.
    return(newSsaSymbol(s.name.intern(),s.type));
  }
  
  /**  Called from TranslateToSsa.
   * Get a new symbol of the SSA variable.
   * @param s The old symbol
   * @return A new symbol of the SSA variable
   **/
  Symbol newSsaSymbol1(Symbol s){    /////
	  if (isPhyReg(s))    /////
		  return s;
	  else
		  return newSsaSymbol(s);
  }
  
  public boolean isPhyReg(Symbol s){    /////
      EnumRegVars rn = (EnumRegVars)function.require(EnumRegVars.analyzer);    /////
      int nPhyRegs = rn.nPhyRegs();    /////

	  return (s.storage==Storage.REG  && rn.index(s) < nPhyRegs);
  }
  
  Symbol newGlobalSymbol(String name){    /////
	  	name = name.intern();
	  	Symbol symbol;
	  	symbol = function.module.globalSymtab.addSymbol(
	  			    name, Storage.STATIC, Type.UNKNOWN, 4,
	                  ".text", "XDEF", ImList.Empty);
	  	return symbol;
  }

  /**
   * Get a new symbol of the SSA variable.
   * @param name The base name of the symbol
   * @param type The type of the symbol
   * @return A new symbol of the SSA variable
  **/
  Symbol newSsaSymbol(String name,int type){
    if(Type.tag(type)!=Type.INT && Type.tag(type)!=Type.FLOAT)
      return(null);

    String fullName=name+Type.toString(type);
    Symbol s=function.localSymtab.get(fullName.intern());
    if(s==null){
      // NOTICE
      // not set the offset!!!
      int boundary=0;
      switch(Type.bits(type)){
        case 8: boundary=1;break;
        case 16: boundary=2;break;
        case 32: boundary=4;break;
        case 64: boundary=8;break;
        case 128: boundary=16;break;
      }
      s=function.addSymbol(fullName,Storage.REG,type,boundary,0,ImList.Empty);
    }
    SsaSymbol ssym=(SsaSymbol)symbols.get(s);
    if(ssym==null){
      ssym=new SsaSymbol(s);
      symbols.put(s,ssym);
    }
    return(ssym.newSymbol());
  }
}
