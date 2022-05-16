/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
//import java.io.FileInputStream;
//import java.io.InputStream;
import java.io.IOException;
import java.io.StringReader;
import java.util.BitSet;
//import java.util.Properties;

import coins.IoRoot;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.Keyword;
import coins.backend.LocalTransformer;
import coins.backend.Module;
import coins.backend.Op;
import coins.backend.Storage;
//import coins.backend.SyntaxErrorException;
import coins.backend.Type;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.util.BiLink;
import coins.backend.util.BiList;
import coins.backend.util.ImList;
import coins.backend.util.QuotedString;
import coins.backend.sym.Symbol;
//import coins.driver.CoinsOptions;
import coins.driver.CompileSpecification;

/**
 * Counting LIR instructions in each basic block.<br>
 *
 */
public class CountingInstructionsOfBB implements LocalTransformer {

	//@Override
	public boolean doIt(Data data, ImList args) {	return true; }
	public String name() { return "CountingInstructionsOfBB"; }
	public String subject() { return "CountingInstructionsOfBB" ; }

  private static String TMPDIR="tmpdir";
	/** The current function **/
	private Function f;
    private String winseparator="\\";
  private String fileSeparator="/";
  private String cntpath="/tmp";
	/** Names of the target Modules and Functions are written in the file  **/
	private String fname="/tmp/file_list.dat";
	private String filenamelist="filenamelist";
	private Symbol filelistSym;
	private String filenamePrefix="";
	/** The output file name **/
	private String funclistname="funcList";
	private Symbol funclistSym;
  //	/** The current SSA symbol table **/
  //	private SsaSymTab sstab;
	/** The current SSA environment **/
	private SsaEnvironment env;
  //	private int mode;
	private int size;
	/** The name of counter : <module name>.<function name>**/
	private String counterName;

	/**
	 * The max number of files
	 */
	private int maxfs;
	/**
	 * The max number of basic blocks
	 */
	private int maxbb;
	/**
	 * The symbol of maxfs
	 */
	private Symbol maxfsSym;
	/**
	 * The symbol of maxbb
	 */
	private Symbol maxbbSym;
	/** The function name symbol of printCounter **/
	private Symbol printcallSym;
	/** The return value symbol of print function **/
	private Symbol printRtnValSym;
	/**
	 * Name of the print function
	 */
	private static String printcallStr="__cntbb_printCounter";
  /**
   * Coins options name
   */
  private String prefixoptname="ssa-cntbb-prefix";

  //  private static String propertyFilename="ssa.properties";
  //  private Properties ssaProperties=new Properties();

	/**
	 * Constructor.
     * @param e The environment of the SSA module
	 * @param tab The symbol table of the SSA module
	 * @param md not used
	 * @param sz the size of int type of the counter (bytes)
	 */
  public CountingInstructionsOfBB(SsaEnvironment e, SsaSymTab tab, int md, int sz) {
    //    sstab=tab;
    env=e;
    String prefixVal=e.opt.getArg(prefixoptname);
    if(prefixVal!=null) filenamePrefix=prefixVal+".";
    // Next values are temporary.
    //    mode=md;
    size=sz;
    cntpath=getCntpath();
    //    if(File.separator.equals(winseparator)) {
    //      fileSeparator=winseparator;
    //    } else {
    //      fileSeparator=File.separator;
    //    }
    fileSeparator=File.separator;
    fname=cntpath+fileSeparator+"file_list.dat";
  }
	public CountingInstructionsOfBB(SsaEnvironment e, int md, int sz) {
		env=e;
    //		mode=md;
		size=sz;
	}

  private String getCntpath() {
    String tmpdir="/tmp";
    if(env.opt.isSet(TMPDIR)) {
      tmpdir=env.opt.getArg(TMPDIR);
    }
    return tmpdir;
  }
	
	/**
	 * Main method of this class.
	 * @param func the current function
	 * @param args not used
	 */
	public boolean doIt(Function func, ImList args) {
		if(func.symbol.name.equals(printcallStr)) return true;
		f=func;
		// Make printRtnValSym
		//   ("printRtnVal" STATIC I32 4 ".data" XDEF &syminfo "printRtnVal" <module name> 3 0)
		printRtnValSym=f.localSymtab.get("printRtnVal");
		if(printRtnValSym==null) {
			printRtnValSym=f.addSymbol("printRtnVal", Storage.FRAME,
				Type.type(Type.INT, 32), 4, 0, ImList.Empty);
		}
		counterName=getProperModulename(f.module.name)+"."+f.symbol.name;
		File file=new File(fname);
		// if there is no file_list file, do 1st pass options.
		try {
			file.createNewFile();

			// check the existence of my function name in the file.
			// if not, do 1st pass options
			if(!isRegisteredFuncname(file, func)) {
			//    register the function name to the file.
				registerFuncname(file, func);
			}
			// otherwise do 2nd pass options
			else {
				checkFile(file);
				funclistSym=f.module.globalSymtab.get(funclistname);
			    filelistSym=f.module.globalSymtab.get(filenamelist);
				printcallSym=f.module.globalSymtab.get(printcallStr);
				if(printcallSym==null) {
					printcallSym=f.module.globalSymtab.addSymbol(printcallStr,
							Storage.STATIC, Type.UNKNOWN, 4, ".text", "XREF", ImList.list("&syminfo",
                                                                            new QuotedString(getProperModulename(f.module.name)), "1", "0"));
				}
			    //  if func is "main" and global variables is not created then cereate them
				if(hasMain(f.module)) {
					createNewGlobalvarXdef(file, func);
				}
				else {
					createNewGlobalvarXref(file, func);
				}
				// In each basic blocks, insert counting LIR instructions.
				for(BiLink pp=f.flowGraph().basicBlkList.first(); !pp.atEnd(); pp=pp.next()) {
					BasicBlk blk=(BasicBlk)pp.elem();
					if(blk==f.flowGraph().exitBlk()) continue;
					// The number of instructions
					int count=0;
					for(BiLink p=blk.instrList().first(); !p.atEnd(); p=p.next()) {
						count++;
					}
					embedCount(blk, count);
				}
				//  Before calling exit, insert the print function call.
				for(BiLink pp=f.flowGraph().basicBlkList.first(); !pp.atEnd(); pp=pp.next()) {
					BasicBlk blk=(BasicBlk)pp.elem();
					if(blk==f.flowGraph().exitBlk()) continue;
					for(BiLink p=blk.instrList().first(); !p.atEnd(); p=p.next()) {
						LirNode instr=(LirNode)p.elem();
						if(isCallExit(instr)) {
							p.addBefore(makePrintCall());
						}
					}
				}
				//  In return blocks of "main" function, insert the print function call.
				if(f.symbol.name.intern()=="main".intern()) {
					BasicBlk exit=f.flowGraph().exitBlk();
					// Insert printing blocks
					BitSet blks=new BitSet(f.flowGraph().idBound());
//					for(BiLink bp=exit.predList().first(); !bp.atEnd(); bp=bp.next()) {
//						BasicBlk insp=(BasicBlk)bp.elem();
//						if(blks.get(insp.id)) continue;
//						BiLink last=insp.instrList().last();
//						last.addBefore(makePrintCall());
//						blks.set(insp.id);
//					}
					BasicBlk insBlk=f.flowGraph().insertNewBlkBefore(exit);
					for(BiLink bp=exit.predList().first();!bp.atEnd();bp=bp.next()) {
						BasicBlk pblk=(BasicBlk)bp.elem();
						if(blks.get(pblk.id)) continue;
						pblk.replaceSucc(exit, insBlk);
						blks.set(pblk.id);
					}
					insBlk.replaceSucc(insBlk, exit);
					BiLink last=insBlk.instrList().last();
					last.addBefore(makePrintCall());
					f.flowGraph().touch();
				}
			}
		} catch (IOException e) {
			System.err.println("CountingInstructionsBB:can't create new file "+fname);
			return false;
		}
		return true;
	}


  private String getProperModulename(String str) {
    String separator=File.separator;
    if(separator.equals(winseparator)) separator=winseparator+winseparator;
    String[] path=str.split(separator);
    if(path.length==0) return str;
    return path[path.length-1];
  }

	/** 
	 * Check if the Function is registered to the fileList
	 * @param file the file to be checked
	 * @param func the current function
	 */
	boolean isRegisteredFuncname(File file, Function func) {
		try {
			BufferedReader rdr=new BufferedReader(new FileReader(file));
			String line;
			while((line=rdr.readLine())!=null) {
				if(counterName.equals(getFuncstr(line))) {
					rdr.close();
					return true;
				}
			}
			rdr.close();
		} catch (Exception e) {
			System.err.println("CountingInstructionsBB:file read error");
			return false;
		}
		return false;
	}
	
	/**
	 * Write the funtion name and the number of basic blocks in the function
	 * @param file the file in which the function name and the number are written
	 * @param func the function
	 */
	private boolean registerFuncname(File file, Function func) {
		try {
			BufferedWriter wrt=new BufferedWriter(new FileWriter(file,true));
			wrt.write(counterName+":");
			wrt.write(String.valueOf(f.flowGraph().idBound()-1));
			wrt.newLine();
			wrt.close();
			return true;
		} catch (Exception e) {
			System.err.println("CountingInstructionsBB:can't write the function name");
			return false;
		}
	}
	
	/**
	 * Read function lists from a file, 
	 * and count the number of functions and the max number of basic blocks
	 * @param file the file in which function lists are written
	 */
	private void checkFile(File file) {
		try {
			BufferedReader rdr=new BufferedReader(new FileReader(file));
			int tmpbb;
			String line;
			while((line=rdr.readLine())!=null) {
				maxfs++;
				tmpbb=getMaxBb(line);
				maxbb=(tmpbb>maxbb ? tmpbb: maxbb);
			}
		} catch (Exception e) {
			System.err.println("CountingInstructionsOfBB checkFile");
		}
	}
	
	/**
	 * Register "XDEF" symbols to the global Sym Tab
	 * @param file the file in which function lists are written
	 * @param func the current Function
	 */
  private void createNewGlobalvarXdef(File file, Function func) {
    // Define the global var if not exists.
    Symbol sym=f.module.globalSymtab.get(funclistname);
    if(sym==null) {
      try {
        BufferedReader rdr=new BufferedReader(new FileReader(file));
        String line;
        //				int lineno=0;
        // Make an array for each counter. (i.e. <module name>.<function name>)
        ImList datalist=ImList.Empty;
        ImList funclistDataElements=ImList.list(addrTypeStr());
        ImList fnamedatalist=ImList.Empty;
        ImList filelistDataElements=ImList.list(addrTypeStr());
        //        String tmpdir="/tmp";
        while((line=rdr.readLine())!=null) {
          //					lineno++;
          String funcstr=getFuncstr(line);
          String funcstr2=convStr(funcstr);
          String filenamestr=filenamePrefix+funcstr+".cnt";
          String filenamestr2=convStr(filenamestr);
          //int maxbb=getMaxBb(line);
          Symbol funcname=f.module.globalSymtab.get(funcstr2);
          if(funcname==null) {
            funcname=f.module.globalSymtab.addSymbol(funcstr2,
                                                     Storage.STATIC,Type.type(Type.AGGREGATE,maxbb*size*8),4,
                                                     ".data","XDEF",ImList.list("&syminfo",new QuotedString(funcstr2),
                                                                                new QuotedString(getProperModulename(f.module.name)),"1","0"));
            f.module.globalSymtab.addSymbol(filenamestr2,
                                            Storage.STATIC, Type.UNKNOWN, 4, ".text", "XDEF",
                                            ImList.list("&syminfo", new QuotedString(filenamestr2),
                                                        new QuotedString(getProperModulename(f.module.name)), "1", "0"));
            ImList funclistDataElm=ImList.list("STATIC", addrTypeStr(), funcstr2);
            funclistDataElements=funclistDataElements.append(ImList.list(funclistDataElm));
            ImList filelistDataElm=ImList.list("STATIC", addrTypeStr(), filenamestr2);
            filelistDataElements=filelistDataElements.append(ImList.list(filelistDataElm));
            // Make data entry for funcstr
            ImList funcdata=ImList.list(Keyword.DATA, new QuotedString(funcstr2),
                                        ImList.list("SPACE", Integer.toString(maxbb*size)));
            datalist=datalist.append(ImList.list(funcdata));
            // "/tmp/" is the default direcory in Linux/Unix and must be changed in Windows.
            //            ImList fnamedata=ImList.list(Keyword.DATA, new QuotedString(filenamestr2),
            //                                         ImList.list("I8").append(toCharList("/tmp/"+filenamestr)).append(ImList.list("0")));
            ImList fnamedata=ImList.list(Keyword.DATA, new QuotedString(filenamestr2),
                                         ImList.list("I8").append(toCharList(cntpath+fileSeparator+filenamestr)).append(ImList.list("0")));
            fnamedatalist=fnamedatalist.append(ImList.list(fnamedata));
          }
        }
        // Make an array for output files.
        //   (funclistname STATIC Axx 4 ".data" XDEF &syminfo <module name> 1 0)
        funclistSym=f.module.globalSymtab.addSymbol(funclistname, 
                                                    Storage.STATIC, Type.type(Type.AGGREGATE,maxfs*size*8), 4,
                                                    ".data","XDEF", ImList.list("&syminfo",new QuotedString(funclistname),
                                                                                new QuotedString(getProperModulename(f.module.name)),"1","0"));
        // Make data entry for "funclistname"
        //   (Data <funclistname> (I32 .......))
        ImList funclistData= ImList.list(Keyword.DATA,
                                         new QuotedString(funclistname),
                                         funclistDataElements);
        // Make an array for file name list
        //   (filenamelist STATIC Axx 4 ".data" XDEF &syminfo <module name> 1 0)
        filelistSym=f.module.globalSymtab.addSymbol(filenamelist,
                                                    Storage.STATIC, Type.type(Type.AGGREGATE,maxfs*32), 4,".data","XDEF",
                                                    //						ImList.list("&syminfo",new QuotedString(filenamelist),
                                                    //								new QuotedString(f.module.name),"1","0"));
                                                    ImList.Empty);
        ImList filenamelistData=ImList.list(Keyword.DATA,
                                            new QuotedString(filenamelist),
                                            filelistDataElements);
        // Make maxfsSym
        //   ("maxfs" STATIC I32 4 ".data" XDEF &syminfo "maxfs" <module name> 3 0)
        maxfsSym=f.module.globalSymtab.addSymbol("maxfs", Storage.STATIC,
                                                 Type.type(Type.INT, 32),4, ".data", "XDEF", ImList.list("&syminfo", new QuotedString("maxfs"),
                                                                                                         new QuotedString(getProperModulename(f.module.name)), "3", "0"));
        Data maxfsData=new Data(f.module, ImList.list(Keyword.DATA, new QuotedString("maxfs"),
                                                      ImList.list("I32", Integer.toString(maxfs))));
        // Make maxbbSym
        //   ("maxbb" STATIC I32 4 ".data" XDEF &syminfo "maxbb" <module name> 3 0)
        maxbbSym=f.module.globalSymtab.addSymbol("maxbb", Storage.STATIC,
                                                 Type.type(Type.INT, 32),4, ".data", "XDEF", ImList.list("&syminfo", new QuotedString("maxbb"),
                                                                                                         new QuotedString(getProperModulename(f.module.name)), "3", "0"));
        Data maxbbData=new Data(f.module, ImList.list(Keyword.DATA,	new QuotedString("maxbb"),
                                                      ImList.list("I32", Integer.toString(maxbb))));
        try {
          for(ImList p=datalist; !p.atEnd(); p=p.next()) {
            env.module.elements.add(new Data(f.module, (ImList)p.elem()));
          }
          for(ImList p=fnamedatalist; !p.atEnd(); p=p.next()) {
            env.module.elements.add(new Data(f.module, (ImList)p.elem()));
          }
          env.module.elements.add(maxfsData);
          env.module.elements.add(maxbbData);
          env.module.elements.add(new Data(f.module, filenamelistData));
          env.module.elements.add(new Data(f.module,funclistData));
        } catch(Exception e) {
          System.err.println("Syntax error in new Data: "+e);
        }
      } catch (Exception e) {
        System.err.println("CountingInstructionsBB:can't create global vars:"+e);
      }
    }
  }
	
	private String convStr(String str) {
	    StringBuffer buf=new StringBuffer();
	    int lth=str.length();
        for(int i=0; i<lth; i++) {
        	char a=str.charAt(i);
        	if(a=='-') {
        		buf.append("__");
        	} else {
        		buf.append(a);
        	}
        }
        return buf.toString();
	}

  private int addrType() {
    return f.module.targetMachine.typeAddress;
  }

  private String addrTypeStr() {
    return Type.toString(addrType());
  }

	private String getFuncstr(String line) {
		int n=line.indexOf(":");
		if(n<1) {
			System.err.println("CountingInstructionsOfBB getFuncstr : "+line);
		}
		return line.substring(0,n);
	}
	
	private int getMaxBb(String line) {
		int n=line.indexOf(":");
		if(n<1) {
			System.err.println("CountingInstructionsOfBB getMaxBb : "+line);
		}
		return Integer.valueOf(line.substring(n+1));
	}
	
	/**
	 * Register "XREF" symbols to the module.
	 * @param file the file which has function names and basic block numbers
	 * @param func the Function to be registered symbols 
	 * @return
	 */
	private boolean createNewGlobalvarXref(File file, Function func) {
		try {
			BufferedReader rdr=new BufferedReader(new FileReader(file));
			String line;
			while((line=rdr.readLine())!=null) {
				String modpart=getModPart(line);
				if(modpart.intern()==getProperModulename(func.module.name).intern()) {
					String funcstr=convStr(getFuncstr(line));
					int maxbb=getMaxBb(line);
					Symbol funcname=func.module.globalSymtab.get(funcstr);
					if(funcname==null) {
						func.module.globalSymtab.addSymbol(funcstr,
								Storage.STATIC,Type.type(Type.AGGREGATE,maxbb*size*8),4,
								"data","XREF",ImList.list("&syminfo",new QuotedString(funcstr),
                                          new QuotedString(getProperModulename(func.module.name)),"1","0"));
					}
				}
			}
			for(BiLink pp=func.flowGraph().basicBlkList.first(); !pp.atEnd(); pp=pp.next()) {
				BasicBlk blk=(BasicBlk)pp.elem();
				for(BiLink p=blk.instrList().first(); !p.atEnd(); p=p.next()) {
					LirNode inst=(LirNode)p.elem();
					if(isCallExit(inst)) {
						// funclist
						funclistSym=func.module.globalSymtab.get(funclistname);
						if(funclistSym==null) {
							funclistSym=func.module.globalSymtab.addSymbol(funclistname,
									Storage.STATIC, Type.type(Type.AGGREGATE, maxfs*size*8), 4,
									".data", "XREF", ImList.Empty);
						}
						// filelist
						filelistSym=func.module.globalSymtab.get(filenamelist);
						if(filelistSym==null) {
							filelistSym=func.module.globalSymtab.addSymbol(filenamelist,
									Storage.STATIC, Type.type(Type.AGGREGATE, maxfs*32),4,
									".data","XREF",ImList.Empty);
						}
						// maxfsSym
						maxfsSym=func.module.globalSymtab.addSymbol("maxfs",
								Storage.STATIC,Type.type(Type.INT,32), 4,
								".data", "XREF", ImList.list("&syminfo", new QuotedString("maxfs"),
                                             new QuotedString(getProperModulename(func.module.name)), "1", "0"));
						// maxbbSym
						maxbbSym=func.module.globalSymtab.addSymbol("maxbb",
								Storage.STATIC,Type.type(Type.INT,32), 4,
								".data", "XREF", ImList.list("&syminfo", new QuotedString("maxbb"),
                                             new QuotedString(getProperModulename(func.module.name)), "1", "0"));
					}
				}
			}
			if(printRtnValSym==null) {
				printRtnValSym=func.module.globalSymtab.addSymbol("printRtnVal", Storage.STATIC,
						Type.type(Type.INT, 32), 4, ".data", "XREF", ImList.list("&syminfo",
								new QuotedString("printRtnVal"),
                                                                     new QuotedString(getProperModulename(func.module.name)), "3", "0"));
			}
			return true;
		} catch (Exception e) {
			System.err.println("CountingInstructionsBB:can't create global vars");
			return false;
		}
	}
	
	/**
	 * Pickup the module part in the line.
	 * @param line the string to be parsed.
	 * @return return a module part
	 */
	String getModPart(String line) {
		int pos=line.lastIndexOf('.');
		if(pos<1) {
			System.err.println("CountingInstructionsBB:No module part error.");
// throw an exception			
		}
		return line.substring(0,pos);
	}
	
	/**
	 * Check if the module contains the "main" function
	 * @param module the module to be checked
	 * @return return true if the module contains the "man" function
	 */
	boolean hasMain(Module module) {
		for(BiLink p=module.elements.first();!p.atEnd();p=p.next()) {
			if(p.elem() instanceof Function) {
				if(((Function)p.elem()).symbol.name.intern()=="main".intern()) return true;
			}
		}
		return false;
	}

	/**
	 * Make and insert an LIR which represents a counter of instructions.
	 * @param blk the basic block to be inserted the LIR
	 * @param cnt the number of instructions in the blk
	 */
	// Embed counting instructions at the first position of a basic block
	// except the phi-function and the prologue.
    void embedCount(BasicBlk blk, int cnt) {
    	for(BiLink p=blk.instrList().first(); !p.atEnd(); p=p.next()) {
    		LirNode inst=(LirNode)p.elem();
    		if(inst.opCode==Op.PHI || inst.opCode==Op.PROLOGUE) continue;
    		p.addBefore(makeCountInstr(blk,cnt));
    		break;
    	}
    }
    
    /**
     * Make an LIR which represents counting instructions.
     * @param blk the basic block to be inserted the LIR.
     * @param cnt the number of counting to be embedded into the LIR instruction.
     * @return the LIR creaed in this method.
     */
    // make the next LIR:
    // (SET <type>
    //   (MEM <type> (ADD I32 (STATIC I32 <counterName>) (MUL I32 <blk id> (ICONST I32 <size>))))
    //   (ADD <type> (MEM <type> (ADD I32 (STATIC I32 <counterName>) (MUL I32 <blk id> (ICONST I32 4))))
    //     (ICONST <type> <cnt>)))
    // where <type>=<size>*8
    LirNode makeCountInstr(BasicBlk blk,int cnt) {
      Symbol counterSym=f.module.globalSymtab.get(convStr(counterName));
      LirNode funInst=env.lir.symRef(counterSym);
      int type=Type.type(Type.INT,size*8);
      //      int addrtype=Type.type(Type.INT, 32);
      int addrtype=addrType();
      LirNode cntInst=env.lir.iconst(type,cnt);
      LirNode oneInst=env.lir.iconst(addrtype,size);
      LirNode blkInst=env.lir.iconst(addrtype,blk.id-1);
      LirNode mulInst=env.lir.operator(Op.MUL,addrtype,blkInst,oneInst,ImList.Empty);
      LirNode addInst=env.lir.operator(Op.ADD, addrtype,funInst,mulInst,ImList.Empty);
      LirNode tgtInst=env.lir.operator(Op.MEM, type,addInst,ImList.Empty);
      LirNode addInst2=env.lir.operator(Op.ADD, type, tgtInst, cntInst,ImList.Empty);
      LirNode inst=env.lir.operator(Op.SET, type,tgtInst,addInst2,ImList.Empty);
      return inst;
    }
    
    /**
     * Check if a function contains the exit call.
     * @param func the function to be checked.
     * @return the result of the check.
     */
    boolean containsCallExit(Function func) {
    	for(BiLink pp=f.flowGraph().basicBlkList.first(); !pp.atEnd(); pp=pp.next()) {
    		BasicBlk blk=(BasicBlk)pp.elem();
    		for(BiLink p=blk.instrList().first(); !p.atEnd(); p=p.next()) {
    			if(isCallExit((LirNode)p.elem())) return true;    			
    		}
    	}
    	return false;
    }
    
    /**
     * Check if a LIR instruction represents calling exit function.
     * @param instr the LIR instruction to be checked.
     * @return the result  of the check(true or false)
     */
	boolean isCallExit(LirNode instr) {
		if(instr.kid(0) instanceof LirSymRef) {
			return instr.opCode==Op.CALL  &&
				((LirSymRef)instr.kid(0)).symbol.name.intern()=="exit".intern();
		} else {
			return false;
		}
	}
	
	/**
	 * Make an LIR instruction which represents calling the printing function.
	 * @return an LirNode of the printing function
	 */
	// (CALL (STATIC I32 "__cntbb_printCounter")            callee
	//          ((MEM I32 (STATIC I32 "maxfs"))      parameters
	//           (MEM I32 (STATIC I32 "maxbb"))
	//           (STATIC I32 "func_list")
	//           (STATIC I32 "file_list")
	//         ((REG I32 "functionvalue")))              return values
	LirNode makePrintCall() {
		LirNode[] paramsymrefs=new LirNode[4];
	    //paramsymrefs[0]=env.lir.operator(Op.MEM,Type.type(Type.INT, 32),env.lir.symRef(maxfsSym),ImList.Empty);
		//paramsymrefs[1]=env.lir.operator(Op.MEM,Type.type(Type.INT, 32),env.lir.symRef(maxbbSym),ImList.Empty);
		paramsymrefs[0]=env.lir.iconst(Type.type(Type.INT, 32), maxfs);
		paramsymrefs[1]=env.lir.iconst(Type.type(Type.INT, 32), maxbb);
	    paramsymrefs[2]=env.lir.symRef(funclistSym);
	    paramsymrefs[3]=env.lir.symRef(filelistSym);
		LirNode params=env.lir.operator(Op.LIST, Type.UNKNOWN, paramsymrefs, ImList.Empty);
		LirNode rtnsElm=env.lir.operator(Op.MEM,Type.type(Type.INT,32),
				env.lir.symRef(printRtnValSym),
				ImList.Empty);
		LirNode rtns=env.lir.operator(Op.LIST, Type.UNKNOWN, rtnsElm,	null);
		LirNode lir=env.lir.operator(Op.CALL, Type.UNKNOWN, 
				env.lir.symRef(printcallSym),
				params,rtns, ImList.Empty);
		return lir;
	}

	/**
	 * Convert a string into an ImList of chars.
	 * @param s the string to be converted.
	 * @return the ImList of chars
	 */
	private ImList toCharList(String s) {
		char[] charArray=s.toCharArray();
		ImList list= ImList.Empty;
		for(int i=0; i<charArray.length; i++)
			list=list.append(new ImList(Integer.toString(((int) charArray[i]))));
		return list;
	}

	/**
	 * Printing function of the counters.
	 */
	class PrintFunction {
		private int size;
		
		/**
		 * Constructor
		 * @param sz the int size of the counter (bytes) 
		 */
		PrintFunction(int sz) {
			size=sz;
		}
		
		/**
		 * Check whether cntbb is in the ssa options.
		 * If there is, add the printCounter function to the module
		 * which contains the main function.
		 */
		public void chkProfOpt(Module m, CompileSpecification spec, IoRoot io, SsaEnvironment env) {
			String optstr=env.opt.getArg(OptionName.LIR_OPT);
			if(optstr==null) optstr=env.opt.getArg(OptionName.LIR_OPT2);
			if(optstr==null) optstr=env.opt.getArg(OptionName.SSA_OPT);
			BiList opts=parseSsaOpt(optstr);
			BiLink location=opts.locateEqual(OptionName.CNTBB);
			if(location!=null && hasMain(m)) {
				loadSymData(m);
				loadPrintFunction(m);
        //				loadPrintFunctionFromFile(m);
			}
		}
		
		/**
		 * Register symbols of the printing function, fprintf, fopen, fclose.
		 * Register symbols and data of the file open mode, and the print format
		 * @param m the module which the symbols are registered to.
		 */
		private void loadSymData(Module m) {
			if(m.globalSymtab.get(printcallStr)==null)
				m.globalSymtab.addSymbol(printcallStr,Storage.STATIC,Type.UNKNOWN,4,".text",
						"XDEF",ImList.list("&syminfo",new QuotedString(printcallStr),
								new QuotedString(m.name),"1","0"));
			if(m.globalSymtab.get("fprintf")==null)
				m.globalSymtab.addSymbol("fprintf", Storage.STATIC, Type.UNKNOWN, 4, ".text",
						"XREF", ImList.list("&syminfo", new QuotedString("fprintf"), 
								new QuotedString(m.name), "331", "0"));
			if(m.globalSymtab.get("fopen")==null)
				m.globalSymtab.addSymbol("fopen", Storage.STATIC, Type.UNKNOWN, 4, ".text",
						"XREF", ImList.list("&syminfo", new QuotedString("fopen"), 
								new QuotedString(m.name), "249", "0"));
			if(m.globalSymtab.get("fclose")==null)
				m.globalSymtab.addSymbol("fclose", Storage.STATIC, Type.UNKNOWN, 4, ".text",
						"XREF", ImList.list("&syminfo", new QuotedString("fclose"), 
								new QuotedString(m.name), "214", "0"));
			Symbol filemodeSym=m.globalSymtab.get("filemode");
			if(filemodeSym==null) {
				filemodeSym=
					m.globalSymtab.addSymbol("filemode", Storage.STATIC, Type.UNKNOWN, 4, ".text",
							"XREF", ImList.list("&syminfo", new QuotedString("filemode"), 
									new QuotedString(m.name), "0", "0"));
				ImList filemodeList=(new ImList("I8")).append(toCharList("a")).append(new ImList("0"));
				try {
					Data filemodeData=
						new Data(m, ImList.list(Keyword.DATA, new QuotedString("filemode"), filemodeList));
					m.elements.add(filemodeData);
				}
				catch (Exception e) {
					System.err.println("CountingInstructionsOfBB:loadSymData:"+e);
				}
			}
			Symbol printformatSym=m.globalSymtab.get("printformat");
			if(printformatSym==null) {
				m.globalSymtab.addSymbol("printformat", Storage.STATIC, Type.UNKNOWN, 4, ".text",
					"XREF", ImList.list("&syminfo", new QuotedString("printformat"), 
							new QuotedString(m.name), "0", "0"));
				String fmt;
				if(size==8) {
					fmt="%d:%lld\n";
				}
				else {
					fmt="%d:%d\n";
				}
				ImList printformatList=(new ImList("I8")).append(toCharList(fmt)).append(new ImList("0"));
				try {
					Data printformatData=
						new Data(m, ImList.list(Keyword.DATA, new QuotedString("printformat"),	printformatList));
					m.elements.add(printformatData);
				}
				catch (Exception e) {
					System.err.println("CountingInstructionsOfBB:loadSymData:"+e);
				}
			}
		}
			
    //		/**
    //		 * Load the Function definition of printing the counter from the definition file.
    //		 * @param m the module which is added the function
    //		 */
    //		private void loadPrintFunctionFromFile(Module m) {
    //        	final String filename="/home/ojima/COINS/COINS-H21/work/printCounter.lir";
    //          //			final String filename="/home/ojima/COINS/COINS-H21/work/printCounter64.lir";
    //			File file=new File(filename);
    //			try {
    //				BufferedReader rdr=new BufferedReader(new FileReader(file));
    //				Object tmp=ImList.readSexp(rdr);
    //				rdr.close();
    //				if(tmp==null || !(tmp instanceof ImList)) {
    //					throw new SyntaxErrorException("readSexp syntax error");
    //				}
    //				ImList sexp=(ImList)tmp;
    //				m.elements.add(new Function(m, sexp));
    //			}
    //			catch (Exception e) {
    //				System.err.println(e+"::SsaDriver loadPrintFunction:can't open file "+filename);
    //			}
    //		}
		
		/**
		 * Add the Function definition of printing the counters 
		 * @param m the module which is added the function
		 */
		private void loadPrintFunction(Module m) {
      String addrTypeStr=Type.toString(m.targetMachine.typeAddress);
      int sizeByType;

			try {
        if(addrTypeStr.equals("I64")) {
          sizeByType=8;
        } else {
          sizeByType=4;
        }

				String printfunctionStr=
        "(FUNCTION "+"\""+printcallStr+"\""+"    (SYMTAB      (\"maxfs.1\" FRAME I32 4 0 &syminfo \"printCounter_maxfs\" \"Print.c\" 3 0)      (\"maxbbs.2\" FRAME I32 4 0 &syminfo \"printCounter_maxbbs\" \"Print.c\" 3 0)      (\"funclist.3\" FRAME "+addrTypeStr+" 8 0 &syminfo \"printCounter_funclist\" \"Print.c\" 3 0)      (\"filelist.4\" FRAME "+addrTypeStr+" 8 0 &syminfo \"printCounter_filelist\" \"Print.c\" 3 0)      (\"i.5\" FRAME I32 4 0 &syminfo \"printCounter_i\" \"Print.c\" 4 0)      (\"j.6\" FRAME I32 4 0 &syminfo \"printCounter_j\" \"Print.c\" 4 0)      (\"fp.7\" FRAME "+addrTypeStr+" 8 0 &syminfo \"printCounter_fp\" \"Print.c\" 15 0)      (\"functionvalue.9\" FRAME I32 4 0)      (\"functionvalue.11\" FRAME I32 4 0))    (PROLOGUE (0 0) (MEM I32 (FRAME "+addrTypeStr+" \"maxfs.1\")) (MEM I32 (FRAME "+addrTypeStr+" \"maxbbs.2\")) (MEM "+addrTypeStr+" (FRAME "+addrTypeStr+" \"funclist.3\")) (MEM "+addrTypeStr+" (FRAME "+addrTypeStr+" \"filelist.4\")))   (DEFLABEL \"_lab1\")    (SET I32 (MEM I32 (FRAME "+addrTypeStr+" \"i.5\")) (INTCONST I32 0))   (DEFLABEL \"_lab9\")    (JUMPC (TSTLTS I32 (MEM I32 (FRAME "+addrTypeStr+" \"i.5\")) (MEM I32 (FRAME "+addrTypeStr+" \"maxfs.1\"))) (LABEL "+addrTypeStr+" \"_lab10\") (LABEL "+addrTypeStr+" \"_lab4\"))   (DEFLABEL \"_lab10\")    (CALL (STATIC "+addrTypeStr+" \"fopen\") ((MEM "+addrTypeStr+" (ADD "+addrTypeStr+" (MEM "+addrTypeStr+" (FRAME "+addrTypeStr+" \"filelist.4\")) (MUL "+addrTypeStr+" (INTCONST "+addrTypeStr+" "+sizeByType+") (CONVSX "+addrTypeStr+" (MEM I32 (FRAME "+addrTypeStr+" \"i.5\")))))) (STATIC "+addrTypeStr+" \"filemode\")) ((MEM "+addrTypeStr+" (FRAME "+addrTypeStr+" \"fp.7\"))))    (SET I32 (MEM I32 (FRAME "+addrTypeStr+" \"j.6\")) (INTCONST I32 0))   (DEFLABEL \"_lab7\")    (JUMPC (TSTLTS I32 (MEM I32 (FRAME "+addrTypeStr+" \"j.6\")) (MEM I32 (FRAME "+addrTypeStr+" \"maxbbs.2\"))) (LABEL "+addrTypeStr+" \"_lab8\") (LABEL "+addrTypeStr+" \"_lab6\"))   (DEFLABEL \"_lab8\")    (CALL (STATIC "+addrTypeStr+" \"fprintf\") ((MEM "+addrTypeStr+" (FRAME "+addrTypeStr+" \"fp.7\")) (STATIC "+addrTypeStr+" \"printformat\") (MEM I32 (FRAME "+addrTypeStr+" \"j.6\")) (MEM I64 (ADD "+addrTypeStr+" (MEM "+addrTypeStr+" (ADD "+addrTypeStr+" (MEM "+addrTypeStr+" (FRAME "+addrTypeStr+" \"funclist.3\")) (MUL "+addrTypeStr+" (INTCONST "+addrTypeStr+" "+sizeByType+") (CONVSX "+addrTypeStr+" (MEM I32 (FRAME "+addrTypeStr+" \"i.5\")))))) (MUL "+addrTypeStr+" (INTCONST "+addrTypeStr+" 8) (CONVSX "+addrTypeStr+" (MEM I32 (FRAME "+addrTypeStr+" \"j.6\"))))))) ((MEM I32 (FRAME "+addrTypeStr+" \"functionvalue.9\"))))    (SET I32 (MEM I32 (FRAME "+addrTypeStr+" \"j.6\")) (ADD I32 (MEM I32 (FRAME "+addrTypeStr+" \"j.6\")) (INTCONST I32 1)))    (JUMP (LABEL "+addrTypeStr+" \"_lab7\"))   (DEFLABEL \"_lab6\")    (CALL (STATIC "+addrTypeStr+" \"fclose\") ((MEM "+addrTypeStr+" (FRAME "+addrTypeStr+" \"fp.7\"))) ((MEM I32 (FRAME "+addrTypeStr+" \"functionvalue.11\"))))    (SET I32 (MEM I32 (FRAME "+addrTypeStr+" \"i.5\")) (ADD I32 (MEM I32 (FRAME "+addrTypeStr+" \"i.5\")) (INTCONST I32 1)))    (JUMP (LABEL "+addrTypeStr+" \"_lab9\"))   (DEFLABEL \"_lab4\")   (DEFLABEL \"_epilogue\")    (EPILOGUE (0 0))))";
				ImList printfunctionSexp=(ImList)ImList.readSexp(new StringReader(printfunctionStr));
				m.elements.add(new Function(m, printfunctionSexp));
			}
			catch (Exception e) {
				System.err.println(e+" CountingInstructionsOfBB:PrintCounter:loadPrintFunction:can't create Function.");
			}
		}
		
		/**
		 * Parse the ssa-opt
		 * @param optstr the ssa-opt string
		 * @return BiList
		 */
		private BiList parseSsaOpt(String optstr) {
			final int delimiter='/';
			BiList optList=new BiList();
			int beginIndex=0;
			int endIndex=0;
			int length=optstr.length();
			while(endIndex<=length) {
				beginIndex=endIndex;
				endIndex=optstr.indexOf(delimiter, beginIndex);
				if(endIndex==-1) endIndex=length;
				if(endIndex>beginIndex) {
					String opt=optstr.substring(beginIndex, endIndex);
					opt=opt.trim();
					optList.add(opt);
				}
				endIndex++;
			}
			return optList;
		}
	}
	
	/**
	 * Check whether cntbb is in the ssa options.
	 * If there is, add the printCounter function to the module
	 * which contains the main function.
	 */
	public void chkProfOpt(Module m, CompileSpecification spec, IoRoot io, SsaEnvironment env) {
		PrintFunction pf=new PrintFunction(size);
		pf.chkProfOpt(m, spec, io, env);
	}
}
