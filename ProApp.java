/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import java.io.BufferedReader;
import java.io.File;
import java.io.FilenameFilter;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;

/*
 *  The profile of counting instructions
 */
public class ProApp {
  private final char OPTION_INIT='n';
  private final String ACT_INITIALIZE="initialize";
  private final String ACT_TMPDIR="tmpdir";
  private static final String CNTFILE_SUFFIX=".cnt";
  private String prefix="";
  private String winseparator="\\";
  private Hashtable<String,ArrayList<Integer>> profileInfo;
  private String tmpdir="/tmp";
  private String cntdir="/tmp";
  private static String filelistName="file_list.dat";
  private String fileList=tmpdir+"/"+filelistName;
  private ArrayList<String> actions;
  
  /*
   *  Constructor
   */
  public ProApp() throws Exception {
    profileInfo=new Hashtable<String,ArrayList<Integer>>();
    actions=new ArrayList<String>();
  }
  public ProApp(String pre) throws Exception {
	  this();
	  prefix=pre;
  }
  
  /**
   * Main method of ProApp 
   */
public void doIt() throws Exception {
  // Read fileList
  File file=new File(fileList);
  if(!file.exists()) {
    System.err.println("File not exists:"+file.getName());
    throw new Exception("File not exists:"+file.getName());
  }
  try {
    file.createNewFile();
    BufferedReader rdr=new BufferedReader(new FileReader(file));
    String line;
    while((line=rdr.readLine())!=null) {
      String funcstr=getFuncstr(line);
      String separator=File.separator;
      //      if(separator.equals(winseparator)) {
      //        separator=separator+separator;
      //      }
      String filename;
      if(prefix.equals("")) {
        filename=cntdir+separator+funcstr+".cnt";
      } else {
        filename=cntdir+separator+prefix+"."+funcstr+".cnt";
      }
      File infofile=new File(filename);
      int maxbb=getMaxBb(line);
      ArrayList<Integer> cntlist=new ArrayList<Integer>();
      profileInfo.put(filename, cntlist);
      // Retrieve and save cnt infos.
      readCountingInfos(infofile, maxbb, cntlist);
    }
  } catch (Exception e) {
    System.err.println("ProApp:");
    throw new Exception("ProApp.doIt(): "+e);
  }
}
  
  /**
   *  Read instrucsion counts for each basic blocks.
   * @param file The file in which instructions counts for each basic blocks are written.
   * @param maxbb The max number of basic blocks
   * @param cnts An array list of instructions counts
   */
    private void readCountingInfos(File file, int maxbb, ArrayList<Integer> cnts) throws Exception {
    	if(!file.exists()) {
    		System.err.println("File not exists: "+file.getName());
    		throw new Exception("File not exists: "+file.getName());
    	}
    	try {
    		file.createNewFile();
    		BufferedReader rdr=new BufferedReader(new FileReader(file));
    		String line;
            for(int n=0; n<maxbb; n++) {
            	if((line=rdr.readLine())!=null) {
            		int cnt=getCnt(line);
            		cnts.add(cnt);
            	}
            }
    	} catch (Exception e) {
    		System.err.println("ProApp.readCountinginfs:");
    		throw new Exception("ProApp.readCountinginfos: "+e);
    	}
    }
    
    /**
     * Pick up the file name part from a line
     * @param line The string of a file name and a maximu number of blocks 
     * @return The file name part
     */
	private String getFuncstr(String line) {
		int n=line.indexOf(":");
		if(n<1) {
			System.err.println("CountingInstructionsOfBB getFuncstr : "+line);
		}
		return line.substring(0,n);
	}
	
	/**
	 * Pick up the maximum number of basic blocks from a line
	 * @param line The string of a file name and a maximum number of basic blocks
	 * @return The maximum number of basic blocks
	 */
	private int getMaxBb(String line) {
		int n=line.indexOf(":");
		if(n<1) {
			System.err.println("CountingInstructionsOfBB getMaxBb : "+line);
		}
		return Integer.valueOf(line.substring(n+1));
	}

  //	/**
  //	 * Pick up the basic block number part of a line
  //	 * @param line The string of a pair of a basic block number and an instructions count
  //	 * @return The basic block number
  //	 */
  //	private int getBlknum(String line) {
  //		int n=line.indexOf(":");
  //		if(n<1) {
  //			System.err.println("ProApp getBlknum : "+line);
  //			return 0;
  //		}
  //		return Integer.valueOf(line.substring(0,n));
  //	}

	/**
	 * Pick up the instructions count part of a line
	 * @param line The string of a pair of a basic block number and an instructions count
	 * @return The instructions count
	 */
	private int getCnt(String line) {
		int n=line.indexOf(":");
		if(n<1) {
			System.err.println("ProApp getCnt : "+line);
			return 0;
		}
		return Integer.valueOf(line.substring(n+1));
	}
	
	/**
	 *  Pick up the instructions count of a basic block
	 * @param modPlusFunc <module name>.<function name>
	 * @param blkNum The number of the basic block
	 * @return The instructions count
	 */
	public int get(String modPlusFunc, int blkNum) {
		ArrayList<Integer> cnts=profileInfo.get(modPlusFunc);
		return cnts.get(blkNum);
	}

  private void initWorkData() throws Exception {
    // Remove "/tmp/file_list.dat"
    File file=new File(fileList);
    if(file.canWrite()) {
      file.delete();
      System.out.println(fileList+": deleted");
    }
    // Remove "/tmp/*.cnt"
    File dir=new File(cntdir);
    if(dir.isDirectory() && dir.canWrite()) {
      /*
      File[] cntfilelist=dir.listFiles();
      for(int i=0; i<cntfilelist.length; i++) {
        if(cntfilelist[i].getName().endsWith(CNTFILE_SUFFIX)) {
          cntfilelist[i].delete();
          System.out.println(cntfilelist[i].getName()+": deleted");
        }
      }
      */
      CntFilenameFilter fnamefilter=new CntFilenameFilter();
      File[] cntfilelist=dir.listFiles(fnamefilter);
      for(int i=0; i<cntfilelist.length; i++) {
        cntfilelist[i].delete();
        System.out.println(cntfilelist[i].getName()+": deleted");
      }
    }
  }

  private void decodeArgs(String[] args) {
    int i=0;
    while(i<args.length) {
      String str=args[i];
      if(str.charAt(0)=='-') {
        if(str.charAt(1)==OPTION_INIT) {
          actions.add(ACT_INITIALIZE);
        }
        if(str.charAt(1)=='p') {
          i++;
          prefix=args[i];
        }
        if(str.charAt(1)=='t') {
          i++;
          tmpdir=args[i];
          cntdir=tmpdir;
          actions.add(0, ACT_TMPDIR);
        }
        //        if(str.charAt(1)=='c') {
        //          i++;
        //          cntdir=args[i];
        //        }
      }
      i++;
    }
  }

  private void doOpt() throws Exception {
    for(int i=0; i<actions.size(); i++) {
      String act=actions.get(i);
      if(act.equals(ACT_INITIALIZE)) {
        initWorkData();
        throw new Exception("initialized");
      }
      if(act.equals(ACT_TMPDIR)) {
        String separator=File.separator;
        if(separator.equals(winseparator)) {
          separator=separator+separator;
        }
        fileList=tmpdir+separator+filelistName;
      }
    }
  }

  private void print() {
    // Print the numbers of executed LIRs for each basic blocks.
    for(Enumeration<String> keys=profileInfo.keys(); keys.hasMoreElements(); ) {
      // Print "<module name>.<function name>.cnt".
      String k=keys.nextElement();
      System.out.println(k+":");
      ArrayList<Integer> cnts=profileInfo.get(k);
      // Print the total number of the executed LIRs in the k.
      int total=0;
      for(int n=0; n<cnts.size(); n++) {
        total=total+cnts.get(n);
      }
      System.out.println("total: " + total);
      int cnt=0;
      int n1;
      for(int n=0; n<cnts.size(); n++) {
        // Print <the basic block number>:<the number of the executed LIR>
        // The basic block number starts from 1.
        cnt=cnts.get(n);
        if(cnt !=0) {
          n1=n+1;
          System.out.println(n1 + ":" +cnt);
        }
      }
    }
  }

  /**
   * Test method
   * @param args
   */
  public static void main(String[] args) {
    try {
      ProApp pa=new ProApp();
      pa.decodeArgs(args);
      pa.doOpt();
      pa.doIt();
      pa.print();
    } catch (Exception e) {
      System.out.println("ProApp:"+e);
      return;
    }
  }

  class CntFilenameFilter implements FilenameFilter {
    public boolean accept(File dir, String name) {
      return name.endsWith(CNTFILE_SUFFIX);
    }
  }
}
