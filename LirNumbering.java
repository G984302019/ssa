/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.Type;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirFactory;
import coins.backend.lir.LirNode;
import coins.backend.sym.Label;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;

/**
 *   Line Number for LirNodes in the flow graph.
 *
 */
public class LirNumbering implements LocalTransformer {

	/** Action modes **/
	public static final int NON_MODE=0;
	public static final int SET_LINE_NUMBER=1;
	public static final int INSERT_LINE_NUMBER=2;
	public static final int REMOVE_LINE_NUMBER=3;
	public static final int SHOW_LINE_NUMBER=4;
	public static final int CLEAR_LINE_NUMBER=5;
	
	public boolean doIt(Data data, ImList args) { return true;	}
	
	/**
	 * Processing of line numbers by an action mode
	 */
	public boolean doIt(Function func, ImList list) {
		if(mode==SET_LINE_NUMBER) {
			numbering();
		}
		else if(mode==INSERT_LINE_NUMBER) {
			insertLineNum();
		}
		else if(mode==REMOVE_LINE_NUMBER) {
			removeLineNum();
		}
		else if(mode==SHOW_LINE_NUMBER) {
			showLineNum();
		}
		else if(mode==CLEAR_LINE_NUMBER) {
			clearLineNum();
		}
		return true;
	}
	public String name() { return "LirNumbering"; }
	public String subject() { return "LirNumbering"; }

	/** Current line number. **/
	private int curLineNum=1;
	/** The current function **/ 
	private Function f;
	private static final String ssaline="SSA_LINE";
	private LirFactory lfact;
	/** Action mode **/
	private int mode;

	/**
	 * Constructor(not used)
	 * @param env The current environment
	 * @param sstab The current SSA symbol table
	 */
	public LirNumbering(SsaEnvironment env, SsaSymTab sstab) {
		// dummy
	}
	/**
	 * Constructor
	 * @param func The current function
	 * @param md The action mode
	 */
	public LirNumbering(Function func, int md) {
		f=func;
		lfact=func.newLir;
		mode=md;
	}
	public LirNumbering(Function func) {
		f=func;
		lfact=func.newLir;
		mode=NON_MODE;;
	}

	/**
	 *  Numbering instructions.
	 */
	public void numbering() {
		for(BiLink bp=f.flowGraph().basicBlkList.first(); !bp.atEnd(); bp=bp.next()) {
			BasicBlk blk=(BasicBlk)bp.elem();
			for(BiLink ip=blk.instrList().first(); !ip.atEnd(); ip=ip.next()) {
				LirNode inst=(LirNode)ip.elem();
				ImList opt=inst.opt;
				ip.setElem(lfact.replaceOptions(inst,	opt.append(ImList.list(ssaline+curLineNum++))));
			}
		}
	}
	
	/**
	 *  Insert "(LINE *)" before each instructions
	 */
	public void insertLineNum() {
		for(BiLink bp=f.flowGraph().basicBlkList.first(); !bp.atEnd(); bp=bp.next()) {
			BasicBlk blk=(BasicBlk)bp.elem();
			for(BiLink ip=blk.instrList().first(); !ip.atEnd(); ip=ip.next()) {
				LirNode inst=(LirNode)ip.elem();
        // for trial 2011.5.10 -- Begin
        if(inst.opCode==Op.PHI) continue;
        // -- End
				int num=pickupLineNumber(inst);
				if(num>0) {
					LirNode lnum=f.newLir.iconst(Type.type(Type.INT,32),num*(-1));
					LirNode lir=f.newLir.operator(Op.LINE, Type.UNKNOWN,lnum,null);
					ip.addBefore(lir);				
				}
			}
		}
	}
	
	/**
	 *  Remove "(LINE *)" from instructions list
	 */
	public void removeLineNum() {
		for(BiLink bp=f.flowGraph().basicBlkList.first(); !bp.atEnd(); bp=bp.next()) {
			BasicBlk blk=(BasicBlk)bp.elem();
			for(BiLink ip=blk.instrList().first(); !ip.atEnd(); ip=ip.next()) {
				LirNode inst=(LirNode)ip.elem();
				if(inst.opCode==Op.LINE) ip.unlink();
			}
		}
	}
	
	/**
	 *  Clear the opt in the LirNodes in the Function
	 */
	public void clearLineNum() {
		for(BiLink bp=f.flowGraph().basicBlkList.first(); !bp.atEnd(); bp=bp.next()) {
			BasicBlk blk=(BasicBlk)bp.elem();
			for(BiLink ip=blk.instrList().first(); !ip.atEnd(); ip=ip.next()) {
				LirNode inst=(LirNode)ip.elem();
				ip.setElem(lfact.replaceOptions(inst,	clearLineNumFromOpt(inst.opt)));
			}
		}
	}
	
	/**
	 * 
	 */
	private ImList clearLineNumFromOpt(ImList opt) {
		ImList list=ImList.Empty;
		for(ImList ls=opt; !ls.atEnd(); ls=ls.next()) {
			Object elm=ls.elem();
			if(elm instanceof String) {
				String str=(String)elm;
				if(((String) elm).startsWith(ssaline)) continue;
			}
			list=new ImList(elm,list);
		}
		return list.destructiveReverse();
	}
	/**
	 *  Print LirNodes in the Function
	 */
	public void showLineNum() {
		System.out.println();
		System.out.println("Function \""+f.symbol.name+"\":");
		for(BiLink bp=f.flowGraph().basicBlkList.first(); !bp.atEnd(); bp=bp.next()) {
			BasicBlk blk=(BasicBlk)bp.elem();
			Label lbl=blk.label();
			System.out.println("Basic block"+lbl.toString()+":");
			for(BiLink ip=blk.instrList().first(); !ip.atEnd(); ip=ip.next()) {
				LirNode inst=(LirNode)ip.elem();
				int num=pickupLineNumber(inst);
				System.out.println("  "+"LINE "+num*(-1)+":"+inst.toString());
			}
		}
	}
		
	/**
	 *  Pick up its line number of an LirNode.
	 *    If the LirNode has no Line number in opt, this method returns 0.
	 * @param instr LirNode
	 * @return Line number holding in opt of the LirNode instr
	 */
	private int pickupLineNumber(LirNode instr) {
		int result=0;
		if(instr.opt.isEmpty()) return result;
		for(ImList ilp=instr.opt; !ilp.atEnd(); ilp=ilp.next()) {
			if(!(ilp.elem() instanceof String)) continue;
			String str=(String)ilp.elem();
			if(str.startsWith(ssaline)) {
				String rest=str.substring(ssaline.length());
				try {
					result=Integer.parseInt(rest);
				}
				catch (NumberFormatException e) {
					System.err.println("LirNumbering: not line number "+ str);
				}
			}		
		}
		return result;
	}
}
