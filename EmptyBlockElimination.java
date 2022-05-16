/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import java.util.Iterator;


import coins.backend.util.ImList;
import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalAnalyzer;
import coins.backend.util.BiLink;
import coins.backend.cfg.BasicBlk;
import coins.backend.Op;
import coins.backend.lir.LirNode;


/**
* Eliminate the empty basic blocks from the current CFG.
**/
class EmptyBlockElimination implements LocalTransformer {
 public boolean doIt(Data data, ImList args) {
   return true;
 }

 public String name() {
   return "EmptyBlockElimination";
 }

 public String subject() {
   return "Eliminate empty basic blocks on SSA form.";
 }

 /** The environment of the SSA module **/
 private SsaEnvironment env;

 /** The threshold of the debug print **/
 public static final int THR = SsaEnvironment.OptThr;

 /** The current function **/
 private Function f;

 /**
  * Constructor
  * 
  * @param e
  *          The environment of the SSA module
  */
 public EmptyBlockElimination(SsaEnvironment e) {
   env = e;
   env.println("  Eliminate the enpty basic blocks", SsaEnvironment.MsgThr);
 }

 /**
  * Eliminate the empty basic blocks from the current CFG.
  * 
  * @param function
  *          The current function
  * @param args
  *          The list of options
  */
 public boolean doIt(Function function, ImList args) {
   env.println("****************** doing EBE to " + function.symbol.name,
       SsaEnvironment.MinThr);
   f = function;

   for (BiLink p = function.flowGraph().basicBlkList.first(); !p.atEnd(); p = p
       .next()) {
     BasicBlk blk = (BasicBlk) p.elem();
     // The primary method.
     // Eliminate if the basic block is empty, reached from only one
     // predecessor and connect to only one successor.
     if (blk.succList().length() == 1 && blk.predList().length() == 1) {
       // env.output.println("candidate1 "+blk.id);
       BasicBlk pred = (BasicBlk) blk.predList().first().elem();
       BasicBlk succ = (BasicBlk) blk.succList().first().elem();

       // Eliminate the current basic block if the number of the successors of
       // the predecessor of the current basic block is 1, and the number of
       // the predecessors of the successor of the current basic block is 1.
       if (pred.succList().length() == 1 && succ.predList().length() == 1) {
         // env.output.println("candidate2 "+blk.id);

         // Eliminate if the current basic block includes only the JUMP node
         // to the next basic block.
         if (blk.instrList().length() == 1) {
           // env.output.println("candidate3 "+blk.id);
           switch (((LirNode) blk.instrList().first().elem()).opCode) {
           case Op.JUMP: {
             // The number of the predecessors of the successor of the
             // current basic block is 1.
             LirNode predLast = (LirNode) pred.instrList().last().elem();

             // The optimizer keep the current basic block if the last
             // LIR node of the predecessor of the current basic block is
             // not a JUMP node.
             if (predLast.opCode == Op.JUMP) {

               predLast.setKid(0, env.lir.labelRefVariant(succ.label()));

               /*
                * 
                * if some instructions in the success BLK refer the deleted BLK label, rewrite the label with the pred Blk's label
               */
               String node_label = (blk.label()).toString();
               Iterator it = succ.instrList().iterator();
               while (it.hasNext()) {
                 LirNode node = (LirNode) it.next();
                 if (node.opCode != Op.PHI) continue;
                 for (int i = 0; i < node.nKids(); i++) {
                   if (node.kid(1).kid(i) == null) continue;
                   if (node.kid(1).kid(i).toString().indexOf(node_label) >= 0) {
                     node.kid(1).setKid(i, env.lir.labelRefVariant(pred.label()));
                   }
                 }
               }



               pred.maintEdges();
               blk.instrList().clear();
               blk.maintEdges();
               p.unlink();
               env.println("EBE : Redundant blk " + blk.id, THR);
             }
             break;
           }
           }
         }
       }
     }
   }

   env.println("", THR);

   return (true);
 }
}
