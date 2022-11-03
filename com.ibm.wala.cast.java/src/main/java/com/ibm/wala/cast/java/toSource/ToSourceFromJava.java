package com.ibm.wala.cast.java.toSource;

import com.ibm.wala.analysis.typeInference.TypeInference;
import com.ibm.wala.cast.ir.toSource.ToSource;
import com.ibm.wala.cast.java.ssa.AstJavaInstructionVisitor;
import com.ibm.wala.cast.java.ssa.AstJavaInvokeInstruction;
import com.ibm.wala.cast.java.ssa.EnclosingObjectReference;
import com.ibm.wala.ipa.cfg.PrunedCFG;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.util.collections.Pair;
import java.util.Map;
import java.util.Set;

public class ToSourceFromJava extends ToSource {

  @Override
  protected RegionTreeNode makeTreeNode(
      IR ir,
      IClassHierarchy cha,
      TypeInference types,
      PrunedCFG<SSAInstruction, ISSABasicBlock> cfg) {
    class JavaRegionTreeNode extends RegionTreeNode {

      public JavaRegionTreeNode(
          IR ir, IClassHierarchy cha, TypeInference types, SSAInstruction r, ISSABasicBlock l) {
        super(ir, cha, types, r, l);
      }

      public JavaRegionTreeNode(RegionTreeNode parent, SSAInstruction r, ISSABasicBlock l) {
        super(parent, r, l);
      }

      @Override
      protected RegionTreeNode makeChild(Pair<SSAInstruction, ISSABasicBlock> k) {
        return new JavaRegionTreeNode(this, k.fst, k.snd);
      }

      @Override
      protected ToCAst makeToCAst(Set<SSAInstruction> c) {
        return new ToCAst(c, new TypeInferenceContext(types)) {

          class JavaVisitor extends Visitor implements AstJavaInstructionVisitor {

            public JavaVisitor(
                SSAInstruction root,
                TypeInferenceContext c,
                Set<SSAInstruction> chunk,
                Map<SSAInstruction, Map<ISSABasicBlock, RegionTreeNode>> children) {
              super(root, c, chunk, children);
            }

            @Override
            public void visitJavaInvoke(AstJavaInvokeInstruction instruction) {
              visitAbstractInvoke(instruction);
            }

            @Override
            public void visitEnclosingObjectReference(EnclosingObjectReference inst) {
              // TODO Auto-generated method stub

            }
          }

          @Override
          protected Visitor makeVisitor(
              SSAInstruction root, TypeInferenceContext c, Set<SSAInstruction> chunk) {
            return new JavaVisitor(root, c, chunk, children);
          }
        };
      }
    }
    return new JavaRegionTreeNode(
        ir, cha, types, cfg.getNode(1).getLastInstruction(), cfg.getNode(2));
  }
}
