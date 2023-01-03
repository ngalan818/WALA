package com.ibm.wala.cast.java.toSource;

import com.ibm.wala.analysis.typeInference.TypeInference;
import com.ibm.wala.cast.ir.toSource.ToSource;
import com.ibm.wala.cast.java.analysis.typeInference.AstJavaTypeInference;
import com.ibm.wala.cast.java.ssa.AstJavaInstructionVisitor;
import com.ibm.wala.cast.java.ssa.AstJavaInvokeInstruction;
import com.ibm.wala.cast.java.ssa.EnclosingObjectReference;
import com.ibm.wala.cast.loader.AstClass;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.cfg.PrunedCFG;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.shrike.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Pair;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

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

  public Set<File> toJava(CallGraph cg, File outDir, Predicate<CGNode> filter) {
    Map<IMethod, IR> code = HashMapFactory.make();
    cg.forEach(
        n -> {
          if (filter.test(n)) {
            code.put(n.getMethod(), n.getIR());
          }
        });

    Set<File> files = HashSetFactory.make();
    for (IClass cls : cg.getClassHierarchy()) {
      if (cls instanceof AstClass) {
        String clsName = cls.getName().toString().substring(1);
        File f = new File(outDir, clsName + ".java");
        try (PrintWriter out = new PrintWriter(new FileWriter(f))) {
          out.println("import java.io.*;");
          out.println("import java.util.*;");
          out.println("public class " + clsName + " {");
          for (IField fr : cls.getDeclaredInstanceFields()) {
            out.println(toSource(fr.getFieldTypeReference()).getName() + " " + fr.getName() + ";");
          }
          for (IMethod m : cls.getDeclaredMethods()) {
            if (code.containsKey(m)) {
              IR ir = code.get(m);
              out.print("  public ");
              if (m.isStatic()) {
                out.print("static ");
              }
              out.print(toSource(m.getReturnType()).getName() + " " + m.getName() + "(");
              for (int i = 0; i < m.getReference().getNumberOfParameters(); i++) {
                if (i != 0) {
                  out.print(", ");
                }
                out.print(
                    toSource(m.getReference().getParameterType(i)).getName() + " var_" + (i + 1));
              }
              out.print(") ");
              TypeReference[] exceptions = m.getDeclaredExceptions();
              if (exceptions != null && exceptions.length > 0) {
                boolean first = true;
                for (TypeReference e : exceptions) {
                  if (first) {
                    first = false;
                    out.print(" throws ");
                  } else {
                    out.print(", ");
                  }
                  out.print(e.getName().getClassName());
                }
              }
              AstJavaTypeInference types = new AstJavaTypeInference(ir, true);
              types.solve();
              toJava(ir, cg.getClassHierarchy(), types, out, 1);
            }
          }
          out.println("}");
          files.add(f);
        } catch (IOException | UnsupportedOperationException | InvalidClassFileException e) {
          assert false : e;
        }
      }
    }
    return files;
  }
}
