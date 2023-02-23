package com.ibm.wala.cast.java.translator.jdt.ecj;

import com.ibm.wala.cast.java.translator.Java2IRTranslator;
import com.ibm.wala.cast.java.translator.SourceModuleTranslator;
import com.ibm.wala.cast.java.translator.jdt.JDTJava2CAstTranslator;
import com.ibm.wala.cast.tree.CAstSourcePositionMap.Position;
import com.ibm.wala.classLoader.ModuleEntry;
import com.ibm.wala.core.util.warnings.Warning;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import java.util.Map;
import java.util.Set;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.FileASTRequestor;

public class ECJSourceModuleTranslator extends ECJSourceModuleProcessor
    implements SourceModuleTranslator {

  protected ECJSourceLoaderImpl sourceLoader;

  private final class ECJAstToIR extends FileASTRequestor {
    private final Map<String, ModuleEntry> sourceMap;

    public ECJAstToIR(Map<String, ModuleEntry> sourceMap) {
      this.sourceMap = sourceMap;
    }

    @Override
    public void acceptAST(String source, CompilationUnit ast) {
      JDTJava2CAstTranslator<Position> jdt2cast = makeCAstTranslator(ast, source);
      final Java2IRTranslator java2ir = makeIRTranslator();
      java2ir.translate(sourceMap.get(source), jdt2cast.translateToCAst());

      IProblem[] problems = ast.getProblems();
      int length = problems.length;
      if (length > 0) {
        for (IProblem problem : problems) {
          sourceLoader.addMessage(
              sourceMap.get(source),
              new Warning() {
                {
                  setLevel(
                      problem.isError()
                          ? Warning.SEVERE
                          : problem.isWarning() ? Warning.MODERATE : Warning.MILD);
                }

                @Override
                public String getMsg() {
                  return problem.getMessage();
                }
              });
        }

        if (!"true".equals(System.getProperty("wala.jdt.quiet"))) {
          StringBuilder buffer = new StringBuilder();
          for (IProblem problem : problems) {
            buffer.append(problem.getMessage());
            buffer.append('\n');
          }
        }
      }
    }
  }

  public ECJSourceModuleTranslator(AnalysisScope scope, ECJSourceLoaderImpl sourceLoader) {
    this(scope, sourceLoader, false);
  }

  public ECJSourceModuleTranslator(
      AnalysisScope scope, ECJSourceLoaderImpl sourceLoader, boolean dump) {
    super(scope, sourceLoader.getReference(), dump);
    this.sourceLoader = sourceLoader;
  }

  @Override
  public void loadAllSources(Set<ModuleEntry> modules) {
    loadAllSources(modules, (sourceMap) -> new ECJAstToIR(sourceMap));
  }

  protected Java2IRTranslator makeIRTranslator() {
    return new Java2IRTranslator(sourceLoader, exclusions);
  }
}
