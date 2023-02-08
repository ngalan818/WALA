package com.ibm.wala.cast.ir.toSource;

import static com.ibm.wala.types.TypeReference.Boolean;
import static com.ibm.wala.types.TypeReference.Char;
import static com.ibm.wala.types.TypeReference.Double;
import static com.ibm.wala.types.TypeReference.Float;
import static com.ibm.wala.types.TypeReference.Int;
import static com.ibm.wala.types.TypeReference.Long;
import static com.ibm.wala.types.TypeReference.Void;

import com.ibm.wala.analysis.typeInference.TypeInference;
import com.ibm.wala.cast.ir.ssa.AssignInstruction;
import com.ibm.wala.cast.ir.ssa.AstPreInstructionVisitor;
import com.ibm.wala.cast.ir.ssa.CAstBinaryOp;
import com.ibm.wala.cast.ir.ssa.analysis.LiveAnalysis;
import com.ibm.wala.cast.tree.CAst;
import com.ibm.wala.cast.tree.CAstAnnotation;
import com.ibm.wala.cast.tree.CAstControlFlowMap;
import com.ibm.wala.cast.tree.CAstEntity;
import com.ibm.wala.cast.tree.CAstNode;
import com.ibm.wala.cast.tree.CAstQualifier;
import com.ibm.wala.cast.tree.CAstSourcePositionMap;
import com.ibm.wala.cast.tree.CAstSourcePositionMap.Position;
import com.ibm.wala.cast.tree.CAstType;
import com.ibm.wala.cast.tree.impl.CAstImpl;
import com.ibm.wala.cast.tree.impl.CAstNodeTypeMapRecorder;
import com.ibm.wala.cast.tree.impl.CAstOperator;
import com.ibm.wala.cast.tree.visit.CAstVisitor;
import com.ibm.wala.cast.util.CAstPattern;
import com.ibm.wala.cfg.ControlFlowGraph;
import com.ibm.wala.cfg.Util;
import com.ibm.wala.cfg.cdg.ControlDependenceGraph;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.core.util.strings.Atom;
import com.ibm.wala.ipa.cfg.ExceptionPrunedCFG;
import com.ibm.wala.ipa.cfg.PrunedCFG;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.shrike.shrikeBT.IBinaryOpInstruction;
import com.ibm.wala.shrike.shrikeBT.IBinaryOpInstruction.IOperator;
import com.ibm.wala.shrike.shrikeBT.IConditionalBranchInstruction;
import com.ibm.wala.shrike.shrikeBT.IUnaryOpInstruction;
import com.ibm.wala.shrike.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.DefUse;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSAArrayLengthInstruction;
import com.ibm.wala.ssa.SSAArrayLoadInstruction;
import com.ibm.wala.ssa.SSAArrayStoreInstruction;
import com.ibm.wala.ssa.SSABinaryOpInstruction;
import com.ibm.wala.ssa.SSACheckCastInstruction;
import com.ibm.wala.ssa.SSAComparisonInstruction;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAConversionInstruction;
import com.ibm.wala.ssa.SSAGetCaughtExceptionInstruction;
import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAGotoInstruction;
import com.ibm.wala.ssa.SSAInstanceofInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSALoadMetadataInstruction;
import com.ibm.wala.ssa.SSAMonitorInstruction;
import com.ibm.wala.ssa.SSANewInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SSAPiInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.ssa.SSAReturnInstruction;
import com.ibm.wala.ssa.SSASwitchInstruction;
import com.ibm.wala.ssa.SSAThrowInstruction;
import com.ibm.wala.ssa.SSAUnaryOpInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.EmptyIterator;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.HashSetFactory;
import com.ibm.wala.util.collections.Heap;
import com.ibm.wala.util.collections.NonNullSingletonIterator;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.graph.GraphSlicer;
import com.ibm.wala.util.graph.impl.GraphInverter;
import com.ibm.wala.util.graph.impl.SlowSparseNumberedGraph;
import com.ibm.wala.util.graph.traverse.DFS;
import com.ibm.wala.util.graph.traverse.SCCIterator;
import com.ibm.wala.util.graph.traverse.Topological;
import com.ibm.wala.util.intset.BasicNaturalRelation;
import com.ibm.wala.util.intset.BitVector;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.IntSetUtil;
import com.ibm.wala.util.intset.IntegerUnionFind;
import com.ibm.wala.util.intset.MutableIntSet;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.UTFDataFormatException;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

public class ToSource {

  private static <T> Stream<T> streamify(Iterable<T> stuff) {
    return streamify(stuff.iterator());
  }

  private static <T> Stream<T> streamify(Iterator<T> iterator) {
    return StreamSupport.stream(
        Spliterators.spliteratorUnknownSize(iterator, Spliterator.ORDERED), false);
  }

  private static CAstPattern varDefPattern(String varName) {
    return CAstPattern.parse("DECL_STMT(VAR(\"" + varName + "\"),**)");
  }

  private static CAstPattern varUsePattern(String varName) {
    return CAstPattern.parse("VAR(\"" + varName + "\")");
  }

  private static boolean deemedFunctional(
      SSAInstruction inst, List<SSAInstruction> regionInsts, IClassHierarchy cha) {
    if ((inst instanceof SSABinaryOpInstruction)
        || (inst instanceof SSAUnaryOpInstruction)
        || (inst instanceof SSAComparisonInstruction)
        || (inst instanceof SSAConversionInstruction)) {
      return true;
    } else if (inst instanceof SSAAbstractInvokeInstruction) {
      MethodReference method = ((SSAAbstractInvokeInstruction) inst).getDeclaredTarget();
      TypeReference targetClass = method.getDeclaringClass();
      if (cha.lookupClass(targetClass) != null) {
        targetClass = cha.lookupClass(targetClass).getReference();
      }
      if ((targetClass == TypeReference.JavaLangBoolean)
          || (targetClass == TypeReference.JavaLangByte)
          || (targetClass == TypeReference.JavaLangCharacter)
          || (targetClass == TypeReference.JavaLangInteger)
          || (targetClass == TypeReference.JavaLangFloat)
          || (targetClass == TypeReference.JavaLangDouble)
          || (targetClass == TypeReference.JavaLangMath)
          || (targetClass == TypeReference.JavaLangString)) {
        return true;
      }
    } else if (inst instanceof SSAGetInstruction) {
      FieldReference read = ((SSAGetInstruction) inst).getDeclaredField();
      TypeReference cls = read.getDeclaringClass();
      if (cha.lookupClass(cls) != null) {
        cls = cha.lookupClass(cls).getReference();
      }
      if (((SSAGetInstruction) inst).isStatic() && cls == TypeReference.JavaLangSystem) {
        return true;
      }
      Set<FieldReference> written = HashSetFactory.make();
      regionInsts.forEach(
          i -> {
            if (i instanceof SSAPutInstruction) {
              written.add(((SSAPutInstruction) i).getDeclaredField());
            }
          });
      if (!written.contains(read)) {
        return true;
      }
    }

    return false;
  }

  private static class TreeBuilder {
    private boolean functionalOnly = false;
    private final IClassHierarchy cha;
    private final ControlDependenceGraph<ISSABasicBlock> cdg;
    private final ControlFlowGraph<SSAInstruction, ISSABasicBlock> cfg;

    private TreeBuilder(
        IClassHierarchy cha,
        ControlFlowGraph<SSAInstruction, ISSABasicBlock> cfg,
        ControlDependenceGraph<ISSABasicBlock> cdg) {
      this.cha = cha;
      this.cdg = cdg;
      this.cfg = cfg;
    }

    private void gatherInstructions(
        Set<SSAInstruction> stuff,
        IR ir,
        DefUse du,
        List<SSAInstruction> regionInsts,
        int vn,
        Heap<List<SSAInstruction>> chunks,
        SSAInstruction loopControl,
        int limit,
        IntSet unmergeableValues) {
      SSAInstruction inst = du.getDef(vn);
      if (ir.getSymbolTable().isConstant(vn)) {
        return;
      } else if (vn <= ir.getSymbolTable().getNumberOfParameters()) {
        return;
      } else if (du.getUseCount(vn) != 1) {
        if (loopControl == null) {
          return;
        } else {
          ISSABasicBlock loop = cfg.getBlockForInstruction(loopControl.iIndex());
          ISSABasicBlock me = cfg.getBlockForInstruction(inst.iIndex());
          if (loop != me && !cdg.hasEdge(loop, me)) {
            return;
          }
        }
      }

      assert inst != null;
      if (inst.iIndex() <= limit) {
        gatherInstructions(
            stuff, ir, du, regionInsts, inst, chunks, unmergeableValues, loopControl);
      }
    }

    private void gatherInstructions(
        Set<SSAInstruction> stuff,
        IR ir,
        DefUse du,
        List<SSAInstruction> regionInsts,
        SSAInstruction inst,
        Heap<List<SSAInstruction>> chunks,
        IntSet unmergeableValues,
        SSAInstruction loopControl) {
      if (!stuff.contains(inst) && regionInsts.contains(inst)) {

        boolean depOk = false;
        if (loopControl != null) {
          ISSABasicBlock loop = cfg.getBlockForInstruction(loopControl.iIndex());
          ISSABasicBlock me = cfg.getBlockForInstruction(inst.iIndex());
          if (loop == me || cdg.hasEdge(loop, me)) {
            System.err.println("depOK: " + loop + " " + me);
            depOk = true;
          }
        }

        if (!depOk && !deemedFunctional(inst, regionInsts, cha)) {
          if (loopControl != null || functionalOnly) {
            if (stuff.isEmpty()) {
              stuff.add(inst);
              chunks.insert(new LinkedList<>(stuff));
            }
            return;
          } else {
            functionalOnly = true;
          }
        }

        stuff.add(inst);
        chunks.insert(new LinkedList<>(stuff));
        for (int i = 0; i < inst.getNumberOfUses(); i++) {
          if (!unmergeableValues.contains(inst.getUse(i)) && !(inst instanceof AssignInstruction)) {
            gatherInstructions(
                stuff,
                ir,
                du,
                regionInsts,
                inst.getUse(i),
                chunks,
                loopControl,
                inst.iIndex(),
                unmergeableValues);
          }
        }
      }
    }
  }

  private static <T> Map<T, Integer> computeFinishTimes(
      Supplier<Iterator<T>> entryPoints, Graph<T> ipcfg) {
    int dfsNumber = 0;
    Map<T, Integer> dfsFinish = HashMapFactory.make();
    Iterator<T> search = DFS.iterateFinishTime(ipcfg, entryPoints.get());
    while (search.hasNext()) {
      T n = search.next();
      assert !dfsFinish.containsKey(n) : n;
      dfsFinish.put(n, dfsNumber++);
    }
    return dfsFinish;
  }

  private static <T> Map<T, Integer> computeStartTimes(
      Supplier<Iterator<T>> entryPoints, Graph<T> ipcfg) {
    int reverseDfsNumber = 0;
    Map<T, Integer> dfsStart = HashMapFactory.make();
    Iterator<T> reverseSearch = DFS.iterateDiscoverTime(ipcfg, entryPoints.get());
    while (reverseSearch.hasNext()) {
      dfsStart.put(reverseSearch.next(), reverseDfsNumber++);
    }
    return dfsStart;
  }

  protected static class CodeGenerationContext implements CAstVisitor.Context {
    private final CAstEntity fakeTop =
        new CAstEntity() {

          @Override
          public int getKind() {
            // TODO Auto-generated method stub
            return 0;
          }

          @Override
          public String getName() {
            // TODO Auto-generated method stub
            return null;
          }

          @Override
          public String getSignature() {
            // TODO Auto-generated method stub
            return null;
          }

          @Override
          public String[] getArgumentNames() {
            // TODO Auto-generated method stub
            return null;
          }

          @Override
          public CAstNode[] getArgumentDefaults() {
            // TODO Auto-generated method stub
            return null;
          }

          @Override
          public int getArgumentCount() {
            // TODO Auto-generated method stub
            return 0;
          }

          @Override
          public Map<CAstNode, Collection<CAstEntity>> getAllScopedEntities() {
            // TODO Auto-generated method stub
            return null;
          }

          @Override
          public Iterator<CAstEntity> getScopedEntities(CAstNode construct) {
            return EmptyIterator.instance();
          }

          @Override
          public CAstNode getAST() {
            // TODO Auto-generated method stub
            return null;
          }

          @Override
          public CAstControlFlowMap getControlFlow() {
            // TODO Auto-generated method stub
            return null;
          }

          @Override
          public CAstSourcePositionMap getSourceMap() {
            // TODO Auto-generated method stub
            return null;
          }

          @Override
          public Position getPosition() {
            // TODO Auto-generated method stub
            return null;
          }

          @Override
          public Position getNamePosition() {
            // TODO Auto-generated method stub
            return null;
          }

          @Override
          public Position getPosition(int arg) {
            // TODO Auto-generated method stub
            return null;
          }

          private final CAstNodeTypeMapRecorder types = new CAstNodeTypeMapRecorder();

          @Override
          public CAstNodeTypeMapRecorder getNodeTypeMap() {
            return types;
          }

          @Override
          public Collection<CAstQualifier> getQualifiers() {
            // TODO Auto-generated method stub
            return null;
          }

          @Override
          public CAstType getType() {
            // TODO Auto-generated method stub
            return null;
          }

          @Override
          public Collection<CAstAnnotation> getAnnotations() {
            // TODO Auto-generated method stub
            return null;
          }
        };

    TypeInference getTypes() {
      return types;
    }

    public IntegerUnionFind getMergePhis() {
      return mergePhis;
    }

    private final TypeInference types;
    private final IntegerUnionFind mergePhis;

    public CodeGenerationContext(TypeInference types, IntegerUnionFind mergePhis) {
      this.types = types;
      this.mergePhis = mergePhis;
    }

    @Override
    public CAstEntity top() {
      return fakeTop;
    }

    @Override
    public CAstSourcePositionMap getSourceMap() {
      // TODO Auto-generated method stub
      return null;
    }
  }

  protected static class RegionTreeNode {

    private final IClassHierarchy cha;
    private final TypeInference types;
    private final Map<Set<Pair<SSAInstruction, ISSABasicBlock>>, Set<ISSABasicBlock>> regions;
    private final Map<Pair<SSAInstruction, ISSABasicBlock>, List<SSAInstruction>> linePhis;
    private final Map<Pair<SSAInstruction, ISSABasicBlock>, List<List<SSAInstruction>>>
        regionChunks;
    private final MutableIntSet mergedValues;
    protected final IntegerUnionFind mergePhis;
    private final SymbolTable ST;
    private final DefUse du;
    private final PrunedCFG<SSAInstruction, ISSABasicBlock> cfg;
    private final Set<ISSABasicBlock> loopHeaders;
    private final Set<ISSABasicBlock> loopExits;
    private final Set<ISSABasicBlock> loopControls;
    private final SSAInstruction r;
    private final ISSABasicBlock l;
    private final ControlDependenceGraph<ISSABasicBlock> cdg;
    private BasicNaturalRelation livenessConflicts;
    protected final Map<SSAInstruction, Map<ISSABasicBlock, RegionTreeNode>> children =
        HashMapFactory.make();

    private Pair<BasicNaturalRelation, Iterable<SSAPhiInstruction>> orderPhisAndDetectCycles(
        Iterator<SSAPhiInstruction> blockPhis) {
      Graph<SSAPhiInstruction> G = SlowSparseNumberedGraph.make();
      blockPhis.forEachRemaining(phi -> G.addNode(phi));
      G.iterator()
          .forEachRemaining(
              p -> {
                G.iterator()
                    .forEachRemaining(
                        s -> {
                          for (int i = 0; i < s.getNumberOfUses(); i++) {
                            int d = mergePhis.find(p.getDef());
                            int u = mergePhis.find(s.getUse(i));
                            if (d == u && !G.hasEdge(s, p)) {
                              G.addEdge(s, p);
                            }
                          }
                        });
              });

      BasicNaturalRelation rename = new BasicNaturalRelation();
      System.err.println("phi scc: ------- ");
      new SCCIterator<>(G)
          .forEachRemaining(
              new Consumer<Set<SSAPhiInstruction>>() {
                private int idx = ST.getMaxValueNumber() + 1;

                @Override
                public void accept(Set<SSAPhiInstruction> t) {
                  System.err.println("phi scc: " + t);
                  if (t.size() > 1) {
                    System.err.println(
                        mergePhis.find(t.iterator().next().getDef()) + " --> " + idx);
                    rename.add(mergePhis.find(t.iterator().next().getDef()), idx++);
                  }
                }
              });

      return Pair.make(rename, Topological.makeTopologicalIter(G));
    }

    public RegionTreeNode(RegionTreeNode parent, SSAInstruction r, ISSABasicBlock l) {
      this.r = r;
      this.l = l;
      this.cha = parent.cha;
      this.types = parent.types;
      this.regions = parent.regions;
      this.linePhis = parent.linePhis;
      this.regionChunks = parent.regionChunks;
      this.mergedValues = parent.mergedValues;
      this.mergePhis = parent.mergePhis;
      this.ST = parent.ST;
      this.du = parent.du;
      this.cfg = parent.cfg;
      this.loopHeaders = parent.loopHeaders;
      this.loopExits = parent.loopExits;
      this.loopControls = parent.loopControls;
      this.livenessConflicts = parent.livenessConflicts;
      this.cdg = parent.cdg;
      this.packages = parent.packages;
      initChildren();
      System.err.println("added children for " + r + "," + l + ": " + children);
    }

    private static boolean hasAllByIdentity(List<SSAInstruction> all, List<SSAInstruction> some) {
      return !some.stream()
          .filter(si -> !all.stream().anyMatch(ai -> ai == si))
          .findFirst()
          .isPresent();
    }

    private static void removeAllByIdentity(List<SSAInstruction> all, List<SSAInstruction> some) {
      for (Iterator<SSAInstruction> insts = all.iterator(); insts.hasNext(); ) {
        SSAInstruction inst = insts.next();
        if (some.stream().anyMatch(si -> si == inst)) {
          insts.remove();
        }
      }
    }

    private static int positionByIdentity(List<SSAInstruction> all, SSAInstruction item) {
      for (int i = 0; i < all.size(); i++) {
        if (all.get(i) == item) {
          return i;
        }
      }

      return -1;
    }

    public RegionTreeNode(
        IR ir, IClassHierarchy cha, TypeInference types, SSAInstruction r, ISSABasicBlock l) {
      this.r = r;
      this.l = l;
      this.cha = cha;
      this.types = types;
      du = new DefUse(ir);
      cfg = ExceptionPrunedCFG.makeUncaught(ir.getControlFlowGraph());
      packages = HashMapFactory.make();

      livenessConflicts = new BasicNaturalRelation();
      LiveAnalysis.Result liveness = LiveAnalysis.perform(ir);
      cfg.forEach(
          bb -> {
            List<BiFunction<ISSABasicBlock, Integer, Boolean>> lfs = new LinkedList<>();
            lfs.add(liveness::isLiveEntry);
            lfs.add(liveness::isLiveExit);
            for (BiFunction<ISSABasicBlock, Integer, Boolean> get : lfs) {
              for (int i = 1; i <= ir.getSymbolTable().getMaxValueNumber(); i++) {
                if (get.apply(bb, i)) {
                  for (int j = i + 1; j <= ir.getSymbolTable().getMaxValueNumber(); j++) {
                    if (get.apply(bb, j)) {
                      livenessConflicts.add(i, j);
                      livenessConflicts.add(j, i);
                    }
                  }
                }
              }
            }
            bb.iteratePhis()
                .forEachRemaining(
                    p1 -> {
                      bb.iteratePhis()
                          .forEachRemaining(
                              p2 -> {
                                if (p1 != p2) {
                                  livenessConflicts.add(p1.getDef(), p2.getDef());
                                }
                              });
                    });
          });
      List<Function<Integer, BitVector>> lfs = new LinkedList<>();
      lfs.add(liveness::getLiveBefore);
      // lfs.add(liveness::getLiveAfter);
      for (SSAInstruction inst : ir.getInstructions()) {
        if (inst != null) {
          lfs.forEach(
              f -> {
                BitVector live = f.apply(inst.iIndex());
                int lv = 0;
                while ((lv = live.nextSetBit(lv + 1)) > 0) {
                  int rv = lv + 1;
                  while ((rv = live.nextSetBit(rv + 1)) > 0) {
                    livenessConflicts.add(rv, lv);
                    livenessConflicts.add(lv, rv);
                  }
                }
              });
        }
      }
      System.err.println("liveness conflicts");
      System.err.println(livenessConflicts);
      cdg = new ControlDependenceGraph<>(cfg, true);
      System.err.println(cdg);
      IRToCAst.toCAst(ir)
          .entrySet()
          .forEach(
              e -> {
                System.err.println(e);
              });

      Map<ISSABasicBlock, Integer> cfgFinishTimes =
          computeFinishTimes(() -> NonNullSingletonIterator.make(cfg.entry()), cfg);
      Map<ISSABasicBlock, Integer> cfgStartTimes =
          computeStartTimes(() -> NonNullSingletonIterator.make(cfg.entry()), cfg);

      BiPredicate<ISSABasicBlock, ISSABasicBlock> isBackEdge =
          (pred, succ) ->
              cfgStartTimes.get(pred) >= cfgStartTimes.get(succ)
                  && cfgFinishTimes.get(pred) <= cfgFinishTimes.get(succ);

      loopHeaders =
          cfg.stream()
              .filter(
                  bb -> {
                    Iterator<ISSABasicBlock> ps = cfg.getPredNodes(bb);
                    while (ps.hasNext()) {
                      ISSABasicBlock pred = ps.next();
                      if (isBackEdge.test(pred, bb)) {
                        return true;
                      }
                    }
                    return false;
                  })
              .collect(Collectors.toSet());

      System.err.println("loop headers: " + loopHeaders);

      loopExits = HashSetFactory.make();
      loopControls = HashSetFactory.make();
      Graph<ISSABasicBlock> cfgNoBack = GraphSlicer.prune(cfg, (p, s) -> !isBackEdge.test(p, s));
      cfg.forEach(
          n -> {
            cfg.getPredNodes(n)
                .forEachRemaining(
                    p -> {
                      if (isBackEdge.test(p, n)) {
                        System.err.println("back:" + p + " --> " + n);

                        Set<ISSABasicBlock> forward =
                            DFS.getReachableNodes(cfgNoBack, Collections.singleton(n));
                        Set<ISSABasicBlock> backward =
                            DFS.getReachableNodes(
                                GraphInverter.invert(cfgNoBack), Collections.singleton(p));

                        Set<ISSABasicBlock> loop = HashSetFactory.make(forward);
                        loop.retainAll(backward);

                        System.err.println("loop: " + loop);

                        loop.forEach(
                            bb -> {
                              streamify(cfg.getSuccNodes(bb))
                                  .filter(b -> !loop.contains(b))
                                  .forEach(sb -> loopExits.add(sb));
                            });

                        loopControls.add(
                            loop.stream()
                                .filter(
                                    bb -> {
                                      System.err.println("1: " + bb);
                                      return streamify(cfg.getSuccNodes(bb))
                                          .anyMatch(
                                              b -> {
                                                return !loop.contains(b);
                                              });
                                    })
                                .filter(
                                    bb -> {
                                      System.err.println(
                                          "2: "
                                              + bb
                                              + ": "
                                              + DFS.getReachableNodes(
                                                  GraphSlicer.prune(
                                                      cfgNoBack, (pb, s) -> pb.equals(bb)),
                                                  Collections.singleton(n)));

                                      return n.equals(bb)
                                          || !DFS.getReachableNodes(
                                                  GraphSlicer.prune(
                                                      cfgNoBack, (pb, s) -> pb.equals(bb)),
                                                  Collections.singleton(n))
                                              .contains(p);
                                    })
                                .sorted(
                                    (a, b) -> {
                                      return a.getFirstInstructionIndex()
                                          - b.getFirstInstructionIndex();
                                    })
                                .findFirst()
                                .get());
                      }
                    });
          });

      System.err.println("loop controls: " + loopControls);

      for (ISSABasicBlock b : cfg) {
        if (loopHeaders.contains(b)) {
          System.err.println("bad flow: starting " + b);
          cfg.getPredNodes(b)
              .forEachRemaining(
                  s -> {
                    System.err.println("bad flow: pred " + s);
                    if (isBackEdge.test(s, b)) {
                      System.err.println("bad flow: back edge");
                      int n = Util.whichPred(cfg, s, b);
                      b.iteratePhis()
                          .forEachRemaining(
                              phi -> {
                                System.err.println("bad flow: phi " + phi);
                                int vn = phi.getUse(n);
                                SSAInstruction def = du.getDef(vn);
                                System.err.println("bad flow: def " + def);
                                if (def instanceof SSAPhiInstruction) {
                                  System.err.println("bad flow: " + vn + " --> " + phi.getDef());
                                  for (int i = 0; i < def.getNumberOfUses(); i++) {
                                    livenessConflicts.add(def.getDef(), def.getUse(i));
                                  }
                                }
                              });
                    }
                  });
        }
      }

      ST = ir.getSymbolTable();
      mergedValues = IntSetUtil.make();
      mergePhis = new IntegerUnionFind(ST.getMaxValueNumber());
      ir.getControlFlowGraph()
          .iterator()
          .forEachRemaining(
              bb -> {
                bb.iteratePhis()
                    .forEachRemaining(
                        phi -> {
                          int def = phi.getDef();
                          for (int i = 0; i < phi.getNumberOfUses(); i++) {
                            int use = phi.getUse(i);
                            if (!ST.isConstant(use) && !livenessConflicts.contains(def, use)) {
                              IntSet currentDefConflicts = livenessConflicts.getRelated(def);
                              IntSet currentUseConflicts = livenessConflicts.getRelated(use);
                              currentDefConflicts.foreach(
                                  vn -> {
                                    livenessConflicts.add(mergePhis.find(use), mergePhis.find(vn));
                                    livenessConflicts.add(mergePhis.find(vn), mergePhis.find(use));
                                  });
                              currentUseConflicts.foreach(
                                  vn -> {
                                    livenessConflicts.add(mergePhis.find(def), mergePhis.find(vn));
                                    livenessConflicts.add(mergePhis.find(vn), mergePhis.find(def));
                                  });

                              System.err.println("merging " + def + " and " + use);
                              mergePhis.union(def, use);
                              mergedValues.add(use);
                              mergedValues.add(def);
                            }
                          }
                        });
              });
      regions = HashMapFactory.make();
      linePhis = HashMapFactory.make();
      cdg.forEach(
          node -> {
            Set<Pair<SSAInstruction, ISSABasicBlock>> regionKey = HashSetFactory.make();
            cdg.getPredNodes(node)
                .forEachRemaining(
                    p -> {
                      cdg.getEdgeLabels(p, node)
                          .forEach(
                              lbl -> {
                                if (!(isBackEdge.test(p, node))) {
                                  regionKey.add(
                                      Pair.make(p.getLastInstruction(), (ISSABasicBlock) lbl));
                                }
                              });
                    });

            if (!regions.containsKey(regionKey)) {
              regions.put(regionKey, HashSetFactory.make());
            }
            regions.get(regionKey).add(node);
          });
      regions
          .entrySet()
          .forEach(
              es -> {
                System.err.println("----");
                System.err.println(es.getKey());
                System.err.println(es.getValue());
              });

      MutableIntSet unmergeableValues = IntSetUtil.make();
      regionChunks = HashMapFactory.make();
      regions
          .entrySet()
          .forEach(
              es -> {
                List<SSAInstruction> regionInsts = new LinkedList<>();
                es.getValue().stream()
                    .sorted((a, b) -> a.getLastInstructionIndex() - b.getLastInstructionIndex())
                    .forEach(
                        bb -> {
                          bb.iterator()
                              .forEachRemaining(
                                  inst -> {
                                    if (!(inst instanceof SSAPhiInstruction)) {
                                      regionInsts.add(inst);
                                    }
                                  });
                          cfg.getSuccNodes(bb)
                              .forEachRemaining(
                                  sb -> {
                                    boolean backEdge =
                                        bb.getLastInstructionIndex() >= 0
                                            && sb.getLastInstructionIndex() >= 0
                                            && bb.getLastInstructionIndex()
                                                < sb.getFirstInstructionIndex();
                                    List<SSAInstruction> ii;
                                    if ((Util.endsWithConditionalBranch(cfg, bb)
                                            && (Util.getTakenSuccessor(cfg, bb).equals(sb)
                                                || Util.getNotTakenSuccessor(cfg, bb).equals(bb)))
                                        || (Util.endsWithSwitch(cfg, bb)
                                            && Util.getFallThruBlock(cfg, bb).equals(sb))) {

                                      Pair<SSAInstruction, ISSABasicBlock> lineKey =
                                          Pair.make(bb.getLastInstruction(), sb);
                                      if (!linePhis.containsKey(lineKey)) {
                                        linePhis.put(lineKey, new LinkedList<>());
                                      }
                                      ii = linePhis.get(lineKey);
                                    } else {
                                      ii = regionInsts;
                                    }

                                    Pair<BasicNaturalRelation, Iterable<SSAPhiInstruction>> order =
                                        orderPhisAndDetectCycles(sb.iteratePhis());
                                    System.err.println("order: " + order);

                                    order
                                        .snd
                                        .iterator()
                                        .forEachRemaining(
                                            phi -> {
                                              System.err.println(
                                                  "phi at "
                                                      + bb
                                                      + " with "
                                                      + bb.getLastInstruction()
                                                      + " "
                                                      + cfg.getSuccNodeCount(bb));
                                              int lv = phi.getDef();
                                              int rv = phi.getUse(Util.whichPred(cfg, bb, sb));
                                              if (mergePhis.find(lv) != mergePhis.find(rv)) {
                                                int lh = lv, rh = rv;
                                                if (order.fst.anyRelated(mergePhis.find(rv))) {

                                                  int tmp =
                                                      order
                                                          .fst
                                                          .getRelated(mergePhis.find(rv))
                                                          .intIterator()
                                                          .next();
                                                  ir.getSymbolTable().ensureSymbol(tmp);
                                                  ii.add(
                                                      new AssignInstruction(
                                                          bb.getLastInstructionIndex() + 1,
                                                          tmp,
                                                          mergePhis.find(rv)));

                                                  lh = mergePhis.find(lv);
                                                  rh =
                                                      order
                                                          .fst
                                                          .getRelated(mergePhis.find(rv))
                                                          .intIterator()
                                                          .next();
                                                }
                                                AssignInstruction assign =
                                                    new AssignInstruction(
                                                        bb.getLastInstructionIndex() + 1, lh, rh);
                                                if (backEdge
                                                    && sb.getLastInstruction()
                                                        instanceof
                                                        SSAConditionalBranchInstruction) {
                                                  System.err.println(
                                                      "back edge for "
                                                          + sb.getLastInstructionIndex());
                                                  System.err.println("back edge for " + assign);
                                                  System.err.println(
                                                      "back edge for " + es.getKey());
                                                }
                                                if (Util.endsWithConditionalBranch(cfg, bb)
                                                    && (Util.getTakenSuccessor(cfg, bb).equals(sb)
                                                        || Util.getNotTakenSuccessor(cfg, bb)
                                                            .equals(bb))) {
                                                  System.err.println(
                                                      "found line phi for "
                                                          + bb
                                                          + " to "
                                                          + sb
                                                          + " for "
                                                          + rv
                                                          + " -> "
                                                          + lv);
                                                }

                                                System.err.println("adding " + assign);
                                                ii.add(assign);
                                              }
                                            });
                                  });
                        });

                Heap<List<SSAInstruction>> chunks =
                    new Heap<List<SSAInstruction>>(regionInsts.size()) {
                      @Override
                      protected boolean compareElements(
                          List<SSAInstruction> elt1, List<SSAInstruction> elt2) {
                        return elt1.size() > elt2.size()
                            ? true
                            : elt1.size() < elt2.size()
                                ? false
                                : elt1.toString().compareTo(elt2.toString()) > 0;
                      }
                    };
                System.err.println("insts: " + regionInsts);
                List<SSAInstruction> all = new LinkedList<>(regionInsts);
                regionInsts.forEach(
                    inst -> {
                      Set<SSAInstruction> insts = HashSetFactory.make();
                      (new TreeBuilder(cha, cfg, cdg))
                          .gatherInstructions(
                              insts,
                              ir,
                              du,
                              regionInsts,
                              inst,
                              chunks,
                              unmergeableValues,
                              (inst instanceof SSAConditionalBranchInstruction)
                                      && loopControls.contains(
                                          cfg.getBlockForInstruction(inst.iIndex()))
                                  ? inst
                                  : null);
                      if (insts.isEmpty()) {
                        insts.add(inst);
                      }
                      System.err.println("chunk for " + inst + ": " + insts);
                    });
                System.err.println("chunks: " + chunks);
                while (chunks.size() > 0 && !regionInsts.isEmpty()) {
                  List<SSAInstruction> chunk = chunks.take();
                  System.err.println(
                      "taking "
                          + chunk.stream()
                              .map(i -> i + " " + i.iIndex())
                              .reduce("", (a, b) -> a + ", " + b));
                  if (hasAllByIdentity(regionInsts, chunk)) {
                    removeAllByIdentity(regionInsts, chunk);
                    System.err.println(
                        "using "
                            + chunk.stream()
                                .map(i -> i + " " + i.iIndex())
                                .reduce("", (a, b) -> a + ", " + b));
                    es.getKey()
                        .forEach(
                            p -> {
                              if (!regionChunks.containsKey(p)) {
                                regionChunks.put(p, new LinkedList<>());
                              }
                              regionChunks.get(p).add(chunk);
                            });
                  }
                }

                es.getKey()
                    .forEach(
                        p -> {
                          if (regionChunks.containsKey(p)) {
                            regionChunks
                                .get(p)
                                .sort(
                                    (lc, rc) ->
                                        positionByIdentity(all, lc.iterator().next())
                                            - positionByIdentity(all, rc.iterator().next()));
                          }
                        });

                assert regionInsts.isEmpty() : regionInsts + " remaining, with chunks " + chunks;
              });

      System.err.println("root region chunks: " + regionChunks);

      ir.iterateNormalInstructions()
          .forEachRemaining(
              inst -> {
                if (inst instanceof SSAGotoInstruction) {
                  ISSABasicBlock bb = cfg.getBlockForInstruction(inst.iIndex());
                  if (loopHeaders.containsAll(cfg.getNormalSuccessors(bb))) {
                    System.err.println("loop edge " + inst);
                  } else if (loopExits.containsAll(cfg.getNormalSuccessors(bb))) {
                    System.err.println("break edge " + inst);
                  }
                }
              });

      initChildren();
    }

    private void initChildren() {
      bbs()
          .forEach(
              bb -> {
                regions
                    .entrySet()
                    .forEach(
                        es -> {
                          es.getKey()
                              .forEach(
                                  k -> {
                                    System.err.println(
                                        "checking " + k.fst + " with " + bb.getLastInstruction());
                                    if (k.fst == bb.getLastInstruction()) {
                                      if (!children.containsKey(k.fst)) {
                                        children.put(k.fst, HashMapFactory.make());
                                      }
                                      children.get(k.fst).put(k.snd, makeChild(k));
                                      System.err.println(
                                          "child of "
                                              + k.fst
                                              + " for "
                                              + k.snd
                                              + " is "
                                              + children.get(k.fst).get(k.snd));
                                    }
                                  });
                        });
              });
      System.err.println("children for " + this + ": " + children);
    }

    protected RegionTreeNode makeChild(Pair<SSAInstruction, ISSABasicBlock> k) {
      return new RegionTreeNode(this, k.fst, k.snd);
    }

    Iterable<ISSABasicBlock> bbs() {
      Set<Pair<SSAInstruction, ISSABasicBlock>> key = Collections.singleton(Pair.make(r, l));
      if (regions.containsKey(key)) {
        return regions.get(key);
      } else {
        return Collections.emptySet();
      }
    }

    private static void indent(StringBuffer text, int level) {
      for (int i = 0; i < level; i++) {
        text.append("  ");
      }
    }

    /*
     * private boolean phiChunk(Set<SSAInstruction> insts) { return insts.size()
     * == 1 && insts.iterator().next() instanceof SSAPhiInstruction; }
     */

    private boolean gotoChunk(List<SSAInstruction> insts) {
      return insts.size() == 1 && insts.iterator().next() instanceof SSAGotoInstruction;
    }

    boolean controlOrderedInChunk(SSAInstruction l, SSAInstruction r, List<SSAInstruction> chunk) {
      return !(deemedFunctional(l, chunk, cha) && deemedFunctional(r, chunk, cha))
          && l.iIndex() < r.iIndex();
    }

    /*
     * boolean controlOrderedChunks( List<SSAInstruction> ls,
     * List<SSAInstruction> rs, List<SSAInstruction> insts) { for
     * (SSAInstruction l : ls) { if (!deemedFunctional(l, insts, cha)) { for
     * (SSAInstruction r : rs) { if (!deemedFunctional(r, insts, cha)) { return
     * l.iIndex() < r.iIndex(); } } } } return false; }
     */

    public CAstNode toCAst() {
      CAst ast = new CAstImpl();
      List<CAstNode> elts = new LinkedList<>();
      List<CAstNode> decls = new LinkedList<>();
      List<List<SSAInstruction>> chunks = regionChunks.get(Pair.make(r, l));
      chunks.forEach(
          chunkInsts -> {
            if (!gotoChunk(chunkInsts)) {
              Pair<CAstNode, List<CAstNode>> stuff =
                  makeToCAst(chunkInsts).processChunk(decls, packages);
              elts.add(stuff.fst);
              decls.addAll(stuff.snd);
            }
          });
      chunks.stream()
          .filter(this::gotoChunk)
          .forEach(
              c -> {
                Pair<CAstNode, List<CAstNode>> stuff = makeToCAst(c).processChunk(decls, packages);
                elts.add(stuff.fst);
                decls.addAll(stuff.snd);
              });
      decls.addAll(elts);
      return ast.makeNode(CAstNode.BLOCK_STMT, decls.toArray(new CAstNode[decls.size()]));
    }

    protected ToCAst makeToCAst(List<SSAInstruction> insts) {
      return new ToCAst(insts, new CodeGenerationContext(types, mergePhis));
    }

    private void toString(StringBuffer text, int level) {
      List<List<SSAInstruction>> chunks = regionChunks.get(Pair.make(r, l));
      if (chunks == null) {
        return;
      }
      chunks.forEach(
          insts -> {
            if (!gotoChunk(insts)) {
              insts
                  .iterator()
                  .forEachRemaining(
                      i -> {
                        indent(text, level + 1);
                        text.append(i).append("\n");
                        if (children.containsKey(i)) {
                          children
                              .get(i)
                              .entrySet()
                              .forEach(
                                  ls -> {
                                    indent(text, level + 1);
                                    text.append("---\n");
                                    ls.getValue().toString(text, level + 2);
                                  });
                          indent(text, level + 1);
                          text.append("---\n");
                        }
                      });
            }
          });
      chunks.stream()
          .filter(this::gotoChunk)
          .forEach(
              c -> {
                indent(text, level + 1);
                text.append(c).append("\n");
              });
    }

    @Override
    public String toString() {
      StringBuffer sb = new StringBuffer();
      toString(sb, 0);
      return sb.toString();
    }

    private final CAst ast = new CAstImpl();

    private final Map<String, Set<String>> packages;

    protected class ToCAst {
      private final List<SSAInstruction> chunk;
      private final CodeGenerationContext c;

      protected class Visitor implements AstPreInstructionVisitor {
        private CAstNode node = ast.makeNode(CAstNode.EMPTY);
        private List<SSAInstruction> chunk;
        private Map<SSAInstruction, Map<ISSABasicBlock, RegionTreeNode>> children;
        private SSAInstruction root;
        protected final List<CAstNode> parentDecls;
        private final List<CAstNode> decls = new LinkedList<>();
        private final Map<String, Set<String>> packages;

        public Visitor(
            SSAInstruction root,
            CodeGenerationContext c,
            List<SSAInstruction> chunk2,
            List<CAstNode> parentDecls,
            Map<String, Set<String>> parentPackages,
            Map<SSAInstruction, Map<ISSABasicBlock, RegionTreeNode>> children) {
          this.root = root;
          this.chunk = chunk2;
          this.children = children;
          this.parentDecls = parentDecls;
          this.packages = parentPackages;
          root.visit(this);
          if (root.hasDef()) {
            if (node.getKind() != CAstNode.EMPTY) {
              int def = root.getDef();
              if (mergedValues.contains(mergePhis.find(def))
                  || du.getDef(def) instanceof SSAPhiInstruction) {
                CAstNode val = node;
                node =
                    ast.makeNode(
                        CAstNode.EXPR_STMT,
                        ast.makeNode(
                            CAstNode.ASSIGN,
                            ast.makeNode(
                                CAstNode.VAR, ast.makeConstant("var_" + mergePhis.find(def))),
                            val));
              } else {
                CAstNode val = node;
                CAstType type;
                try {
                  type = toSource(c.getTypes().getType(def).getTypeReference());
                } catch (IndexOutOfBoundsException e) {
                  type = toSource(TypeReference.Int);
                }
                node =
                    ast.makeNode(
                        CAstNode.DECL_STMT,
                        ast.makeNode(CAstNode.VAR, ast.makeConstant("var_" + mergePhis.find(def))),
                        ast.makeConstant(type),
                        val);
              }
            }
          }
        }

        private boolean checkDecls(int def, List<CAstNode> decls) {
          return decls.stream()
              .noneMatch(d -> varDefPattern("var_" + mergePhis.find(def)).match(d, null));
        }

        private boolean checkDecl(int def) {
          return ST.getNumberOfParameters() < def
              && checkDecls(def, decls)
              && checkDecls(def, parentDecls);
        }

        private CAstNode visit(int vn) {
          if (ST.isConstant(vn)) {
            return ast.makeConstant(ST.getConstantValue(vn));
          } else if (ST.getNumberOfParameters() >= vn) {
            if (cfg.getMethod().isStatic()) {
              return ast.makeNode(CAstNode.VAR, ast.makeConstant("var_" + mergePhis.find(vn)));
            } else {
              if (vn == 1) {
                return ast.makeNode(CAstNode.THIS);
              } else {
                return ast.makeNode(
                    CAstNode.VAR, ast.makeConstant("var_" + mergePhis.find(vn - 1)));
              }
            }
          } else {
            SSAInstruction inst = du.getDef(vn);
            if (chunk.contains(inst)) {
              inst.visit(this);
              if (root instanceof SSAConditionalBranchInstruction
                  && loopControls.contains(cfg.getBlockForInstruction(root.iIndex()))
                  && inst.hasDef()
                  && du.getNumberOfUses(vn) > 1) {

                if (checkDecl(mergePhis.find(vn))) {
                  decls.add(
                      ast.makeNode(
                          CAstNode.DECL_STMT,
                          ast.makeNode(CAstNode.VAR, ast.makeConstant("var_" + mergePhis.find(vn))),
                          ast.makeConstant(toSource(c.getTypes().getType(vn).getTypeReference()))));
                }

                return ast.makeNode(
                    CAstNode.BLOCK_EXPR,
                    ast.makeNode(
                        CAstNode.ASSIGN,
                        ast.makeNode(CAstNode.VAR, ast.makeConstant("var_" + mergePhis.find(vn))),
                        node));
              } else {
                return node;
              }
            } else {
              return ast.makeNode(CAstNode.VAR, ast.makeConstant("var_" + mergePhis.find(vn)));
            }
          }
        }

        @Override
        public void visitGoto(SSAGotoInstruction inst) {
          ISSABasicBlock bb = cfg.getBlockForInstruction(inst.iIndex());
          if (loopHeaders.containsAll(cfg.getNormalSuccessors(bb))) {
            // node = ast.makeNode(CAstNode.CONTINUE);
          } else if (loopExits.containsAll(cfg.getNormalSuccessors(bb))) {
            node = ast.makeNode(CAstNode.BLOCK_STMT, ast.makeNode(CAstNode.BREAK));
          } else {
            node = ast.makeNode(CAstNode.BLOCK_STMT, ast.makeNode(CAstNode.GOTO));
          }
        }

        @Override
        public void visitArrayLoad(SSAArrayLoadInstruction instruction) {
          CAstNode array = visit(instruction.getArrayRef());
          CAstNode index = visit(instruction.getIndex());
          CAstNode elt = ast.makeConstant(toSource(instruction.getElementType()));
          node = ast.makeNode(CAstNode.ARRAY_REF, array, elt, index);
        }

        @Override
        public void visitArrayStore(SSAArrayStoreInstruction instruction) {
          CAstNode array = visit(instruction.getArrayRef());
          CAstNode index = visit(instruction.getIndex());
          CAstNode value = visit(instruction.getValue());
          CAstNode elt = ast.makeConstant(toSource(instruction.getElementType()));
          node =
              ast.makeNode(
                  CAstNode.EXPR_STMT,
                  ast.makeNode(
                      CAstNode.ASSIGN, ast.makeNode(CAstNode.ARRAY_REF, array, elt, index), value));
        }

        @Override
        public void visitBinaryOp(SSABinaryOpInstruction instruction) {
          CAstNode left = visit(instruction.getUse(0));
          CAstNode right = visit(instruction.getUse(1));

          CAstOperator op = null;
          IOperator operator = instruction.getOperator();
          if (operator instanceof IBinaryOpInstruction.Operator) {
            switch ((IBinaryOpInstruction.Operator) operator) {
              case ADD:
                op = CAstOperator.OP_ADD;
                break;
              case AND:
                op = CAstOperator.OP_BIT_AND;
                break;
              case DIV:
                op = CAstOperator.OP_DIV;
                break;
              case MUL:
                op = CAstOperator.OP_MUL;
                break;
              case OR:
                op = CAstOperator.OP_BIT_OR;
                break;
              case REM:
                op = CAstOperator.OP_MOD;
                break;
              case SUB:
                op = CAstOperator.OP_SUB;
                break;
              case XOR:
                op = CAstOperator.OP_BIT_XOR;
                break;
              default:
                assert false;
                break;
            }
          } else if (operator instanceof CAstBinaryOp) {
            switch ((CAstBinaryOp) operator) {
              case CONCAT:
                op = CAstOperator.OP_CONCAT;
                break;
              case EQ:
                op = CAstOperator.OP_EQ;
                break;
              case GE:
                op = CAstOperator.OP_GE;
                break;
              case GT:
                op = CAstOperator.OP_GT;
                break;
              case LE:
                op = CAstOperator.OP_LE;
                break;
              case LT:
                op = CAstOperator.OP_LT;
                break;
              case NE:
                op = CAstOperator.OP_NE;
                break;
              case STRICT_EQ:
                op = CAstOperator.OP_EQ;
                break;
              case STRICT_NE:
                op = CAstOperator.OP_NE;
                break;
              default:
                break;
            }
          }

          node = ast.makeNode(CAstNode.BINARY_EXPR, op, left, right);
        }

        @Override
        public void visitUnaryOp(SSAUnaryOpInstruction instruction) {
          CAstNode arg = visit(instruction.getUse(0));

          CAstOperator op = null;
          switch ((IUnaryOpInstruction.Operator) instruction.getOpcode()) {
            case NEG:
              op = CAstOperator.OP_NOT;
              break;
            default:
              assert false;
          }

          node = ast.makeNode(CAstNode.UNARY_EXPR, op, arg);
        }

        @Override
        public void visitConversion(SSAConversionInstruction instruction) {
          CAstNode value = visit(instruction.getUse(0));
          node =
              ast.makeNode(
                  CAstNode.CAST, ast.makeConstant(toSource(instruction.getToType())), value);
        }

        @Override
        public void visitComparison(SSAComparisonInstruction instruction) {
          CAstNode left = visit(instruction.getUse(0));
          CAstNode right = visit(instruction.getUse(1));

          CAstOperator op = null;
          switch (instruction.getOperator()) {
            case CMP:
              op = CAstOperator.OP_EQ;
              break;
            case CMPG:
              op = CAstOperator.OP_GT;
              break;
            case CMPL:
              op = CAstOperator.OP_LT;
              break;
            default:
              assert false;
          }

          node = ast.makeNode(CAstNode.BINARY_EXPR, op, left, right);
        }

        private CAstNode checkLinePhi(
            CAstNode block, SSAInstruction branch, ISSABasicBlock target) {
          Pair<SSAInstruction, ISSABasicBlock> key = Pair.make(branch, target);
          System.err.println(
              "checking for line phi for instruction "
                  + branch
                  + " and target "
                  + target
                  + "in "
                  + linePhis);
          if (linePhis.containsKey(key)) {
            List<SSAInstruction> insts = linePhis.get(key);
            List<CAstNode> lp = handlePhiAssignments(insts);
            if (block != null) {
              lp.add(block);
            }
            return ast.makeNode(CAstNode.BLOCK_STMT, lp.toArray(new CAstNode[lp.size()]));
          } else {
            return block;
          }
        }

        private List<CAstNode> handlePhiAssignments(List<SSAInstruction> insts) {
          List<CAstNode> lp = new LinkedList<>();
          for (SSAInstruction inst : insts) {
            assert inst instanceof AssignInstruction;
            Visitor v =
                makeToCAst(insts)
                    .makeVisitor(inst, c, Collections.singletonList(inst), parentDecls, packages);
            lp.add(
                ast.makeNode(
                    CAstNode.EXPR_STMT,
                    ast.makeNode(
                        CAstNode.ASSIGN, v.visit(inst.getDef()), v.visit(inst.getUse(0)))));
          }
          return lp;
        }

        @Override
        public void visitConditionalBranch(SSAConditionalBranchInstruction instruction) {
          assert children.containsKey(instruction) : "children of " + instruction + ":" + children;

          CAstOperator castOp = null;
          IConditionalBranchInstruction.IOperator op = instruction.getOperator();
          if (op instanceof IConditionalBranchInstruction.Operator) {
            switch ((IConditionalBranchInstruction.Operator) op) {
              case EQ:
                castOp = CAstOperator.OP_EQ;
                break;
              case GE:
                castOp = CAstOperator.OP_GE;
                break;
              case GT:
                castOp = CAstOperator.OP_GT;
                break;
              case LE:
                castOp = CAstOperator.OP_LE;
                break;
              case LT:
                castOp = CAstOperator.OP_LT;
                break;
              case NE:
                castOp = CAstOperator.OP_NE;
                break;
              default:
                assert false;
                break;
            }
          }
          CAstNode test;
          test:
          {
            CAstNode v1 = visit(instruction.getUse(0));
            CAstNode v2 = visit(instruction.getUse(1));
            if (v2.getValue() instanceof Number && ((Number) v2.getValue()).equals(0)) {
              if (castOp == CAstOperator.OP_NE) {
                test = v1;
                break test;
              } else if (castOp == CAstOperator.OP_EQ) {
                test = ast.makeNode(CAstNode.UNARY_EXPR, CAstOperator.OP_NOT, v1);
                break test;
              }
            }
            test = ast.makeNode(CAstNode.BINARY_EXPR, castOp, v1, v2);
          }

          Map<ISSABasicBlock, RegionTreeNode> cc = children.get(instruction);
          ISSABasicBlock branchBB = cfg.getBlockForInstruction(instruction.iIndex());
          if (loopControls.contains(branchBB)) {
            assert cc.size() <= 2;

            ISSABasicBlock body = cfg.getBlockForInstruction(instruction.iIndex() + 1);
            List<List<SSAInstruction>> loopChunks = regionChunks.get(Pair.make(instruction, body));
            RegionTreeNode lr = cc.get(body);
            List<CAstNode> loopBlock = handleBlock(loopChunks, lr);

            node =
                ast.makeNode(
                    CAstNode.LOOP,
                    test,
                    ast.makeNode(
                        CAstNode.BLOCK_STMT, loopBlock.toArray(new CAstNode[loopBlock.size()])));

            ISSABasicBlock next = cfg.getBlockForInstruction(instruction.getTarget());
            node = checkLinePhi(node, instruction, next);

            if (cc.size() > 1) {
              HashMap<ISSABasicBlock, RegionTreeNode> copy = HashMapFactory.make(cc);
              assert copy.remove(body) != null;
              ISSABasicBlock after = copy.keySet().iterator().next();
              assert after != null;

              List<List<SSAInstruction>> afterChunks =
                  regionChunks.get(Pair.make(instruction, after));
              RegionTreeNode ar = cc.get(after);
              List<CAstNode> afterBlock = handleBlock(afterChunks, ar);

              node =
                  ast.makeNode(
                      CAstNode.BLOCK_STMT,
                      node,
                      afterBlock.toArray(new CAstNode[afterBlock.size()]));
            }
          } else {
            List<CAstNode> takenBlock = null;

            ISSABasicBlock notTaken;
            ISSABasicBlock taken = cfg.getBlockForInstruction(instruction.getTarget());
            if (cc.containsKey(taken)) {
              HashMap<ISSABasicBlock, RegionTreeNode> copy = HashMapFactory.make(cc);
              assert copy.remove(taken) != null;
              notTaken = copy.keySet().iterator().next();
              List<List<SSAInstruction>> takenChunks =
                  regionChunks.get(Pair.make(instruction, taken));
              RegionTreeNode tr = cc.get(taken);
              takenBlock = handleBlock(takenChunks, tr);

            } else {
              assert cc.size() == 1;
              notTaken = cc.keySet().iterator().next();
            }
            assert notTaken != null;

            Pair<SSAConditionalBranchInstruction, ISSABasicBlock> notTakenKey =
                Pair.make(instruction, notTaken);
            List<List<SSAInstruction>> notTakenChunks = regionChunks.get(notTakenKey);
            RegionTreeNode fr = cc.get(notTaken);
            List<CAstNode> notTakenBlock = handleBlock(notTakenChunks, fr);

            CAstNode notTakenStmt =
                notTakenBlock.size() == 1
                    ? notTakenBlock.iterator().next()
                    : ast.makeNode(
                        CAstNode.BLOCK_STMT,
                        notTakenBlock.toArray(new CAstNode[notTakenBlock.size()]));

            notTakenStmt = checkLinePhi(notTakenStmt, instruction, notTaken);

            CAstNode takenStmt = null;
            if (takenBlock != null) {
              takenStmt =
                  takenBlock.size() == 1
                      ? takenBlock.iterator().next()
                      : ast.makeNode(
                          CAstNode.BLOCK_STMT, takenBlock.toArray(new CAstNode[takenBlock.size()]));
            }
            takenStmt = checkLinePhi(takenStmt, instruction, taken);

            if (takenStmt != null) {
              node = ast.makeNode(CAstNode.IF_STMT, test, takenStmt, notTakenStmt);
            } else {
              node =
                  ast.makeNode(
                      CAstNode.IF_STMT,
                      ast.makeNode(CAstNode.UNARY_EXPR, CAstOperator.OP_NOT, test),
                      notTakenStmt);
            }
          }
        }

        private List<CAstNode> handleBlock(
            List<List<SSAInstruction>> loopChunks, RegionTreeNode lr) {

          List<Pair<CAstNode, List<CAstNode>>> normalStuff =
              handleInsts(
                  loopChunks, lr, x -> !(x.iterator().next() instanceof SSAGotoInstruction));

          List<Pair<CAstNode, List<CAstNode>>> gotoStuff =
              handleInsts(loopChunks, lr, x -> x.iterator().next() instanceof SSAGotoInstruction);

          List<CAstNode> block = new LinkedList<>();
          normalStuff.forEach(p -> block.addAll(p.snd));
          gotoStuff.forEach(p -> block.addAll(p.snd));
          normalStuff.forEach(p -> block.add(p.fst));
          gotoStuff.forEach(p -> block.add(p.fst));
          System.err.println("final block: " + block);
          return block;
        }

        private List<Pair<CAstNode, List<CAstNode>>> handleInsts(
            List<List<SSAInstruction>> loopChunks,
            RegionTreeNode lr,
            Predicate<? super List<SSAInstruction>> assignFilter) {
          if (loopChunks == null || loopChunks.isEmpty()) {
            return Collections.emptyList();
          } else {
            return streamify(loopChunks)
                .filter(assignFilter)
                .map(c -> lr.makeToCAst(c).processChunk(parentDecls, packages))
                .collect(Collectors.toList());
          }
        }

        @Override
        public void visitSwitch(SSASwitchInstruction instruction) {
          assert children.containsKey(instruction) : "children of " + instruction + ":" + children;

          CAstNode value = visit(instruction.getUse(0));
          List<CAstNode> switchCode = new LinkedList<>();
          Map<ISSABasicBlock, RegionTreeNode> cc = children.get(instruction);
          int[] casesAndLabels = instruction.getCasesAndLabels();
          for (int i = 0; i < casesAndLabels.length - 1; i++) {
            CAstNode caseValue = ast.makeConstant(casesAndLabels[i]);
            i++;
            ISSABasicBlock caseBlock = cfg.getBlockForInstruction(casesAndLabels[i]);
            List<List<SSAInstruction>> labelChunks =
                regionChunks.get(Pair.make(instruction, caseBlock));
            RegionTreeNode fr = cc.get(caseBlock);
            List<CAstNode> labelBlock = handleBlock(labelChunks, fr);
            switchCode.add(
                ast.makeNode(
                    CAstNode.LABEL_STMT,
                    caseValue,
                    ast.makeNode(
                        CAstNode.BLOCK_STMT, labelBlock.toArray(new CAstNode[labelBlock.size()]))));
          }

          assert instruction.getDefault() != -1;
          ISSABasicBlock defaultBlock = cfg.getBlockForInstruction(instruction.getDefault());
          List<List<SSAInstruction>> defaultChunks =
              regionChunks.get(Pair.make(instruction, defaultBlock));
          RegionTreeNode fr = cc.get(defaultBlock);
          List<CAstNode> defaultStuff = handleBlock(defaultChunks, fr);

          node =
              ast.makeNode(
                  CAstNode.SWITCH,
                  value,
                  ast.makeNode(
                      CAstNode.BLOCK_STMT, defaultStuff.toArray(new CAstNode[defaultStuff.size()])),
                  switchCode.toArray(new CAstNode[switchCode.size()]));
        }

        @Override
        public void visitReturn(SSAReturnInstruction instruction) {
          if (!instruction.returnsVoid()) {
            CAstNode arg = visit(instruction.getUse(0));
            node = ast.makeNode(CAstNode.RETURN, arg);
          }
        }

        @Override
        public void visitGet(SSAGetInstruction instruction) {
          node =
              ast.makeNode(
                  CAstNode.OBJECT_REF,
                  instruction.isStatic()
                      ? ast.makeConstant(
                          instruction
                              .getDeclaredField()
                              .getDeclaringClass()
                              .getName()
                              .getClassName())
                      : visit(instruction.getRef()),
                  ast.makeConstant(instruction.getDeclaredField()));
        }

        @Override
        public void visitPut(SSAPutInstruction instruction) {
          if (instruction.isStatic()) {
            node =
                ast.makeNode(
                    CAstNode.EXPR_STMT,
                    ast.makeNode(
                        CAstNode.ASSIGN,
                        ast.makeNode(
                            CAstNode.OBJECT_REF,
                            ast.makeConstant(
                                instruction
                                    .getDeclaredField()
                                    .getDeclaringClass()
                                    .getName()
                                    .getClassName()),
                            ast.makeConstant(instruction.getDeclaredField())),
                        visit(instruction.getVal())));
          } else {
            node =
                ast.makeNode(
                    CAstNode.EXPR_STMT,
                    ast.makeNode(
                        CAstNode.ASSIGN,
                        ast.makeNode(
                            CAstNode.OBJECT_REF,
                            visit(instruction.getRef()),
                            ast.makeConstant(instruction.getDeclaredField())),
                        visit(instruction.getVal())));
          }
        }

        protected void visitAbstractInvoke(SSAAbstractInvokeInstruction inst) {
          CAstNode[] args = new CAstNode[inst.getNumberOfUses() + 2];
          for (int i = 0; i < inst.getNumberOfUses(); i++) {
            args[i + 2] = visit(inst.getUse(i));
          }

          args[0] = ast.makeConstant(inst.getDeclaredTarget());

          if (inst.getCallSite().isStatic() || inst.getDeclaredTarget().isInit()) {
            recordPackage(inst.getDeclaredTarget().getDeclaringClass());
            System.err.println("looking at type " + inst.getDeclaredTarget().getDeclaringClass());
          }

          args[1] = ast.makeConstant(inst.getCallSite().isStatic());

          if (Void.equals(inst.getDeclaredResultType())) {
            node = ast.makeNode(CAstNode.EXPR_STMT, ast.makeNode(CAstNode.CALL, args));
          } else {
            node = ast.makeNode(CAstNode.CALL, args);
          }
        }

        @Override
        public void visitInvoke(SSAInvokeInstruction instruction) {
          visitAbstractInvoke(instruction);
        }

        @Override
        public void visitNew(SSANewInstruction instruction) {
          TypeReference newType = instruction.getConcreteType();
          if (newType.isArrayType()) {
            CAstNode dims[] = new CAstNode[instruction.getNumberOfUses()];

            for (int i = 0; i < instruction.getNumberOfUses(); i++) {
              dims[i] = visit(instruction.getUse(i));
            }

            recordPackage(newType);

            node = ast.makeNode(CAstNode.NEW, ast.makeConstant(newType), dims);
          }
        }

        private void recordPackage(TypeReference newType) {
          String pkg = toPackage(newType);
          if (pkg != null) {
            if (!packages.containsKey(pkg)) {
              packages.put(pkg, HashSetFactory.make());
            }
            packages.get(pkg).add(toSource(newType).getName());
          }
        }

        @Override
        public void visitArrayLength(SSAArrayLengthInstruction instruction) {
          node =
              ast.makeNode(
                  CAstNode.OBJECT_REF,
                  visit(instruction.getArrayRef()),
                  ast.makeConstant("length"));
        }

        @Override
        public void visitThrow(SSAThrowInstruction instruction) {
          node = ast.makeNode(CAstNode.THROW, visit(instruction.getUse(0)));
        }

        @Override
        public void visitMonitor(SSAMonitorInstruction instruction) {
          assert false;
        }

        @Override
        public void visitCheckCast(SSACheckCastInstruction instruction) {
          node =
              ast.makeNode(
                  CAstNode.CAST,
                  ast.makeConstant(toSource(instruction.getDeclaredResultTypes()[0])),
                  visit(instruction.getVal()));
        }

        @Override
        public void visitInstanceof(SSAInstanceofInstruction instruction) {
          node =
              ast.makeNode(
                  CAstNode.INSTANCEOF,
                  ast.makeConstant(instruction.getCheckedType()),
                  visit(instruction.getRef()));
        }

        @Override
        public void visitPhi(SSAPhiInstruction instruction) {
          // assert false;
        }

        @Override
        public void visitPi(SSAPiInstruction instruction) {
          assert false;
        }

        @Override
        public void visitGetCaughtException(SSAGetCaughtExceptionInstruction instruction) {
          assert false;
        }

        @Override
        public void visitLoadMetadata(SSALoadMetadataInstruction instruction) {
          node = ast.makeConstant(instruction.getToken());
        }

        @Override
        public void visitAssign(AssignInstruction inst) {
          node = visit(inst.getUse(0));
        }
      }

      protected Visitor makeVisitor(
          SSAInstruction root,
          CodeGenerationContext c,
          List<SSAInstruction> chunk2,
          List<CAstNode> parentDecls,
          Map<String, Set<String>> packages) {
        return new Visitor(root, c, chunk2, parentDecls, packages, children);
      }

      public ToCAst(List<SSAInstruction> insts, CodeGenerationContext c) {
        this.chunk = insts;
        this.c = c;
      }

      Pair<CAstNode, List<CAstNode>> processChunk(
          List<CAstNode> parentDecls, Map<String, Set<String>> packages) {
        SSAInstruction root = chunk.iterator().next();
        Visitor x = makeVisitor(root, c, chunk, parentDecls, packages);
        return Pair.make(x.node, x.decls);
      }
    }
  }

  static class ToJavaVisitor extends CAstVisitor<CodeGenerationContext> {
    private final IR ir;
    private final int indent;
    private final PrintWriter out;

    private ToJavaVisitor(int indent, IR ir, PrintWriter out) {
      this.ir = ir;
      this.out = out;
      this.indent = indent;
    }

    private void indent() {
      for (int i = 0; i < indent; i++) {
        out.print("  ");
      }
    }

    @Override
    protected boolean visitInclude(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      out.println(
          "import "
              + ((String) n.getChild(0).getValue()).replace('/', '.')
              + "."
              + n.getChild(1).getValue()
              + ";");
      return true;
    }

    @Override
    protected boolean visitSwitch(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      indent();
      out.print("switch (");
      visit(n.getChild(0), c, visitor);
      out.println(") {");

      ToJavaVisitor cv = new ToJavaVisitor(indent + 1, ir, out);
      for (int i = 2; i < n.getChildCount(); i++) {
        CAstNode caseCAst = n.getChild(i);
        cv.indent();
        out.print("case ");
        cv.visit(caseCAst.getChild(0), c, cv);
        out.println(":");
        cv.visit(caseCAst.getChild(1), c, cv);
        cv.indent();
        out.println("break;");
      }

      cv.indent();
      out.println("default:");
      cv.visit(n.getChild(1), c, cv);

      indent();
      out.println("}");

      return true;
    }

    @Override
    protected boolean visitDeclStmt(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      indent();
      out.print(((CAstType) n.getChild(1).getValue()).getName() + " ");
      visit(n.getChild(0), c, visitor);
      if (n.getChildCount() > 2 && n.getChild(2).getKind() != CAstNode.EMPTY) {
        out.print(" = ");
        visit(n.getChild(2), c, visitor);
      }
      out.println(";");
      return true;
    }

    @Override
    protected boolean visitBlockStmt(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      try (ByteArrayOutputStream b = new ByteArrayOutputStream()) {
        try (PrintWriter bw = new PrintWriter(b)) {

          ToJavaVisitor cv = new ToJavaVisitor(indent + 1, ir, bw);
          for (CAstNode child : n.getChildren()) {
            if (child.getKind() != CAstNode.EMPTY) {
              cv.visit(child, c, cv);
            }
          }

          bw.flush();
          String javaText = b.toString();

          if (javaText.length() > 0) {
            indent();
            out.println("{");
            out.println(javaText);
            indent();
            out.println("}");
          }
        }
      } catch (IOException e) {
        assert false : e;
      }
      return true;
    }

    @Override
    protected boolean visitConstant(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      Object v = n.getValue();
      if (v instanceof FieldReference) {
        out.print(((FieldReference) v).getName().toString());
      } else if (v instanceof Character) {
        out.print("'" + v + "'");
      } else if (v instanceof String) {
        out.print('"' + (String) v + '"');
      } else {
        out.print(v);
      }
      return true;
    }

    @Override
    protected boolean visitVar(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      out.print(n.getChild(0).getValue());
      return true;
    }

    @Override
    public boolean visitAssign(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      visit(n.getChild(0), c, visitor);
      out.print(" = ");
      visit(n.getChild(1), c, visitor);
      return true;
    }

    @Override
    protected boolean visitCall(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      MethodReference target = (MethodReference) n.getChild(0).getValue();
      boolean isStatic = ((Boolean) n.getChild(1).getValue()).booleanValue();
      if ("<init>".equals(target.getName().toString())) {
        assert !isStatic;
        Atom type = target.getDeclaringClass().getName().getClassName();
        visit(n.getChild(2), c, this);
        out.print(" = new " + type + "(");
        for (int i = 3; i < n.getChildCount(); i++) {
          if (i != 3) {
            out.print(", ");
          }
          visit(n.getChild(i), c, visitor);
        }
      } else if (isStatic) {
        Atom type = target.getDeclaringClass().getName().getClassName();
        Atom name = target.getName();
        out.print(type + "." + name + "(");
        for (int i = 2; i < n.getChildCount(); i++) {
          if (i != 2) {
            out.print(", ");
          }
          visit(n.getChild(i), c, visitor);
        }
      } else {
        if (n.getChild(2).getKind() != CAstNode.THIS) {
          visit(n.getChild(2), c, this);
          out.print(".");
        }
        out.print(target.getName() + "(");
        for (int i = 3; i < n.getChildCount(); i++) {
          if (i != 3) {
            out.print(", ");
          }
          visit(n.getChild(i), c, visitor);
        }
      }
      out.print(")");
      return true;
    }

    @Override
    protected boolean visitBlockExpr(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      assert n.getChildCount() == 1;
      out.print("(");
      visit(n.getChild(0), c, visitor);
      out.print(")");
      return true;
    }

    @Override
    protected boolean visitExprStmt(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      indent();
      visit(n.getChild(0), c, visitor);
      out.println(";");
      return true;
    }

    @Override
    protected boolean visitLoop(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      ToJavaVisitor cv = new ToJavaVisitor(indent + 1, ir, out);
      indent();
      out.print("while (");
      cv.visit(n.getChild(0), c, cv);
      out.println(")");
      cv.visit(n.getChild(1), c, cv);
      return true;
    }

    @Override
    protected boolean visitIfStmt(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      ToJavaVisitor cv = new ToJavaVisitor(indent + 1, ir, out);
      indent();
      out.print("if (");
      cv.visit(n.getChild(0), c, cv);
      out.println(")");

      try (ByteArrayOutputStream b = new ByteArrayOutputStream()) {
        try (PrintWriter bw = new PrintWriter(b)) {

          ToJavaVisitor cthen = new ToJavaVisitor(indent + 1, ir, bw);
          cthen.visit(n.getChild(1), c, cthen);

          bw.flush();
          String javaText = b.toString();

          if (javaText.length() > 0) {
            out.println(javaText);
          } else {
            indent();
            out.println(" {}");
          }
        }
      } catch (IOException e) {
        assert false : e;
      }

      if (n.getChildCount() > 2) {
        try (ByteArrayOutputStream b = new ByteArrayOutputStream()) {
          try (PrintWriter bw = new PrintWriter(b)) {

            ToJavaVisitor celse = new ToJavaVisitor(indent + 1, ir, bw);
            celse.visit(n.getChild(2), c, celse);

            bw.flush();
            String javaText = b.toString();

            if (javaText.length() > 0) {
              indent();
              out.println("else");
              out.println(javaText);
            }
          }
        } catch (IOException e) {
          assert false : e;
        }
      }
      return true;
    }

    @Override
    public boolean visitNode(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      return true;
    }

    @Override
    protected boolean doVisit(
        CAstNode n, CodeGenerationContext context, CAstVisitor<CodeGenerationContext> visitor) {
      switch (n.getKind()) {
        case CAstNode.BREAK:
          {
            indent();
            out.println("break;");
            return true;
          }
        default:
          break;
      }
      return true;
    }

    @Override
    protected boolean visitReturn(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      indent();
      out.print("return");
      if (n.getChildCount() > 0) {
        out.print(" ");
        visit(n.getChild(0), c, this);
      }
      out.println(";");
      return true;
    }

    @Override
    protected boolean visitBinaryExpr(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      out.print("(");
      visit(n.getChild(1), c, this);
      out.print(" " + n.getChild(0).getValue() + " ");
      visit(n.getChild(2), c, this);
      out.print(")");
      return true;
    }

    @Override
    protected boolean visitUnaryExpr(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      out.print(n.getChild(0).getValue() + " ");
      visit(n.getChild(1), c, this);
      return true;
    }

    @Override
    protected boolean visitCast(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      out.print("(" + ((CAstType) n.getChild(0).getValue()).getName() + ") ");
      visit(n.getChild(1), c, visitor);
      return true;
    }

    @Override
    protected boolean visitArrayRef(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      visit(n.getChild(0), c, visitor);
      out.print("[");
      visit(n.getChild(2), c, visitor);
      out.print("]");
      return true;
    }

    @Override
    protected boolean visitObjectRef(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      visit(n.getChild(0), c, visitor);
      out.print(".");
      if (n.getChild(1).getValue() instanceof String) {
        out.print(n.getChild(1).getValue());
      } else {
        visit(n.getChild(1), c, visitor);
      }
      return true;
    }

    @Override
    protected boolean visitNew(
        CAstNode n, CodeGenerationContext c, CAstVisitor<CodeGenerationContext> visitor) {
      TypeReference type = (TypeReference) n.getChild(0).getValue();
      if (type.isArrayType()) {
        TypeReference eltType = type.getInnermostElementType();
        out.print("new " + toSource(eltType));
        for (int i = 1; i < n.getChildCount(); i++) {
          out.print("[");
          visit(n.getChild(i), c, visitor);
          out.print("]");
        }
        return true;
      } else {
        return super.visitNew(n, c, visitor);
      }
    }
  }

  public void toJava(
      IR ir,
      IClassHierarchy cha,
      TypeInference types,
      PrintWriter out,
      Consumer<CAstNode> includes,
      int level) {
    PrunedCFG<SSAInstruction, ISSABasicBlock> cfg =
        ExceptionPrunedCFG.makeUncaught(ir.getControlFlowGraph());
    System.err.println(ir);

    RegionTreeNode root = makeTreeNode(ir, cha, types, cfg);

    System.err.println("tree");
    System.err.println(root);
    CAstNode ast = root.toCAst();
    System.err.println(ast);

    MutableIntSet done = IntSetUtil.make();

    IMethod m = ir.getMethod();
    if (m.isClinit()) {
      out.println("  static");

    } else {
      out.print("  public ");
      if (m.isStatic()) {
        out.print("static ");
      }
      if (m.isInit()) {
        out.println(m.getDeclaringClass().getName().getClassName() + "(");
      } else {
        out.print(toSource(m.getReturnType()).getName() + " " + m.getName() + "(");
      }
      for (int i = 0; i < m.getReference().getNumberOfParameters(); i++) {
        done.add(root.mergePhis.find(i + 1));
        if (i != 0) {
          out.print(", ");
        }
        out.print(
            toSource(m.getReference().getParameterType(i)).getName()
                + " var_"
                + root.mergePhis.find(i + 1));
      }
      out.print(") ");
      try {
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
      } catch (InvalidClassFileException e) {
        assert false : e;
      }
    }

    CAst cast = new CAstImpl();

    root.packages.forEach(
        (p, cs) -> {
          cs.forEach(
              c -> {
                includes.accept(
                    cast.makeNode(
                        CAstNode.INCLUDE,
                        cast.makeConstant(p.replace('/', '.')),
                        cast.makeConstant(c)));
              });
        });

    List<CAstNode> inits = new LinkedList<>();

    System.err.println("looking at " + ast);

    for (int vn = ir.getSymbolTable().getNumberOfParameters() + 1;
        vn <= ir.getSymbolTable().getMaxValueNumber();
        vn++) {
      if (!done.contains(vn)
          && !CAstPattern.findAll(varUsePattern("var_" + vn), ast).isEmpty()
          && CAstPattern.findAll(varDefPattern("var_" + vn), ast).isEmpty()) {
        System.err.println("found " + vn);
        done.add(vn);
        inits.add(
            cast.makeNode(
                CAstNode.DECL_STMT,
                cast.makeNode(CAstNode.VAR, cast.makeConstant("var_" + vn)),
                cast.makeConstant(toSource(types.getType(vn).getTypeReference()))));
      }
    }

    assert ast.getKind() == CAstNode.BLOCK_STMT;

    for (CAstNode c : ast.getChildren()) {
      inits.add(c);
    }
    ast = cast.makeNode(CAstNode.BLOCK_STMT, inits);

    ToJavaVisitor toJava = new ToJavaVisitor(level, ir, out);
    toJava.visit(ast, new CodeGenerationContext(types, root.mergePhis), toJava);
  }

  protected RegionTreeNode makeTreeNode(
      IR ir,
      IClassHierarchy cha,
      TypeInference types,
      PrunedCFG<SSAInstruction, ISSABasicBlock> cfg) {
    RegionTreeNode root =
        new RegionTreeNode(ir, cha, types, cfg.getNode(1).getLastInstruction(), cfg.getNode(2));
    return root;
  }

  protected static String toPackage(TypeReference type) {
    if (type.isArrayType()) {
      return toPackage(type.getArrayElementType());
    } else if (type.isReferenceType()) {
      try {
        if (type.getName().getPackage() != null) {
          return type.getName().getPackage().toUnicodeString();
        } else {
          return null;
        }
      } catch (UTFDataFormatException e) {
        assert false : e;
        return type.getName().getPackage().toString();
      }
    } else {
      return null;
    }
  }

  protected static CAstType toSource(TypeReference type) {
    if (type.isArrayType()) {
      return new CAstType.Array() {

        @Override
        public Collection<CAstType> getSupertypes() {
          return null;
        }

        @Override
        public String getName() {
          return toSource(type.getArrayElementType()).getName() + "[]";
        }

        @Override
        public int getNumDimensions() {
          CAstType elt = toSource(type.getArrayElementType());
          if (elt instanceof CAstType.Array) {
            return 1 + ((CAstType.Array) elt).getNumDimensions();
          } else {
            return 1;
          }
        }

        @Override
        public CAstType getElementType() {
          return toSource(type.getArrayElementType());
        }

        @Override
        public String toString() {
          return getName();
        }
      };
    } else if (type.isPrimitiveType()) {
      return new CAstType.Primitive() {

        @Override
        public Collection<CAstType> getSupertypes() {
          return null;
        }

        @Override
        public String getName() {
          if (Boolean.equals(type)) {
            return "boolean";
          } else if (Int.equals(type)) {
            return "int";
          } else if (Long.equals(type)) {
            return "long";
          } else if (Float.equals(type)) {
            return "float";
          } else if (Double.equals(type)) {
            return "double";
          } else if (Char.equals(type)) {
            return "char";
          } else if (Void.equals(type)) {
            return "void";
          } else {
            assert false : type;
            return null;
          }
        }

        @Override
        public String toString() {
          return getName();
        }
      };
    } else if (type.isClassType()) {
      return new CAstType.Class() {

        @Override
        public Collection<CAstType> getSupertypes() {
          // TODO Auto-generated method stub
          return null;
        }

        @Override
        public String getName() {
          return type.getName().getClassName().toString();
        }

        @Override
        public boolean isInterface() {
          // TODO Auto-generated method stub
          return false;
        }

        @Override
        public Collection<CAstQualifier> getQualifiers() {
          // TODO Auto-generated method stub
          return null;
        }

        @Override
        public String toString() {
          return getName();
        }
      };
    } else {
      assert false;
      return null;
    }
  }
}
