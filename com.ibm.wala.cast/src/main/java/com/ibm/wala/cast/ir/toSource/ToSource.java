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
import com.ibm.wala.cfg.Util;
import com.ibm.wala.cfg.cdg.ControlDependenceGraph;
import com.ibm.wala.core.util.strings.Atom;
import com.ibm.wala.ipa.cfg.ExceptionPrunedCFG;
import com.ibm.wala.ipa.cfg.PrunedCFG;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.shrike.shrikeBT.IBinaryOpInstruction;
import com.ibm.wala.shrike.shrikeBT.IBinaryOpInstruction.IOperator;
import com.ibm.wala.shrike.shrikeBT.IConditionalBranchInstruction;
import com.ibm.wala.shrike.shrikeBT.IUnaryOpInstruction;
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
import com.ibm.wala.util.collections.ReverseIterator;
import com.ibm.wala.util.graph.AbstractGraph;
import com.ibm.wala.util.graph.EdgeManager;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.graph.NodeManager;
import com.ibm.wala.util.graph.traverse.DFS;
import com.ibm.wala.util.graph.traverse.Topological;
import com.ibm.wala.util.intset.BitVector;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.intset.IntSetUtil;
import com.ibm.wala.util.intset.IntegerUnionFind;
import com.ibm.wala.util.intset.MutableIntSet;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

public class ToSource {

  static MutableIntSet xSet(
      SSAInstruction inst,
      Function<SSAInstruction, Integer> count,
      BiFunction<SSAInstruction, Integer, Integer> elt) {
    MutableIntSet xu = IntSetUtil.make();
    for (int i = 0; i < count.apply(inst); i++) {
      xu.add(elt.apply(inst, i));
    }

    return xu;
  }

  static MutableIntSet xSet(
      Set<SSAInstruction> insts,
      Function<SSAInstruction, Integer> count,
      BiFunction<SSAInstruction, Integer, Integer> elt) {
    MutableIntSet xu = IntSetUtil.make();
    for (SSAInstruction inst : insts) {
      xu.addAll(xSet(inst, count, elt));
    }
    return xu;
  }

  static MutableIntSet useSet(SSAInstruction inst) {
    return xSet(inst, SSAInstruction::getNumberOfUses, SSAInstruction::getUse);
  }

  static MutableIntSet defSet(SSAInstruction inst) {
    return xSet(inst, SSAInstruction::getNumberOfDefs, SSAInstruction::getDef);
  }

  static MutableIntSet usesSet(Set<SSAInstruction> inst) {
    return xSet(inst, SSAInstruction::getNumberOfUses, SSAInstruction::getUse);
  }

  static MutableIntSet defsSet(Set<SSAInstruction> inst) {
    return xSet(inst, SSAInstruction::getNumberOfDefs, SSAInstruction::getDef);
  }

  private static boolean deemedFunctional(
      SSAInstruction inst, Set<SSAInstruction> regionInsts, IClassHierarchy cha) {
    if ((inst instanceof SSABinaryOpInstruction)
        || (inst instanceof SSAUnaryOpInstruction)
        || (inst instanceof SSAComparisonInstruction)
        || (inst instanceof SSAConversionInstruction)) {
      return true;
    } else if (inst instanceof SSAAbstractInvokeInstruction) {
      TypeReference targetClass =
          ((SSAAbstractInvokeInstruction) inst).getDeclaredTarget().getDeclaringClass();
      targetClass = cha.lookupClass(targetClass).getReference();
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
      // cls = cha.lookupClass(cls).getReference();
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

    TreeBuilder(IClassHierarchy cha) {
      this.cha = cha;
    }

    void gatherInstructions(
        Set<SSAInstruction> stuff,
        IR ir,
        DefUse du,
        Set<SSAInstruction> regionInsts,
        int vn,
        Heap<Set<SSAInstruction>> chunks) {
      if (ir.getSymbolTable().isConstant(vn)) {
        return;
      } else if (vn <= ir.getSymbolTable().getNumberOfParameters()) {
        return;
      } else if (du.getUseCount(vn) != 1) {
        return;
      } else {
        SSAInstruction inst = du.getDef(vn);
        assert inst != null;
        gatherInstructions(stuff, ir, du, regionInsts, inst, chunks);
      }
    }

    void gatherInstructions(
        Set<SSAInstruction> stuff,
        IR ir,
        DefUse du,
        Set<SSAInstruction> regionInsts,
        SSAInstruction inst,
        Heap<Set<SSAInstruction>> chunks) {
      if (!stuff.contains(inst) && regionInsts.contains(inst)) {
        if (!deemedFunctional(inst, regionInsts, cha)) {
          if (functionalOnly) {
            return;
          } else {
            functionalOnly = true;
          }
        }
        stuff.add(inst);
        chunks.insert(HashSetFactory.make(stuff));
        for (int i = 0; i < inst.getNumberOfUses(); i++) {
          gatherInstructions(stuff, ir, du, regionInsts, inst.getUse(i), chunks);
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

  protected static class TypeInferenceContext implements CAstVisitor.Context {

    private final TypeInference types;

    public TypeInferenceContext(TypeInference types) {
      this.types = types;
    }

    @Override
    public CAstEntity top() {
      return new CAstEntity() {

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
    }

    @Override
    public CAstSourcePositionMap getSourceMap() {
      // TODO Auto-generated method stub
      return null;
    }

    TypeInference getTypes() {
      return types;
    }
  }

  protected static class RegionTreeNode {

    <T> Iterable<T> orderByInsts(
        Set<T> chunks, Function<T, IntSet> defSet, Function<T, IntSet> useSet) {
      return orderByInsts(chunks, defSet, useSet, (l, r) -> false);
    }

    <T> Iterable<T> orderByInsts(
        Set<T> chunks,
        Function<T, IntSet> defSet,
        Function<T, IntSet> useSet,
        BiPredicate<T, T> cfg) {
      if (chunks == null) {
        return Collections.emptyList();
      }
      Graph<T> G =
          new AbstractGraph<T>() {
            private final NodeManager<T> nm =
                new NodeManager<T>() {

                  @Override
                  public Stream<T> stream() {
                    return chunks.stream();
                  }

                  @Override
                  public int getNumberOfNodes() {
                    return chunks.size();
                  }

                  @Override
                  public void addNode(T n) {
                    throw new UnsupportedOperationException();
                  }

                  @Override
                  public void removeNode(T n) throws UnsupportedOperationException {
                    throw new UnsupportedOperationException();
                  }

                  @Override
                  public boolean containsNode(T n) {
                    return chunks.contains(n);
                  }
                };

            @Override
            protected NodeManager<T> getNodeManager() {
              return nm;
            }

            private final EdgeManager<T> em =
                new EdgeManager<T>() {

                  private final Map<T, Set<T>> forwardEdges = HashMapFactory.make();
                  private final Map<T, Set<T>> backwardEdges = HashMapFactory.make();

                  {
                    for (T left : chunks) {
                      for (T right : chunks) {
                        if (cfg.test(left, right)
                            || defSet.apply(left).containsAny(useSet.apply(right))) {
                          if (!forwardEdges.containsKey(left)) {
                            forwardEdges.put(left, HashSetFactory.make());
                          }
                          if (!backwardEdges.containsKey(right)) {
                            backwardEdges.put(right, HashSetFactory.make());
                          }
                          forwardEdges.get(left).add(right);
                          backwardEdges.get(right).add(left);
                        }
                      }
                    }
                  }

                  @Override
                  public Iterator<T> getPredNodes(T n) {
                    return backwardEdges.containsKey(n)
                        ? backwardEdges.get(n).iterator()
                        : EmptyIterator.instance();
                  }

                  @Override
                  public int getPredNodeCount(T n) {
                    return backwardEdges.containsKey(n) ? backwardEdges.get(n).size() : 0;
                  }

                  @Override
                  public Iterator<T> getSuccNodes(T n) {
                    return forwardEdges.containsKey(n)
                        ? forwardEdges.get(n).iterator()
                        : EmptyIterator.instance();
                  }

                  @Override
                  public int getSuccNodeCount(T N) {
                    return forwardEdges.containsKey(N) ? forwardEdges.get(N).size() : 0;
                  }

                  @Override
                  public boolean hasEdge(T src, T dst) {
                    return forwardEdges.containsKey(src)
                        ? forwardEdges.get(src).contains(dst)
                        : false;
                  }

                  @Override
                  public void addEdge(T src, T dst) {
                    throw new UnsupportedOperationException();
                  }

                  @Override
                  public void removeEdge(T src, T dst) throws UnsupportedOperationException {
                    throw new UnsupportedOperationException();
                  }

                  @Override
                  public void removeAllIncidentEdges(T node) throws UnsupportedOperationException {
                    throw new UnsupportedOperationException();
                  }

                  @Override
                  public void removeIncomingEdges(T node) throws UnsupportedOperationException {
                    throw new UnsupportedOperationException();
                  }

                  @Override
                  public void removeOutgoingEdges(T node) throws UnsupportedOperationException {
                    throw new UnsupportedOperationException();
                  }
                };

            @Override
            protected EdgeManager<T> getEdgeManager() {
              return em;
            }
          };

      return Topological.makeTopologicalIter(G);
    }

    private final IClassHierarchy cha;
    private final TypeInference types;
    private final Map<Set<Pair<SSAInstruction, ISSABasicBlock>>, Set<ISSABasicBlock>> regions;
    private final Map<Pair<SSAInstruction, ISSABasicBlock>, Set<SSAInstruction>> linePhis;
    private final Map<Pair<SSAInstruction, ISSABasicBlock>, Set<Set<SSAInstruction>>> regionChunks;
    private final MutableIntSet mergedValues;
    private final IntegerUnionFind mergePhis;
    private final SymbolTable ST;
    private final DefUse du;
    private final PrunedCFG<SSAInstruction, ISSABasicBlock> cfg;
    private final Set<ISSABasicBlock> loopHeaders;
    private final Set<ISSABasicBlock> loopExits;
    private final SSAInstruction r;
    private final ISSABasicBlock l;
    private Map<Integer, MutableIntSet> livenessConflicts;
    protected final Map<SSAInstruction, Map<ISSABasicBlock, RegionTreeNode>> children =
        HashMapFactory.make();

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
      this.livenessConflicts = parent.livenessConflicts;
      initChildren();
    }

    public RegionTreeNode(
        IR ir, IClassHierarchy cha, TypeInference types, SSAInstruction r, ISSABasicBlock l) {
      this.r = r;
      this.l = l;
      this.cha = cha;
      this.types = types;
      du = new DefUse(ir);
      cfg = ExceptionPrunedCFG.makeUncaught(ir.getControlFlowGraph());
      livenessConflicts = HashMapFactory.make();
      LiveAnalysis.Result liveness = LiveAnalysis.perform(ir);
      System.err.println("liveness");
      System.err.println(liveness);
      for (SSAInstruction inst : ir.getInstructions()) {
        if (inst != null) {
          BitVector live = liveness.getLiveBefore(inst.iIndex());
          int lv = 0;
          while ((lv = live.nextSetBit(lv + 1)) > 0) {
            int rv = lv + 1;
            while ((rv = live.nextSetBit(rv + 1)) > 0) {
              if (!livenessConflicts.containsKey(lv)) {
                livenessConflicts.put(lv, IntSetUtil.make());
              }
              livenessConflicts.get(lv).add(rv);
              if (!livenessConflicts.containsKey(rv)) {
                livenessConflicts.put(rv, IntSetUtil.make());
              }
              livenessConflicts.get(rv).add(lv);
            }
          }
        }
      }
      ControlDependenceGraph<ISSABasicBlock> cdg = new ControlDependenceGraph<>(cfg, true);
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

      loopHeaders =
          cfg.stream()
              .filter(
                  bb -> {
                    Iterator<ISSABasicBlock> ps = cfg.getPredNodes(bb);
                    while (ps.hasNext()) {
                      ISSABasicBlock p = ps.next();
                      if (cfgStartTimes.get(p) > cfgStartTimes.get(bb)
                          && cfgFinishTimes.get(p) < cfgFinishTimes.get(bb)) {
                        return true;
                      }
                    }
                    return false;
                  })
              .collect(Collectors.toSet());

      loopExits = HashSetFactory.make();
      loopHeaders.forEach(
          lh -> {
            SSAInstruction inst = lh.getLastInstruction();
            assert inst instanceof SSAConditionalBranchInstruction;
            int bbn = ((SSAConditionalBranchInstruction) inst).getTarget();
            if (bbn < 0) {
              loopExits.add(cfg.exit());
            } else {
              loopExits.add(cfg.getBlockForInstruction(bbn));
            }
          });

      ST = ir.getSymbolTable();
      mergedValues = IntSetUtil.make();
      mergePhis = new IntegerUnionFind(ST.getMaxValueNumber());
      /*
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
                                  int min = Math.min(def, use);
                                  int max = Math.max(def, use);
                                  if (!ST.isConstant(use)
                                      && (!livenessConflicts.containsKey(min)
                                          || !livenessConflicts.get(min).contains(max))
                                      && (!livenessConflicts.containsKey(max)
                                          || !livenessConflicts.get(max).contains(min))) {
                                    if (!livenessConflicts.containsKey(max)) {
                                      livenessConflicts.put(max, IntSetUtil.make());
                                    }
                                    if (!livenessConflicts.containsKey(min)) {
                                      livenessConflicts.put(min, IntSetUtil.make());
                                    }

                                    livenessConflicts.get(max).addAll(livenessConflicts.get(min));
                                    livenessConflicts.get(min).addAll(livenessConflicts.get(max));

                                    mergePhis.union(min, max);
                                    mergedValues.add(use);
                                    mergedValues.add(def);
                                  }
                                }
                              });
                    });
      */
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
                                if (!(cfgStartTimes.get(p) >= cfgStartTimes.get(node)
                                    && cfgFinishTimes.get(p) <= cfgFinishTimes.get(node))) {
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
      regionChunks = HashMapFactory.make();
      regions
          .entrySet()
          .forEach(
              es -> {
                Set<SSAInstruction> regionInsts = HashSetFactory.make();
                es.getValue()
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
                                    sb.iteratePhis()
                                        .forEachRemaining(
                                            phi -> {
                                              int lv = phi.getDef();
                                              int rv = phi.getUse(Util.whichPred(cfg, bb, sb));
                                              if (mergePhis.find(lv) != mergePhis.find(rv)) {
                                                AssignInstruction assign =
                                                    new AssignInstruction(
                                                        bb.getLastInstructionIndex() + 1, lv, rv);

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
                                                  Pair<SSAInstruction, ISSABasicBlock> lineKey =
                                                      Pair.make(bb.getLastInstruction(), sb);
                                                  if (!linePhis.containsKey(lineKey)) {
                                                    linePhis.put(lineKey, HashSetFactory.make());
                                                  }
                                                  linePhis.get(lineKey).add(assign);
                                                } else {
                                                  regionInsts.add(assign);
                                                }
                                              }
                                            });
                                  });
                        });

                Heap<Set<SSAInstruction>> chunks =
                    new Heap<Set<SSAInstruction>>(regionInsts.size()) {
                      @Override
                      protected boolean compareElements(
                          Set<SSAInstruction> elt1, Set<SSAInstruction> elt2) {
                        return elt1.size() > elt2.size();
                      }
                    };
                regionInsts.forEach(
                    inst -> {
                      Set<SSAInstruction> insts = HashSetFactory.make();
                      (new TreeBuilder(cha))
                          .gatherInstructions(insts, ir, du, regionInsts, inst, chunks);
                      System.err.println("chunk for " + inst + ": " + insts);
                    });
                while (chunks.size() > 0 && !regionInsts.isEmpty()) {
                  Set<SSAInstruction> chunk = chunks.take();
                  if (regionInsts.containsAll(chunk)) {
                    regionInsts.removeAll(chunk);
                    System.err.println("using " + chunk);
                    es.getKey()
                        .forEach(
                            p -> {
                              if (!regionChunks.containsKey(p)) {
                                regionChunks.put(p, HashSetFactory.make());
                              }
                              regionChunks.get(p).add(chunk);
                            });
                  }
                }
                assert regionInsts.isEmpty();
              });

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
                                    if (k.fst == bb.getLastInstruction()) {
                                      if (!children.containsKey(k.fst)) {
                                        children.put(k.fst, HashMapFactory.make());
                                      }
                                      children.get(k.fst).put(k.snd, makeChild(k));
                                    }
                                  });
                        });
              });
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
    private boolean phiChunk(Set<SSAInstruction> insts) {
      return insts.size() == 1 && insts.iterator().next() instanceof SSAPhiInstruction;
    }
    */

    private boolean gotoChunk(Set<SSAInstruction> insts) {
      return insts.size() == 1 && insts.iterator().next() instanceof SSAGotoInstruction;
    }

    boolean controlOrderedInChunk(SSAInstruction l, SSAInstruction r, Set<SSAInstruction> chunk) {
      return !(deemedFunctional(l, chunk, cha) && deemedFunctional(r, chunk, cha))
          && l.iIndex() < r.iIndex();
    }

    boolean controlOrderedChunks(
        Set<SSAInstruction> ls, Set<SSAInstruction> rs, Set<SSAInstruction> insts) {
      for (SSAInstruction l : ls) {
        if (!deemedFunctional(l, insts, cha)) {
          for (SSAInstruction r : rs) {
            if (!deemedFunctional(r, insts, cha)) {
              return l.iIndex() < r.iIndex();
            }
          }
        }
      }
      return false;
    }

    public CAstNode toCAst() {
      CAst ast = new CAstImpl();
      List<CAstNode> elts = new LinkedList<>();
      Set<Set<SSAInstruction>> chunks = regionChunks.get(Pair.make(r, l));
      orderChunks(chunks)
          .forEach(
              chunkInsts -> {
                if (!gotoChunk(chunkInsts)) {
                  elts.add(makeToCAst(chunkInsts).processChunk());
                }
              });
      chunks.stream()
          .filter(this::gotoChunk)
          .forEach(
              c -> {
                elts.add(makeToCAst(c).processChunk());
              });
      return ast.makeNode(CAstNode.BLOCK_STMT, elts.toArray(new CAstNode[elts.size()]));
    }

    protected ToCAst makeToCAst(Set<SSAInstruction> c) {
      return new ToCAst(c, new TypeInferenceContext(types));
    }

    private static int chunkIndex(Set<SSAInstruction> chunk) {
      Iterator<SSAInstruction> insts = chunk.iterator();
      while (insts.hasNext()) {
        SSAInstruction inst = insts.next();
        if (!(inst instanceof AssignInstruction)) {
          return inst.iIndex();
        }
      }
      return chunk.iterator().next().iIndex();
    }

    private static List<Set<SSAInstruction>> orderChunks(Set<Set<SSAInstruction>> chunks) {
      Set<SSAInstruction>[] cs = chunks.toArray(new Set[chunks.size()]);
      Arrays.sort(cs, (l, r) -> chunkIndex(l) - chunkIndex(r));
      return Arrays.asList(cs);
    }

    private void toString(StringBuffer text, int level) {
      Set<Set<SSAInstruction>> chunks = regionChunks.get(Pair.make(r, l));
      if (chunks == null) {
        return;
      }
      Set<SSAInstruction> allInsts =
          chunks.stream()
              .reduce(
                  (l, r) -> {
                    Set<SSAInstruction> b = HashSetFactory.make(l);
                    b.addAll(r);
                    return b;
                  })
              .get();
      orderChunks(chunks)
          .forEach(
              insts -> {
                if (!gotoChunk(insts)) {
                  Iterable<SSAInstruction> ii =
                      orderByInsts(
                          insts,
                          ToSource::defSet,
                          ToSource::useSet,
                          (x, y) -> controlOrderedInChunk(x, y, allInsts));
                  ii.forEach(
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

    protected class ToCAst {
      private final CAst ast = new CAstImpl();
      private final Set<SSAInstruction> chunk;
      private final TypeInferenceContext c;

      protected class Visitor implements AstPreInstructionVisitor {
        private CAstNode node = ast.makeNode(CAstNode.EMPTY);
        private Set<SSAInstruction> chunk;
        private Map<SSAInstruction, Map<ISSABasicBlock, RegionTreeNode>> children;

        public Visitor(
            SSAInstruction root,
            TypeInferenceContext c,
            Set<SSAInstruction> chunk,
            Map<SSAInstruction, Map<ISSABasicBlock, RegionTreeNode>> children) {
          this.chunk = chunk;
          this.children = children;
          root.visit(this);
          if (root.hasDef()) {
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
              node =
                  ast.makeNode(
                      CAstNode.DECL_STMT,
                      ast.makeNode(CAstNode.VAR, ast.makeConstant("var_" + mergePhis.find(def))),
                      ast.makeConstant(toSource(c.getTypes().getType(def).getTypeReference())),
                      val);
            }
          }
        }

        private CAstNode visit(int vn) {
          if (ST.isConstant(vn)) {
            return ast.makeConstant(ST.getConstantValue(vn));
          } else if (ST.getNumberOfParameters() >= vn) {
            if (cfg.getMethod().isStatic()) {
              return ast.makeNode(CAstNode.VAR, ast.makeConstant("var_" + vn));
            } else {
              if (vn == 1) {
                return ast.makeNode(CAstNode.THIS);
              } else {
                return ast.makeNode(CAstNode.VAR, ast.makeConstant("var_" + (vn - 1)));
              }
            }
          } else {
            SSAInstruction inst = du.getDef(vn);
            if (chunk.contains(inst)) {
              inst.visit(this);
              return node;
            } else {
              return ast.makeNode(CAstNode.VAR, ast.makeConstant("var_" + mergePhis.find(vn)));
            }
          }
        }

        @Override
        public void visitGoto(SSAGotoInstruction inst) {
          ISSABasicBlock bb = cfg.getBlockForInstruction(inst.iIndex());
          if (loopHeaders.containsAll(cfg.getNormalSuccessors(bb))) {
            //          node = ast.makeNode(CAstNode.CONTINUE);
          } else if (loopExits.containsAll(cfg.getNormalSuccessors(bb))) {
            node = ast.makeNode(CAstNode.BREAK);
          } else {
            node = ast.makeNode(CAstNode.GOTO);
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
            List<CAstNode> lp = new LinkedList<>();
            for (SSAInstruction inst : linePhis.get(key)) {
              assert inst instanceof AssignInstruction;
              Visitor v =
                  makeToCAst(linePhis.get(key)).makeVisitor(inst, c, Collections.singleton(inst));
              lp.add(
                  ast.makeNode(
                      CAstNode.EXPR_STMT,
                      ast.makeNode(
                          CAstNode.ASSIGN, v.visit(inst.getDef()), v.visit(inst.getUse(0)))));
            }
            if (block != null) {
              lp.add(block);
            }
            return ast.makeNode(CAstNode.BLOCK_STMT, lp.toArray(new CAstNode[lp.size()]));
          } else {
            return block;
          }
        }

        @Override
        public void visitConditionalBranch(SSAConditionalBranchInstruction instruction) {
          assert children.containsKey(instruction) : children;

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
          ISSABasicBlock ibb = cfg.getBlockForInstruction(instruction.iIndex());
          if (loopHeaders.contains(ibb)) {
            assert cc.size() <= 2;

            ISSABasicBlock body = cfg.getBlockForInstruction(instruction.iIndex() + 1);
            Set<Set<SSAInstruction>> loopChunks = regionChunks.get(Pair.make(instruction, body));
            RegionTreeNode lr = cc.get(body);
            List<CAstNode> loopBlock = handleBlock(loopChunks, lr);

            node =
                ast.makeNode(
                    CAstNode.LOOP,
                    test,
                    ast.makeNode(
                        CAstNode.BLOCK_STMT, loopBlock.toArray(new CAstNode[loopBlock.size()])));

            if (cc.size() > 1) {
              HashMap<ISSABasicBlock, RegionTreeNode> copy = HashMapFactory.make(cc);
              assert copy.remove(body) != null;
              ISSABasicBlock after = copy.keySet().iterator().next();
              assert after != null;

              Set<Set<SSAInstruction>> afterChunks =
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
              Set<Set<SSAInstruction>> takenChunks =
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
            Set<Set<SSAInstruction>> notTakenChunks = regionChunks.get(notTakenKey);
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

        private List<CAstNode> handleBlock(Set<Set<SSAInstruction>> loopChunks, RegionTreeNode lr) {
          List<CAstNode> block =
              StreamSupport.stream(orderChunks(loopChunks).spliterator(), false)
                  .sorted(
                      (x, y) -> {
                        boolean gx = x.iterator().next() instanceof SSAGotoInstruction;
                        boolean gy = y.iterator().next() instanceof SSAGotoInstruction;
                        return (gx ? 1 : -1) + (gy ? -1 : 1);
                      })
                  .map(c -> lr.makeToCAst(c).processChunk())
                  .collect(Collectors.toList());
          return block;
        }

        @Override
        public void visitSwitch(SSASwitchInstruction instruction) {
          // TODO Auto-generated method stub
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
                            ast.makeConstant(null),
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
          if (instruction.getConcreteType().isArrayType()) {
            node =
                ast.makeNode(
                    CAstNode.NEW,
                    ast.makeConstant(instruction.getConcreteType()),
                    visit(instruction.getUse(0)));
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
          //                        assert false;
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
          SSAInstruction root, TypeInferenceContext c, Set<SSAInstruction> chunk) {
        return new Visitor(root, c, chunk, children);
      }

      public ToCAst(Set<SSAInstruction> chunk, TypeInferenceContext c) {
        this.chunk = chunk;
        this.c = c;
      }

      CAstNode processChunk() {
        SSAInstruction root =
            ReverseIterator.reverse(
                    orderByInsts(chunk, ToSource::defSet, ToSource::useSet).iterator())
                .next();
        Visitor x = makeVisitor(root, c, chunk);
        return x.node;
      }
    }
  }

  static class ToJavaVisitor extends CAstVisitor<TypeInferenceContext> {
    private final int indent;
    private final PrintWriter out;

    private ToJavaVisitor(int indent, PrintWriter out) {
      this.out = out;
      this.indent = indent;
    }

    private void indent() {
      for (int i = 0; i < indent; i++) {
        out.print("  ");
      }
    }

    @Override
    protected boolean visitDeclStmt(
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
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
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
      indent();
      out.println("{");
      ToJavaVisitor cv = new ToJavaVisitor(indent + 1, out);
      for (CAstNode child : n.getChildren()) {
        if (child.getKind() != CAstNode.EMPTY) {
          cv.visit(child, c, cv);
        }
      }
      indent();
      out.println("}");
      return true;
    }

    @Override
    protected boolean visitConstant(
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
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
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
      out.print(n.getChild(0).getValue());
      return true;
    }

    @Override
    public boolean visitAssign(
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
      visit(n.getChild(0), c, visitor);
      out.print(" = ");
      visit(n.getChild(1), c, visitor);
      return true;
    }

    @Override
    protected boolean visitCall(
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
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
        visit(n.getChild(2), c, this);
        out.print("." + target.getName() + "(");
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
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
      for (int i = 0; i < n.getChildCount(); i++) {
        if (n.getChild(i).getKind() != CAstNode.EMPTY) {
          visit(n.getChild(i), c, visitor);
          out.println(";");
        }
      }
      return true;
    }

    @Override
    protected boolean visitExprStmt(
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
      indent();
      visit(n.getChild(0), c, visitor);
      out.println(";");
      return true;
    }

    @Override
    protected boolean visitLoop(
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
      ToJavaVisitor cv = new ToJavaVisitor(indent + 1, out);
      indent();
      out.print("while (");
      cv.visit(n.getChild(0), c, cv);
      out.println(")");
      cv.visit(n.getChild(1), c, cv);
      return true;
    }

    @Override
    protected boolean visitIfStmt(
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
      ToJavaVisitor cv = new ToJavaVisitor(indent + 1, out);
      indent();
      out.print("if (");
      cv.visit(n.getChild(0), c, cv);
      out.println(")");
      cv.visit(n.getChild(1), c, cv);
      if (n.getChildCount() > 2) {
        indent();
        out.println("else");
        cv.visit(n.getChild(2), c, cv);
      }
      return true;
    }

    @Override
    public boolean visitNode(
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
      return true;
    }

    @Override
    protected boolean doVisit(
        CAstNode n, TypeInferenceContext context, CAstVisitor<TypeInferenceContext> visitor) {
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
    protected boolean visitBinaryExpr(
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
      out.print("(");
      visit(n.getChild(1), c, this);
      out.print(" " + n.getChild(0).getValue() + " ");
      visit(n.getChild(2), c, this);
      out.print(")");
      return true;
    }

    @Override
    protected boolean visitUnaryExpr(
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
      out.print(n.getChild(0).getValue() + " ");
      visit(n.getChild(1), c, this);
      return true;
    }

    @Override
    protected boolean visitCast(
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
      out.print("(" + ((CAstType) n.getChild(0).getValue()).getName() + ") ");
      visit(n.getChild(1), c, visitor);
      return true;
    }

    @Override
    protected boolean visitArrayRef(
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
      visit(n.getChild(0), c, visitor);
      out.print("[");
      visit(n.getChild(2), c, visitor);
      out.print("]");
      return true;
    }

    @Override
    protected boolean visitObjectRef(
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
      visit(n.getChild(0), c, visitor);
      out.print(".");
      visit(n.getChild(1), c, visitor);
      return true;
    }

    @Override
    protected boolean visitNew(
        CAstNode n, TypeInferenceContext c, CAstVisitor<TypeInferenceContext> visitor) {
      TypeReference type = (TypeReference) n.getChild(0).getValue();
      if (type.isArrayType()) {
        out.print("new " + type.getArrayElementType().getName().getClassName() + "[");
        visit(n.getChild(1), c, visitor);
        out.print("]");
        return true;
      } else {
        return super.visitNew(n, c, visitor);
      }
    }
  }

  public void toJava(IR ir, IClassHierarchy cha, TypeInference types, PrintWriter out, int level) {
    PrunedCFG<SSAInstruction, ISSABasicBlock> cfg =
        ExceptionPrunedCFG.makeUncaught(ir.getControlFlowGraph());
    System.err.println(ir);

    RegionTreeNode root = makeTreeNode(ir, cha, types, cfg);

    System.err.println("tree");
    System.err.println(root);
    CAstNode ast = root.toCAst();
    System.err.println(ast);

    CAst cast = new CAstImpl();
    MutableIntSet done = IntSetUtil.make();
    List<CAstNode> inits = new LinkedList<>();

    DefUse du = new DefUse(ir);
    for (int n = 1; n <= ir.getSymbolTable().getMaxValueNumber(); n++) {
      int vn = root.mergePhis.find(n);
      if (du.getDef(vn) instanceof SSAPhiInstruction && !done.contains(vn)) {
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

    ToJavaVisitor toJava = new ToJavaVisitor(level, out);
    toJava.visit(ast, new TypeInferenceContext(types), toJava);
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
