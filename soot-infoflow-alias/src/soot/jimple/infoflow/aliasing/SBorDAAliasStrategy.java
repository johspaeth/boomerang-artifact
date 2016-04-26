package soot.jimple.infoflow.aliasing;

import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Sets;
import com.google.common.collect.Table;

import alias.ManuMayAliasAnalysis;
import alias.Util;
import edu.osu.cse.pa.YanMayAlias;
import heros.solver.PathEdge;
import iohoister.analysis.MayAliasAnalysis;
import soot.Local;
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.Scene;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.infoflow.IInfoflow.AliasingAlgorithm;
import soot.jimple.infoflow.Infoflow;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.solver.IInfoflowSolver;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.toolkits.pointer.DumbPointerAnalysis;

/**
 * A simple points-to-based aliasing strategy for FlowDroid
 * 
 * @author Johannes Spaeth
 */
public class SBorDAAliasStrategy extends AbstractBulkAliasStrategy {

  private final Table<SootMethod, Abstraction, Set<Abstraction>> aliases = HashBasedTable.create();
  private Set<Key> alreadyQueried = new HashSet<>();
  private AliasingAlgorithm aliasingAlgorithm;

  public SBorDAAliasStrategy(IInfoflowCFG cfg, AliasingAlgorithm aliasingAlgorithm) {
    super(cfg);
    this.aliasingAlgorithm = aliasingAlgorithm;
    // Option necessary, otherwise DA crashed
    Util.TWEAK_BODY = false;
  }

  @Override
  public void computeAliasTaints(Abstraction d1, Stmt src, Value targetValue,
      Set<Abstraction> taintSet, SootMethod method, Abstraction newAbs) {
    computeAliasTaintsInternal(d1, method, newAbs, Collections.<SootField>emptyList(),
        Collections.<Type>emptyList(), newAbs.getAccessPath().getTaintSubFields(), src);
  }

  public void computeAliasTaintsInternal(Abstraction d1, SootMethod method, Abstraction newAbs,
      List<SootField> appendFields, List<Type> appendTypes, boolean taintSubFields, Stmt actStmt) {
    // Record the incoming abstraction
    synchronized (aliases) {
      if (aliases.contains(method, newAbs)) {
        Set<Abstraction> d1s = aliases.get(method, newAbs);
        if (d1s.contains(d1))
          return;
        d1s.add(d1);
      } else {
        Set<Abstraction> d1s = Sets.newIdentityHashSet();
        d1s.add(d1);
        aliases.put(method, newAbs, d1s);
      }
    }
    // Also check for aliases for parts of the access path
    final AccessPath ap = newAbs.getAccessPath();
    if ((ap.isInstanceFieldRef() && ap.getFirstField() != null)
        || (ap.isStaticFieldRef() && ap.getFieldCount() > 1)) {
      List<SootField> appendList = new LinkedList<SootField>(appendFields);
      appendList.add(0, newAbs.getAccessPath().getLastField());
      List<Type> typesList = new LinkedList<Type>(appendTypes);
      typesList.add(0, newAbs.getAccessPath().getLastFieldType());

      computeAliasTaintsInternal(d1, method,
          newAbs.deriveNewAbstraction(newAbs.getAccessPath().dropLastField(), actStmt), appendList,
          typesList, taintSubFields, actStmt);
    }

    // Do not try to compute points-to-sets on complex access paths
    if (ap.getFieldCount() > 1)
      return;

    SootField[] appendFieldsA = appendFields.toArray(new SootField[appendFields.size()]);
    Type[] appendTypesA = appendTypes.toArray(new Type[appendTypes.size()]);



    for (Unit u : method.getActiveBody().getUnits()) {

      Stmt stmt = (Stmt) u;

      if (stmt.containsInvokeExpr()) {
        // If we have a call, we must check whether the base or one of
        // the parameter aliases with the given taint
        InvokeExpr invExpr = (InvokeExpr) stmt.getInvokeExpr();
        boolean baseAliases = false;
        if (invExpr instanceof InstanceInvokeExpr && !newAbs.getAccessPath().isStaticFieldRef()) {
          InstanceInvokeExpr iinvExpr = (InstanceInvokeExpr) invExpr;
          baseAliases =
              isAliasedAtStmt(new AccessPath((Local) iinvExpr.getBase(), false), newAbs
                  .getAccessPath().getPlainValue(), method);
        }

        boolean parameterAliases = false;
        for (Value arg : invExpr.getArgs())
          if (arg instanceof Local) {
            if (isAliasedAtStmt(newAbs.getAccessPath(), arg, method)) {
              parameterAliases = true;
              break;
            }
          }

        if (baseAliases || parameterAliases) {
          Abstraction absCallee =
              newAbs.deriveNewAbstraction(
                  newAbs.getAccessPath().appendFields(appendFieldsA, appendTypesA, taintSubFields),
                  stmt);
          getForwardSolver().processEdge(new PathEdge<Unit, Abstraction>(d1, u, absCallee));
        }
      } else if (u instanceof DefinitionStmt) {
        DefinitionStmt assign = (DefinitionStmt) u;

        // If we have a = b and our taint is an alias to b, we must add
        // a taint for a.
        if (assign.getRightOp() instanceof FieldRef || assign.getRightOp() instanceof Local
            || assign.getRightOp() instanceof ArrayRef) {
          if (isAliasedAtStmt(newAbs.getAccessPath(), assign.getRightOp(), method)
              && (appendFields != null && appendFields.size() > 0)) {
            Abstraction aliasAbsLeft =
                newAbs.deriveNewAbstraction(new AccessPath(assign.getLeftOp(), appendFieldsA,
                    taintSubFields), stmt);
            getForwardSolver().processEdge(new PathEdge<Unit, Abstraction>(d1, u, aliasAbsLeft));
          }
        }

        // If we have a = b and our taint is an alias to a, we must add
        // a taint for b.
        if (assign.getLeftOp() instanceof FieldRef || assign.getLeftOp() instanceof Local
            || assign.getLeftOp() instanceof ArrayRef)
          if (assign.getRightOp() instanceof FieldRef || assign.getRightOp() instanceof Local
              || assign.getRightOp() instanceof ArrayRef) {
            if (isAliasedAtStmt(newAbs.getAccessPath(), assign.getLeftOp(), method)) {
              Abstraction aliasAbsRight =
                  newAbs.deriveNewAbstraction(new AccessPath(assign.getRightOp(), appendFieldsA,
                      taintSubFields), stmt);
              getForwardSolver().processEdge(new PathEdge<Unit, Abstraction>(d1, u, aliasAbsRight));
            }
          }
      }
    }

  }

  private boolean isAliasedAtStmt(final AccessPath ap, final Value val, final SootMethod m1) {
    if (alreadyQueried.add(new Key(ap.getPlainValue(), val, m1))) {
      Infoflow.aliasQueryCounter++;
    }
    if (ap.isLocal() && val instanceof Local) {
      Infoflow.SBandDACounter++;
      Boolean res = false;
      Util.TIME_BUDGET = Infoflow.aliasTimeoutInMilliSeconds;
      long before = System.currentTimeMillis();
      Util.aliasStart = System.currentTimeMillis();
      MayAliasAnalysis.queryCrashed = false;
      if (aliasingAlgorithm == AliasingAlgorithm.SB) {
        res =
            ManuMayAliasAnalysis.v().mayAlias(ap.getPlainValue(), null, m1, (Local) val, null, m1);
      } else if (aliasingAlgorithm == AliasingAlgorithm.DA) {
        YanMayAlias.v().buildSPG();
        res = YanMayAlias.v().mayAlias(ap.getPlainValue(), null, m1, (Local) val, null, m1);
      }
      if (MayAliasAnalysis.queryCrashed)
        Infoflow.aliasQueryCounterTimeout++;
      long after = System.currentTimeMillis();
      Infoflow.aliasQueryTime += (after - before);
      if (!MayAliasAnalysis.queryCrashed)
        return res;
    }
    // Fallback solution in the case if the access path is not only a local variable or the analysis
    // crashed
    PointsToSet ptsRight = getPointsToSet(val);
    if (ptsRight == null)
      return false;
    PointsToSet ptsTaint = getPointsToSet(ap);
    return ptsTaint.hasNonEmptyIntersection(ptsRight);
  }

  private class Key {
    private Local ap;
    private Value val;
    private SootMethod m1;

    Key(Local val1, Value val, SootMethod m1) {
      this.ap = val1;
      this.val = val;
      this.m1 = m1;
    }

    @Override
    public int hashCode() {
      final int prime = 31;
      int result = 1;
      result = prime * result + ((ap == null) ? 0 : ap.hashCode());
      result = prime * result + ((m1 == null) ? 0 : m1.hashCode());
      result = prime * result + ((val == null) ? 0 : val.hashCode());
      return result;
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj)
        return true;
      if (obj == null)
        return false;
      if (getClass() != obj.getClass())
        return false;
      Key other = (Key) obj;
      if (ap == null) {
        if (other.ap != null)
          return false;
      } else if (!ap.equals(other.ap))
        return false;
      if (m1 == null) {
        if (other.m1 != null)
          return false;
      } else if (!m1.equals(other.m1))
        return false;
      if (val == null) {
        if (other.val != null)
          return false;
      } else if (!val.equals(other.val))
        return false;
      return true;
    }

  }

  /**
   * Gets the points-to-set for the given value
   * 
   * @param targetValue The value for which to get the points-to-set
   * @return The points-to-set for the given value
   */
  private PointsToSet getPointsToSet(Value targetValue) {
    PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
    if (pta instanceof DumbPointerAnalysis)
      throw new RuntimeException("Scene's points-to analysis should be one by SPARK");
    synchronized (pta) {
      if (targetValue instanceof Local)
        return pta.reachingObjects((Local) targetValue);
      else if (targetValue instanceof InstanceFieldRef) {
        InstanceFieldRef iref = (InstanceFieldRef) targetValue;
        return pta.reachingObjects((Local) iref.getBase(), iref.getField());
      } else if (targetValue instanceof StaticFieldRef) {
        StaticFieldRef sref = (StaticFieldRef) targetValue;
        return pta.reachingObjects(sref.getField());
      } else if (targetValue instanceof ArrayRef) {
        ArrayRef aref = (ArrayRef) targetValue;
        return pta.reachingObjects((Local) aref.getBase());
      }
      return null;
    }
  }

  /**
   * Gets the points-to-set for the given access path
   * 
   * @param accessPath The access path for which to get the points-to-set
   * @return The points-to-set for the given access path
   */
  public PointsToSet getPointsToSet(AccessPath accessPath) {
    PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
    if (pta instanceof DumbPointerAnalysis)
      throw new RuntimeException("Scene's points-to analysis should be one by SPARK");
    if (accessPath.isLocal())
      return pta.reachingObjects(accessPath.getPlainValue());
    else if (accessPath.isInstanceFieldRef())
      return pta.reachingObjects(accessPath.getPlainValue(), accessPath.getFirstField());
    else if (accessPath.isStaticFieldRef())
      return pta.reachingObjects(accessPath.getFirstField());
    else
      throw new RuntimeException("Unexepected access path type");
  }

  @Override
  public void injectCallingContext(Abstraction abs, IInfoflowSolver fSolver, SootMethod callee,
      Unit callSite, Abstraction source, Abstraction d1) {

  }

  @Override
  public boolean isFlowSensitive() {
    return false;
  }

  @Override
  public boolean requiresAnalysisOnReturn() {
    return true;
  }

  @Override
  public void shutdown() {}

}
