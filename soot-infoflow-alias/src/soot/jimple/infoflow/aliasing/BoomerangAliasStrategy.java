package soot.jimple.infoflow.aliasing;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;

import boomerang.AliasFinder;
import boomerang.BoomerangContext;
import boomerang.BoomerangTimeoutException;
import boomerang.accesspath.AccessGraph;
import boomerang.accesspath.WrappedSootField;
import boomerang.cache.AliasResults;
import boomerang.cache.Query;
import boomerang.cache.ResultCache;
import boomerang.context.Context;
import boomerang.context.IContextRequester;
import heros.solver.Pair;
import soot.ArrayType;
import soot.Local;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.Stmt;
import soot.jimple.infoflow.Infoflow;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.solver.IInfoflowSolver;
import soot.jimple.infoflow.solver.cfg.BackwardsInfoflowCFG;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;

/**
 * A fully flow-sensitive aliasing strategy
 * 
 * @author Johannes Spaeth
 */
public class BoomerangAliasStrategy extends AbstractBulkAliasStrategy {

  private final IInfoflowCFG icfg;
  private Multimap<Pair<SootMethod, Abstraction>, Pair<Unit, Abstraction>> incomingMap =
      HashMultimap.create();
  private IInfoflowCFG bwicfg;
  private AliasFinder boomerang;
  private LinkedList<String> methodIgnoreList;
  private Map<Query, AliasResults> alreadyQueried = new HashMap<>();

  public BoomerangAliasStrategy(IInfoflowCFG cfg) {
    super(cfg);
    this.icfg = cfg;
    this.bwicfg = new BackwardsInfoflowCFG(icfg);
    this.boomerang = new AliasFinder(new BoomerangContext(icfg, bwicfg));

    methodIgnoreList = new LinkedList<String>();
    methodIgnoreList.add("int hashCode()");
    methodIgnoreList.add("boolean equals(java.lang.Object)");
  }

  private boolean isIgnoredMethod(SootMethod m) {
    for (String ign : methodIgnoreList) {
      if (m.getSignature().contains(ign))
        return true;
    }

    return false;
  }

  @Override
  public void computeAliasTaints(final Abstraction d1, final Stmt src, final Value targetValue,
      Set<Abstraction> taintSet, SootMethod method, Abstraction newAbs) {
    newAbs.getAccessPath();
    Local base = newAbs.getAccessPath().getPlainValue();

    if (isIgnoredMethod(icfg.getMethodOf(src)))
      return;
    if (base == null)
      return;

    // There are two different queries necessary: At field writes and at method return statements,
    // when there might be new alias in the caller scope.
    if (src.containsInvokeExpr())
      handleReturn(d1, src, taintSet, newAbs, base);
    else
      handleFieldWrite(d1, src, taintSet, newAbs, base);
  }

  private void handleFieldWrite(final Abstraction d1, final Stmt src, Set<Abstraction> taintSet,
      Abstraction newAbs, Local base) {
    if (base == null)
      return;

    SootMethod method = icfg.getMethodOf(src);

    // Query for the base variable
    AliasResults res = queryBoomerang(new AccessGraph(base, base.getType()), src, method, d1);
    Set<AccessGraph> accessPathOnly = res.mayAliasSet();
    SootField[] fields = newAbs.getAccessPath().getFields();
    // append the fields the incoming access path had to the result set
    if (fields != null)
      accessPathOnly =
          AliasResults.appendFields(accessPathOnly, toListFieldWithStmt(fields), boomerang.context);
    for (AccessGraph ap : accessPathOnly) {
      Abstraction flowDroidAccessPath = toFlowDroidAccessPath(ap, src, newAbs);
      // add all access path to the taintSet for further propagation
      if (flowDroidAccessPath != null)
        taintSet.add(flowDroidAccessPath);
    }
  }

  private WrappedSootField[] toListFieldWithStmt(SootField[] fields) {
    LinkedList<WrappedSootField> list = new LinkedList<>();
    if (fields == null)
      return null;
    for (SootField f : fields)
      list.add(new WrappedSootField(f, f.getType(), null));
    WrappedSootField[] fieldws = new WrappedSootField[list.size()];
    fieldws = list.toArray(fieldws);
    return fieldws;
  }

  private void handleReturn(Abstraction d1, Stmt src, Set<Abstraction> taintSet,
      Abstraction newAbs, Local base) {

    // Upon return, the last field access is dropped from the abstraction and a query is triggered
    // for this access graph. Then for each of the result, the last field is re-appended and those
    // access paths are propagated forward
    SootField lastField = newAbs.getAccessPath().getLastField();
    if (newAbs.getAccessPath().getLastFieldType() instanceof ArrayType) {

      // Special handling for arrays
      SootField[] fields = newAbs.getAccessPath().getFields();
      AccessGraph accessPath = new AccessGraph(base, base.getType(), toListFieldWithStmt(fields));
      SootMethod method = boomerang.context.icfg.getMethodOf(src);

      AliasResults res = queryBoomerang(accessPath, src, method, d1);
      Set<AccessGraph> accessPathOnly = res.mayAliasSet();

      for (AccessGraph ap : accessPathOnly) {
        taintSet.add(toFlowDroidAccessPath(ap, src, newAbs));
      }
      return;
    }
    if (lastField == null)
      return;
    if (d1.equals(newAbs))
      return;
    SootField[] fields = newAbs.getAccessPath().getFields();
    AccessGraph accessPath = new AccessGraph(base, base.getType(), toListFieldWithStmt(fields));
    Set<AccessGraph> withoutLastFields = accessPath.popLastField();
    SootMethod method = icfg.getMethodOf(src);
    for (AccessGraph withoutLastField : withoutLastFields) {
      // trigger query for access graph with droped/popped last field.
      AliasResults res = queryBoomerang(withoutLastField, src, method, d1);
      Set<AccessGraph> accessPathOnly = res.mayAliasSet();
      if (lastField != null)
        // add the last field again.
        accessPathOnly =
            AliasResults.appendField(accessPathOnly,
            new WrappedSootField(lastField, lastField.getType(), null), boomerang.context);

      for (AccessGraph ap : accessPathOnly) {
        Abstraction flowDroidAccessPath = toFlowDroidAccessPath(ap, src, newAbs);
        if (flowDroidAccessPath != null)
          taintSet.add(flowDroidAccessPath);
      }
    }
  }

  private AliasResults queryBoomerang(final AccessGraph ap, final Unit stmt, SootMethod method,
      final Abstraction d1) {
    Query query = new Query(ap, stmt, method);
    if (!alreadyQueried.containsKey(query)) {
      Infoflow.aliasQueryCounter++;
    } else {
      return alreadyQueried.get(query);
    }
    boomerang.context.budgetInMilliSeconds = Infoflow.aliasTimeoutInMilliSeconds;
    long start = System.currentTimeMillis();
    boomerang.context.startTime = start;
    AliasResults res = new AliasResults();
    try {

      // triggers the query for Boomerang, as a context requestor we use the
      // FlowDroidContextRequestor. This follows the incoming set of the solver (by using the
      // contextMap)
      res = boomerang.findAliasAtStmt(ap, stmt, new FlowDroidContextRequestor(d1));
    } catch (Exception e) {
      try {
        boomerang.context.forceTerminate();
      } catch (ThreadDeath e1) {
      }

      if (e instanceof BoomerangTimeoutException) {
        Infoflow.aliasQueryCounterTimeout++;
      } else
        e.printStackTrace();
    }
    BoomerangContext boomerangContext = new BoomerangContext(icfg, bwicfg);

    // Reuse the same internal cache for all queries
    ResultCache cache = boomerang.context.querycache;
    boomerangContext.querycache = cache;
    // reinstantiate Boomerang, to remove path edges etc for next query.
    boomerang = new AliasFinder(boomerangContext);
    long after = System.currentTimeMillis();
    Infoflow.aliasQueryTime += (after - start);
    alreadyQueried.put(query, res);
    return res;

  }

  /**
   * Maps an Boomerang access graph to a FlowDroid access path (Abstraction).
   * 
   * @return
   */
  private Abstraction toFlowDroidAccessPath(AccessGraph ap, Stmt src, Abstraction newAbs) {
    if (ap.getFieldCount() < 1) {
      return newAbs.deriveNewAbstraction(new soot.jimple.infoflow.data.AccessPath(ap.getBase(),
          newAbs.getAccessPath().isCutOffApproximation()), src);
    }
    WrappedSootField[] fields = ap.getRepresentative();
    ArrayList<SootField> fdFields = new ArrayList<>();
    ArrayList<Type> fdFieldType = new ArrayList<>();
    int accessPathLength = Infoflow.getAccessPathLength();
    for (int i = 0; i < Math.min(fields.length, accessPathLength); i++) {
      WrappedSootField field = fields[i];
      if (field.getField().equals(AliasFinder.ARRAY_FIELD)) {
        if (!fdFieldType.isEmpty()) {
          int last = fdFieldType.size() - 1;
          Type type = fdFieldType.get(last);
          Type buildArrayOrAddDimension = buildArrayOrAddDimension(type);
          fdFieldType.remove(last);
          fdFieldType.add(buildArrayOrAddDimension);
        }
      } else {
        fdFields.add(field.getField());
        fdFieldType.add(field.getField().getType());
      }
    }
    Type[] fdFieldTypeArray = fdFieldType.toArray(new Type[] {});
    SootField[] fdFieldArray = fdFields.toArray(new SootField[] {});

    Value plainValue = ap.getBase();
    Type baseType = null;
    if (plainValue != null)
      baseType = plainValue.getType();

    if (plainValue == null && fdFields.isEmpty())
      return null;
    return newAbs.deriveNewAbstraction(new soot.jimple.infoflow.data.AccessPath(plainValue,
        fdFieldArray, baseType, fdFieldTypeArray,
        (newAbs.getAccessPath().isCutOffApproximation() || fields.length > accessPathLength)), src);
  }


  /**
   * Builds a new array of the given type if it is a base type or increments the dimensions of the
   * given array by 1 otherwise.
   * 
   * @param type The base type or incoming array
   * @return The resulting array
   */
  private Type buildArrayOrAddDimension(Type type) {
    if (type instanceof ArrayType) {
      ArrayType array = (ArrayType) type;
      return array.makeArrayType();
    } else
      return ArrayType.v(type, 1);
  }

  @Override
  public void injectCallingContext(Abstraction d3, IInfoflowSolver fSolver, SootMethod callee,
      Unit callSite, Abstraction source, Abstraction d1) {
    // This is called whenever something is added to the incoming set of the forward solver of the
    // FlowDroid IFDS solver.
    Pair<SootMethod, Abstraction> calleepair = new Pair<>(callee, d3);
    Pair<Unit, Abstraction> callerpair = new Pair<>(callSite, d1);
    incomingMap.put(calleepair, callerpair);
  }

  @Override
  public boolean isFlowSensitive() {
    return true;
  }

  @Override
  public boolean requiresAnalysisOnReturn() {
    return true;
  }

  private class FlowDroidContextRequestor implements IContextRequester {
    private final Abstraction d1;

    private FlowDroidContextRequestor(Abstraction d1) {
      this.d1 = d1;
    }

    @Override
    public Collection<Context> getCallSiteOf(Context c) {
      if (!(c instanceof FlowDroidContext)) {
        throw new RuntimeException("Context must be an instanceof FlowDroidContext");
      }
      FlowDroidContext cont = (FlowDroidContext) c;
      Unit callSite = cont.getStmt();
      SootMethod methodOf = icfg.getMethodOf(callSite);
      Abstraction abstraction = cont.getAbstraction();
      Set<Context> boomerangCallerContexts = new HashSet<>();

      if (BoomerangAliasStrategy.this.getForwardSolver().getZeroValue().equals(d1)) {
        // If we reached the 0-Fact the analysis propagates to all callers
        Collection<Unit> callersOf = icfg.getCallersOf(methodOf);
        for (Unit call : callersOf) {
          if (isIgnoredMethod(icfg.getMethodOf(call)))
            continue;
          FlowDroidContext newContext = new FlowDroidContext(call, d1);
          boomerangCallerContexts.add(newContext);
        }
        return boomerangCallerContexts;
      }

      // If we did not have the 0-Fact as start fact, we query the incomingMap to see via which
      // callsite the forward analysis entered a method
      Collection<Pair<Unit, Abstraction>> callerContexts =
          incomingMap.get(new Pair<SootMethod, Abstraction>(methodOf, abstraction));


      for (Pair<Unit, Abstraction> callerContext : callerContexts) {
        if (isIgnoredMethod(icfg.getMethodOf(callerContext.getO1())))
          continue;
        FlowDroidContext newContext =
            new FlowDroidContext(callerContext.getO1(), callerContext.getO2());
        boomerangCallerContexts.add(newContext);
      }
      return boomerangCallerContexts;
    }

    @Override
    public Context initialContext(Unit stmt) {
      return new FlowDroidContext(stmt, d1);
    }

  }

  private class FlowDroidContext implements Context {
    private Unit stmt;
    private Abstraction abs;
    private SootMethod method;

    public FlowDroidContext(Unit stmt, Abstraction abs) {
      this.stmt = stmt;
      this.abs = abs;
      this.method = icfg.getMethodOf(stmt);
    }

    public Abstraction getAbstraction() {
      return abs;
    }

    @Override
    public Unit getStmt() {
      return stmt;
    }

    public String toString() {
      return "FDContext[" + stmt + ", " + abs + "," + method + "]";
    }

    @Override
    public int hashCode() {
      final int prime = 31;
      int result = 1;
      result = prime * result + getOuterType().hashCode();
      result = prime * result + ((abs == null) ? 0 : abs.hashCode());
      result = prime * result + ((stmt == null) ? 0 : stmt.hashCode());
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
      FlowDroidContext other = (FlowDroidContext) obj;
      if (!getOuterType().equals(other.getOuterType()))
        return false;
      if (abs == null) {
        if (other.abs != null)
          return false;
      } else if (!abs.equals(other.abs))
        return false;
      if (stmt == null) {
        if (other.stmt != null)
          return false;
      } else if (!stmt.equals(other.stmt))
        return false;
      return true;
    }

    private BoomerangAliasStrategy getOuterType() {
      return BoomerangAliasStrategy.this;
    }

  }

  @Override
  public void shutdown() {}

}
