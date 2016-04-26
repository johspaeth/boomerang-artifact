package soot.jimple.infoflow.aliasing;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
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
import soot.Scene;
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
public class BoomerangAliasStrategyAC extends AbstractBulkAliasStrategy {

  private final IInfoflowCFG icfg;
  private Multimap<Pair<SootMethod, Abstraction>, Pair<Unit, Abstraction>> incomingMap =
      HashMultimap.create();
  private IInfoflowCFG bwicfg;
  private AliasFinder boomerang;
  private LinkedList<String> methodIgnoreList;
  private Map<Query, AliasResults> alreadyQueried = new HashMap<>();
  private AliasFinder boomerangAC;

  public int moreContextRequest;
  public int allPossibleContext;
  public int selectedContexts;

  public int moreContextRequestAC;
  public int allPossibleContextAC;
  public int selectedContextsAC;
  private FileWriter writer;

  public BoomerangAliasStrategyAC(IInfoflowCFG cfg) {
    super(cfg);
    File file = new File("AllContext_vs_FlowDroidContexts.csv");
    writer = null;
    if (!file.exists()) {
      try {
        writer = new FileWriter(file);
        writer
.write(
            "Alias Result Size (FDC); Alias Analysis Time (FDC); #Context Requests (FDC); #Selected Contexts (FDC); #All Possible Context (FDC);Alias Result Size (AC); Alias Analysis Time (AC); #Context Requests (AC); #Selected Contexts (AC); #All Possible Context (AC);");
        writer.write("\n" + Scene.v().getSootClassPath() + ";");
      } catch (IOException e) {
        e.printStackTrace();
      }
    } else {
      try {
        writer = new FileWriter("AllContext_vs_FlowDroidContexts.csv", true);
        writer.write("\n" + Scene.v().getSootClassPath() + ";");
      } catch (IOException e) {
        e.printStackTrace();
      }
    }
    if (writer == null)
      throw new RuntimeException("OOPS");
    this.icfg = cfg;
    this.bwicfg = new BackwardsInfoflowCFG(icfg);
    this.boomerang = new AliasFinder(new BoomerangContext(icfg, bwicfg));
    this.boomerangAC = new AliasFinder(new BoomerangContext(icfg, bwicfg));

    methodIgnoreList = new LinkedList<String>();
    methodIgnoreList.add("int hashCode()");
    methodIgnoreList.add("boolean equals(java.lang.Object)");
  }

  public boolean isIgnoredMethod(SootMethod m) {
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

    AliasResults res = queryDart(new AccessGraph(base, base.getType()), src, method, d1);
    Set<AccessGraph> accessPathOnly = res.mayAliasSet();
    SootField[] fields = newAbs.getAccessPath().getFields();
    if (fields != null)
      accessPathOnly =
          AliasResults.appendFields(accessPathOnly, toListFieldWithStmt(fields), boomerang.context);
    for (AccessGraph ap : accessPathOnly) {
      Abstraction flowDroidAccessPath = toFlowDroidAccessPath(ap, src, newAbs);
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
    SootField lastField = newAbs.getAccessPath().getLastField();
    if (newAbs.getAccessPath().getLastFieldType() instanceof ArrayType) {
      SootField[] fields = newAbs.getAccessPath().getFields();
      AccessGraph accessPath = new AccessGraph(base, base.getType(), toListFieldWithStmt(fields));
      SootMethod method = boomerang.context.icfg.getMethodOf(src);

      AliasResults res = queryDart(accessPath, src, method, d1);
      Set<AccessGraph> accessPathOnly = res.mayAliasSet();
      // Set<AccessPath> accessPathOnly = res.mayAliasSet();

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
      AliasResults res = queryDart(withoutLastField, src, method, d1);
      Set<AccessGraph> accessPathOnly = res.mayAliasSet();
      if (lastField != null)
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

  private AliasResults queryDart(final AccessGraph ap, final Unit stmt, SootMethod method,
      final Abstraction d1) {
    Query query = new Query(ap, stmt, method);
    if (!alreadyQueried.containsKey(query)) {
      Infoflow.aliasQueryCounter++;
    } else {
      return alreadyQueried.get(query);
    }
    selectedContexts = 0;
    allPossibleContext = 0;
    moreContextRequest = 0;
    selectedContextsAC = 0;
    allPossibleContextAC = 0;
    moreContextRequestAC = 0;

    long time = -1;
    long timeAC = -1;
    long resSize = -1;
    long resSizeAC = -1;
    boomerang.context.budgetInMilliSeconds = Infoflow.aliasTimeoutInMilliSeconds;
    boomerang.context.startTime = System.currentTimeMillis();
    boomerangAC.context.budgetInMilliSeconds = Infoflow.aliasTimeoutInMilliSeconds;
    boomerangAC.context.startTime = System.currentTimeMillis();

    // We trigger the query first with the FlowDroidContextRequestor (Following the incoming set of
    // FlowDroid)
    AliasResults res = new AliasResults();
    try {
      long before = System.currentTimeMillis();
      res = boomerang.findAliasAtStmt(ap, stmt, new FlowDroidContextRequestor(d1));
      long after = System.currentTimeMillis();
      time = (after - before);
      resSize = res.size();
    } catch (Exception e) {
      try {
        boomerang.context.forceTerminate();
      } catch (ThreadDeath e1) {
      }
      ResultCache cache = boomerang.context.querycache;
      cache.clean();
      BoomerangContext dartContext = new BoomerangContext(icfg, bwicfg);
      dartContext.querycache = cache;
      boomerang = new AliasFinder(dartContext);
      if (e instanceof BoomerangTimeoutException) {
        Infoflow.aliasQueryCounterTimeout++;
      } else
        e.printStackTrace();
    }

    // and now with the AllContextRequestor (Not following the incoming set of FlowDroid)
    try {
      long before = System.currentTimeMillis();
      AliasResults res2 = boomerangAC.findAliasAtStmt(ap, stmt, new AllContextRequestor());
      long after = System.currentTimeMillis();
      timeAC = (after - before);
      resSizeAC = res2.size();
    } catch (Exception e) {
      try {
        boomerangAC.context.forceTerminate();
      } catch (ThreadDeath e1) {
      }
      ResultCache cache = boomerangAC.context.querycache;
      cache.clean();
      BoomerangContext dartContext = new BoomerangContext(icfg, bwicfg);
      dartContext.querycache = cache;
      boomerangAC = new AliasFinder(dartContext);
    }
    long after = System.currentTimeMillis();
    try {
      // output differences
      writer.write("\n");
      writer.write(resSize + ";" + time + ";" + moreContextRequest + ";" + selectedContexts + ";"
          + allPossibleContext + ";" + resSizeAC + ";" + timeAC + ";" + moreContextRequestAC + ";"
          + selectedContextsAC + ";" + allPossibleContextAC + ";");
    } catch (IOException e) {
      e.printStackTrace();
    }

    Infoflow.aliasQueryTime += (after - boomerang.context.startTime);
    alreadyQueried.put(query, res);
    return res;

  }

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
  public Type buildArrayOrAddDimension(Type type) {
    if (type instanceof ArrayType) {
      ArrayType array = (ArrayType) type;
      return array.makeArrayType();
    } else
      return ArrayType.v(type, 1);
  }

  @Override
  public void injectCallingContext(Abstraction d3, IInfoflowSolver fSolver, SootMethod callee,
      Unit callSite, Abstraction source, Abstraction d1) {
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
      moreContextRequest++;
      allPossibleContext += icfg.getCallersOf(methodOf).size();
      Abstraction abstraction = cont.getAbstraction();

      if (BoomerangAliasStrategyAC.this.getForwardSolver().getZeroValue().equals(d1)) {
        Set<Context> dartCallerContexts = new HashSet<>();
        Collection<Unit> callersOf = icfg.getCallersOf(methodOf);
        for (Unit call : callersOf) {
          if (isIgnoredMethod(icfg.getMethodOf(call)))
            continue;
          FlowDroidContext newContext = new FlowDroidContext(call, d1);
          dartCallerContexts.add(newContext);
        }
        selectedContexts += dartCallerContexts.size();
        return dartCallerContexts;
      }
      Collection<Pair<Unit, Abstraction>> callerContexts =
          incomingMap.get(new Pair<SootMethod, Abstraction>(methodOf, abstraction));
      Set<Context> dartCallerContexts = new HashSet<>();



      for (Pair<Unit, Abstraction> callerContext : callerContexts) {
        if (isIgnoredMethod(icfg.getMethodOf(callerContext.getO1())))
          continue;
        FlowDroidContext newContext =
            new FlowDroidContext(callerContext.getO1(), callerContext.getO2());
        dartCallerContexts.add(newContext);
      }
      selectedContexts = dartCallerContexts.size();
      return dartCallerContexts;
    }

    @Override
    public Context initialContext(Unit stmt) {
      return new FlowDroidContext(stmt, d1);
    }

  }

  private class AllContextRequestor implements IContextRequester {

    private AllContextRequestor() {}

    @Override
    public Collection<Context> getCallSiteOf(Context c) {
      Unit callSite = c.getStmt();
      SootMethod methodOf = icfg.getMethodOf(callSite);
      if (isIgnoredMethod(methodOf))
        return Collections.emptySet();
      moreContextRequestAC++;
      allPossibleContextAC += icfg.getCallersOf(methodOf).size();
      Set<Context> dartCallerContexts = new HashSet<>();
      Collection<Unit> callersOf = icfg.getCallersOf(methodOf);
      for (Unit call : callersOf) {
        if (isIgnoredMethod(icfg.getMethodOf(call)))
          continue;
        AllContext newContext = new AllContext(call);
        dartCallerContexts.add(newContext);
      }
      selectedContextsAC += dartCallerContexts.size();
      return dartCallerContexts;

    }

    @Override
    public Context initialContext(Unit stmt) {
      return new AllContext(stmt);
    }

  }
  private class AllContext implements Context {
    private Unit stmt;

    public AllContext(Unit stmt) {
      this.stmt = stmt;
    }


    @Override
    public Unit getStmt() {
      return stmt;
    }

    public String toString() {
      return "ALLContext[" + stmt + "]";
    }

    @Override
    public int hashCode() {
      final int prime = 31;
      int result = 1;
      result = prime * result + getOuterType().hashCode();
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
      if (stmt == null) {
        if (other.stmt != null)
          return false;
      } else if (!stmt.equals(other.stmt))
        return false;
      return true;
    }

    private BoomerangAliasStrategyAC getOuterType() {
      return BoomerangAliasStrategyAC.this;
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

    private BoomerangAliasStrategyAC getOuterType() {
      return BoomerangAliasStrategyAC.this;
    }

  }

  @Override
  public void shutdown() {
    try {
      writer.close();
    } catch (IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  }
}
