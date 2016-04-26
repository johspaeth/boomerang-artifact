package evaluator.impl;

import alias.Util;
import evaluator.Main;
import evaluator.pointerbench.parser.QueryInfo;
import iohoister.analysis.MayAliasAnalysis;
import soot.Local;
import soot.PointsToSet;
import soot.jimple.spark.ondemand.AllocAndContextSet;
import soot.jimple.spark.ondemand.WrappedPointsToSet;
import soot.jimple.spark.sets.EmptyPointsToSet;
import spa.jimple.spark.ondemand.DemandCSPointsTo;

public class SBEvaluator extends Evaluator {

  public SBEvaluator(QueryInfo queryInfo) {
    super(queryInfo);
  }


  @Override
  protected boolean alias(String l) {
    Util.TIME_BUDGET = Main.ANALYSIS_TIMEOUT_MS;
    MayAliasAnalysis.queryCrashed = false;
    Util.aliasStart = System.currentTimeMillis();
    DemandCSPointsTo pta = DemandCSPointsTo.makeWithBudget(75000, 10);
    PointsToSet res1 = pta.reachingObjects(parse(l));
    if (res1 == null || res1.isEmpty())
      return false;
    Util.aliasStart = System.currentTimeMillis();
    MayAliasAnalysis.queryCrashed = false;
    PointsToSet res2 = pta.reachingObjects(parse(testVariable));
    if (res2 == null || res2.isEmpty())
      return false;
    return res1.hasNonEmptyIntersection(res2);
  }


  private Local parse(String var) {
    if (var.contains(".")) {
      // There is no way of querying an access path directly.
      throw new AccessPathNotSupportedException("AccessPath are not supported");
    }
    return Util.findSingleLocal(this.method.getActiveBody().getLocals(), var);
  }


  @Override
  protected int getPointsToSize() {
    Util.TIME_BUDGET = 5000;
    Util.aliasStart = System.currentTimeMillis();
    DemandCSPointsTo pta = DemandCSPointsTo.makeWithBudget(75000, 10);
    PointsToSet other = pta.reachingObjects(parse(testVariable));
    if (other instanceof AllocAndContextSet) {
      return ((AllocAndContextSet) other).size();
    } else if (other instanceof WrappedPointsToSet) {
      return ((WrappedPointsToSet) other).getWrapped().size();
    } else if (other instanceof EmptyPointsToSet) {
      return 0;
    }

    throw new RuntimeException("Is of class " + other.getClass());
  }

}
