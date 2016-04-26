package evaluator.impl;

import alias.Util;
import edu.osu.cse.pa.YanMayAlias;
import evaluator.Main;
import evaluator.pointerbench.parser.QueryInfo;
import iohoister.analysis.MayAliasAnalysis;
import soot.Local;

public class DAEvaluator extends Evaluator {

  public DAEvaluator(QueryInfo queryInfo) {
    super(queryInfo);
  }

  private Local parse(String var) {
    if (var.contains(".")) {
      throw new AccessPathNotSupportedException("AccessPath are not supported");
    }
    return Util.findSingleLocal(this.method.getActiveBody().getLocals(), var);
  }

  @Override
  protected boolean alias(String l) {
    YanMayAlias analysis = new YanMayAlias();
    analysis.buildSPG();
    Util.TIME_BUDGET = Main.ANALYSIS_TIMEOUT_MS;
    Util.aliasStart = System.currentTimeMillis();
    MayAliasAnalysis.queryCrashed = false;
    boolean mayAlias = analysis.mayAlias(parse(l), null, method, parse(testVariable), null, method);
    return mayAlias;
  }

  @Override
  protected int getPointsToSize() {
    return -1;
  }

}
