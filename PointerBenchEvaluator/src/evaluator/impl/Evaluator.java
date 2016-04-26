package evaluator.impl;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import soot.SootMethod;
import soot.jimple.Stmt;

import com.google.common.collect.Sets;

import evaluator.pointerbench.parser.AliasInfo;
import evaluator.pointerbench.parser.ExprResult;
import evaluator.pointerbench.parser.QueryInfo;

public abstract class Evaluator {
  protected SootMethod method;
  protected String testVariable;
  protected Stmt testStmt;
  protected Map<String, AliasInfo> allocationSites;


  public Evaluator(QueryInfo queryInfo) {
    method = queryInfo.getMethod();
    testVariable = queryInfo.getVariable();
    testStmt = queryInfo.getStmt();
    allocationSites = queryInfo.getAllocationSiteInfo();
  }

  public ExprResult evaluateAlias() {
    Set<String> falseNegativesPairs = new HashSet<>();
    Set<String> falsePositivesPairs = new HashSet<>();
    Set<String> gt = new HashSet<>();
    for (String k : allocationSites.keySet()) {
      AliasInfo aliasInfo = allocationSites.get(k);
      for (String l : aliasInfo.getAliases()) {
        gt.add(l);
        if (!alias(l)) {
          falseNegativesPairs.add(l);
        };
      };
    }
    Set<String> notAliasIntersection = null;
    for (String k : allocationSites.keySet()) {
      AliasInfo aliasInfo = allocationSites.get(k);
      if (notAliasIntersection == null) {
        notAliasIntersection = aliasInfo.getNotAliases();
      } else {
        notAliasIntersection = Sets.intersection(notAliasIntersection, aliasInfo.getNotAliases());
      }
    }
    if (notAliasIntersection != null) {
      for (String l : notAliasIntersection) {
        if (alias(l)) {
          falsePositivesPairs.add(l);
        };
      };
    }
    int pointsToSize = getPointsToSize();
    System.out.println("=========RESULTS FOR  " + method.getDeclaringClass().getName()
        + this.getClass().getSimpleName() + " ========");
    System.out.println("Ground Truth:" + gt.size() + "," + gt);
    System.out.println("False Negative:" + falseNegativesPairs.size() + "," + falseNegativesPairs);
    System.out.println("False Positive:" + falsePositivesPairs.size() + "," + falsePositivesPairs);
    return new ExprResult(falsePositivesPairs, falseNegativesPairs, pointsToSize);
  }


  protected abstract boolean alias(String l);

  protected abstract int getPointsToSize();
}
