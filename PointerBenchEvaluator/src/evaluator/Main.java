package evaluator;

import java.io.FileWriter;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import evaluator.impl.AccessPathNotSupportedException;
import evaluator.impl.BoomerangEvaluator;
import evaluator.impl.DAEvaluator;
import evaluator.impl.SBEvaluator;
import evaluator.pointerbench.parser.ExprResult;
import evaluator.pointerbench.parser.QueryInfo;
import soot.Body;
import soot.G;
import soot.PackManager;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.Transform;
import soot.Unit;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.options.Options;

public class Main {
  public final static String[] testcases = new String[] {
"basic.SimpleAlias1", "basic.Loops1", "basic.Loops2", "basic.Interprocedural1",
          "basic.Interprocedural2", "basic.Parameter1", "basic.Parameter2", "basic.Recursion1",
          "basic.ReturnValue1", "basic.ReturnValue2", "basic.ReturnValue3", "basic.Branching1",

          "cornerCases.AccessPath1", "cornerCases.ContextSensitivity1",
          "cornerCases.ContextSensitivity2", "cornerCases.ContextSensitivity3",
          "cornerCases.FieldSensitivity1", "cornerCases.FieldSensitivity2",
          "cornerCases.FlowSensitivity1", "cornerCases.ObjectSensitivity1",
          "cornerCases.ObjectSensitivity2", "cornerCases.StrongUpdate1",
          "cornerCases.StrongUpdate2",

          "generalJava.Exception1", "generalJava.Exception2", "generalJava.Interface1",
          "generalJava.Null1", "generalJava.Null2", "generalJava.OuterClass1",
          "generalJava.StaticVariables1", "generalJava.SuperClasses1",

          "collections.Array1", "collections.List1", "collections.List2", "collections.Map1",
          "collections.Set1"
  };


  private static int ALIAS_GROUND_TRUTH_TRUE_POSITIVES = 0;
  private static int ALLOCATION_GROUND_TRUTH_TRUE_POSITIVES = 0;

  private static int ALIAS_MANU_FALSE_NEGATIVES = 0;
  private static int ALIAS_BOOMERANG_FALSE_NEGATIVES = 0;
  private static int ALIAS_YAN_FALSE_NEGATIVES = 0;

  private static int ALIAS_MANU_FALSE_POSITIVES = 0;
  private static int ALIAS_BOOMERANG_FALSE_POSITIVES = 0;
  private static int ALIAS_YAN_FALSE_POSITIVES = 0;

  private static int ALLOCATIONS_MANU_FALSE_NEGATIVES = 0;
  private static int ALLOCATIONS_BOOMERANG_FALSE_NEGATIVES = 0;

  private static int ALLOCATIONS_MANU_FALSE_POSITIVES = 0;
  private static int ALLOCATIONS_BOOMERANG_FALSE_POSITIVES = 0;


  /**
   * Every analysis budget in milliseconds
   */
  public final static int ANALYSIS_TIMEOUT_MS = 10000;


  private final static String FALSE_POSITIVE = "+";
  private final static String FALSE_NEGATIVE = "×";
  private final static String TRUE_POSITIVE = "✓";


  public static void main(String... args) throws IOException {
    final FileWriter writer = new FileWriter("PointerBench-Evaluation.csv");
    writer.write(
        "Testcase;Ground Truth: Alias Pairs;Ground Truth: Allocation Sites;DA - Alias Pairs;SB - Alias Pairs;SB - Allocation Sites;Boomerang - Alias Pairs;Boomerang - Allocation Sites;\n");
    for (final String testcase : testcases) {
      initializeSoot(testcase);
      Transform callConstantTransformer = new Transform("wjtp.preparation", new SceneTransformer() {

        @Override
        protected void internalTransform(String phaseName, Map<String, String> options) {
          try {
            QueryInfo queryInfo = retrieveQueryInfo();
            int testTP = queryInfo.getTruePositives().size();
            int ptsTP = queryInfo.computeExecpectedPointsToSize();
            ALIAS_GROUND_TRUTH_TRUE_POSITIVES += testTP;
            ALLOCATION_GROUND_TRUTH_TRUE_POSITIVES += ptsTP;
            writer.write(testcase + ";" + testTP + ";" + ptsTP + ";");
            int fp;
            int fn;
            ExprResult res;

            // Analysis with Yan (DA in paper).
            try {
              DAEvaluator yan = new DAEvaluator(queryInfo);
              res = yan.evaluateAlias();
              fp = res.getFalsePositive().size();
              fn = res.getFalseNegatives().size();
            } catch (AccessPathNotSupportedException e) {
              fn = testTP;
              fp = 0;
            }
            ALIAS_YAN_FALSE_NEGATIVES += fn;
            ALIAS_YAN_FALSE_POSITIVES += fp;
            writer.write(
                multiplyString((testTP - fn), TRUE_POSITIVE) + multiplyString((fp), FALSE_POSITIVE)
                    + multiplyString((fn), FALSE_NEGATIVE) + ";");

            // Analysis with Manu (SB in paper).
            int ptsrep = 0;
            boolean accessPathNotSupported = false;
            try {
              SBEvaluator manu = new SBEvaluator(queryInfo);
              res = manu.evaluateAlias();
              fp = res.getFalsePositive().size();
              fn = res.getFalseNegatives().size();
              ptsrep = res.getPointsToSetSize();
            } catch (AccessPathNotSupportedException e) {
              fn = testTP;
              fp = 0;
              accessPathNotSupported = true;
            }
            ALIAS_MANU_FALSE_NEGATIVES += fn;
            ALIAS_MANU_FALSE_POSITIVES += fp;
            ALLOCATIONS_MANU_FALSE_NEGATIVES += (accessPathNotSupported ? ptsTP : 0);
            ALLOCATIONS_MANU_FALSE_POSITIVES += (ptsrep - ptsTP);
            writer.write(multiplyString((testTP - fn), TRUE_POSITIVE)
                + multiplyString((fp), FALSE_POSITIVE) + multiplyString((fn), FALSE_NEGATIVE) + ";"
                + multiplyString((accessPathNotSupported ? 0 : ptsTP), TRUE_POSITIVE)
                + multiplyString((accessPathNotSupported ? ptsTP : 0), FALSE_NEGATIVE)
                + multiplyString((ptsrep - ptsTP), FALSE_POSITIVE) + ";");


            // Analysis with our analysis (Boomerang)

            BoomerangEvaluator dart = new BoomerangEvaluator(queryInfo);
            res = dart.evaluateAlias();
            fp = res.getFalsePositive().size();
            fn = res.getFalseNegatives().size();
            ptsrep = res.getPointsToSetSize();
            ALIAS_BOOMERANG_FALSE_NEGATIVES += fn;
            ALIAS_BOOMERANG_FALSE_POSITIVES += fp;
            ALLOCATIONS_BOOMERANG_FALSE_NEGATIVES += 0;
            ALLOCATIONS_BOOMERANG_FALSE_POSITIVES += (ptsrep - ptsTP);
            writer.write(multiplyString((testTP - fn), TRUE_POSITIVE)
                + multiplyString((fp), FALSE_POSITIVE) + multiplyString((fn), FALSE_NEGATIVE) + ";"
                + multiplyString(ptsTP, TRUE_POSITIVE)
                + multiplyString((ptsrep - ptsTP), FALSE_POSITIVE) + ";\n");

          } catch (IOException e) {
            e.printStackTrace();
          }
        }

        private String multiplyString(int j, String string) {
          String s = "";
          for (int i = 0; i < j; i++) {
            s += " " + string;
          }
          return s;
        }

      });


      PackManager.v().getPack("cg").apply();
      PackManager.v().getPack("wjtp").add(callConstantTransformer);
      PackManager.v().getPack("wjtp").apply();
    }
    float manuRecall = recall(ALIAS_GROUND_TRUTH_TRUE_POSITIVES, ALIAS_MANU_FALSE_NEGATIVES);
    float manuPrecision = precision(ALIAS_GROUND_TRUTH_TRUE_POSITIVES, ALIAS_MANU_FALSE_POSITIVES);

    float boomerangRecall = recall(ALIAS_GROUND_TRUTH_TRUE_POSITIVES, ALIAS_BOOMERANG_FALSE_NEGATIVES);
    float boomerangPrecision =
        precision(ALIAS_GROUND_TRUTH_TRUE_POSITIVES, ALIAS_BOOMERANG_FALSE_POSITIVES);

    float yanRecall = recall(ALIAS_GROUND_TRUTH_TRUE_POSITIVES, ALIAS_YAN_FALSE_NEGATIVES);
    float yanPrecision = precision(ALIAS_GROUND_TRUTH_TRUE_POSITIVES, ALIAS_YAN_FALSE_POSITIVES);


    float manuAllocRecall =
        recall(ALLOCATION_GROUND_TRUTH_TRUE_POSITIVES, ALLOCATIONS_MANU_FALSE_NEGATIVES);
    float manuAllocPrecision =
        precision(ALLOCATION_GROUND_TRUTH_TRUE_POSITIVES, ALLOCATIONS_MANU_FALSE_POSITIVES);

    float boomerangAllocRecall =
        recall(ALLOCATION_GROUND_TRUTH_TRUE_POSITIVES, ALLOCATIONS_BOOMERANG_FALSE_NEGATIVES);
    float boomerangAllocPrecision =
        precision(ALLOCATION_GROUND_TRUTH_TRUE_POSITIVES, ALLOCATIONS_BOOMERANG_FALSE_POSITIVES);

    writer.write("~~~~~~~~~~~Alias Pairs~~~~~~~~~~~\n");
    writer.write("Precision DA=" + yanPrecision + ",");
    writer.write("Recall DA=" + yanRecall + "\n");

    writer.write("Precision SB=" + manuPrecision + ",");
    writer.write("Recall SB=" + manuRecall + "\n");

    writer.write("Precision Boomerang=" + boomerangPrecision + ",");
    writer.write("Recall Boomerang=" + boomerangRecall + "\n");

    writer.write("~~~~~~~~~~~Allocation Sites~~~~~~~~~~~\n");
    writer.write("Precision SB=" + manuAllocPrecision + ",");
    writer.write("Recall SB=" + manuAllocRecall + "\n");

    writer.write("Precision Boomerang=" + boomerangAllocPrecision + ",");
    writer.write("Recall Boomerang=" + boomerangAllocRecall + "\n");
    writer.close();
  }


  private static float recall(int tp, int fn) {
    return ((float) tp) / (tp + fn);
  }

  private static float precision(int tp, int fp) {
    return ((float) tp) / (tp + fp);
  }

  protected static QueryInfo retrieveQueryInfo() {
    String alloc = null;
    QueryInfo queryInfo = new QueryInfo();
    for (SootClass sc : Scene.v().getClasses()) {
      for (SootMethod sm : sc.getMethods()) {
        if (!sm.hasActiveBody())
          continue;
        Body methodBody = sm.retrieveActiveBody();
        for (Unit u : methodBody.getUnits()) {
          Stmt s = (Stmt) u;

          if (s.containsInvokeExpr()) {
            InvokeExpr ie = s.getInvokeExpr();
            SootMethod callee = ie.getMethod();

            if (callee.getDeclaringClass().getName().equals("benchmark.internal.Benchmark")) {
              if (callee.getName().equals("test")) {
                String variableToTest = ie.getArg(0).toString();
                String results = ie.getArg(1).toString();
                queryInfo.registerTestInfo(s, sm, variableToTest, results);

              } else if (callee.getName().equals("alloc")) {
                alloc = ie.getArgs().get(0).toString();
              }
            }
          } else if (s instanceof AssignStmt && alloc != null) {
            queryInfo.registerAllocationSite(s, alloc);
            alloc = null;
          }
        }
      }
    }
    return queryInfo;
  }


  @SuppressWarnings("static-access")
  private static void initializeSoot(String testcase) {
    G.v().reset();
    String sootCp = System.getProperty("BenchmarkDir");

    Options.v().set_soot_classpath(sootCp);
    Options.v().set_main_class(testcase);
    Options.v().set_whole_program(true);
    Options.v().set_output_format(Options.output_format_none);
    Options.v().set_prepend_classpath(true);
    Options.v().set_no_bodies_for_excluded(true);
    Options.v().set_allow_phantom_refs(true);

    Options.v().setPhaseOption("cg", "trim-clinit:false");
    Options.v().setPhaseOption("jb", "use-original-names:true");
    Options.v().setPhaseOption("cg.spark", "on");

    List<String> includeList = new LinkedList<String>();
    includeList.add("java.lang.*");
    includeList.add("java.util.*");
    includeList.add("java.io.*");
    includeList.add("sun.misc.*");
    includeList.add("java.net.*");
    includeList.add("javax.servlet.*");
    includeList.add("javax.crypto.*");

    Options.v().set_include(includeList);

    Scene.v().addBasicClass(testcase, SootClass.BODIES);
    Scene.v().loadNecessaryClasses();
    SootClass c = Scene.v().forceResolve(testcase, SootClass.BODIES);
    if (c != null) {
      c.setApplicationClass();
    }
    SootMethod methodByName = c.getMethodByName("main");
    List<SootMethod> ePoints = new LinkedList<>();
    ePoints.add(methodByName);
    Scene.v().setEntryPoints(ePoints);
  }
}
