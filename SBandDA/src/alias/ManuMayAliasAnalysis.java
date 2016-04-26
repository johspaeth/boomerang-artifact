package alias;

import iohoister.analysis.MayAliasAnalysis;
import soot.Local;
import soot.PointsToAnalysis;
import soot.SootMethod;
import soot.jimple.DefinitionStmt;
import soot.jimple.spark.ondemand.DemandCSPointsTo;

public class ManuMayAliasAnalysis extends MayAliasAnalysis {
	private static ManuMayAliasAnalysis ins;
	private PointsToAnalysis pta;
	
	public ManuMayAliasAnalysis() {		
		pta = DemandCSPointsTo.makeWithBudget(
			Util.MANU_MAX_TRAVERSAL, Util.MANU_MAX_PASSES, false);
	}
	
	public static ManuMayAliasAnalysis v() {
		if (ins == null) {
			ins = new ManuMayAliasAnalysis();
		}
		
		return ins;
	}
	
	@Override
	public boolean mayAlias(Local v1, DefinitionStmt s1, SootMethod m1,
			Local v2, DefinitionStmt s2, SootMethod m2) {
		return Util.traditionalMayAlias(v1, m1, v2, m2, pta);
	}

	@Override
	public void setQueryCounter(int counter) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void shutdown() {
		// TODO Auto-generated method stub
		
	}

}
