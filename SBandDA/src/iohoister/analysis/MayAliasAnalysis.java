package iohoister.analysis;

import soot.Local;
import soot.SootMethod;
import soot.jimple.DefinitionStmt;

public abstract class MayAliasAnalysis {
	public static boolean queryCrashed = false;
	public abstract boolean mayAlias(Local v1, DefinitionStmt s1, SootMethod m1, Local v2,  DefinitionStmt s2, SootMethod m2);
	public abstract void setQueryCounter(int counter);
	public abstract void shutdown();
}
