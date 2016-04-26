package soot.jimple.infoflow.android.TestApps;

import java.io.IOException;
import java.util.Arrays;

import soot.jimple.infoflow.Infoflow;

public class AliasRunner {
  public static void main(String args[]) {
    System.out.println("STARTING with " + Arrays.toString(args));
    try {
      System.setProperty("aliasstrategy", "boomerang");
      Test.main(args);
    } catch (IOException | InterruptedException e) {
      System.out.println("Boomerang crashed on" + args[0]);
      System.out.println("Queries were executed" + Infoflow.aliasQueryCounter);
      e.printStackTrace();
    };

    try {
      System.setProperty("aliasstrategy", "da");
      Test.main(args);
    } catch (IOException | InterruptedException e) {
      System.out.println("DA crashed on" + args[0]);
      System.out.println("Queries were executed" + Infoflow.aliasQueryCounter);
      e.printStackTrace();
    };
    try {
      System.setProperty("aliasstrategy", "sb");
      Test.main(args);
    } catch (IOException | InterruptedException e) {
      System.out.println("SB crashed on" + args[0]);
      System.out.println("Queries were executed" + Infoflow.aliasQueryCounter);
      e.printStackTrace();
    };
    try {
      System.setProperty("aliasstrategy", "flow");
      Test.main(args);
    } catch (IOException | InterruptedException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    };



  }
}
