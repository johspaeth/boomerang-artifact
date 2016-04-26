package soot.jimple.infoflow.android.TestApps;

import java.io.IOException;
import java.util.Arrays;

import soot.jimple.infoflow.Infoflow;

public class ACvsCCRunner {
  public static void main(String args[]) {
    System.out.println("STARTING with " + Arrays.toString(args));
    try {
      System.setProperty("aliasstrategy", "boomerangAC");
      Test.main(args);
    } catch (IOException | InterruptedException e) {
      System.out.println("Dart crashed on" + args[0]);
      System.out.println("Queries were executed" + Infoflow.aliasQueryCounter);
      e.printStackTrace();
    };
  }
}
