# Boomerang Artifact Evaluation

This is the artifact which was evaluated within the paper. It is a bundle to be able to evaluate soundness and precision of the Boomerang, SB[1] and DA[2]. In addition to that the artifact can be used to run it on arbitrary Android applications.

It consists of six Eclipse projects:

* Boomerang - Contains examples on how to use Boomerang.
* PointerBench - The Benchmark suite to evaluate precision and soundness of general pointer analyses.
* PointerBenchEvaluator - Parser and driver to execute and evaluate all queries of PointerBench with Boomerang, SB and DA, as used in RQ1 of the paper.
* SBandDA - Contains the implementation of the analyses as referred to SB and DA in the paper. </p></li>
* soot-infoflow-alias - Adopted FlowDroid integration for Boomerang, SB and DA.
* soot-infoflow-android - FlowDroid's implementation to be able to run on Android.

To run the experiments **RQ1** use method `evaluator.Main.main()`from the [PointerBenchEvaluator](wiki/pointerbenchevaluator.html) project. Supply `-Xmx4g -DBenchmarkDir=/absolute/path/to/pointerbench/bin` as additional VM arguments.

For the experiments conducted in **RQ2** and *RQ3**, see the detailed instruction in the [soot-infoflow-android](s) project.

[1] **Refinement-based context-sensitive points-to analysis for Java.** 

by Manu Sridharan and Rastislav Bodík

[2] **Demand-Driven Context-Sensitive Alias Analysis for Java**

by Dacong Yan, Guoqing Xu and Atanas Rountev
