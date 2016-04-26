#!/bin/bash
JAVA_CP="boomerang.jar:infoflow-android.jar:infoflow.jar:sbandda.jar:../Boomerang/lib/grph-1.8.0-big.jar:../Boomerang/lib/soot-trunk.jar:../Boomerang/lib/heros-trunk.jar:../soot-infoflow-android/lib/AXMLPrinter2.jar:../soot-infoflow-android/lib/axml-2.0.jar"
JVM_ARGS="-Xms32g -Xmx32g"
FD_CLASS="soot.jimple.infoflow.android.TestApps.AliasRunner"
ANDROID_PLATFORM="path/to/android/platforms"
TIMEOUT="15"
FILES="apps/*.apk"



for apk in $FILES
	do
		java $JVM_ARGS -classpath $JAVA_CP $FD_CLASS "${apk}" $ANDROID_PLATFORM --timeout $TIMEOUT --aplength 5
	done

