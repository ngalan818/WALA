rootProject.name = "com.ibm.wala"

includeBuild("build-logic")

include(
    "com.ibm.wala.cast",
    "com.ibm.wala.cast:smoke_main",
    "com.ibm.wala.cast:xlator_test",
    "com.ibm.wala.cast:cast",
    "com.ibm.wala.cast.java",
    "com.ibm.wala.cast.java.ecj",
    "com.ibm.wala.cast.java.test.data",
    "com.ibm.wala.cast.js",
    "com.ibm.wala.cast.js.html.nu_validator",
    "com.ibm.wala.cast.js.nodejs",
    "com.ibm.wala.cast.js.rhino",
    "com.ibm.wala.core",
    "com.ibm.wala.dalvik",
    "com.ibm.wala.ide",
    "com.ibm.wala.ide.jdt",
    "com.ibm.wala.ide.jdt.test",
    "com.ibm.wala.ide.jsdt",
    "com.ibm.wala.ide.jsdt.tests",
    "com.ibm.wala.ide.tests",
    "com.ibm.wala.scandroid",
    "com.ibm.wala.shrike",
    "com.ibm.wala.util",
)