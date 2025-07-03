package uk.gre.ac.openjmlsec.generatedClasses;

//@ model import org.jmlspecs.lang.*;

public class TestReplace {
  
  public static class SubClass {
    int TestReplace;
    
    public void TestReplace(int a) {
      TestReplace = 5;
    }
  }
  
  public static void foo() {
    int TestReplace;
  }
    /*@
      requires a != 1854674; 
   */

  /*@ pure*/ public void TestReplace(int a) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.TestReplace", "", "int", "TestReplace", new java.lang.Object[]{a})) {
      throw new java.lang.RuntimeException();
    }
  }
  
  public static void main(String[] args) {
    TestReplace main = new TestReplace();
    TestReplace.foo();
    main.TestReplace(3);
  }
}