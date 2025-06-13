package uk.gre.ac.openjmlsec.generatedClasses;

//@ model import org.jmlspecs.lang.*;

public class VerifyTest {
  
  public static class SubClass {
        /*@
        requires i == 10; 
     */

    /*@ pure*/ public static int Func(int i) {
      if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.VerifyTest", "SubClass", "int", "Func", new java.lang.Object[]{i})) {
        throw new java.lang.RuntimeException();
      }
      return i;
    }
  }
    /*@
      requires i == 0; 
   */

  /*@ pure*/ public static void Func(int i, int a) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.VerifyTest", "", "int,int", "Func", new java.lang.Object[]{i, a})) {
      throw new java.lang.RuntimeException();
    }
  }
    /*@
      requires 'a' <= c && c <= 'z'; 
   */

  /*@ pure*/ public static void Func(char c, int a) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.VerifyTest", "", "char,int", "Func", new java.lang.Object[]{c, a})) {
      throw new java.lang.RuntimeException();
    }
  }
  
  public static void main(String[] args) {
    Func(0, 2);
  }
}