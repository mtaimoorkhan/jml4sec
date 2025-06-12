package uk.gre.ac.openjmlsec.generatedClasses;

//@ model import org.jmlspecs.lang.*;

public class Authentication {
    /*@
      requires x > 0 && x < 10000 && y > 0 && y < 10000; 
   */

  /*@ pure*/ public static int add(int x, int y) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.Authentication", "", "int,int", "add", new java.lang.Object[]{x, y})) {
      throw new java.lang.RuntimeException();
    }
    return x + y;
  }
  
  public static void main(String[] args) {
    add(100, 100);
  }
}