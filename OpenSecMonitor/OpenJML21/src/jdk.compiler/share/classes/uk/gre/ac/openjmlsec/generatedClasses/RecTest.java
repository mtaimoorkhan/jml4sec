package uk.gre.ac.openjmlsec.generatedClasses;

//@ model import org.jmlspecs.lang.*;

public class RecTest {
  
  static class Rec {
    Rec test;
    int v;
    
    Rec() {
    }
  }
    /*@
      requires t != null;
      requires t.v > 4; 
also
    compromised_behavior
      requires t.v <= 4; 
   */

  /*@ pure*/ static void a() {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.RecTest", "", "", "a", new java.lang.Object[]{t})) {
      boolean EscVerify_recovered = false;
      if (!EscVerify_recovered) throw new java.lang.RuntimeException();
    }
  }
  static Rec t = new Rec();
  
  public static void main(String[] args) {
    t.test = t;
    t.v = 5;
    a();
    t.v = 0;
    a();
  }
}