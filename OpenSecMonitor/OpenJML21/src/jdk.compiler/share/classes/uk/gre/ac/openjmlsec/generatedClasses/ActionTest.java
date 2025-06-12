package uk.gre.ac.openjmlsec.generatedClasses;

//@ model import org.jmlspecs.lang.*;

public class ActionTest {
    /*@
      requires x == 3; 
also
    compromised_behavior
      requires x != 3; 
      alarms "ident?" aFunc(); 
      action "ident?" aFunc(); 
   */

  /*@ pure*/ static void A(int x) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.ActionTest", "", "int", "A", new java.lang.Object[]{x})) {
      if (x != 3) aFunc();
    }
  }
  
  public static void main(String[] args) {
    A(3);
  }
  
  public static void aFunc() {
  }
}