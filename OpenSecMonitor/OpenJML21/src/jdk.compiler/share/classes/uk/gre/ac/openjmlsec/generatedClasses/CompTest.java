package uk.gre.ac.openjmlsec.generatedClasses;

//@ model import org.jmlspecs.lang.*;

public class CompTest {
    /*@
    public normal_behavior
      requires !isZero(b) && !isNeg(a); 
      ensures \result == a / b; 
also
    compromised_behavior
      requires isNeg(a); 
      alarms negative isNeg(a); 
      action negative {
        System.out.println("negative was caught");
        a = -a;
      }; 
also
    exceptional_behavior
      requires isZero(b); 
      signals_only RuntimeException; 
      signals (RuntimeException) isZero(b); 
   */

  /*@ pure*/ public static double Div(double a, double b) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.CompTest", "", "double,double", "Div", new java.lang.Object[]{a, b})) {
      boolean EscVerify_recovered = false;
      if (isNeg(a)) {
        System.out.println("negative was caught");
        a = -a;
        EscVerify_recovered = true;
      }
      if (isZero(b)) throw new RuntimeException();
      if (!EscVerify_recovered) throw new java.lang.RuntimeException();
    }
    if (b == 0) throw new RuntimeException();
    return a / b;
  }
  
  public static void main(String[] args) {
    System.out.println("Div: " + Div(10, 2));
    System.out.println("Div: " + Div(-10, 2));
    System.out.println("Div: " + Div(10, 0));
  }
    /*@
      ensures \result == (b == 0); 
   */

  /*@ pure*/ public static boolean isZero(double b) {
    return b == 0;
  }
    /*@
      ensures \result == (a < 0); 
   */

  /*@ pure*/ public static boolean isNeg(double a) {
    return a < 0;
  }
}