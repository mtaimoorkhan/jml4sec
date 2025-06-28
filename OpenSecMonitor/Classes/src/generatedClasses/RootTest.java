package generatedClasses;

//@ model import org.jmlspecs.lang.*;

public class RootTest {
  RootTest some_random_var;
  int v;
    /*@
      requires b != null; 
      requires b.v > 4; 
also
    compromised_behavior
      requires b.v <= 4; 
   */

  /*@ pure*/ void a(RootTest b) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("testclasses.RootTest", "", "RootTest", "a", new java.lang.Object[]{b})) {
      boolean EscVerify_recovered = false;
      if (!EscVerify_recovered) throw new java.lang.RuntimeException();
    }
  }
  
  public static void main(String[] args) {
    RootTest r = new RootTest();
    r.v = 100;
    r.a(r);
  }
}