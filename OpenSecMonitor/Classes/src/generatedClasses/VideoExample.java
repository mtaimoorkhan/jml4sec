package generatedClasses;

//@ model import org.jmlspecs.lang.*;
import uk.gre.ac.openjmlsec.gen.EscRunner;

public class VideoExample {
    /*@
    normal_behavior
      requires x >= 10 && y % 2 == 0; 
also
    compromised_behavior
      requires x < 10 || y % 2 != 0; 
      alarms TO_SMALL x < 10; 
      action TO_SMALL {
        EscRunner.Log("X is too small (" + x + "), setting to 10");
        x = 10;
      }; 
      alarms NOT_EVEN y % 2 != 0; 
      action NOT_EVEN {
        EscRunner.Log("Y is not even (" + y + "), doubling it");
        y *= 2;
      }; 
      action null {
        EscRunner.Log("# Verification failed!");
        return;
      }; 
   */

  /*@ pure*/ public static void Foo(int x, int y) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("testclasses.VideoExample", "", "int,int", "Foo", new java.lang.Object[]{x, y})) {
      boolean EscVerify_recovered = false;
      if (x < 10) {
        EscRunner.Log("X is too small (" + x + "), setting to 10");
        x = 10;
        EscVerify_recovered = true;
      }
      if (y % 2 != 0) {
        EscRunner.Log("Y is not even (" + y + "), doubling it");
        y *= 2;
        EscVerify_recovered = true;
      }
      if (!EscVerify_recovered) {
        EscRunner.Log("# Verification failed!");
        return;
      }
    }
  }
  
  public static void main(String[] args) {
    Foo(100, 2);
    Foo(1, 6);
    Foo(10, 1);
    Foo(1, 1);
  }
}