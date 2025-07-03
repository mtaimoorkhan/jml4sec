package generatedClasses;

//@ model import org.jmlspecs.lang.*;

public class PaperExample {
    /*@
    normal_behavior
      requires Math.abs(y) >= Math.abs(x); 
      ensures -1.0 <= \result <= 1.0; 
also
    compromised_behavior
      requires x > y; 
      alarms OUT_OF_BOUNDS Math.abs(y) < Math.abs(x); 
      action OUT_OF_BOUNDS {
        int temp = x;
        x = y;
        y = temp;
      }; 
also
    exceptional_behavior
      requires y == 0; 
      signals (RuntimeException) y == 0; 
   */

  public static double Foo(int x, int y) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("testclasses.PaperExample", "", "int,int", "Foo", new java.lang.Object[]{x, y})) {
      boolean EscVerify_recovered = false;
      if (Math.abs(y) < Math.abs(x)) {
        int temp = x;
        x = y;
        y = temp;
        EscVerify_recovered = true;
      }
      if (y == 0) throw new RuntimeException();
      if (!EscVerify_recovered) throw new java.lang.RuntimeException();
    }
    return (double)x / (double)y;
  }
  
  public static void main(String[] args) {
    System.out.println(Foo(10, 100));
    System.out.println(Foo(-10, 100));
    System.out.println(Foo(10, -100));
    System.out.println(Foo(-10, -100));
    System.out.println(Foo(100, 10));
    System.out.println(Foo(-100, 10));
    System.out.println(Foo(100, -10));
    System.out.println(Foo(-100, -10));
    System.out.println(Foo(0, 0));
  }
}