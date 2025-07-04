package testclasses;

//@ model import org.jmlspecs.lang.*;

public class Test_7217477913780133054 {
    /*@
    normal_behavior
      requires Math.abs(y) >= Math.abs(x); 
      ensures -1.0 <= \result <= 1.0; 
also
    compromised_behavior
      requires !(x > y); 
      alarms OUT_OF_BOUNDS Math.abs(y) < Math.abs(x); 
      action OUT_OF_BOUNDS {
        var temp = x;
        x = y;
        y = temp;
      }; 
also
    exceptional_behavior
      requires x == 0 && y == 0; 
      signals (RuntimeException) x == 0 && y == 0; 
   */

  /*@ pure*/ public static double Foo(int x, int y) {
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
  
  private void test_Foo() {
    Foo(10, 100);
  }
}