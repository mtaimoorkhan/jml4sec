package testclasses;

//@ model import org.jmlspecs.lang.*;

public class Test_15352812224170754130 {
    /*@
      ensures \result >= 0; 
   */

  //@ model pure static int ABS(int x);
    /*@
    normal_behavior
      requires ABS(y) >= ABS(x); 
      ensures -1.0 <= \result && \result <= 1.0; 
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
      requires y == 0; 
      signals (RuntimeException) y == 0; 
   */

  /*@ pure*/ public static double Foo(int x, int y) {
    if (y == 0) throw new RuntimeException();
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