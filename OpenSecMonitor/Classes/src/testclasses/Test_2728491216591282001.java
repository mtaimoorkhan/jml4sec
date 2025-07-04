package testclasses;

//@ model import org.jmlspecs.lang.*;

public class Test_2728491216591282001 {
    /*@
    normal_behavior
      requires y >= x; 
      ensures 0.0 <= \result && \result <= 1.0; 
also
    compromised_behavior
      requires !(x > y); 
      alarms OUT_OF_BOUNDS x > y; 
      action OUT_OF_BOUNDS {
        var temp = x;
        x = y;
        y = temp;
      }; 
   */

  /*@ pure*/ public static double Foo(int x, int y) {
    if (y == 0 || y > x) return 0;
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