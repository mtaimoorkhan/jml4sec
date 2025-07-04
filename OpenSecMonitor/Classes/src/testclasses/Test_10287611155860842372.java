package testclasses;

//@ model import org.jmlspecs.lang.*;
//@ model import java.lang.Math.*;

public class Test_10287611155860842372 {
    /*@
    normal_behavior
      requires Math.abs(y) >= Math.abs(x); 
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
    if (y == 0) return 0;
    return x / (double)y;
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
    Foo(10, -100);
  }
}