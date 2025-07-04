package testclasses;

//@ model import java.lang.Math.*;

public class PaperExample {
	//@ normal_behavior
	//@		requires Math.abs(y) >= Math.abs(x);
	//@ compromised_behavior
	//@     requires Math.abs(y) < Math.abs(x);
	//@     alarms OUT_OF_BOUNDS Math.abs(y) < Math.abs(x);
	/*@     action OUT_OF_BOUNDS {
	 			var temp = x;
	            x = y;
	            y = temp;
	        };*/
	//@ pure
	public static double Foo(int x, int y) {
		if (y == 0) return 0;
	    return x / (double) y;
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
