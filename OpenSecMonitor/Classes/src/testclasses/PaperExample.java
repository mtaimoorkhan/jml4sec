package testclasses;

public class PaperExample {
	//@ normal_behavior
	//@     requires Math.abs(y) >= Math.abs(x);
	//@     ensures -1.0 <= \result <= 1.0;
	//@ compromised_behavior
	//@     requires x > y;
	//@     alarms OUT_OF_BOUNDS Math.abs(y) < Math.abs(x);
	/*@     action OUT_OF_BOUNDS {
	 			var temp = x;
	            x = y;
	            y = temp;
	        };*/
	//@ exceptional_behavior
	//@		requires y == 0;
	//@		signals (RuntimeException) y == 0;
	public static double Foo(int x, int y){
	    return (double) x / (double) y;
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
