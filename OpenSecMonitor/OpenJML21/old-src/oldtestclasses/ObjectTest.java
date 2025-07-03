package uk.gre.ac.openjmlsec.testclasses;

public class ObjectTest {
	static class Cls{
		public int value;

	    //modifies value;
		public Cls(int arg) {
			value = arg;
		}
	}
	
	Cls cls = new Cls(10);
	
	//@ requires a < cls.value;
	//@ pure
	void do_something(int a) {
		
	}
	
	//@ requires a.value > 5;
	//@ pure
	void do_something2(Cls a) {
		
	}

	//@ requires classes != null;
	//@ requires classes.length >= 1;
	//@ requires classes[0].value > 10;
	//@ pure
	void do_array(Cls[] classes) {
		
	}
	
	
	public static void main(String[] args) {
		ObjectTest test = new ObjectTest();
		test.do_something(5);
		test.do_something2(test.cls);
		test.do_array(new Cls[] {new Cls(9001), null, test.cls});
	}
}
