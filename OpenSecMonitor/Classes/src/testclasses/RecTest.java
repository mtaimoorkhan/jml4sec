package testclasses;

public class RecTest {
	static class Rec{
		Rec test;
		int v;
		
		Rec(){}
		
	}
	//@ requires t != null;
	//@ requires t.v > 4;
	//@ compromised_behavior
		//@ requires t.v <= 4;
	//@ pure
	static void a() {
		
	}
	static Rec t = new Rec();
	
	public static void main(String[] args) {
		t.test = t;
		t.v = 5;
		a();
		t.v = 0;
		a();
	}
}
