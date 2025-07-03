package uk.gre.ac.openjmlsec.testclasses;

public class A {
	//@ spec_public
	private int spg_var;

	//@ requires a > 0 && a < 100;
    public static /*@pure*/ int inc(int a) {
    	return a + 1;
    }
    
    public static void main(String[] args) {
    	int b = inc(1);
    	System.out.println("B:" + b);
    }
}
