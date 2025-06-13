package uk.gre.ac.openjmlsec.testclasses;

public class Inv {
	public int a = 100;
	
	//@ public invariant a > 10;
	
	//@ pure
	Inv(){
		
	}
	
	//@ requires 0 <= i && i < (Integer.MAX_VALUE - (a + 1));
	//@ modifies a;
	public void add_a(int i) {
		a += i;
	}
	
	public static void main (String[] args) {
		Inv inv = new Inv();
		inv.add_a(3);
	}
}
