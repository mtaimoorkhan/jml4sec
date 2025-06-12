package uk.gre.ac.openjmlsec.testclasses;

public class ActionTest {
	
	//@ requires x == 3;
	//@ action "ident?" aFunc();
	//@ compromised_behavior
	//@ requires x != 3;
	//@ alarms "ident?" aFunc();
	//@ pure
	static void A(int x) {
		
	}
	
	public static void main(String[] args) {
		A(3);
		
	}
	
	public static boolean aFunc() {
		return true;
	}
}
