package uk.gre.ac.openjmlsec.testclasses;

public class CompTest {
	

	//@ public normal_behavior
	//@ requires b != 0;
	//@ ensures \result == a / b;
	//@ also compromised_behavior
	//@ requires a < 0;
	//@ alarms "negative" isNeg(a);
	//@ action "negative" { System.out.println("negative was caught"); a = -a; }
	//@ also exceptional_behavior
	//@ signals (RuntimeException) isZero(b);
	//@ pure
	public static double Div(double a, double b) {
		if (b == 0) throw new RuntimeException();
		return a / b;
	}
	
	public static void main(String[] args) {
		System.out.println("Div: " + Div(10, 2));
	}
	
	//@ pure
	static boolean isZero(double b) {
		return b == 0;
	}
	
	//@ pure
	static boolean isNeg(double a) {
		return a < 0;
	}
}
