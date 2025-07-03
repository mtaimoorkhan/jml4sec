package testclasses;

public class CompTest {
	

	//@ public normal_behavior
		//@ requires !isZero(b) && !isNeg(a);
		//@ ensures \result == a / b;
	//@ also compromised_behavior
		//@ requires isNeg(a);
		//@ alarms negative isNeg(a);
		/*@ action negative {
			System.out.println("negative was caught");
			a = -a;
		};*/
	//@ also exceptional_behavior
		//@ requires isZero(b);
		//@ signals_only RuntimeException;
		//@ signals (RuntimeException) isZero(b);
	//@ pure
	public static double Div(double a, double b) {
		if (b == 0) throw new RuntimeException();
		return a / b;
	}
	// alarms default !recovered /*uk.gre.ac.openjmlsec.gen.EscVerify.Recovered();*/;
	
	public static void main(String[] args) {
		System.out.println("Div: " + Div(10, 2));
		System.out.println("Div: " + Div(-10, 2));
		System.out.println("Div: " + Div(10, 0));
	}

	//@ ensures \result == (b == 0);
	//@ pure
	static public boolean isZero(double b) {
		return b == 0;
	}

	//@ ensures \result == (a < 0);
	//@ pure
	static public boolean isNeg(double a) {
		return a < 0;
	}
}
