package uk.gre.ac.openjmlsec.testclasses;

//@ model import java.lang.String;

/*
 * An example class to show the detection on Malicious input
 * 
 * In this example,
 * we have simplified the "Malicious input" to containing a null byte.
 * However, this can be easily changed.
 */

public class MalInput {
	public static String GetInput(int pos) {
		//The function would get sure input, for the sake of testing, it returns a constant
		
		return 
			(pos == 0)?
				"Some Good Input"
			: (pos == 1)?
				"Some BAd INPUT\0W"
			: (pos == 2)?
				"LONG ********************************************************* Input"
			: null;
	}
	//@ normal_behavior
	//@ requires input != null && !Attacks.IsTooLong(input) && !Attacks.IsMalformedInput(input);
	//@ also compromised_behavior
	//@ requires Attacks.IsTooLong(input) || Attacks.IsMalformedInput(input);
	//@ alarms TOO_LONG_INPUT Attacks.IsTooLong(input);
	//@ alarms MALFORMED_INPUT Attacks.IsMalformedInput(input);
	/*@ action MALFORMED_INPUT {
		Attacks.Log("Malformed input passed");
		input = Attacks.RemoveMalformedCharacters(input);
	}*/
	/*@ action TOO_LONG_INPUT {
		Attacks.Log("Too long input passed");
		input = Attacks.CutInputLength(input);
	};*/
	//@ also exceptional_behavior
	//@ requires input == null;
	//@ signals (NullPointerException) input == null;
	//@ pure
	public static void DoSomething(String input) {
		if (input == null) {
			throw new NullPointerException();
		}
	}
	

	
	public static void main(String[] args) {
		for (int i = 0; i < 4; i++)
			DoSomething(GetInput(i));
	}
	
	private class Attacks {
		//@ public normal_behavior
		//@ requires input != null;
		//@ ensures \result == !(\forall int j; 0<=j && j<input.length(); !String.charEqualsIgnoreCase(input.charAt(j), '\0'));
		//@ pure
		public static boolean IsMalformedInput(String input){
			//No null bytes
			return input.contains("\0");
		}
		
		//@ public normal_behavior
		//@ requires input != null;
		//@ ensures \result == (input.length() > 32);
		//@ pure
		public static boolean IsTooLong(String input) {
			return input.length() > 32;
		}
		
		public static String CutInputLength(String input) {
			return input.substring(0, 31);
		}
		
		public static String RemoveMalformedCharacters(String inp) {
			return inp.replace('\0', ' ');
		}
		
		public static void Log(String msg) {
			System.err.println("\n\n*************:" + msg + "\n");
		}
	}
		
		
}
