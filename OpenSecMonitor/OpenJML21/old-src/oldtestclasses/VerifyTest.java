package uk.gre.ac.openjmlsec.testclasses;

public class VerifyTest {
	
	public static class SubClass{
		//@ requires i == 10;
		//@ pure
		public static int Func(int i) {
			return i;
		}
	}
	
	//@ requires i == 0;
	//@ pure
	public static void Func(int i, int a) {
		
	}
	
	//@ requires 'a' <= c && c <= 'z';
	//@ pure
	public static void Func(char c, int a) {
		
	}
	
	public static void main(String[] args) {
		Func(0, 2);
	}
}
