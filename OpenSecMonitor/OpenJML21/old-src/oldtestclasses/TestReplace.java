package uk.gre.ac.openjmlsec.testclasses;

public class TestReplace {
	public static class SubClass{

		int TestReplace;
		
		public void TestReplace(int a) {
			TestReplace = 5;
		}
	}
	
	public static void foo() {
		int TestReplace;
	}
	
	//@ requires a != 1854674;
	//@ pure
	public void TestReplace(int a) {
		
	}
	
	public static void main(String[] args) {
		TestReplace main = new TestReplace();
		
		TestReplace.foo();
		
		main.TestReplace(3);
	}
}
