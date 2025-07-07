package testclasses;

import uk.gre.ac.openjmlsec.gen.EscRunner;

public class VideoExample {
	//@ normal_behavior
	//@ 	requires x >= 10 && y % 2 == 0;
	//@ compromised_behavior
	//@ 	requires x < 10 || y % 2 != 0;
	//@		alarms TO_SMALL x < 10;
	/*@		action TO_SMALL {
				EscRunner.Log("X is too small ("+x+"), setting to 10");
				x = 10;
			};*/
	//@		alarms NOT_EVEN y % 2 != 0;
	/*@		action NOT_EVEN {
				EscRunner.Log("Y is not even ("+y+"), doubling it");
				y *= 2;
			};*/
	/*@		action default {
				EscRunner.Log("# Verification failed!");
				return;	
			};*/
	//@ pure
	public static void Foo(int x, int y) {
		//Some logic...
	}
	
	public static void main(String[] args) {
		Foo(100, 2);
		Foo(1, 6);
		Foo(10, 1);
		Foo(1, 1);
	}
}
