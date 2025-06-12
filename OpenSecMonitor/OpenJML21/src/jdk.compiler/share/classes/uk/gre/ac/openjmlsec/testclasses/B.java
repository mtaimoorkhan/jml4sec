package uk.gre.ac.openjmlsec.testclasses;

public class B {

	static /*@ spec_public*/ int j;
	
	//@ normal_behavior
	//@ modifies j;
	//@ ensures j == i;
	//@ requires i >= 0;
	//@ also compromised_behavior
	//@ requires i < 0;
	//@ alarms "injection" reportAttack();
	//@ assignable j; 
	public static void setj(int i) {
		j = i;
		return;
	}
	
	//@ pure
	public static boolean reportAttack() {
		System.out.println("ATTACK!");
		return true;
	}
	
	public static void main(String[] args) {
		setj(2848);
		return;
	}
}
