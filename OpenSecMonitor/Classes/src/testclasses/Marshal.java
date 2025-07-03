package testclasses;

public class Marshal {
	/*@ spec_public*/ int value;
	
	//@ normal_behavior
		//@ requires value_arg >= 0 && value_arg <= 10000;
		//@ modifies value;
	//@ compromised_behavior
		//@ requires value_arg < 0 || value_arg > 10000;
		//@ modifies value;
		//@ alarms NEGATIVE_VALUE value_arg < 0;
		//@ action NEGATIVE_VALUE {value_arg = 0;};
		//@ alarms TOO_BIG value_arg > 10000;
		//@ action TOO_BIG {value_arg = 10000;};
	public void setValue(int value_arg) {
		value = value_arg;
	}
	
	public static void main(String[] args) {
		new Marshal().setValue(2873);
		new Marshal().setValue(83487935);
	}
}
