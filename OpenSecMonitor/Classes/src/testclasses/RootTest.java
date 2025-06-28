package testclasses;

public class RootTest {
	RootTest some_random_var;
	int v;

	//@ requires b != null;
	//@ requires b.v > 4;
	//@ compromised_behavior
		//@ requires b.v <= 4;
	//@ pure
	void a(RootTest b) {
		
	}
	
	public static void main(String[] args) {
		RootTest r = new RootTest();
		r.v = 100;
		r.a(r);
	}
}
