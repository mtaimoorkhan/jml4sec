package uk.gre.ac.openjmlsec.testclasses;

public class C {
	//@ ghost public int x = 1;
    
    //@ requires x == 1;
    //@ requires a >= 0 && a < 300;
	//@ assignable x;
    public int A(int a) {
        //@set x = 2;
    	return a + 2;
    }
    
    //@ requires x == 2;
	//@ assignable x;
    public int B() {
        //@set x = 1;
    	return 1234;
    }
    
    public static void main(String[] args) {
        C c = new C();
        System.out.println(c.A(1));
        System.out.println(c.B());
    }
}
