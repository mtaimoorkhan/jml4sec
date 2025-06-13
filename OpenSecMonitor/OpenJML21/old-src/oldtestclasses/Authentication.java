package uk.gre.ac.openjmlsec.testclasses;

public class Authentication {
    
    /*@ requires x > 0 && x < 10000 && y > 0 && y < 10000;
    */
	//@ pure
    public static int add(int x, int y) {
        return x + y;
    }
    
    public static void main(String[] args) {
        add(100, 100);
        //add(100000, 100);
    }
}