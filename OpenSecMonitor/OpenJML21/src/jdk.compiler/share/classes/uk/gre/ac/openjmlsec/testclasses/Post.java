package uk.gre.ac.openjmlsec.testclasses;

public class Post {
	//@ requires 0 < a && a < 300;
    //@ ensures \result == a + 2;
	//@ pure
    public int test_func(int a) {
        return a + 1;
    }
    
    public static void main(String[] args) {
        Post p = new Post();
        p.test_func(2);
    }
}
