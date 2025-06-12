package uk.gre.ac.openjmlsec.testclasses;

//@ model import org.jmlspecs.lang.*;

public class TestRunner {
  
  class Cls {
    public int value;

    //modifies value;
    public Cls(int arg) {
      value = arg;
    }
  }
  Cls cls = new Cls(10);
    /*@
      requires a < cls.value; 
   */

  /*@ pure*/ void do_something(int a) {
  }
    /*@
      requires a.value > 5; 
   */

  /*@ pure*/ void do_something2(Cls a) {
  }
  
  public static void main(String[] args) {
    TestRunner test = new TestRunner();
    test.do_something(5);
    test.do_something2(test.cls);
  }
  
  Cls temp19327493;
  private void test_do_something2() {
	//@ assume temp19327493 != null;
	//@ assume temp19327493.value == 10;
    do_something2(temp19327493);
  }
}