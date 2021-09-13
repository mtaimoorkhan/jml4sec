package uk.ac.gre.openjmlsec;

import java.util.*;

public class Balance {
	
private final int MAX_BALANCE = 100;
    
    /*@ invariant balance < MAX_BALACE;
      @*/
    private int balance = 1;
    
    /*@ public normal_behavior
      @ requires a > 0;
      @*/
    public void add(int a) {
        this.balance += a;
    }
    
    
    public void printBalance() {
        System.out.println("Balance: " + this.balance);
    }
    
    public static void main(String[] arg) {
    
        Balance t = new Balance();
        
        if (arg.length == 1)
            t.add(new Integer(arg[0]));
    
        t.printBalance();
        
        //System.out.println(t.add(10));
        System.out.println("Done");
    
    }

}
