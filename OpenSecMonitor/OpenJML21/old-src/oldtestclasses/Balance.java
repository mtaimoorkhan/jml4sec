package uk.gre.ac.openjmlsec.testclasses;

import java.io.IOException;

public class Balance {
    
	//@ spec_public
    private final long MAX_BALANCE = 100L;
    
    Attackes attacks = new Attackes();

	//@ spec_public
    private long              balance     = 1;

    

    /*@ public normal_behavior
    @ requires 0 < a && a < MAX_BALANCE;
    @ assignable balance;
    @ also compromised_behavior
    @ assignable balance;
    @ requires a < 0;
    @ alarms "injection" attacks.reportInjectionAttack();
    @ requires a < -100;
    @ alarms "major injection" attacks.reportMajorInjectionAttack();
    @ alarms "attack" attacks.reportAttack();
    @*/
   public void add(long a) {
       this.balance += a;
   }
   
   /*@ public normal_behavior
   @ requires a > 0;
   @ also exceptional_behavior
   @ requires a < 0;
   @ signals (RuntimeException) attacks.reportInjectionAttack();
   @ also compromised_behavior
   @ requires a == 0;
   @ alarms "Is 0" attacks.reportAttack();
   @*/
  public void substract(long a) {
      this.balance -= a;
  }
  
  /*@ action_behavior
  @ requires x != 0;
  @ action x = 1;
  @ */
  public void mult(double x) {
      long diff = (long) ((this.balance * x) - this.balance);
      add(diff);
  }
  
  public void printBalance() {
      System.out.println("Balance: " + this.balance);
  }

    public static void main(String[] args) {
        Balance t = new Balance();
        int value = 10;
        if (args.length == 1) {
        	value = Integer.parseInt(args[0]);
        }
        t.add(value);

        t.printBalance();
    }
    
    public class Attackes {
        
    	/*@pure*/
        public boolean isSQLiORAttack(String password) {
            return password.contains("OR");
        }
        
        /*@pure*/
        public boolean reportInjectionAttack() {
            System.out.println("Injection attack occurred in");
            return true;
        }
        
        /*@pure*/
        public boolean reportAttack() {
            System.out.println("attack occurred in");
            return true;
        }
        
        /*@pure*/
        public boolean reportMajorInjectionAttack() {
            System.out.println("Major Injection attack occurred in");
            return true;
        }

    }

}
