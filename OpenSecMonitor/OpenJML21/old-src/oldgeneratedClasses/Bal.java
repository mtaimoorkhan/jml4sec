package uk.gre.ac.openjmlsec.generatedClasses;

//@ model import org.jmlspecs.lang.*;

public class Bal {
  /*@ spec_public*/ protected final long MAX_BALANCE = 100L;
  /*@ spec_public*/ protected long balance = 1;
  //@ public invariant 0 <= balance && balance <= MAX_BALANCE; 
    /*@
    normal_behavior
      requires 0 <= a && a + balance <= MAX_BALANCE; 
      assignable balance; 
also
    compromised_behavior
      assignable balance; 
      requires a < 0; 
      alarms "injection" Attacks.reportInjectionAttack();
   */

  public void add(long a) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.Bal", "", "long", "add", new java.lang.Object[]{a, balance, MAX_BALANCE})) {
      if (a < 0) Attacks.reportInjectionAttack();
    }
    if (a + balance >= MAX_BALANCE) this.balance = MAX_BALANCE; else if (a >= 0) this.balance += a;
  }
    /*@
    public normal_behavior
      requires a > 0; 
      assignable balance; 
also
    exceptional_behavior
      assignable balance; 
      requires a < 0; 
      signals (RuntimeException) Attacks.isNeg(a);
      
   */

  public void substract(long a) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.Bal", "", "long", "substract", new java.lang.Object[]{a})) {
      if (Attacks.isNeg(a)) {
        throw new RuntimeException();
      }
    }
    this.balance -= a;
  }
  
  /*@ pure*/ public void printBalance() {
    System.out.println("Balance: " + this.balance);
  }
  
  public static void main(String[] args) {
    Bal t = new Bal();
    int value = 1010;
    if (args.length == 1) {
      value = Integer.parseInt(args[0]);
    }
    t.add(value);
    t.printBalance();
  }
  
  public class Attacks {
    
    /*@ pure*/ public static boolean isSQLiORAttack(String password) {
      return password.contains("OR");
    }
    
    /*@ pure*/ public static boolean reportInjectionAttack() {
      System.out.println("Injection attack occurred in");
      return true;
    }
    
    /*@ pure*/ public static boolean isNeg(long val) {
      if (val < 0) System.err.println("neg attack");
      return val < 0;
    }
  }
}