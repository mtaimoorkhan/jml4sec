package uk.gre.ac.openjmlsec.generatedClasses;

//@ model import org.jmlspecs.lang.*;

public class Spam implements Runnable {
  static int num_pings = 0;
  static int MAX_PINGS = 2;
    /*@
    private normal_behavior
      requires num_pings >= 0 && num_pings < MAX_PINGS; 
      assignable num_pings; 
also
    private compromised_behavior
      requires num_pings >= MAX_PINGS; 
      assignable num_pings; 
      alarms SPAM num_pings >= MAX_PINGS; 
      action SPAM {
        System.err.println("Too many pings, aborting");
        return;
      }; 
   */

  void Ping() {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.Spam", "", "", "Ping", new java.lang.Object[]{MAX_PINGS, num_pings})) {
      if (num_pings >= MAX_PINGS) {
        System.err.println("Too many pings, aborting");
        return;
      }
    }
    num_pings += 1;
    try {
      Thread.sleep(40000);
    } catch (Exception e) {
      e.printStackTrace();
    }
    num_pings -= 1;
  }
  
  public void run() {
    Ping();
  }
  
  public static void main(String[] args) {
    Spam spam = new Spam();
    try {
      new Thread(spam).start();
      Thread.sleep(3000);
      new Thread(spam).start();
      Thread.sleep(3000);
      new Thread(spam).start();
      Thread.sleep(3000);
      new Thread(spam).start();
      Thread.sleep(3000);
      new Thread(spam).start();
      Thread.sleep(3000);
      new Thread(spam).start();
      Thread.sleep(3000);
      new Thread(spam).start();
    } catch (InterruptedException e) {
      e.printStackTrace();
    }
  }
}