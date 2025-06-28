package generatedClasses;

//@ model import org.jmlspecs.lang.*;

public class Spam {
  static final long BLOCK_OUT = 10L;
  long last_call = 0;
  long prev_call = BLOCK_OUT + 1;
    /*@
    private normal_behavior
      requires prev_call > BLOCK_OUT + last_call; 
      assignable prev_call, last_call, System.time, System.nexttime; 
also
    private compromised_behavior
      requires prev_call <= BLOCK_OUT + last_call; 
      assignable prev_call, last_call, System.time, System.nexttime; 
      alarms SPAM prev_call <= BLOCK_OUT + last_call; 
      action SPAM {
        System.err.println("Too many pings within time frame, aborting");
        prev_call = System.currentTimeMillis() / 1000L;
        return;
      }; 
   */

  void Ping() {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("testclasses.Spam", "", "", "Ping", new java.lang.Object[]{BLOCK_OUT, prev_call, last_call})) {
      boolean EscVerify_recovered = false;
      if (prev_call <= BLOCK_OUT + last_call) {
        System.err.println("Too many pings within time frame, aborting");
        prev_call = System.currentTimeMillis() / 1000L;
        return;
      }
      if (!EscVerify_recovered) throw new java.lang.RuntimeException();
    }
    last_call = prev_call;
    prev_call = System.currentTimeMillis() / 1000L;
    try {
      Thread.sleep(10);
    } catch (Exception e) {
      e.printStackTrace();
    }
  }
  
  public static void main(String[] args) {
    Spam spam = new Spam();
    spam.Ping();
    spam.Ping();
    spam.Ping();
    spam.Ping();
    spam.Ping();
    spam.Ping();
  }
}