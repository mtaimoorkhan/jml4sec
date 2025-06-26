package uk.gre.ac.openjmlsec.testclasses;

//@ model import org.jmlspecs.lang.*;

public class Test_8115400091001000424 {
  long last_call = 0;
  static final long BLOCK_OUT = 10L;
  long prev_call = BLOCK_OUT + 1;
    /*@
    private normal_behavior
      requires prev_call > BLOCK_OUT + last_call; 
      assignable prev_call, last_call, System.time, System.nexttime; 
also
    private compromised_behavior
      requires !(prev_call <= BLOCK_OUT + last_call); 
      assignable prev_call, last_call, System.time, System.nexttime; 
      alarms SPAM prev_call <= BLOCK_OUT + last_call; 
      action SPAM {
        System.err.println("Too many pings within time frame, aborting");
        return;
      }; 
   */

  void Ping() {
    last_call = prev_call;
    prev_call = System.currentTimeMillis() / 1000L;
    try {
      Thread.sleep(10);
    } catch (Exception e) {
      e.printStackTrace();
    }
  }
  
  public static void main(String[] args) {
    Test_8115400091001000424 spam = new Test_8115400091001000424();
    spam.Ping();
    spam.Ping();
    spam.Ping();
    spam.Ping();
  }
  
  private void test_Ping() {
    /*@ assume last_call == 0L;*/
    /*@ assume prev_call == 10L;*/
    /*@ assume BLOCK_OUT == 10L;*/
    Ping();
  }
}