package uk.gre.ac.openjmlsec.testclasses;

//@ model import org.jmlspecs.lang.*;

public class Test_9312536825623634893 {
  //@ ghost static int FlowVar = 0;
    /*@
    normal_behavior
      requires FlowVar == 0; 
      ensures FlowVar == 1; 
      assignable FlowVar; 
also
    compromised_behavior
      requires !(FlowVar != 0); 
      assignable FlowVar; 
      alarms ALREADY_LOGGED_IN FlowVar != 0; 
      action ALREADY_LOGGED_IN return;; 
   */

  public static void LogIn(String user, int data) {
    //@ set FlowVar = 1;
    System.out.println("************************************** LogIn " + user);
  }
    /*@
    normal_behavior
      requires FlowVar == 1; 
      ensures FlowVar == 2; 
      assignable FlowVar; 
also
    compromised_behavior
      requires FlowVar != 1; 
      assignable FlowVar; 
      alarms AT_Y FlowVar == 2; 
      action AT_Y {
        //@ set FlowVar = 1;
      }; 
      alarms FLOW_BREAK FlowVar != 1; 
      action FLOW_BREAK {
        LogOut(user);
        return;
      }; 
   */

  public static void DoX(String user) {
    System.out.println("************************************** DoX " + user);
    //@ set FlowVar = 2;
  }
    /*@
    normal_behavior
      requires FlowVar == 2; 
      assignable FlowVar; 
also
    compromised_behavior
      requires FlowVar != 2; 
      assignable FlowVar; 
      alarms FLOW_BREAK FlowVar != 1; 
      action FLOW_BREAK {
        LogOut(user);
        return;
      }; 
   */

  public static void DoY(String user) {
    System.out.println("************************************** DoY " + user);
  }
    /*@
    normal_behavior
      ensures FlowVar == 0; 
      assignable FlowVar; 
   */

  public static void LogOut(String user) {
    System.out.println("************************************** LogOut " + user);
    //@ set FlowVar = 0;
  }
  
  public static void main(String[] args) {
    LogIn("USER1", 1234);
    DoX("USER2");
    DoY("USER3");
    DoY("USER4");
    LogOut("USER5");
    LogOut("USER6");
    LogIn("USER7", 1234);
    LogIn("USER8", 1234);
    LogOut("USER9");
    DoX("USER10");
    LogIn("USER11", 1234);
    DoY("USER12");
    LogOut("USER13");
  }
  
  private void test_LogIn() {
    /*@ assume FlowVar == 0;*/
    LogIn("USER11", 1234);
  }
}