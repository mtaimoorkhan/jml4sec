package uk.gre.ac.openjmlsec.generatedClasses;

//@ model import org.jmlspecs.lang.*;
import uk.gre.ac.openjmlsec.testclasses.Attacks;
import uk.gre.ac.openjmlsec.testclasses.Test;

public class SqlInjection {
  private final int VARCHAR_SIZE = 100;
    /*@
    normal_behavior
      requires an_agrument != null; 
also
    compromised_behavior
      alarms SQL_INJECTION Attacks.HasSQLInjection(an_agrument); 
      action SQL_INJECTION LogMessage("An SQL injection detected: " + an_agrument);; 
   */

  /*@ pure*/ private static boolean SomeSqlCall(int value, String an_agrument) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.SqlInjection", "", "int,String", "SomeSqlCall", new java.lang.Object[]{value, an_agrument})) {
      if (Attacks.HasSQLInjection(an_agrument)) LogMessage("An SQL injection detected: " + an_agrument);
    }
    if (Test.VALUE == 1) return false;
    return true;
  }
  
  public static void main(String[] args) {
    System.out.println(Test.VALUE);
    SomeSqlCall(10, "hello");
    SomeSqlCall(10, "hello \' oR   \t1235   =   1235");
  }
  
  /*@ pure*/ public static void LogMessage(String msg) {
    System.out.println(msg);
  }
}