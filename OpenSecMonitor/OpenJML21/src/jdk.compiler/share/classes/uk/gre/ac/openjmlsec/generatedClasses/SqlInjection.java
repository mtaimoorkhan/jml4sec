package uk.gre.ac.openjmlsec.generatedClasses;

//@ model import org.jmlspecs.lang.*;
//@ model import java.util.regex.Pattern;

public class SqlInjection {
  private final int VARCHAR_SIZE = 100;
  private static boolean ForceCheck = false;
    /*@
    private normal_behavior
      requires an_agrument != null && !Attacks.HasSQLInjection(an_agrument); 
also
    private compromised_behavior
      requires an_agrument == null || Attacks.HasSQLInjection(an_agrument); 
      alarms SQL_INJECTION Attacks.HasSQLInjection(an_agrument); 
      action SQL_INJECTION Attacks.Log("An SQL injection detected: " + an_agrument);; 
   */

  /*@ pure*/ private static boolean SomeSqlCall(int value, String an_agrument) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.SqlInjection", "", "int,String", "SomeSqlCall", new java.lang.Object[]{value, an_agrument})) {
      if (Attacks.HasSQLInjection(an_agrument)) Attacks.Log("An SQL injection detected: " + an_agrument);
    }
    return true;
  }
  
  public static void main(String[] args) {
    SomeSqlCall(10, "hello");
    SomeSqlCall(10, "hello \' oR   \t1235   =   1235");
  }
  
  private class Attacks {
        /*@
      public normal_behavior
        requires input != null; 
        ensures \result == !(\forall int j; 0 <= j && j < input.length(); !String.charEqualsIgnoreCase(input.charAt(j), '\'')); 
     */

    /*@ pure*/ public static boolean HasSQLInjection(String input) {
      return input.contains("\'");
    }
    
    public static void Log(String msg) {
      System.out.println(msg);
    }
  }
}