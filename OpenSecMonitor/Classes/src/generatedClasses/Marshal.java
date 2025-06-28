package generatedClasses;

//@ model import org.jmlspecs.lang.*;

public class Marshal {
  int value;
    /*@
    normal_behavior
      requires value_arg >= 0 && value_arg <= 10000; 
      assignable value; 
also
    compromised_behavior
      requires value_arg < 0 || value_arg > 10000; 
      alarms NEGATIVE_VALUE value_arg < 0; 
      action NEGATIVE_VALUE value_arg = 0;; 
      alarms TOO_BIG value_arg > 10000; 
      action TOO_BIG value_arg = 10000;; 
      assignable value; 
   */

  public void setValue(int value_arg) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("testclasses.Marshal", "", "int", "setValue", new java.lang.Object[]{value_arg})) {
      boolean EscVerify_recovered = false;
      if (value_arg < 0) {
        value_arg = 0;
        EscVerify_recovered = true;
      }
      if (value_arg > 10000) {
        value_arg = 10000;
        EscVerify_recovered = true;
      }
      if (!EscVerify_recovered) throw new java.lang.RuntimeException();
    }
    value = value_arg;
  }
  
  public static void main(String[] args) {
    new Marshal().setValue(2873);
    new Marshal().setValue(83487935);
  }
}