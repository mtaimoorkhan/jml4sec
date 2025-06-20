package uk.gre.ac.openjmlsec.generatedClasses;

//@ model import org.jmlspecs.lang.*;
//@ model import java.lang.String;

public class MalInput {
  
  public static String GetInput(int pos) {
    return (pos == 0) ? "Some Good Input" : (pos == 1) ? "Some BAd INPUT\u0000W" : (pos == 2) ? "LONG ********************************************************* Input" : null;
  }
    /*@
    normal_behavior
      requires input != null && !Attacks.IsTooLong(input) && !Attacks.IsMalformedInput(input); 
also
    exceptional_behavior
      requires input == null; 
      signals (NullPointerException) input == null; 
also
    compromised_behavior
      requires Attacks.IsTooLong(input) || Attacks.IsMalformedInput(input); 
      alarms TOO_LONG_INPUT Attacks.IsTooLong(input); 
      alarms MALFORMED_INPUT Attacks.IsMalformedInput(input); 
      action MALFORMED_INPUT {
        Attacks.Log("Malformed input passed");
        input = Attacks.RemoveMalformedCharacters(input);
      }; 
      action TOO_LONG_INPUT {
        Attacks.Log("Too long input passed");
        input = Attacks.CutInputLength(input);
      }; 
   */

  /*@ pure*/ public static void DoSomething(String input) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("uk.gre.ac.openjmlsec.testclasses.MalInput", "", "String", "DoSomething", new java.lang.Object[]{input})) {
      if (input == null) {
        throw new NullPointerException();
      }
      if (Attacks.IsTooLong(input)) {
        Attacks.Log("Too long input passed");
        input = Attacks.CutInputLength(input);
      }
      if (Attacks.IsMalformedInput(input)) {
        Attacks.Log("Malformed input passed");
        input = Attacks.RemoveMalformedCharacters(input);
      }
    }
  }
  
  public static void main(String[] args) {
    for (int i = 0; i < 4; i++) DoSomething(GetInput(i));
  }
  
  private class Attacks {
        /*@
      public normal_behavior
        requires input != null; 
        ensures \result == !(\forall int j; 0 <= j && j < input.length(); !String.charEqualsIgnoreCase(input.charAt(j), '\u0000')); 
     */

    /*@ pure*/ public static boolean IsMalformedInput(String input) {
      return input.contains("\u0000");
    }
        /*@
      public normal_behavior
        requires input != null; 
        ensures \result == (input.length() > 32); 
     */

    /*@ pure*/ public static boolean IsTooLong(String input) {
      return input.length() > 32;
    }
    
    public static String CutInputLength(String input) {
      return input.substring(0, 31);
    }
    
    public static String RemoveMalformedCharacters(String inp) {
      return inp.replace('\u0000', ' ');
    }
    
    public static void Log(String msg) {
      System.err.println("\n\n*************:" + msg + "\n");
    }
  }
}