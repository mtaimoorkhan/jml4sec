package generatedClasses;

//@ model import org.jmlspecs.lang.*;

public class Memory {
  private static int[] the_array = null;
  public static final int MAX_LENGTH = 100;
  //@ private invariant the_array.length <= MAX_LENGTH; 
  
  public Memory() {
  }
    /*@
    private normal_behavior
      requires size >= 0 && size <= MAX_LENGTH; 
      assignable the_array; 
also
    private compromised_behavior
      requires size > MAX_LENGTH; 
      alarms TOO_BIG size > MAX_LENGTH; 
      action TOO_BIG {
        System.err.println("Size is too big:" + size);
        size = MAX_LENGTH;
      }; 
      assignable the_array; 
also
    exceptional_behavior
      requires size < 0; 
      signals (NumberFormatException) size < 0; 
      assignable \nothing; 
   */

  public void MakeArray(int size) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("testclasses.Memory", "", "int", "MakeArray", new java.lang.Object[]{size, MAX_LENGTH})) {
      boolean EscVerify_recovered = false;
      if (size > MAX_LENGTH) {
        System.err.println("Size is too big:" + size);
        size = MAX_LENGTH;
        EscVerify_recovered = true;
      }
      if (size < 0) throw new NumberFormatException();
      if (!EscVerify_recovered) throw new java.lang.RuntimeException();
    }
    if (size < 0 || size > MAX_LENGTH) throw new RuntimeException();
    the_array = new int[size];
  }
  
  public void DeleteArray() {
    the_array = null;
  }
    /*@
    private normal_behavior
      requires the_array != null; 
      requires index >= 0 && index < the_array.length; 
      assignable \nothing; 
also
    private exceptional_behavior
      requires the_array == null; 
      signals (NullPointerException) the_array == null; 
      assignable \nothing; 
also
    private exceptional_behavior
      requires index < -the_array.length || index >= the_array.length; 
      signals (NumberFormatException) index < 0 || index >= the_array.length; 
      assignable \nothing; 
   */

  public int GetValue(int index) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("testclasses.Memory", "", "int", "GetValue", new java.lang.Object[]{index, the_array})) {
      boolean EscVerify_recovered = false;
      if (the_array == null) throw new NullPointerException();
      if (index < 0 || index >= the_array.length) throw new NumberFormatException();
      if (!EscVerify_recovered) throw new java.lang.RuntimeException();
    }
    if (index < 0 || index >= the_array.length) throw new RuntimeException();
    return the_array[index];
  }
    /*@
    private normal_behavior
      requires the_array != null; 
      requires index >= 0 && index < the_array.length; 
      assignable the_array[index]; 
also
    private exceptional_behavior
      requires the_array == null; 
      signals (NullPointerException) the_array == null; 
      assignable \nothing; 
also
    private exceptional_behavior
      requires index < -the_array.length || index >= the_array.length; 
      signals (NumberFormatException) index < 0 || index >= the_array.length; 
      assignable \nothing; 
   */

  public void SetValue(int index, int value) {
    if (!uk.gre.ac.openjmlsec.gen.EscVerify.verify("testclasses.Memory", "", "int,int", "SetValue", new java.lang.Object[]{index, value, the_array})) {
      boolean EscVerify_recovered = false;
      if (the_array == null) throw new NullPointerException();
      if (index < 0 || index >= the_array.length) throw new NumberFormatException();
      if (!EscVerify_recovered) throw new java.lang.RuntimeException();
    }
    if (index < 0 || index >= the_array.length) throw new RuntimeException();
    the_array[index] = value;
  }
  
  public static void main(String[] args) {
    Memory mem = new Memory();
    System.out.println("\n\n\n");
    mem.MakeArray(Memory.MAX_LENGTH);
    System.out.println("\n\n\n");
    mem.MakeArray(Memory.MAX_LENGTH * 2);
    System.out.println("\n\n\n");
    mem.SetValue(50, 14);
    System.out.println("\n\n\nValue:" + mem.GetValue(50) + "\n\n\n");
    mem.MakeArray(10);
    System.out.println("\n\n\n");
    mem.SetValue(8, 14);
    System.out.println("\n\n\nValue:" + mem.GetValue(-2) + "\n\n\n");
  }
}