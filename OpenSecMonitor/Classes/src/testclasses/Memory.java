package testclasses;

public class Memory {
	private static int[] the_array = null;
	public static final int MAX_LENGTH = 100;
	//@ private invariant the_array.length <= MAX_LENGTH;
	
	public Memory() {}
	
	//@ private normal_behavior
		//@ requires size >= 0 && size <= MAX_LENGTH;
		//@ modifies the_array;
	//@ private compromised_behavior
		//@ requires size > MAX_LENGTH;
		//@ alarms TOO_BIG size > MAX_LENGTH;
		/*@ action TOO_BIG {
		 	System.err.println("Size is too big:" + size);
			size = MAX_LENGTH;
		};*/
		//@ modifies the_array;
	//@ exceptional_behavior
		//@ requires size < 0;
		//@ signals (NumberFormatException) size < 0;
	//@ modifies \nothing;
	public void MakeArray(int size) {
		if (size < 0 || size > MAX_LENGTH) throw new RuntimeException();
		the_array = new int[size];
	}
	
	
	public void DeleteArray() {
		the_array = null;
	}

	//@ private normal_behavior
		//@ requires the_array != null;
		//@ requires index >= 0 && index < the_array.length;
		//@ modifies \nothing;
	//@ private exceptional_behavior
		//@ requires the_array == null;
		//@ signals (NullPointerException) the_array == null;
		//@ modifies \nothing;
	//@ private exceptional_behavior
		//@ requires index < -the_array.length || index >= the_array.length;
		//@ signals (NumberFormatException) index < 0 || index >= the_array.length;
		//@ modifies \nothing;
	public int GetValue(int index) {
		if (index < 0 || index >= the_array.length) throw new RuntimeException();
		return the_array[index];
		
	}


	//@ private normal_behavior
		//@ requires the_array != null;
		//@ requires index >= 0 && index < the_array.length;
		//@ modifies the_array[index];
	//@ private exceptional_behavior
		//@ requires the_array == null;
		//@ signals (NullPointerException) the_array == null;
		//@ modifies \nothing;
	//@ private exceptional_behavior
		//@ requires index < -the_array.length || index >= the_array.length;
		//@ signals (NumberFormatException) index < 0 || index >= the_array.length;
		//@ modifies \nothing;
	public void SetValue(int index, int value) {
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
		System.out.println("\n\n\nValue:" + mem.GetValue(50)+ "\n\n\n");
		mem.MakeArray(10);
		System.out.println("\n\n\n");
		mem.SetValue(8, 14);
		System.out.println("\n\n\nValue:" + mem.GetValue(-2) + "\n\n\n"); // Error
	}
}
