package uk.gre.ac.openjmlsec.testclasses;

public class ArrayTest {
    public static int[][] a = {{1, 2}, {1}, null, {}};

    //@ requires arr != null;
    //@ requires 0 <= index < arr.length;
    //@ ensures \result == arr[index];
    //@ pure
    public static int[] getElement(int[][] arr, int index) {
        return arr[index];
    }
    
    
    public static void main(String[] args) {
        System.out.println("VALUE:" + getElement(a, 1));
    }
}
