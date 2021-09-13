package uk.ac.gre.openjmlsec;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import org.jmlspecs.annotation.Pure;

public class B {

    static int j, k;
    static boolean SQLINJECTION;
    static boolean T=true;

 
    public static void setj(int i) {
        j = i;
        return;
    }
    
/*@ compromised_behavior 
    alarms IsSQLiORAttack(password) ==> SQLINJECTION;   
*/
    public static void setj(String password) {
        
        return;
    }
    @Pure
    public static boolean IsSQLiORAttack(String pass) {
        return true;
    }

    public static void m1 () {
        
    }
    
    public static void main(String[] args) {
        setj(3);
        return;
    }

   
    public static void readfile() {
        File file = new File("C:\\Users\\pankaj\\Desktop\\test.txt");
        BufferedReader br;
        try {
            br = new BufferedReader(new FileReader(file));
            String st;
            try {
                while ((st = br.readLine()) != null) System.out.println(st);
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        } catch (FileNotFoundException e) {
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            System.exit(1);
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }
}
