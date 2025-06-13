package uk.gre.ac.openjmlsec.testclasses;

import static uk.gre.ac.openjmlsec.testclasses.Attacks.*;
import uk.gre.ac.openjmlsec.testclasses.Attacks;


public class TestClass {
    TestClass(){
        
    }

    public static final String NONE = "";
    public static final String _currentAttack = "SQL_INJECTION";

    /*@
    compromised_behavior
        requires isSqlInjection(user); 
        alarms "SQL_INJECTION" reportInjectionAttack();
     */
    
    public void login(String user) {
        RunSql("SELECT * FROM Users WHERE username='"+user+"'");
    }
    
    public void RunSql(String sql) {
        //...
    }
    
    public static void main(String[] args) {
        TestClass tc = new TestClass();
        
        tc.login("Hello OR");
    }

    /*@pure*/
    public static boolean reportInjectionAttack() {
        System.out.println("SQL INJECTION ATTACK OCCURED");
        return true;
    }
    /*@pure*/
    public static boolean reportEmptyAttack() {
        System.out.println("EMPTY");
        return true;
    }
    /*@pure*/
    public static boolean isSqlInjection(String s) {
        /* Copied for ease of coding*/
        return s.contains("OR");
    }
    /*@pure*/
    public static boolean emptyTester(String s) {
        return s.isEmpty();
    }
}
