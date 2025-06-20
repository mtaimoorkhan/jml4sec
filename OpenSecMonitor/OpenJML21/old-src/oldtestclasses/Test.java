package uk.gre.ac.openjmlsec.testclasses;

public class Test {
	private final int VARCHAR_SIZE = 100;
	
	/*
	 * Updates some value in the data base
	 */
	//@ private normal_behavior
	//@ requires an_agrument != null;
	//@ also private compromised_behavior
	//@ alarms SQL_INJECTION Attacks.HasSQLInjection(an_agrument);
	//@ action SQL_INJECTION Attacks.Log("An SQL injection detected: " + an_agrument);
	//@ pure // It probably wont be pure, but for this test case it is
	private static boolean SomeSqlCall(int value, String an_agrument){
		// Code calls a SQL lite or MySQL database
		// Use PreparedStatement to avoid SQLi attack
		// But we would still want to know
		// if someone is trying to probe around and attempt a SQLi attack
		return true;
	}
	
	public static void main(String[] args){
		SomeSqlCall(10, "hello"); // Fine
		SomeSqlCall(10, "hello ' oR   	1235   =   1235"); // Message printed
	}
}
