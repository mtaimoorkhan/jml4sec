package uk.gre.ac.openjmlsec.testclasses;

public class App {

	private final int VARCHAR_SIZE = 100;
	
	/*
	 * Updates some value in the data base
	 */
	//@ public normal_behavior
	//@ requires value >= 0;
	//@ requires an_agrument != NULL;
	//@ requires an_agrument.length <= VARCHAR_SIZE;
	//@ ensures \result == true; //If it returns false an error occurred, and should be flagged.
	//@ also public compromised_behavior
	//@ alarms "negative_value" value < 0;
	//@ action "negative_value" value = Math.abs(value);
	//@ alarms "null_argument" an_agrument == null;
	//@ action "null_argument" an_agrument = "";
	//@ alarms "overflow" an_agrument > VARCHAR_SIZE;
	//@ action "overflow" an_agrument = an_argument.substring(0, VARCHAR_SIZE);
	//@ alarms SQL_INJECTION Attacks.HasSQLInjection(an_agrument);
	//@ action SQL_INJECTION Log.Log("An SQL injection detected: " + an_agrument);
	//@ pure // It probably wont be pure, but for this test case it is
	private static boolean SomeSqlCall(int value, String an_agrument){
		// Code calls a SQL lite or MySQL database
		// Use PreparedStatement to avoid SQLi attack
		// But we would still want to know
		// if someone is trying to probe around and attempt a SQLi attack
		
		return true;
	}
}
