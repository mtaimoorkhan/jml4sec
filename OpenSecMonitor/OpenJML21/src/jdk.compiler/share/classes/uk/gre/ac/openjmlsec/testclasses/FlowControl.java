package uk.gre.ac.openjmlsec.testclasses;

public class FlowControl {
	//@ ghost static int FlowVar = 0;

	//@ normal_behavior
	//@ requires FlowVar == 0;
	//@ ensures FlowVar == 1;
	//@ modifies FlowVar, System.out.outputText;
	//@ also compromised_behavior
	//@ requires FlowVar != 0;
	//@ modifies FlowVar, System.out.outputText;
	//@ alarms ALREADY_LOGGED_IN FlowVar != 0;
	//@ action ALREADY_LOGGED_IN return;
	public static void LogIn(String user, int data) {
		//@ set FlowVar = 1;
		System.out.println("\n\n\n\n\n\n LogIn " + user + "\n\n\n\n\n\n");
	}
	
	//@ normal_behavior
	//@ requires FlowVar == 1;
	//@ ensures FlowVar == 2;
	//@ modifies FlowVar, System.out.outputText;
	//@ also compromised_behavior
	//@ requires FlowVar != 1;
	//@ modifies FlowVar, System.out.outputText;
	//@ alarms AT_Y FlowVar == 2;
	/*@ action AT_Y {
		FlowVar = 1;
	}*/
	//@ alarms FLOW_BREAK FlowVar != 1;
	/*@ action FLOW_BREAK {
		LogOut(user);
		return;
	}*/
	public static void DoX(String user) {
		System.out.println("\n\n\n\n\n\n DoX " + user + "\n\n\n\n\n\n");
		//@ set FlowVar = 2;
	}
	
	//@ normal_behavior
	//@ requires FlowVar == 2;
	//@ modifies FlowVar, System.out.outputText;
	//@ also compromised_behavior
	//@ requires FlowVar != 2;
	//@ modifies FlowVar, System.out.outputText;
	//@ alarms FLOW_BREAK FlowVar != 1 || FlowVar != 2;
	/*@ action FLOW_BREAK {
		LogOut(user);
		return;
	}*/
	public static void DoY(String user) {
		System.out.println("\n\n\n\n\n\n DoY " + user + "\n\n\n\n\n\n");
	}

	//@ normal_behavior
	//@ ensures FlowVar == 0;
	//@ modifies FlowVar;
	public static void LogOut(String user) {
		System.out.println("\n\n\n\n\n\n LogOut " + user + "\n\n\n\n\n\n");
		//@ set FlowVar = 0;
	}
	
	public static void main(String[] args) {
		LogIn("USER1", 1234);
		DoX("USER2");
		DoY("USER3");
		DoY("USER4");
		LogOut("USER5");
		LogOut("USER6");
		
		LogIn("USER7", 1234);
		LogIn("USER8", 1234);
		LogOut("USER9");
		DoX("USER10");
		LogIn("USER11", 1234);
		DoY("USER12");
		LogOut("USER13");
	}
}
