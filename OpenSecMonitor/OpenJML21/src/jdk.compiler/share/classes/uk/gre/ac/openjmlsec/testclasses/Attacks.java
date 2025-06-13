package uk.gre.ac.openjmlsec.testclasses;

public class Attacks {
	public int NONE = 0;
	public int SQL_INJECTION = 1;
	
	//@ pure
	public static boolean HasSQLInjection(String s) {
		return 
			s.matches(".*['\"](\\s|.*)(([oO][rR])|([aA][nN][dD]))\\s([^=]*)[=].*")
			|| s.matches(".*['\"](\\s|.*)([uU][nN][iI][oO][nN])\\s([sS][eE][lL][eE][cC][tT]).*")
			|| s.matches(".*['\"](\\s|.*)([uU][nN][iI][oO][nN])\\s([sS][eE][lL][eE][cC][tT]).*")
		;
	}
	
	//@ pure
	public static void Log(String msg) {
		System.out.println(msg);
	}
	
}
