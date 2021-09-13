package gre.ens.utility;

public class SecJML {

public static int IsValidServer(String url) { 
		return 1;
}

public static int IsValidEcomUrl(String url) { 
		return 1;
}

public static boolean IsValidPassword(String password) {
	
	return true;	
}
public static boolean IsSQLiORAttack (String input) {
	input = input.toUpperCase();
	if (input.contains(" OR")== true)
		return false;
	return true;
}

public static boolean IsSQLiUnionAttack (String input) {
	input = input.toUpperCase();
	if (input.contains(" UNION")== true)
		return false;
	return true;
}

public static boolean IsSQLiBlindAttack(String input){
	input = input.toUpperCase();
	if (input.contains(" AND")== true)
		return false;
	return true;
	
}

public static boolean IsErrorBasedSQLi(String input){
	input = input.toUpperCase();
	if (input.contains(" '")== true)
		return false;
	return true;
	
}




}
