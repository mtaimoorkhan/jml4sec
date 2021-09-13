package greenwich.ensuresec.structure;

import java.util.LinkedList;

import org.antlr.runtime.Token;



public class JMLStore {

static String className;
static LinkedList<JMLClause> clauses= new LinkedList<JMLClause>();
static LinkedList<JMLMethodParameter> methParameters= new LinkedList<JMLMethodParameter>();
static String clauseType;
static String ghostName;


public static void create() {	
	
	clauses= new LinkedList<JMLClause>();
	methParameters= new LinkedList<JMLMethodParameter>();
}

public static void reset() {
	clauses.clear();
	methParameters.clear();
	
}


public static void addMethCallCond(String operator, String rightOp) {
	
	JMLMethodCall jmc=(JMLMethodCall)clauses.getLast();
	jmc.setOperator(operator);
	jmc.setRightOp(rightOp);
	
}

public static JMLClause getClause(int i) {
	return clauses.get(i);
	
}

public static JMLMethodCall getRequiresMethodCall(int i) {
	return (JMLMethodCall)clauses.get(i);	
}

public static int getClausesSize() {
	return clauses.size();
	
}

public static void setClassName(String name) {
	
	className=name;
}

public static String getClassName() {
	
	return className;
}

public static void AddAlarms(String threat) {
	
	clauses.getLast().setThreat(threat);
	
//	JMLMethodCall jmc=(JMLMethodCall)clauses.getLast();
//	jmc.setThreat(threat);
	
}


public static void addMethCallParameter(String param) {
    
	JMLMethodCall jmc=(JMLMethodCall)clauses.getLast();
	jmc.addParameter(param);
	
}

public static void addMethCall(String mName) {
	JMLMethodCall jmlMethod= new JMLMethodCall(mName,clauseType);
	clauses.add(jmlMethod);
	
}

public static void setClauseType(String _clause) {
	clauseType=_clause;
	
}
public static String getClauseType() {
	return clauseType;
}

public static void setGhostName(String name) {
	ghostName=name;
	
}
public static String getGhostName() {
	return ghostName;
}


public static void addBinaryCon(String leftOp, String operator, String rightOp) {
	
	JMLConditionalClause jmlReq = new JMLConditionalClause(leftOp,operator,rightOp,clauseType);
	clauses.add(jmlReq);
}

public static void addMethQualifiedName(String qName) {
	
	JMLMethodCall jmc=(JMLMethodCall)clauses.getLast();
	jmc.setQualifiedName(qName);
	
	
}

public static void AddException(String value) {
	
	JMLException jmlException= new JMLException("noException");
	jmlException.setValue(value);
	clauses.add(jmlException);
	
}

public static void addFileName(String fileName) {
	
	JMLMethodCall jmc=(JMLMethodCall)clauses.getLast();
	jmc.setLogFileName(fileName);

}

public static void addMessage(String message, String fileName ) {
	
	JMLMethodCall jmc=(JMLMethodCall)clauses.getLast();
	jmc.setLogFileName(fileName);
	jmc.setMessage(message);
	
	
}

public static void addSession(String session) {
	
	JMLMethodCall jmc=(JMLMethodCall)clauses.getLast();
	jmc.setSession(session);
	
	
}



public static void addUrlHttp(String url, String http) {
	
	JMLMethodCall jmc=(JMLMethodCall)clauses.getLast();
	jmc.setUrlHttp(url,http);

	
}

public static void addEmailMessage(String msg, String email) {
	JMLMethodCall jmc=(JMLMethodCall)clauses.getLast();
	jmc.setEmailMessage(msg,email);

	
	
	
}

public static void addRightSideMethQualifiedName(String qName) {
	
	JMLMethodCall jmc=(JMLMethodCall)clauses.getLast();
	jmc.rightside.setQualifiedName(qName);
	
}

public static void addRightSideMethCall(String name) {
	
	JMLMethodCall jmc=(JMLMethodCall)clauses.getLast();
	
	JMLMethodCall jmlMethod= new JMLMethodCall(name,"rightside");
	jmc.rightside=jmlMethod;

	
}

public static void addRightSideMethCallParameter(String param) {
	
	JMLMethodCall jmc=(JMLMethodCall)clauses.getLast();
	jmc=jmc.rightside;
	jmc.addParameter(param);
	
	
}




}
