package greenwich.ensuresec.structure;

import java.util.LinkedList;

public class JMLMethodCall extends JMLClause {
	private String name;
	private String qualifiedName;
	private LinkedList<String> parameters= new LinkedList<String>();
	private String operator;
	private String rightOp;
	private Boolean ensures;
	
	private String logFileName;
	private String message;
	private String session;
	private String url;
	private String http;
	private String msg;
	private String email;
	
	public JMLMethodCall rightside;
	
	
	public JMLMethodCall(String mName, String clauseType) {
		super(clauseType);
		this.name=mName;
	}
	public String getName() {
		return name;
	}
	public void setName(String name) {
		this.name = name;
	}
	public LinkedList<String> getParameters() {
		return parameters;
	}
	public void setParameters(LinkedList<String> parameters) {
		this.parameters = parameters;
	}
	public String getOperator() {
		return operator;
	}
	public void setOperator(String operator) {
		this.operator = operator;
	}
	public String getRightOp() {
		return rightOp;
	}
	public void setRightOp(String rightOp) {
		this.rightOp = rightOp;
	}
	public void addParameter(String param) {
		parameters.add(param);
		
	}
	public Boolean getEnsures() {
		return ensures;
	}
	public void setEnsures(Boolean ensures) {
		this.ensures = ensures;
	}

	
	public String getQualifiedName() {
		return qualifiedName;
	}
	public void setQualifiedName(String qualifiedName) {
		this.qualifiedName = qualifiedName;
	}
	public void setLogFileName(String fileName) {
		logFileName=fileName;
		
	}
	public String getLogFileName() {
		return logFileName;
		
	}
	public void setMessage(String msg) {
		message=msg;
		
	}
	
	public String getMessage() {
		return message;
		
	}
	public void setSession(String session) {
		 this.session=session;
		
	}
	
	public String getSession() {
		return session;
		
	}
	
	public String getUrl() {
		return url;
	}
	public void setUrlHttp(String url, String http) {
		
		this.url=url;
		this.http=http;
		
	}
	public String getHttp() {
		return http;
	}
	public void setEmailMessage(String msg, String email) {
		this.msg=msg;
		this.email=email;
		
	}
	public String getMsg() {
		return msg;
	}

	public String getEmail() {
		return email;
	}
	
	

}
