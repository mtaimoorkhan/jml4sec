package greenwich.ensuresec.structure;

public class JMLException extends JMLClause{
	
	String value;

	public JMLException(String clauseType) {
		super(clauseType);
		
	}
	
	public void setValue(String value) {
		this.value=value;
	}
	
	public String getValue() {
		return value;
	}

}
