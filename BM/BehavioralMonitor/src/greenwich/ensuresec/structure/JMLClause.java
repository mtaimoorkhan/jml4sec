package greenwich.ensuresec.structure;

public class JMLClause {
	
	private String clauseType;
	private String threat;
	
	public JMLClause(String clauseType) {
		this.clauseType=clauseType;
	}
	
	public String getClauseType() {
		return clauseType;
	}

	public void setClauseType(String clauseType) {
		this.clauseType = clauseType;
	}
	
	public String getThreat() {
		return threat;
	}
	public void setThreat(String threat) {
		this.threat = threat;
	}

}
