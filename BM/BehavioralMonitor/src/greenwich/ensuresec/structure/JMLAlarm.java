package greenwich.ensuresec.structure;

public class JMLAlarm extends JMLClause{
	private String leftOp, operator, rightOp, threat;
	
	public JMLAlarm(String leftOp, String operator, String rightOp, String threat, String clauseType) {
		super(clauseType);
		this.leftOp=leftOp;
		this.operator=operator;
		this.rightOp=rightOp;
		this.threat=threat;	
	}

	public String getOperator() {
		return operator;
	}

	public void setOperator(String operator) {
		this.operator = operator;
	}

	public String getThreat() {
		return threat;
	}

	public void setThreat(String threat) {
		this.threat = threat;
	}

	public String getRightOp() {
		return rightOp;
	}

	public void setRightOp(String rightOp) {
		this.rightOp = rightOp;
	}

	public String getLeftOp() {
		return leftOp;
	}

	public void setLeftOp(String leftOp) {
		this.leftOp = leftOp;
	}
	

}
