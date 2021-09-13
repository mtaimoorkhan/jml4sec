package greenwich.ensuresec.structure;

public class JMLConditionalClause extends JMLClause {
	
	private String leftOp,  operator, rightOp;
	
	
	
	public JMLConditionalClause(String leftOp, String operator, String rightOp,String clauseType ) {	
		super(clauseType);
		this.leftOp=leftOp;
		this.operator=operator;
		this.rightOp=rightOp;
	}

	public String getLeftOp() {
		return leftOp;
	}

	public void setLeftOp(String leftOp) {
		this.leftOp = leftOp;
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


}
