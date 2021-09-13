package greenwich.ensuresec.vistor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.EnclosedExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt;
import com.github.javaparser.ast.stmt.AssertStmt;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.ast.expr.Expression;

import greenwich.ensuresec.structure.JMLConditionalClause;
import greenwich.ensuresec.structure.JMLException;
import greenwich.ensuresec.structure.JMLMethodCall;
import greenwich.ensuresec.structure.JMLStore;

public class JavaCodeVistor extends  VoidVisitorAdapter<Object> {
	
	MethodDeclaration lastMethod;

    @Override
    public void visit(BlockComment comment, Object arg) {
     //   System.out.println(comment);
     //   System.out.println("A");
        
        JMLStore.reset();
		System.out.println("Annotation to Parse: "+comment.toString());
		String specification= comment.toString();
		
		//int f_index= specification.indexOf("compromised_behavior");
		int f_index= specification.indexOf("/*@");
		int l_index= specification.indexOf("*/");
		String sec_specification;
		if (((f_index !=-1 ) && (l_index !=-1 )))
		{
		sec_specification= specification.substring(f_index+3,l_index);
		
		System.out.println("SPECS to Parse: "+sec_specification);
				
	//	int index=str.indexOf("ENDOFCLASS");
	//	inputFiles.add(str.substring(0,index));
	//	str=str.substring(index+10,str.length());
		
		System.out.println("Parsing specifications of method "+ lastMethod.getNameAsString());
		JMLAnnotatedJavaClass.parseAndStoreJMLAnnotation(sec_specification);
		
		System.out.println("Generating assertions for method "+ lastMethod.getNameAsString()+"\n\n");
		addAssertions(lastMethod);
		}
	    
        super.visit(comment, arg);
       
    }
	
	@Override
    public void visit(LineComment comment, Object arg) {
     //   System.out.println(comment);
        super.visit(comment, arg);
       
    }
    
	@Override
    public void visit(MethodDeclaration node , Object arg) {
        
    //    System.out.println("End of Method: "+ node.getName());
        
        lastMethod=node; // we save method node, as visitor visit the comments after visiting method body
        	super.visit(node, arg);
    
	}	
	
	private void addAssertions(MethodDeclaration node) {
		
		for (int i=0; i<JMLStore.getClausesSize(); i++) {
					
				//	System.out.println("Class type:"+JMLStore.getClause(i));
							
					switch(JMLStore.getClause(i).getClauseType())
			        {
			            case "requires":
			            case "before":
			            		Expression assertExpr;
							if (JMLStore.getClause(i) instanceof JMLConditionalClause) 
								node.getBody().get().getStatements().addFirst(addJMLConditionalClauseAssertion((JMLConditionalClause)JMLStore.getClause(i)));
							else if (JMLStore.getClause(i) instanceof JMLMethodCall) 
								node.getBody().get().getStatements().addFirst(addMethodCallAssertion((JMLMethodCall)JMLStore.getClause(i)));								
			            		break;
			            		
			            case "ensures":
			            		if (JMLStore.getClause(i) instanceof JMLConditionalClause) 
								node.getBody().get().getStatements().addLast(addJMLConditionalClauseAssertion((JMLConditionalClause)JMLStore.getClause(i)));
							else if (JMLStore.getClause(i) instanceof JMLMethodCall) 
								node.getBody().get().getStatements().addLast(addMethodCallAssertion((JMLMethodCall)JMLStore.getClause(i)));								
			            		break;
			            case "alarms":
			            	if (JMLStore.getClause(i) instanceof JMLMethodCall) {
			            		//node.getBody().get().getStatements().addFirst(addAlarm((JMLMethodCall)JMLStore.getClause(i)));
			            		node.getBody().get().getStatements().addFirst(logAttackDetails((JMLMethodCall)JMLStore.getClause(i)));
			            	}
			            	else if (JMLStore.getClause(i) instanceof JMLConditionalClause) {
			               	//node.getBody().get().getStatements().addFirst(addJMLConditionalClauseAssertion((JMLConditionalClause)JMLStore.getClause(i)));
				           	node.getBody().get().getStatements().addFirst(logAttackDetails((JMLConditionalClause)JMLStore.getClause(i)));
				         }   	
			            break;
			            case "noException":
			            	if (JMLStore.getClause(i) instanceof JMLException)
			            		addExitStatement(node, (JMLException)JMLStore.getClause(i));
			           	break;
			           	
			            case "log":
			            	if (JMLStore.getClause(i) instanceof JMLMethodCall)
			            		node.getBody().get().getStatements().addFirst(addLog(node,(JMLMethodCall)JMLStore.getClause(i)));	
			                break;
			                
			            case "logout":
			            	if (JMLStore.getClause(i) instanceof JMLMethodCall)
			            		node.getBody().get().getStatements().addFirst(addLogout(node,(JMLMethodCall)JMLStore.getClause(i)));	
			                break;
			            case "action":
			            	if (JMLStore.getClause(i) instanceof JMLMethodCall)
			            		node.getBody().get().getStatements().addFirst(addRightSide(node,(JMLMethodCall)JMLStore.getClause(i)));	
			                break;
			            case "notify":
			            	if (JMLStore.getClause(i) instanceof JMLMethodCall)
			            		node.getBody().get().getStatements().addFirst(addNotify(node,(JMLMethodCall)JMLStore.getClause(i)));	
			                break;
		            	          		
			            }			  
				}
	}
    
private Statement addRightSide(MethodDeclaration node, JMLMethodCall jmlMethod) {
	IfStmt ifStmt = createIfStatement(jmlMethod);
	ifStmt.setThenStmt(createMethodCallStatement(jmlMethod.rightside));
	
	return ifStmt;
		
	}

private Statement createMethodCallStatement(JMLMethodCall jmc) {
	
	MethodCallExpr method= new MethodCallExpr();
	method.setName(jmc.getName());
	NodeList<Expression> arguments= new NodeList<Expression>();
	
	for (int i=0; i< jmc.getParameters().size();i++)
		arguments.add(new NameExpr(jmc.getParameters().get(i)));
	
 	method.setArguments(arguments);
 	
 	ExpressionStmt expStmt=new ExpressionStmt(method);
	return expStmt;
	
}

private Statement logAttackDetails(JMLConditionalClause clause) {
		
	IfStmt ifStmt = createIfStatement(clause);
	ifStmt.setThenStmt(createAttackDetails(clause));
	
	return ifStmt;
	}

private Statement createAttackDetails(JMLConditionalClause clause) {
	
	MethodCallExpr method= new MethodCallExpr();
	method.setName("Uty.addAttckDetails");
	
	NameExpr argument0= new NameExpr("\""+lastMethod.getNameAsString()+"\"");
	
	NameExpr argument1= new NameExpr("\""+clause.getThreat()+"\"");
	NameExpr argument2= new NameExpr("\""+getBinaryExpr(clause).toString()+"\"");
	NameExpr argument3= new NameExpr("\""+clause.getLeftOp().toString()+"\"");
	NameExpr argument4= new NameExpr(clause.getLeftOp().toString());
	
	
	NodeList<Expression> arguments= new NodeList<Expression>();
	arguments.add(argument0);
 	arguments.add(argument1);
 	arguments.add(argument2);
 	arguments.add(argument3);
 	arguments.add(argument4);
 	method.setArguments(arguments);
 	
 	ExpressionStmt expStmt=new ExpressionStmt(method);
	return expStmt;
}

private IfStmt createIfStatement(JMLConditionalClause clause) {
	
	IfStmt ifStmt= new IfStmt();
	Expression binaryExpr = getBinaryExpr(clause);
	ifStmt.setCondition(binaryExpr);
	return ifStmt;
	
}

private Expression getBinaryExpr(JMLConditionalClause clause) {
	
	Expression binExpr;
	
	binExpr= new BinaryExpr(new NameExpr(clause.getLeftOp()), new IntegerLiteralExpr(clause.getRightOp()), getInfixExpressionOp(clause.getOperator()));
	return binExpr;
}

private Statement logAttackDetails(JMLMethodCall jmlMethod) {
	
	IfStmt ifStmt = createIfStatement(jmlMethod);
	ifStmt.setThenStmt(createAttackDetails(jmlMethod));
	
	return ifStmt;
	
	}

private Statement createAttackDetails(JMLMethodCall jmlMethod) {
//addAttckDetails(String componenet, String type, String condition, String parameter, String value) {
	
	MethodCallExpr method= new MethodCallExpr();
	method.setName("Uty.addAttckDetails");
	
	NodeList<Expression> arguments= new NodeList<Expression>();
	
	NameExpr argument0= new NameExpr("\""+lastMethod.getNameAsString()+"\"");
	
	NameExpr argument1= new NameExpr("\""+jmlMethod.getThreat()+"\"");
	NameExpr argument2= new NameExpr("\""+getMethodCallBinaryExpr(jmlMethod).toString()+"\"");
	
	arguments.add(argument0);
 	arguments.add(argument1);
 	arguments.add(argument2);
 	
 	
 	
	// need to improve
	
	if (jmlMethod.getParameters() !=null) {
		for (int index=0; index<jmlMethod.getParameters().size();index++ ) {
		NameExpr argument3= new NameExpr("\""+jmlMethod.getParameters().get(index).toString()+"\"");
		arguments.add(argument3);
		//arguments.add(3, argument_3);
		NameExpr argument4= new NameExpr(jmlMethod.getParameters().getFirst().toString());
		//arguments.add(4, argument_4);
		arguments.add(argument4);
		
		}
		
		if (arguments.size()==3) {
		NameExpr argument3= new NameExpr("\" NA"+"\"");
	 	NameExpr argument4= new NameExpr("\"NA"+"\"");
	 	arguments.add(argument3);
	 	arguments.add(argument4);
		}
		

	}
	

 	method.setArguments(arguments);
 	
 	ExpressionStmt expStmt=new ExpressionStmt(method);
	return expStmt;
	
}

private Statement addNotify(MethodDeclaration node, JMLMethodCall jmlMethod) {
	
	IfStmt ifStmt = createIfStatement(jmlMethod);
	ifStmt.setThenStmt(createNotifyStatement(jmlMethod));
	
	return ifStmt;

	}

private Statement createNotifyStatement(JMLMethodCall jmlMethod) {
	MethodCallExpr method= new MethodCallExpr();
	method.setName("email");
	NameExpr argument1= new NameExpr("\""+jmlMethod.getMsg()+"\"");
	NameExpr argument2= new NameExpr("\""+jmlMethod.getEmail()+"\"");
	
	NodeList<Expression> arguments= new NodeList<Expression>();
 	arguments.add(argument1);
 	arguments.add(argument2);
 	method.setArguments(arguments);
 	
 	ExpressionStmt expStmt=new ExpressionStmt(method);
	return expStmt;
	
}

private Statement addRedirect(MethodDeclaration node, JMLMethodCall jmlMethod) {
	
	IfStmt ifStmt = createIfStatement(jmlMethod);
	ifStmt.setThenStmt(createRedirectStatement(jmlMethod));
	
	return ifStmt;
	}

private Statement createRedirectStatement(JMLMethodCall jmlMethod) {
	
	MethodCallExpr method= new MethodCallExpr();
	method.setName("Utility.redirect");
	NameExpr argument1= new NameExpr(jmlMethod.getHttp());
	NameExpr argument2= new NameExpr("\""+jmlMethod.getUrl()+"\"");
	
	NodeList<Expression> arguments= new NodeList<Expression>();
 	
 	arguments.add(argument2);
 	arguments.add(argument1);
 	
 	method.setArguments(arguments);
 	
 	ExpressionStmt expStmt=new ExpressionStmt(method);
	return expStmt;


}

private Statement addLogout(MethodDeclaration node, JMLMethodCall jmlMethod) {
	
	IfStmt ifStmt = createIfStatement(jmlMethod);
	
	//ExpressionStmt expStmt=new ExpressionStmt(getMethodCallExpr(jmlMethod)); 
	
	ifStmt.setThenStmt(createLogoutStatement(jmlMethod));
	
	return ifStmt;
	
	}

private Statement createLogoutStatement(JMLMethodCall jmlMethod) {
	
	MethodCallExpr method= new MethodCallExpr();
	method.setName("invalidate");
	NameExpr argument= new NameExpr(jmlMethod.getSession());
	
	NodeList<Expression> arguments= new NodeList<Expression>();
 	arguments.add(argument);
 	
 	method.setArguments(arguments);
 	
 	ExpressionStmt expStmt=new ExpressionStmt(method);
	return expStmt;
}

private Statement addLog(MethodDeclaration node, JMLMethodCall jmlMethod) {
		
	IfStmt ifStmt = createIfStatement(jmlMethod);
	ifStmt.setThenStmt(createLogStatement(jmlMethod));
	
	return ifStmt;
	
	}

private IfStmt createIfStatement(JMLMethodCall jmlMethod) {
	IfStmt ifStmt= new IfStmt();
	Expression binaryExpr = getMethodCallBinaryExpr(jmlMethod);
	ifStmt.setCondition(binaryExpr);
	return ifStmt;
}

private Statement createLogStatement(JMLMethodCall jmlMethod) {
	
	MethodCallExpr method= new MethodCallExpr();
	method.setName("message");
	NameExpr argument1= new NameExpr("\""+jmlMethod.getMessage()+"\"");
	NameExpr argument2= new NameExpr("\""+jmlMethod.getLogFileName()+"\"");
	
	NodeList<Expression> arguments= new NodeList<Expression>();
 	arguments.add(argument1);
 	arguments.add(argument2);
 	method.setArguments(arguments);
 	
 	ExpressionStmt expStmt=new ExpressionStmt(method);
 	//
 	NodeList<Statement> statements= new NodeList<Statement>();
 	statements.add(expStmt);
 	statements.add(expStmt);
 	BlockStmt bs= new BlockStmt(statements);
 	
 	
 	//setStatements(NodeList<Statement> statements) ;
	//return expStmt;
	return bs;
}

private void addExitStatement(MethodDeclaration node, JMLException clause) {
	
	if (clause.getValue().compareToIgnoreCase("TRUE")!=0)
		return;
	
	NodeList<Statement> list= node.getBody().get().getStatements();	
	for (Statement stmt : list) {
		//System.out.println(stmt.getClass().getName());
		if (stmt instanceof TryStmt) {
			System.out.println(stmt.getClass().getName());
			TryStmt tstmt= (TryStmt)stmt;
			NodeList<CatchClause> catchList= tstmt.getCatchClauses(); 
			for (CatchClause catchStatement: catchList)
			{			
				MethodCallExpr method= new MethodCallExpr();
				method.setName("exit");
				NameExpr qName =new NameExpr("System");
				method.setScope(qName);
				
				NodeList<Expression> arguments= new NodeList<Expression>();
				NameExpr argument= new NameExpr("1");
				arguments.add(argument);
				method.setArguments(arguments);
				catchStatement.getBody().addStatement(0,method);
			}
				
		}
			
		}
        
 }

private AssertStmt addAlarm(JMLMethodCall clause) {
	
	AssertStmt aStatement=addMethodCallAssertion(clause);
	StringLiteralExpr  message= new StringLiteralExpr(clause.getThreat());
    aStatement.setMessage(message);
    return aStatement;
}

private AssertStmt addJMLConditionalClauseAssertion(JMLConditionalClause jmlclause) {
	
	Expression assertExpr;
	
	assertExpr= new BinaryExpr(new NameExpr(jmlclause.getLeftOp()), new IntegerLiteralExpr(jmlclause.getRightOp()), getInfixExpressionOp(jmlclause.getOperator()));
	AssertStmt aStatement= new AssertStmt(new EnclosedExpr(assertExpr));
	
	if (jmlclause.getThreat()!=null) {
	StringLiteralExpr  message= new StringLiteralExpr(jmlclause.getThreat());
    aStatement.setMessage(message);
	}
    
    return aStatement;

}

private AssertStmt addMethodCallAssertion(JMLMethodCall jmlMethod) {
	
	Expression binaryExpr = getMethodCallBinaryExpr(jmlMethod);
	return new AssertStmt(new EnclosedExpr(binaryExpr));
	

}

private Expression getMethodCallBinaryExpr(JMLMethodCall jmlMethod) {
	
	MethodCallExpr method = getMethodCallExpr(jmlMethod);
	
	Expression binaryExpr;
	binaryExpr= new BinaryExpr(method, new IntegerLiteralExpr(jmlMethod.getRightOp()), getInfixExpressionOp(jmlMethod.getOperator()));
	return binaryExpr;
}

private MethodCallExpr getMethodCallExpr(JMLMethodCall jmlMethod) {
	MethodCallExpr method= new MethodCallExpr();
	method.setName(jmlMethod.getName());
	
	NodeList<Expression> arguments= new NodeList<Expression>();
	
	 for (int i=0; i <jmlMethod.getParameters().size(); i++)
	 {
		NameExpr argument= new NameExpr(jmlMethod.getParameters().get(i));
	    	arguments.add(argument);
	    	method.setArguments(arguments);
	 }
	 
	 if (!(jmlMethod.getQualifiedName()==null)) {
		 	NameExpr qName =new NameExpr(jmlMethod.getQualifiedName());
	        method.setScope(qName);
	        }
	return method;
}


private BinaryExpr.Operator getInfixExpressionOp(String operator) {
	switch (operator) {
	  case "<":
	       return BinaryExpr.Operator.LESS;
	  case ">":
		    return BinaryExpr.Operator.GREATER;
	  case "=<":
		    return BinaryExpr.Operator.LESS_EQUALS;
	  case "=>":
			return BinaryExpr.Operator.GREATER_EQUALS;
	  case "==":
			return BinaryExpr.Operator.EQUALS;
	  case "!=":
			return BinaryExpr.Operator.NOT_EQUALS;
	}
	
	return null;
}
}
 
