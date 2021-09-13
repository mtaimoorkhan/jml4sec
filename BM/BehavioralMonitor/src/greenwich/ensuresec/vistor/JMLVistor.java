package greenwich.ensuresec.vistor;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;

import greenwich.ensuresec.jmlgrammar.JMLLexer;
import greenwich.ensuresec.jmlgrammar.JMLParser;
import greenwich.ensuresec.plugin.PulseSettings;
import greenwich.ensuresec.structure.*;


import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.TokenStream;
import org.eclipse.jdt.core.dom.*;
import org.eclipse.jdt.core.dom.InfixExpression.Operator;
import org.eclipse.jdt.core.dom.rewrite.ASTRewrite;


public class JMLVistor extends ASTVisitor {
	

	public JMLVistor() {
		super();
	}
	
	@Override
	public void preVisit(ASTNode node) {
		super.preVisit(node);
	}
	
	// just for logging, does not use in parsing
	@Override
	public void postVisit(ASTNode node) {
		super.postVisit(node);
	}

	// we parse and store info but no rules apply for this case
	@Override
	public boolean visit(PackageDeclaration node) {
		
		return super.visit(node);
	}
	
	@Override
	public void endVisit(PackageDeclaration node) {
		
		super.endVisit(node);
	}
	
	@Override
	public boolean visit(TypeDeclaration node) {
		
	/*	
		System.out.println(node.getName().toString());
		JMLStore.setClassName(node.getName().toString());
		AST ast = node.getAST();
		
		VariableDeclarationFragment fragment = ast.newVariableDeclarationFragment();
		fragment.setName(ast.newSimpleName("seq"));
		FieldDeclaration field=ast.newFieldDeclaration(fragment);
		
		FieldDeclaration[] fields= node.getFields();
		fields[2]=field;
	*/	
		
		
		
		
		/*	
		methodName="";
		
		E_Class _class=new E_Class();
		_class.setName(node.getName().toString());
		
		if (PulseSettings.getInheritance()==1 ||PulseSettings.getFullModel()==1){	
			Type superClass=node.getSuperclassType();
			if (superClass!=null)
			_class.setSuperClassName(superClass.toString());
		}
		
		FieldDeclaration[] fields= node.getFields();
		if (fields!=null){
			for (FieldDeclaration field:fields){
				if (!field.getType().isPrimitiveType()){
					E_Field _field=new E_Field();
					_field.setName(((VariableDeclarationFragment)field.fragments().get(0)).getName().toString());
					
					if (field.getType().isParameterizedType())
						_field.setType(((ParameterizedType)field.getType()).getType().toString());
					else if (field.getType().isArrayType()){
						Type componentType=((ArrayType)field.getType()).getComponentType();
						if (componentType.isParameterizedType()){ //
							_field.setType(((ParameterizedType)componentType).getType().toString());
						}
						else
						_field.setType(((ArrayType)field.getType()).getComponentType().toString());
					}
					else
					_field.setType(field.getType().toString());
					
					_field.setModifier(field.getModifiers());
					_class.addField(_field);
				}
			}
			
		}
		
		EVMDD_SMC_Generator.getPkgObject().getClasses().addLast(_class); */
		return super.visit(node);
	}

	@Override
	public void endVisit(TypeDeclaration node) {
		
	//	FileHandler.createFile(JMLStore.getClassName(), node.getRoot().toString());
		
		
		super.endVisit(node);
	}
	
	@Override
	public boolean visit(BlockComment node){
		
		  System.out.println("BCCC: " +node.toString());
		  return super.visit(node);
	}
	
	@Override
	public void endVisit(BlockComment node) {
		System.out.println(node.toString());
		super.endVisit(node);
	}

	@Override
	public boolean visit(MethodDeclaration node) {
	
	        return super.visit(node);
	}
	
	@Override
	public void endVisit(MethodDeclaration node) {
		
		System.out.println("End of Method: "+ node.getName());
		AST ast = node.getAST();
	
			for (int i=0; i<JMLStore.getClausesSize(); i++) {
				
		//		node.getBody().statements().add(0,addAssertions(node, ast, JMLStore.getRequires(i)));
				System.out.println("Class type:"+JMLStore.getClause(i));
				
				switch(JMLStore.getClause(i).getClauseType())
		        {
		            case "requires":
		            case "before":
		            {
		            		if (JMLStore.getClause(i) instanceof JMLConditionalClause)
		            	    node.getBody().statements().add(0,addAssertions(node, ast, (JMLConditionalClause)JMLStore.getClause(i))); 
		            		else if (JMLStore.getClause(i) instanceof JMLMethodCall) 
		            		node.getBody().statements().add(0,addMethodCallAssertions(node, ast,(JMLMethodCall)JMLStore.getClause(i)));
		            			
		            		break;
		            }
		            
		            case "ensures":
		            		if (JMLStore.getClause(i) instanceof JMLConditionalClause)
		            		node.getBody().statements().add(addAssertions(node, ast,(JMLConditionalClause)JMLStore.getClause(i)));
		            		else if (JMLStore.getClause(i) instanceof JMLMethodCall) 
			            	node.getBody().statements().add(addMethodCallAssertions(node, ast,(JMLMethodCall)JMLStore.getClause(i)));
		                break;
		            	
		            case "after":
		            	//	if (JMLStore.getClause(i) instanceof JMLConditionalClause)
		            	ExpressionStatement statement=addAssignmentStatement(node, ast,(JMLConditionalClause)JMLStore.getClause(i));
		            		node.getBody().statements().add(statement);
		            		node.getBody().statements().add(addAssertions(node, ast,(JMLConditionalClause)JMLStore.getClause(i)));
		            	//	else if (JMLStore.getClause(i) instanceof JMLMethodCall) 
			           // 	node.getBody().statements().add(addMethodCallAssertions(node, ast,(JMLMethodCall)JMLStore.getClause(i)));
		            		
		                break;
		                
		            case "alarms":
		            	if (JMLStore.getClause(i) instanceof JMLMethodCall)
		            		node.getBody().statements().add(0,addAlarm(node, ast, (JMLMethodCall)JMLStore.getClause(i)));
		            	
		                break;
		            default:
		                System.out.println("no match");
		        }
				
			}
		JMLStore.reset();
		super.endVisit(node);
	}
	
	private ExpressionStatement addAssignmentStatement(MethodDeclaration node, AST ast, JMLConditionalClause jmlclause) {
		
		
		Assignment asg=ast.newAssignment();
	
		asg.setLeftHandSide(ast.newSimpleName(jmlclause.getLeftOp()));
		asg.setRightHandSide(ast.newNumberLiteral(jmlclause.getRightOp()));
		ExpressionStatement statement=ast.newExpressionStatement(asg);
		
		return statement;
	}

	private AssertStatement addMethodCallAssertions(MethodDeclaration node, AST ast, JMLMethodCall jmlMethod) {
		
		 	AssertStatement aStatement=ast.newAssertStatement();
	        InfixExpression infixexpression= ast.newInfixExpression();
	        
	        infixexpression.setOperator(getInfixExpressionOp(jmlMethod.getOperator())); 
	      //  Expression right= ast.newName(jmlMethod.getRightOp());
	        
	        MethodInvocation methodInvo=ast.newMethodInvocation();
	   	    
	     //   QualifiedName qn= ast.newQualifiedName(ast.newName("qualif"), ast.newSimpleName(jmlMethod.getName()));
	        if (!(jmlMethod.getQualifiedName()==null)) {
	        SimpleName qName =ast.newSimpleName(jmlMethod.getQualifiedName());
	        methodInvo.setExpression(qName);
	        }
	       
	        methodInvo.setName(ast.newSimpleName(jmlMethod.getName()));
	        
	        for (int i=0; i <jmlMethod.getParameters().size(); i++)
	        	methodInvo.arguments().add(ast.newSimpleName(jmlMethod.getParameters().get(i)));
	        
	        
	        infixexpression.setLeftOperand(methodInvo);
	        infixexpression.setRightOperand(ast.newNumberLiteral(jmlMethod.getRightOp()));
	        aStatement.setExpression(infixexpression);
	        System.out.println(aStatement.toString());
	        return aStatement;
	}

	private AssertStatement addAssertions(MethodDeclaration node, AST ast, JMLConditionalClause jmlclause) {
		
		    AssertStatement aStatement=ast.newAssertStatement();
	        InfixExpression infixexpression= ast.newInfixExpression();
	        
	        infixexpression.setOperator(getInfixExpressionOp(jmlclause.getOperator()));
	        
	        Expression left= ast.newName(jmlclause.getLeftOp());
	      //  Expression right= ast.newName(jmlReq.getRightOp());
	        
	        infixexpression.setLeftOperand(left);
	        infixexpression.setRightOperand(ast.newNumberLiteral(jmlclause.getRightOp()));
	        aStatement.setExpression(infixexpression);
	        System.out.println(aStatement.toString());
	        return aStatement;
	        
	      //  System.out.println(node.toString());
	        
		       
	}
	
	
	private AssertStatement addAlarm(MethodDeclaration node, AST ast, JMLMethodCall jmlMethod) {
		
	 	AssertStatement aStatement=ast.newAssertStatement();
      //  InfixExpression infixexpression= ast.newInfixExpression();
        
     //   infixexpression.setOperator(getInfixExpressionOp(jmlMethod.getOperator())); 
      //  Expression right= ast.newName(jmlMethod.getRightOp());
        
        MethodInvocation methodInvo=ast.newMethodInvocation();
   	    
     //   QualifiedName qn= ast.newQualifiedName(ast.newName("qualif"), ast.newSimpleName(jmlMethod.getName()));
       
        methodInvo.setName(ast.newSimpleName(jmlMethod.getName()));
        
        for (int i=0; i <jmlMethod.getParameters().size(); i++)
        	methodInvo.arguments().add(ast.newSimpleName(jmlMethod.getParameters().get(i)));
        
        
     //   infixexpression.setLeftOperand(methodInvo);
     //   infixexpression.setRightOperand(ast.newNumberLiteral(jmlMethod.getRightOp()));
        aStatement.setExpression(methodInvo);
        
        StringLiteral sl= ast.newStringLiteral();
        sl.setLiteralValue(jmlMethod.getThreat());
        aStatement.setMessage(sl);
        
        System.out.println(aStatement.toString());
        return aStatement;
}
	
	
	private AssertStatement addAlarms(MethodDeclaration node, AST ast, JMLAlarm jmlAlarm) {
		
		
	    AssertStatement aStatement=ast.newAssertStatement();
        InfixExpression infixexpression= ast.newInfixExpression();
        
        infixexpression.setOperator(getInfixExpressionOp(jmlAlarm.getOperator()));
        
        Expression left= ast.newName(jmlAlarm.getLeftOp());
      //  Expression right= ast.newName(jmlReq.getRightOp());
        
        infixexpression.setLeftOperand(left);
        infixexpression.setRightOperand(ast.newNumberLiteral(jmlAlarm.getRightOp()));
        aStatement.setExpression(infixexpression);
        
        StringLiteral sl= ast.newStringLiteral();
        sl.setLiteralValue(jmlAlarm.getThreat());
        aStatement.setMessage(sl);
      
        System.out.println(aStatement.toString());
        return aStatement;
        
      //  System.out.println(node.toString());
        
	       
}
	
	private Operator getInfixExpressionOp(String operator) {
		switch (operator) {
		  case "<":
		       return Operator.LESS;
		  case ">":
			    return Operator.GREATER;
		  case "=<":
			    return Operator.LESS_EQUALS;
		  case "=>":
				return Operator.GREATER_EQUALS;
		  case "==":
				return Operator.EQUALS;
		  case "!=":
				return Operator.NOT_EQUALS;
		}
		
		return null;
	}

	
	@Override
	public boolean visit(SingleVariableDeclaration node){
		return super.visit(node);
	}
	@Override
	public boolean visit(TypeParameter node){
		
		return super.visit(node);
	}
	
	@Override 
	public boolean visit(NormalAnnotation node)
	{
		JMLStore.reset();
		System.out.println("Annotation to Parse: "+node.toString());
		
		JMLAnnotatedJavaClass.parseAndStoreJMLAnnotation(node.toString());
		return super.visit(node);
	}
	
	@Override 
	public void endVisit(NormalAnnotation node) {
			super.endVisit(node);
		}
	
	
	@Override 
	public boolean visit(SingleMemberAnnotation node)
	{	
		System.out.println("Class Annotation to Parse: "+node.toString());
		return super.visit(node);
	}

	@Override 
	public void endVisit(SingleMemberAnnotation node) {
		
		System.out.println("from end AnnotationTypeDeclaration"+ node.toString());
		super.endVisit(node);
		
	}


	
	
	
}

