package uk.gre.ac.openjmlsec.gen;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseAction;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseAlarms;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignals;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.ext.ActionClauseExtension;
import org.jmlspecs.openjml.ext.AlarmsClauseExtension;
import org.jmlspecs.openjml.ext.MethodExprClauseExtensions;
import org.jmlspecs.openjml.ext.SignalsClauseExtension;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCNewArray;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;


/**
 * This method is to be used at compile time.
 * 
 * Scans the {@link org.jmlspecs.openjml.JmlTree.JmlCompilationUnit} and adds if
 * condition in each method with JML specification. The condition calls
 * {@link uk.gre.ac.openjmlsec.gen.utils.EscVerify#verify} method
 * 
 * @author Suranjan Poudel & Wyatt Sutton
 */
public class CompileTimeEscVerificationCodeGenerator
{

    public static final CompileTimeEscVerificationCodeGenerator instance = new CompileTimeEscVerificationCodeGenerator();

    private CompileTimeEscVerificationCodeGenerator() {}

    private TreeMaker maker;
    private Names     symbolsTable;
    private Utils     utils;

    public void init(Context context) {
        this.maker = TreeMaker.instance(context);
        this.symbolsTable = Names.instance(context);
        this.utils = Utils.instance(context);
    }
    
    public void addVerifyIfStatement(JmlMethodSpecs tree, String classname, String sub_classes) {
        System.out.println("DEBUG-SYM: " + Thread.currentThread().getStackTrace()[1]);
        
        JCTree.JCBlock methodBody = ((JCTree.JCMethodDecl) tree.decl).body;
        JCTree.JCIf ifStatement = translateSpecsToIfStatements(tree, classname, sub_classes);

        methodBody.stats = methodBody.stats.prepend(ifStatement);
    }
    
    /*
     * Get the statements from jml specs
     * Also get all used variables
     */
    private java.util.List<JCStatement> GetSpecStatements(JmlMethodSpecs tree, HashSet<Name> used_variables){
    	//Parse statements
        java.util.HashMap<String, ArrayList<JCExpression>> alarms_calls = new HashMap<>();
        java.util.HashMap<String, ArrayList<JCStatement>> action_calls = new HashMap<>();
        java.util.HashMap<String, ArrayList<JCExpression>> signals_calls = new HashMap<>();
        
    	for (JmlSpecificationCase specCase : tree.cases) {
            JCTree.JCExpression prev_expr = null;
            for (JmlMethodClause clause : specCase.clauses) {
                String clauseName = clause.clauseKind.keyword;
                
                if (clauseName.equalsIgnoreCase(AlarmsClauseExtension.alarmsID)) {
                	JmlMethodClauseAlarms alarms_clause = (JmlMethodClauseAlarms) clause;
                	String key = alarms_clause.attackType.toString();
                	if (!alarms_calls.containsKey(key)) {
                		alarms_calls.put(key, new ArrayList<>());
                	}
                	alarms_calls.get(key).add(alarms_clause.expression);
                
                } else if (clauseName.equalsIgnoreCase(SignalsClauseExtension.signalsID)) {
                	JmlMethodClauseSignals signals_clause = (JmlMethodClauseSignals) clause;
                	String key = signals_clause.vardef.vartype.toString();
                	if (!signals_calls.containsKey(key)) {
                		signals_calls.put(key, new ArrayList<>());
                	}
                	signals_calls.get(key).add(signals_clause.expression);
                    
                } else if (clauseName.equalsIgnoreCase(ActionClauseExtension.actionID)) {
                    JmlMethodClauseAction action_clause = (JmlMethodClauseAction) clause;
                	String key = action_clause.actionType.toString();
                	if (!action_calls.containsKey(key)) {
                		action_calls.put(key, new ArrayList<>());
                	}
                	action_calls.get(key).add(action_clause.statement);
                } else if (
                		clauseName.equalsIgnoreCase(MethodExprClauseExtensions.ensuresID)
                		|| clauseName.equalsIgnoreCase(MethodExprClauseExtensions.requiresID)
                ) {
                    GetNames(prev_expr, used_variables);
                }
            }
        }
    	
    	//Add code
        java.util.List<JCStatement> statements = new ArrayList<>();
        var run_time_throw = maker.Throw(maker.NewClass(null, null, maker.Ident(symbolsTable.fromString("java.lang.RuntimeException")),  List.nil(), null));
        
        //Alarms is first, if we can recover we should
        for (String key: alarms_calls.keySet()) {
        	java.util.List<JCStatement> action_statements = new ArrayList<>();
        	if (action_calls.containsKey(key)) {
        		for (JCStatement expr: action_calls.get(key)) {
        			action_statements.add(expr);
        		}
        	} else {
        		action_statements.add(run_time_throw);
        	}
        	JCExpression expression = alarms_calls.get(key).get(0);
        	for (int i = 1; i < alarms_calls.get(key).size(); i++) {
        		expression = maker.Binary(JCTree.Tag.OR, expression, alarms_calls.get(key).get(i));
        	}
        	
        	statements.add(maker.If(expression, 
    			(action_statements.size() == 1)?
    				action_statements.get(0):
    				maker.Block(0L, List.from(action_statements)), 
    			null
        	));
        }

        //Signals is next for errors
        for (String key: signals_calls.keySet()) {
            JCStatement code = maker.Block(0L, List.of(maker.Throw(maker.NewClass(null, null, maker.Ident(symbolsTable.fromString(key)), List.nil(), null))));
            
        	JCExpression expression = signals_calls.get(key).get(0);
        	for (int i = 1; i < signals_calls.get(key).size(); i++) {
        		expression = maker.Binary(JCTree.Tag.OR, expression, signals_calls.get(key).get(i));
        	}
            
            statements.add(maker.If(expression, code, null));
        }
        
        //If there were not specs, just throw an error
        if (statements.isEmpty()) {
            statements.add(run_time_throw);
        }
        
        return statements;
    }
    
    private JCMethodInvocation constructMethodCall(JmlMethodSpecs tree, String classname, String sub_classes, HashSet<Name> used_variables) {
    	java.util.List<JCExpression> arguments = new ArrayList<>();
        
        arguments.add(maker.Literal(classname));
        arguments.add(maker.Literal(sub_classes));
        arguments.add(maker.Literal(tree.decl.getParameters().map(type -> type.vartype).toString()));
        arguments.add(maker.Literal(tree.decl.name.toString()));
        
        ArrayList<JCExpression> realMethodParameters = new ArrayList<>();
        for (JCVariableDecl param: tree.decl.params) {
            realMethodParameters.add(maker.Ident(param.name));
        }

        //*
        //Add needed objects from requires and ensures causes - Wyatt
        
        for (JCVariableDecl param: tree.decl.params) {
            if (used_variables.contains(param.name)) {
            	used_variables.remove(param.name);
            }
        }
        
        for (Name name: used_variables) {
            realMethodParameters.add(maker.Ident(name));
        }
        
        //*/
        
        JCNewArray paramArray = maker.NewArray(
                maker.Ident(symbolsTable.fromString("java.lang.Object")),
                List.nil(), List.from(realMethodParameters));

        arguments.add(paramArray);
        
        // Make function call
        return maker.Apply(
        		 List.nil(),
        		 maker.Select(
        				 maker.Ident(symbolsTable.fromString(EscVerify.class.getName())),
        	             symbolsTable.fromString("verify")),
        		 List.from(arguments));
    }
    
    
    /*
     * Adds a if statement with a call to verify() with its body having statements from JML specs
     */
    private JCTree.JCIf translateSpecsToIfStatements(JmlMethodSpecs tree, String classname, String sub_classes) {
        HashSet<Name> used_variables = new HashSet<>();
        java.util.List<JCStatement> statements = GetSpecStatements(tree, used_variables);
        JCMethodInvocation methodInvocation = constructMethodCall(tree, classname, sub_classes, used_variables);
        
        return maker.If(
            maker.Unary(JCTree.Tag.NOT, methodInvocation),
            maker.Block(0L, List.from(statements)), null
       );
    }
    
    /*
     * Finds all JCIdent names within an expression
     * 
     * Parameters:
     * 		expr_base: JCExpression
     * 			the expression to search
     * 		list: HashSet<Name>
     * 			The set to add names too
     */
    public static void GetNames(JCTree.JCExpression expr_base, HashSet<Name> list){
       if (expr_base == null || list == null) return;
       
       if (expr_base instanceof JCTree.JCIdent) {
           list.add(((JCIdent) expr_base).name);
       } else if (expr_base instanceof JCTree.JCBinary) {
           JCTree.JCBinary expr = (JCTree.JCBinary) expr_base;
           GetNames(expr.lhs, list);
           GetNames(expr.rhs, list);
       } else if (expr_base instanceof JCTree.JCMethodInvocation) {
           JCTree.JCMethodInvocation expr = (JCTree.JCMethodInvocation) expr_base;
           GetNames(expr.meth, list);
           for (JCTree.JCExpression arg: expr.args)
               GetNames(arg, list);
        } else if (expr_base instanceof JCTree.JCParens) {
            JCTree.JCParens expr = (JCTree.JCParens) expr_base;
            GetNames(expr.expr, list);
        } else if (expr_base instanceof JCTree.JCUnary) {
            JCTree.JCUnary expr = (JCTree.JCUnary) expr_base;
            GetNames(expr.arg, list);
        } else if (expr_base instanceof JCTree.JCArrayAccess) {
            JCTree.JCArrayAccess expr = (JCTree.JCArrayAccess) expr_base;
            GetNames(expr.index, list);
            GetNames(expr.indexed, list);
        } else if (expr_base instanceof JCTree.JCFieldAccess) {
        	JCTree.JCFieldAccess expr = (JCTree.JCFieldAccess) expr_base;
            GetNames(expr.selected, list);
        } else if (expr_base instanceof JmlTree.JmlChained) {
            JmlTree.JmlChained expr = (JmlTree.JmlChained) expr_base;
            for (JCBinary c: expr.conjuncts) GetNames(c, list);
        } else if (!(
            expr_base instanceof JCTree.JCLiteral
            || expr_base instanceof JmlTree.JmlSingleton
            || expr_base instanceof JCTree.JCErroneous
        )) {
            System.err.println("Unknown JCExpression: " + expr_base.getClass() +"\nPlease add code for it @"+Thread.currentThread().getStackTrace()[1]);
        }
    }
}
