package uk.gre.ac.openjmlsec.gen;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.HashSet;

import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.Factory;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.ext.MethodExprClauseExtensions;
import org.jmlspecs.openjml.ext.SingletonExpressions;
import org.jmlspecs.openjml.ext.StatementExprExtensions;
import org.jmlspecs.openjml.ext.TypeExprClauseExtension;
//import org.jmlspecs.openjml.ext.StatementExprType;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.Tag;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Names;

import uk.gre.ac.openjmlsec.FilePaths;
import uk.gre.ac.openjmlsec.JML4Sec;
import uk.gre.ac.openjmlsec.gen.CompileTimeEscVerificationCodeGenerator;

import com.sun.tools.javac.util.Name;

public class EscVerify {
    
    /*
     * Verifies a function using EscRunner
     * 
     * Parameters:
     * 		className: String
     * 			the full package path to the class (including the class name)
     * 		subClass: String
     * 			Any subclasses that the function is in, separated by a "."
     * 			If there are no subclasses, an empty string is passed
     * 		methodArgs: String
     * 			the type name of all the method arguments separated by a ","
     * 		params: Object[]
     * 			A list of parameters passed to the function along with any variables used within specs
     * 
     * Returns:
     * 		if verification was a success
     */
    public static boolean verify(String className, String subClass, String methodArgs, String methodName, Object[] params) {
        boolean success = false;
        
        String classLocation = className.replaceAll("\\.", "/");
        Path classFilePath = Paths.get(FilePaths.SOURCE_FOLDER + classLocation+ ".java").toAbsolutePath();

        Path sourceFilePath = null;

        try {
        	//Parse file
            API api = Factory.makeAPIImpl();
            RefranceInstanceRegister();
            JmlCompilationUnit unit = api.parseSingleFile(classFilePath.toString());
            
            sourceFilePath = Files.createTempFile(classFilePath.getParent(), "Test_", ".java");
            
            String new_main_class = sourceFilePath.getFileName().toString().replace(".java", "");
            
            //Parse code
            CodeGenerator gen = new CodeGenerator(api.context(), subClass, methodArgs, methodName, params, new_main_class);
            unit.accept(gen);
            
            //Write file
            Files.write(sourceFilePath, unit.toString().getBytes(), StandardOpenOption.WRITE);
            System.out.println(unit.toString());
            
            //Run esc
            java.util.List<String> output = new ArrayList<>();
            success = EscRunner.runEsc(sourceFilePath.toString(), methodName+",test_"+methodName, output);
            output.stream().forEach(System.out::println);
        } catch (Exception th) {
        	//Any errors
            th.printStackTrace();
        } finally {
        	//Clean up temp file.
            if (sourceFilePath != null) {
                try {
                    Files.deleteIfExists(sourceFilePath);
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        }

        return success;
    }
    
	/*
	 * Problem with initialization where subclasses of IJmlClauseKind do not put their keys into the map
	 */
	public static void RefranceInstanceRegister() {
		//References each class by calling to string
    	var temp = ""
		+ TypeExprClauseExtension.invariantClause.toString()
		+ SingletonExpressions.resultKind.toString();
	}

    private static class CodeGenerator extends JmlTreeScanner {
        
        private final String   methodName;
        private final String   methodSubClass;
        private final String   methodArgs;
        private final String   newMainClass;

        private final Object[] params;

        private final TreeMaker 	maker;
        private final Names 		symbolTable;
        private final JmlTree.Maker jml_maker;

        private String   	   subclasses = "";
        private JmlClassDecl   owner = null;
        
        static private int esc_verify_temp_class = 0;

        public CodeGenerator(
        		Context context,
        		String methodSubClass,
        		String methodArgs,
        		String methodName,
        		Object[] params,
        		String newMainClass
        	) {
        	this.methodName = methodName;
            this.methodSubClass = methodSubClass;
            this.methodArgs = methodArgs;
            this.params = params;
            this.newMainClass = newMainClass;

            maker = TreeMaker.instance(context);
            symbolTable = Names.instance(context);
            jml_maker = JmlTree.Maker.instance(context);
        }
        
        /*
         * Replace all old class name with new one
         */
        @Override
        public void visitIdent(JCIdent tree) {
        	if (owner != null && subclasses.equals("") && owner.name.equals(tree.name) ) {
        		tree.name = symbolTable.fromString(newMainClass);
        	}
        	
        	super.visitIdent(tree);
        }
        
        /*
         * Keeps track of what subclass we are in
         * + replaces the root classes name
         */
        @Override
        public void visitJmlClassDecl(JmlClassDecl that) {
            JmlClassDecl prev = owner;
            String old = subclasses;
            if (owner != null) {
            	subclasses += that.name.toString();
            }
            owner = that;
            super.visitJmlClassDecl(that);
            owner = prev;
            subclasses = old;
            
            //Replace name
            if (owner == null) // Root class
            	that.name = symbolTable.fromString(newMainClass);
        }
        
        /*
         * Invert "compromised_behavior" so parser don't get confused - Wyatt (ws3765c@gre.ac.uk)
         * Also gets names of variables used at runtime
         * Can't use remove, so create a new list and add the ones we want.
         * 
         * Parameters:
         * 		tree: JmlMethodSpecs
         * 			The specs to search though
         * Returns:
         * 		A Set of names that were found
         */
        private HashSet<Name> InvertCompromisedBehavior(JmlMethodSpecs tree) {
            HashSet<Name> used_vairables = new HashSet<>();
            //*
            for (JmlSpecificationCase c: tree.cases) {
                boolean reverse = c.token != null && (
                    c.token.keyword.equals("compromised_behavior")
                    || c.token.keyword.equals("exceptional_behavior")
                );
                
                for (JmlMethodClause clause: c.clauses) {
                    if (
                        clause.keyword.equals(MethodExprClauseExtensions.requiresID)
                        || clause.keyword.equals(MethodExprClauseExtensions.ensuresID)
                    ) {
                        JmlMethodClauseExpr expr = (JmlMethodClauseExpr) clause;
                        CompileTimeEscVerificationCodeGenerator.GetNames(expr.expression, used_vairables);
                        
                        if (reverse) {
                            JCTree.JCExpression not_expr = maker.Unary(Tag.NOT, expr.expression);
                            expr.expression = not_expr;
                        }
                    }
                }
            }
            //*/
            
            return used_vairables;
        }
        
        /*
         * Adds the test function to the class
         */
        @Override
        public void visitJmlMethodSpecs(JmlMethodSpecs tree) {
        	//Check if it is the function we are looking for
            if (
	    		!subclasses.equals(methodSubClass)
	    		|| !methodArgs.equals(tree.decl.getParameters().map(type -> type.vartype).toString())
	    		|| !tree.decl.name.toString().equals(methodName)
            ) {
                super.visitJmlMethodSpecs(tree);
                return;
            }
            
            var used_vairables = InvertCompromisedBehavior(tree);
            
            java.util.List<JCStatement> body = new ArrayList<>();
            
            System.out.println("used_vairables:" + used_vairables); 
            
            //*
            //Add assumes clauses as before we could not tell the state of other variables
            
            for (JCVariableDecl param: tree.decl.params) {
                if (used_vairables.contains(param.name)) {
                    used_vairables.remove(param.name);
                }
            }
            
            int j = 0;
            for (Name name: used_vairables) {
            	AddAssume(maker.Ident(name), params[tree.decl.params.size() + j], body);
                j++;
            }
            //*/
            
            //Create method call
            
            java.util.List<JCExpression> arguments = new ArrayList<>();
            for (int i = 0; i < tree.decl.params.size(); i++) {
            	String type_hint = tree.decl.params.get(i).getType().toString();
            	JCTree.JCExpression expr = GetArgument(params[i], type_hint, body);
                arguments.add(expr);
            }
            
            JCMethodInvocation methodInvocation = maker.Apply(List.nil(),
                    maker.Ident(symbolTable.fromString(methodName)),
                    List.from(arguments));

            JCStatement methodCall = maker.Exec(methodInvocation);

            body.add(methodCall);
            
            // Add the test function
            JCMethodDecl testMethodDefinition = maker.MethodDef(
                    maker.Modifiers(Flags.PRIVATE),
                    symbolTable.fromString("test_" + methodName),
                    maker.TypeIdent(TypeTag.VOID), List.nil(), null, List.nil(),
                    List.nil(), maker.Block(0, /*List.of(methodCall)*/ List.from(body)), null);
            
            owner.defs = owner.defs.append(testMethodDefinition);
            
            super.visitJmlMethodSpecs(tree);
        }
        
        /*
         * Gets a compile time value for an run time object
         * 
         * Parameters:
         * 		object: Object
         * 			the object to translate
         * 		type_hint: String
         * 			The possible type for this object, used to help identify its type
         * 		body: List<JCStatement>
         * 			A list of statements used to add assumes for complex types.
         * 
         * Returns:
         * 		A JCExpression representing as close as possible the object.
         */
        public JCTree.JCExpression GetArgument(Object object, String type_hint, java.util.List<JCStatement> body){
        	//Null
        	if (object == null) {
        		return maker.Ident(symbolTable.fromString("null"));
        	}
        	
        	//Primitives
        	else if (
        		object instanceof String
        		|| object instanceof Boolean
        		|| object instanceof Character
        		|| object instanceof Byte
        		|| object instanceof Short
        		|| object instanceof Integer
        		|| object instanceof Long
        		|| object instanceof Float
        		|| object instanceof Double
        		|| object instanceof Integer
        	) {
            	return maker.Literal(object);
            
            //Arrays
        	} else if (object.getClass().isArray()) {
        		java.util.List<Object> list = new ArrayList<>();
                String type_name = "Object";
                if (object instanceof int[]) {
                    for (int v: (int[]) object) list.add(v);
                    type_name = "int";
                }
                else if (object instanceof byte[]) {
                    for (byte v: (byte[]) object) list.add(v);
                    type_name = "byte";
                }
                else if (object instanceof short[]) {
                    for (short v: (short[]) object) list.add(v);
                    type_name = "short";
                }
                else if (object instanceof long[]) {
                    for (long v: (long[]) object) list.add(v);
                    type_name = "long";
                }
                else if (object instanceof float[]) {
                    for (float v: (float[]) object) list.add(v);
                    type_name = "float";
                }
                else if (object instanceof double[]) {
                    for (double v: (double[]) object) list.add(v);
                    type_name = "double";
                }
                else if (object instanceof boolean[]) {
                    for (boolean v: (boolean[]) object) list.add(v);
                    type_name = "boolean";
                }
                else if (object instanceof char[]) {
                    for (char v: (char[]) object) list.add(v);
                    type_name = "char";
                } else {
                	for (Object v: (Object[]) object) list.add(v);
                    if (type_hint != null && type_hint.lastIndexOf("[") != -1) {
                    	type_name = type_hint.substring(0, type_hint.lastIndexOf("["));
                    }
                }
                ArrayList<JCTree.JCExpression> elems = new ArrayList<>();
                JCIdent type = maker.Ident(symbolTable.fromString(type_name));
                for (Object elem: list) {
                    elems.add(GetArgument(elem, type_name, body));
                }
                return maker.NewArray(type, List.nil(), List.from(elems));
            
            //Class instances
        	} else {
        		// A class was passed
        		String name = "__esc_verify_temp_class" + (esc_verify_temp_class++) + "__";
        		var expr = maker.Ident(symbolTable.fromString(name));
        		owner.defs = owner.defs.append(
        			maker.VarDef(maker.Modifiers(Flags.STATIC), symbolTable.fromString(name), maker.Ident(symbolTable.fromString(type_hint)), null)
        		);
        		AddAssume(expr, object, body);
        		
        		return expr;
        	}
        }
        
        /*
         * Adds assume statements for objects for Z3 / esc checking to be able to infer run time values.
         * 
         * Parameters:
         * 		left: JCExpression
         * 			The identifier that will be assumed to be assigned.
         * 		object: Object
         * 			The run time value of this identifier
         *		body: List<JCStatement>
         * 			A list of statements used to add assumes for complex types.
         */
        public void AddAssume(JCTree.JCExpression left, Object object, java.util.List<JCStatement> body) {
        	if (object == null){
        		//assume left == null;
                body.add(jml_maker.JmlExpressionStatement(
                    StatementExprExtensions.assumeID, StatementExprExtensions.assumeClause, Label.EXPLICIT_ASSUME,
                    maker.Binary(Tag.EQ, left, maker.Ident(symbolTable.fromString("null")))
                ));
        	}
        	else if (
        		object instanceof String
        		|| object instanceof Boolean
        		|| object instanceof Character
        		|| object instanceof Byte
        		|| object instanceof Short
        		|| object instanceof Integer
        		|| object instanceof Long
        		|| object instanceof Float
        		|| object instanceof Double
        		|| object instanceof Integer
        	) {
        		//assume left == object;
                body.add(jml_maker.JmlExpressionStatement(
                    StatementExprExtensions.assumeID, StatementExprExtensions.assumeClause, Label.EXPLICIT_ASSUME,
                    maker.Binary(Tag.EQ, left, maker.Literal(object))
                ));
        	}
        	else if (object.getClass().isArray()) {
        		Object[] value;
        		if (object instanceof boolean[]) {
        			value = new Object[((boolean[]) object).length];
        			for (int i = 0; i < value.length; i++) value[i] = Boolean.valueOf(((boolean[]) object)[i]);
        		} else if (object instanceof char[]) {
        			value = new Object[((char[]) object).length];
        			for (int i = 0; i < value.length; i++) value[i] = Character.valueOf(((char[]) object)[i]);
        		} else if (object instanceof byte[]) {
        			value = new Object[((byte[]) object).length];
        			for (int i = 0; i < value.length; i++) value[i] = Byte.valueOf(((byte[]) object)[i]);
        		} else if (object instanceof short[]) {
        			value = new Object[((short[]) object).length];
        			for (int i = 0; i < value.length; i++) value[i] = Short.valueOf(((short[]) object)[i]);
        		} else if (object instanceof int[]) {
        			value = new Object[((int[]) object).length];
        			for (int i = 0; i < value.length; i++) value[i] = Integer.valueOf(((int[]) object)[i]);
        		} else if (object instanceof long[]) {
        			value = new Object[((long[]) object).length];
        			for (int i = 0; i < value.length; i++) value[i] = Long.valueOf(((long[]) object)[i]);
        		} else if (object instanceof float[]) {
        			value = new Object[((float[]) object).length];
        			for (int i = 0; i < value.length; i++) value[i] = Float.valueOf(((float[]) object)[i]);
        		} else if (object instanceof double[]) {
        			value = new Object[((double[]) object).length];
        			for (int i = 0; i < value.length; i++) value[i] = Double.valueOf(((double[]) object)[i]);
        		} else { // Prey
        			value = (Object[]) object;
        		}
        		//assume left.length != null;
    			body.add(jml_maker.JmlExpressionStatement(
                    StatementExprExtensions.assumeID, StatementExprExtensions.assumeClause, Label.EXPLICIT_ASSUME,
                    maker.Binary(Tag.NE, left, maker.Ident(symbolTable.fromString("null")))
                ));
        		//assume left.length == object.length;
        		AddAssume(maker.Select(left, symbolTable.fromString("length")), value.length, body);
        		for (int i = 0; i < value.length; i++) {
            		//assume left[i] == object[i];
        			AddAssume(maker.Indexed(left, maker.Literal(i)), value[i], body);
        		}
        		
        	} else { // Has to be some instance (I hope)
        		try {
        			body.add(jml_maker.JmlExpressionStatement(
                        StatementExprExtensions.assumeID, StatementExprExtensions.assumeClause, Label.EXPLICIT_ASSUME,
                        maker.Binary(Tag.NE, left, maker.Ident(symbolTable.fromString("null")))
                    ));
        			System.out.println("FEILDS:" + object.getClass().getDeclaredFields().length);
					for (var field : object.getClass().getDeclaredFields()) {
					    field.setAccessible(true); // You might want to set modifier to public first.
					    Object value = field.get(object); 
					    if (value != null) {
					        //System.out.println(field.getType() + " " + field.getName() + "=" + value);
					    	//assume left.feild == value;
					    	AddAssume(maker.Select(left, symbolTable.fromString(field.getName())), value, body);
					    }
					}
				} catch (SecurityException | IllegalArgumentException | IllegalAccessException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
        	}
        }
    }
}
