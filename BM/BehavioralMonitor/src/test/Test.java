package test;

	import java.util.HashSet;
	import java.util.Set;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
	import org.eclipse.jdt.core.dom.ASTVisitor;
	import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.ImportDeclaration;
import org.eclipse.jdt.core.dom.SimpleName;
	import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.rewrite.ASTRewrite;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.text.edits.MalformedTreeException;
import org.eclipse.text.edits.TextEdit;

import greenwich.ensuresec.vistor.JMLAnnotatedJavaClass;

import org.eclipse.jdt.core.dom.rewrite.ListRewrite;

	 
	public class Test {
		public static void main(String args[]){
			
			String str="//@compromised_behavior( requires=\"a > 1020 && Islogin (x , y)>115\",ensures=\" b > 10\", \n" + 
					"alarms= \"x > y ==>SQLINJECTION\")";
			
			JMLAnnotatedJavaClass.parseAndStoreJMLAnnotation(str);
		}

		

}
