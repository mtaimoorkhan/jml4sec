package test;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;

public class MyASTVisitor extends ASTVisitor{
	CompilationUnit cu;
	
	public MyASTVisitor(CompilationUnit cu) {
		this.cu=cu;
	}
	
Set names = new HashSet();

public boolean visit(VariableDeclarationFragment node) {
	SimpleName name = node.getName();
	this.names.add(name.getIdentifier());
	System.out.println("Declaration of '"+name+"' at line"+cu.getLineNumber(name.getStartPosition()));
	return false; // do not continue to avoid usage info
}

public boolean visit(SimpleName node) {
	if (this.names.contains(node.getIdentifier())) {
	System.out.println("Usage of '" + node + "' at line " +	cu.getLineNumber(node.getStartPosition()));
	}
	return true;
}

}
