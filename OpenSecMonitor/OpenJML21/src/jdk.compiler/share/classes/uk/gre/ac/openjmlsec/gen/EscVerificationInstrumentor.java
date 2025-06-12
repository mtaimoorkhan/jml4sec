package uk.gre.ac.openjmlsec.gen;

import java.util.ArrayList;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;

import uk.gre.ac.openjmlsec.gen.CompileTimeEscVerificationCodeGenerator;

public class EscVerificationInstrumentor extends JmlTreeScanner {
    private final JmlTree.Maker maker;
    private final JmlAttr attr;
    
    private String classname = null;
    private String sub_classes = "";
    
    public EscVerificationInstrumentor(Context context) {
        super();
        maker = JmlTree.Maker.instance(context);
		attr = JmlAttr.instance(context);
        
        CompileTimeEscVerificationCodeGenerator.instance.init(context);
    }

	/*
	 * This is a work around for the tree.sym not being present in visitJmlMethodSpecs
	 * Finds the class name and subclasses for the functions
	 */
    @Override
    public void visitJmlClassDecl(JmlClassDecl tree) {
    	String old = sub_classes;
    	//First class should be root class;
    	if (classname == null)
    		classname = tree.toplevel.pid.pid + "." + tree.name;
    	else {
    		sub_classes += (sub_classes.isEmpty()? "": ".") + tree.name;
    	}
    	super.visitClassDef(tree);
    	sub_classes = old;
    }
    
    /*
     * Generate specs when we find a function
     */
    @Override
    public void visitJmlMethodSpecs(JmlMethodSpecs tree) {
    	CompileTimeEscVerificationCodeGenerator.instance.addVerifyIfStatement(tree, classname, sub_classes);
    }

    /*
     * Remove @ghost annotations for runtime analysis
     * - Wyatt
     */
    @Override
    public void visitJmlVariableDecl(JmlVariableDecl that) {
		if (attr.isGhost(that.mods)) that.mods.flags &= ~(1<<16);
    	super.visitJmlVariableDecl(that);
    }
    
    /*
     * Translate `@set ...` to expressions for runtime analysis
     * - Wyatt
     */
    @Override
    public void visitBlock(JCBlock tree) {
        super.visitBlock(tree);
        
        ArrayList<JCStatement> statements = new ArrayList<>();

        for (JCStatement stm: tree.stats) {
            //Find @set
            if (stm instanceof JmlVariableDecl && ((JmlVariableDecl) stm).vartype.toString().equals("set")) {
            	JmlVariableDecl jml_stm = (JmlVariableDecl) stm;
                //Add its statement
            	var new_stm = maker.Assign(maker.Ident(jml_stm.name), jml_stm.init);
            	//maker.VarDef(maker.Modifiers(0), jml_stm.name, jml_stm.vartype, jml_stm.init);
                statements.add(maker.Exec(new_stm));
            } else {
                //Add others
                statements.add(stm);
            }
        }
        
        //Replace old statements
        tree.stats = List.from(statements);
    }
    
}
