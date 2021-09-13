package greenwich.ensuresec.vistor;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Path;
import java.util.Calendar;
import java.util.GregorianCalendar;
import java.util.LinkedList;
import java.util.List;
import java.util.ArrayList;

import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.ImportDeclaration;
import org.eclipse.jdt.core.dom.rewrite.ASTRewrite;
import org.eclipse.jdt.core.dom.rewrite.ListRewrite;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.text.edits.MalformedTreeException;
import org.eclipse.text.edits.TextEdit;

import greenwich.ensuresec.structure.JMLStore;

import org.eclipse.core.resources.IFile;



public class UserSelectedClassesAnalysis {
	
	static Time starttime, endtime;
	BufferedWriter dot;
	static int testType;

public static void analyzeFromCommandLine(LinkedList<String> inputFiles, String strType,String strK) {
/*		
	EVMDD_SMC_Generator.reset();
		testType=Integer.parseInt(strType);
		Boolean JML;
		for (String input:inputFiles){
				JML=false;
			    if (input.contains("/*@")==true){
			    	JML=true;
			    	JMLAnnotatedJavaClass JClass=new JMLAnnotatedJavaClass();
			    	input=JClass.translateJMLAnnotationsToPlural(input);
			    }
				ASTParser parser = ASTParser.newParser(3);
				parser.setSource(input.toCharArray());
			    CompilationUnit result = (CompilationUnit) parser.createAST(null);
			    SMC_Visitor visitor = new SMC_Visitor();
			    result.accept(visitor);
			    if (JML==true){
					input=EVMDD_SMC_Generator.modifyConstructorSpecifications(input);
			    	E_GeneratedPluralSpecification.createFromCommandLine(input,"pluralAnnotated");
			    }
			}
	
	E_SMC_Model.setK(Integer.parseInt(strK));
	E_SMC_Model.generateSMCmodel_CommandLine(EVMDD_SMC_Generator.getPkgObject(),testType); // create the model.stm file
	callModelCheckerThroughCommandLine();  // run the model 
*/	
	}
		
	
public void analyzeFromPlugin( List<ICompilationUnit> compilationUnitList, int testType) {

}

public void analyzeJMLFromPlugin( List<ICompilationUnit> compilationUnitList, int testType,IProgressMonitor monitor) {
	
	try {
			this.testType=testType;
			
			JMLStore.create();
			Boolean JML;
			
			for (ICompilationUnit cunit : compilationUnitList) {
				JML=false;
				String prog=getInputStream(cunit);
				CompilationUnit cu=null;
	
			//	prog=JMLAnnotatedJavaClass.parseJML(prog);
				//cu=getCompilationUnit(prog);
				cu=getCompilationUnit(cunit);
				System.out.println("Comments:"+cu.getCommentList().toString());
				
				JMLVistor visitor = new JMLVistor();
				cu.accept(visitor);
				cunit.getBuffer().setContents(cu.toString());
				
				cunit.save(monitor, true);
			}	
			
		} 
	catch (Exception e) {e.printStackTrace();}

}

public static Document add() {
	Document document = new Document("import java.util.List;\nclass X {}\n");
	ASTParser parser = ASTParser.newParser(AST.JLS3);
	parser.setSource(document.get().toCharArray());
	CompilationUnit cu = (CompilationUnit) parser.createAST(null);
	AST ast= cu.getAST();
	ImportDeclaration id= ast.newImportDeclaration();
	id.setName(ast.newName(new String[] {"java", "util", "Set"}));
	ASTRewrite rewriter= ASTRewrite.create(ast);
	ListRewrite lrw=rewriter.getListRewrite(cu, CompilationUnit.IMPORTS_PROPERTY);
	lrw.insertLast(id,null);
	TextEdit edits= rewriter.rewriteAST(document,null);
	try {
		edits.apply(document);
	} catch (MalformedTreeException | BadLocationException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
	}
	System.out.println(document.get());
	return document;
	
}

private CompilationUnit getCompilationUnit(String prog){
	ASTParser parser = ASTParser.newParser(3);
	parser.setSource(prog.toCharArray());
	CompilationUnit cu = (CompilationUnit) parser.createAST(null);
	return cu;
	
}

private CompilationUnit getCompilationUnit(ICompilationUnit cunit){
	
	CompilationUnit compilationUnit = (CompilationUnit)WorkspaceUtilities.getASTNodeFromCompilationUnit(cunit);
	return compilationUnit;
	
}

public String  getInputStream(ICompilationUnit unit)  {
	
	InputStream in=null;
	if (unit != null) {
		try {
			in=((IFile)(unit.getCorrespondingResource())).getContents();
		} 
		catch (CoreException e) {e.printStackTrace();}
		
		    BufferedInputStream bis = new BufferedInputStream(in);
		    ByteArrayOutputStream buf = new ByteArrayOutputStream();
		    int result;
			try {
				result = bis.read();
				 while(result != -1) {
				      byte b = (byte)result;
				      buf.write(b);
				      result = bis.read();
				    }
			}
			catch (IOException e) {e.printStackTrace();}
		           
		    return buf.toString();
		}
	return null;
	
}





	
	
	public static Time getTime() {
			
			Time t= new Time();
			Calendar calendar = new GregorianCalendar();
			t.hour = calendar.get(Calendar.HOUR);
			t.minute =calendar.get(Calendar.MINUTE);
			t.second =calendar.get(Calendar.SECOND);
			t.msecond=calendar.getTimeInMillis();	
			return t;
			
		}
}




