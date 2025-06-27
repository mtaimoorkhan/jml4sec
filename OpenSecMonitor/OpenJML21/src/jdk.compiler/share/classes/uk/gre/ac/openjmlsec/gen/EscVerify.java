package uk.gre.ac.openjmlsec.gen;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;

import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.Factory;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.ext.JmlPrimitiveTypes;
import org.jmlspecs.openjml.ext.QuantifiedExpressions;
import org.jmlspecs.openjml.ext.SingletonExpressions;
import org.jmlspecs.openjml.ext.TypeExprClauseExtension;
import org.jmlspecs.openjml.ext.TypeInitializerClauseExtension;

public class EscVerify {
    static private String LOG_FILE = System.getProperty("OpenJMLSec_LogFile");
    static private String SOURCE_FOLDER = (System.getProperty("OpenJMLSec_SourceFolder") == null)? "./": System.getProperty("OpenJMLSec_SourceFolder");
    
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
        synchronized (EscVerify.class) {
	        boolean success = false;
	        
	        String classLocation = className.replaceAll("\\.", "/");
	        Path classFilePath = Paths.get(SOURCE_FOLDER).resolve(classLocation+ ".java").toAbsolutePath();
	        
	        //File does not exist
	        if (!classFilePath.toFile().isFile()) {
	        	Log("Source file path does not exist: " + classFilePath);
	        	return false;
	        }
	        
	        Path sourceFilePath = null;
	        
	        try {
	        	//Parse file
	            API api = Factory.makeAPIImpl();
	            RefranceInstanceRegister();
	            JmlCompilationUnit unit = api.parseSingleFile(classFilePath.toString());
	            
	            sourceFilePath = Files.createTempFile(classFilePath.getParent(), "Test_", ".java");
	            
	            String new_main_class = sourceFilePath.getFileName().toString().replace(".java", "");
	            
	            //Parse code
	            RunTimeEscVerificationCodeGenerator gen = new RunTimeEscVerificationCodeGenerator(api.context(), subClass, methodArgs, methodName, params, new_main_class);
	            unit.accept(gen);
	            
	            //Write file
	            Files.write(sourceFilePath, unit.toString().getBytes(), StandardOpenOption.WRITE);
	            //System.out.println(unit.toString());
	            
	            //Run esc
	            java.util.List<String> output = new ArrayList<>();
	            success = EscRunner.runEsc(sourceFilePath.toString(), methodName+",test_"+methodName, output);
	            
	            output.stream().forEach(EscVerify::Log);
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
    }
    
    public static void Log(String line) {
    	try {
    		if (LOG_FILE == null) throw new IOException("OpenJMLSec_LogFile parameter not passed");
			Files.writeString(
			    Path.of(LOG_FILE),
			    System.lineSeparator() + line.strip(),
			    StandardOpenOption.CREATE, StandardOpenOption.APPEND
			);
		} catch (IOException e) {
			if (LOG_FILE != null) System.err.println("Could not write to log file: " + LOG_FILE + ", reason:" + e);
			System.err.println(line.strip());
		}
}
    
	/*
	 * Problem with initialization where subclasses of IJmlClauseKind do not put their keys into the map
	 */
	public static void RefranceInstanceRegister() {
		//References each class by calling to string
		TypeExprClauseExtension.invariantClause.toString();
		SingletonExpressions.resultKind.toString();
    	QuantifiedExpressions.qforallKind.toString();
    	JmlPrimitiveTypes.nothingKind.toString();
    	TypeInitializerClauseExtension.staticinitializerClause.toString();
	}
}
