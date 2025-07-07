package uk.gre.ac.openjmlsec;

import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.jmlspecs.openjml.Factory;
import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;

import uk.gre.ac.openjmlsec.gen.EscVerificationInstrumentor;
import uk.gre.ac.openjmlsec.gen.EscVerify;
import uk.gre.ac.openjmlsec.gen.EscRunner;
import java.util.ArrayList;

public class JML4Sec {
	private JML4Sec() {}
	
    public static void main(String[] args) {
        if (args.length != 2) {
            System.err.println("Filename and output folder reqauired as argument.");
            return;
        }
        
        Path filename = Paths.get(args[0]);
        Path output_path = Paths.get(args[1]);
        
        if (!filename.toFile().isFile()) {
        	System.err.println("Not a valid filename: " + filename);
        	return;
        }
        if (!output_path.toFile().exists()) {
        	System.err.println("Not a valid output folder: " + filename);
        	return;
        }

        System.out.println("Reading file: " + filename.toString());
        
        String code = typeCheck(filename);
        if (code != null) {
            writeFile(output_path.resolve(filename.getFileName()), code);
        }
    }
    
    /*
     * Checks the JML Spec is correct and returns generated code
     * 
     * Parameters:
     *      filePath: String
     *          The path to the Java file to check specs for
     * 
     * Returns:
     *      null -> on error
     *      Otherwise -> A string containing the generated code with assertions
     */
    public static String typeCheck(Path filePath) {
        int errors = 0;
        String output_code = null;
        
        //For testing
        /*Do esc check on entire class
        System.out.println("Esc checking");
        ArrayList<String> output = new ArrayList<>();
        if (!EscRunner.runEsc(filePath, null, output)) {
            output.stream().forEach(System.err::println);
            return null;
        }
        System.out.println("Done");
        //*/
        
        //Do type checking
        try {
            System.out.println("Type checking");
            IAPI api = Factory.makeAPI(new String[] {});
            EscVerify.RefranceInstanceRegister();

            System.out.println("1/4 PARSE");
            JmlCompilationUnit unit = api.parseSingleFile(filePath.toString());
            System.out.println("Done");
            
            System.out.println("2/4 TYPECHECK");
            errors = api.typecheck(unit);
            System.out.println("Done");

            System.out.println("3/4 TRANSLATE");
            unit.accept(new EscVerificationInstrumentor(api.context()));
            System.out.println("Done");

            System.out.println("4/4 TO_STRING");
            output_code = unit.toString();
            System.out.println("Done");

        } catch (Throwable th) {
            th.printStackTrace();
            errors += 1;
        } finally {
            System.out.println(errors > 0 ? "Type checking failed."
                    : "Type check successfull.");
            if (errors > 0) output_code = null;
        }
        
        return output_code;
    }
    
    /*
     * Writes the contents of a string to a file on disk
     * 
     * filename: String
     *      A valid filename
     * 
     * content: String
     *      The content to write to the file
     */
    public static void writeFile(Path filename, String content) {
        try {
            FileWriter writer = new FileWriter(filename.toString());
            writer.write(content);
            writer.close();
            System.out.println("Successfully wrote to " + filename);
        } catch (IOException e) {
            System.out.println("An error occurred when trying to write to file: " + filename);
            e.printStackTrace();
        }
    }
}
