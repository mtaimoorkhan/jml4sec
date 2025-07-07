package uk.gre.ac.openjmlsec.gen;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.List;
import java.util.Queue;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.function.Consumer;
import java.util.stream.Collectors;

//import uk.gre.ac.openjmlsec.JML4Sec;


public class EscRunner {
    /*
     * Runs `openjml -esc` on a file with optional method name
     * 
     * Parameters:
     * 		filePath: String
     * 			The path to the file
     * 		methodName: String | null
     * 			The method to verify
     * 			If this value is null, verify the whole file.
     * 		output: List<String>
     * 			A pointer to a list to put the processes output into
     * 
     * Returns:
     * 		if verify was a success
     */
    static private String OPENJML_PATH = (System.getProperty("OpenJMLSec_openjml") == null)? "openjml": System.getProperty("OpenJMLSec_openjml");

    static public String SMALL_BREAK = "-";
    static public String BREAK = "=";
    static public int BREAK_LENGTH = 30;
    
    public static boolean runEsc(String filePath, String methodName, List<String> output) {
        boolean success = false;
        int exitCode = 0;
        ProcessBuilder builder = new ProcessBuilder();
        
        String command =
    		new File(OPENJML_PATH).getAbsolutePath()
    		+ " -classpath \"" + System.getProperty("java.class.path") + "\""
    		// For testing
    		+ " --specs-path /home/workvm/Documents/Work21/Specs/specs"
    		//+ " --new-is-pure"
    		+ " -esc " + filePath
            + (
        		(methodName == null)? "":
        		(" --method " + methodName)
            )
            //For testing
    		//+ " -verbose"
            
    		;
        //System.out.println("command: " + command);
        builder.command("/bin/sh", "-c", command);

        builder.redirectErrorStream(true);
        
        try {

            Process process = builder.start();
            
            Queue<String> outputFragments = new ConcurrentLinkedQueue<>();
            StreamGobbler outputGobbler = new StreamGobbler(
                    process.getInputStream(), outputFragments::add);

            outputGobbler.start();

            exitCode = process.waitFor();
            if (exitCode != 0) {
            	output.add("Failed to check esc. (error code: "+exitCode+")");
            }

            output.addAll(outputFragments.stream().collect(Collectors.toList()));
            success = true;
            
        } catch (Exception e) {
            e.printStackTrace();
            success = false;
        }
        
        for (String line: output) {
            if (!line.equalsIgnoreCase("unsat")) {
                success = false;
            }
            
        }
        output.add(SMALL_BREAK.repeat(BREAK_LENGTH));
        output.add("exitCode: " + exitCode);
        output.add("Success: " + success);
        output.add(BREAK.repeat(BREAK_LENGTH));
        
        //For testing, if console log got too long
        //JML4Sec.writeFile("/mnt/java/output.txt", output_string);
        /* /home/workvm/output.txt */
        //*/

        return success;
    }

    public static class StreamGobbler extends Thread {
        private final InputStream      inputStream;

        private final Consumer<String> consumer;

        public StreamGobbler(InputStream inputStream,
                Consumer<String> consumer) {
            this.inputStream = inputStream;
            this.consumer = consumer;
        }

        @Override
        public void run() {
            try (BufferedReader bufferedReader = new BufferedReader(
                    new InputStreamReader(inputStream))) {
                String line;
                while ((line = bufferedReader.readLine()) != null) {
                    consumer.accept(line);
                }
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    static private String LOG_FILE = System.getProperty("OpenJMLSec_LogFile");
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
}
