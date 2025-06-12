package uk.gre.ac.openjmlsec.gen;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.List;
import java.util.Queue;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import uk.gre.ac.openjmlsec.FilePaths;

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
    public static boolean runEsc(String filePath, String methodName, List<String> output) {
        boolean success = false;
        int exitCode = 0;
        ProcessBuilder builder = new ProcessBuilder();
        
        builder.command("/bin/sh", "-c",
                new File(FilePaths.OPENJML_PATH).getAbsolutePath() + " -esc "
                        + filePath + ((methodName == null)? "": (" --method " + methodName)));

        builder.redirectErrorStream(true);
        
        try {

            Process process = builder.start();
            
            Queue<String> outputFragments = new ConcurrentLinkedQueue<>();
            StreamGobbler outputGobbler = new StreamGobbler(
                    process.getInputStream(), outputFragments::add);

            outputGobbler.start();

            exitCode = process.waitFor();
            if (exitCode != 0) {
                System.out.println("Failed to check esc. (error code: "+exitCode+")");
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
        output.add("exitCode: " + exitCode);
        output.add("Success: " + success);
        
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
}
