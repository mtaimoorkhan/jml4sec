package greenwich.ensuresec.vistor;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;

import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;

public class FileHandler {
	
public static void createFile(String path,String text) {
	
//	IWorkspace workspace = ResourcesPlugin.getWorkspace(); 
//	String folder= workspace.getRoot().getLocation().toFile().getPath().toString();
	FileWriter fstream;
	try {
		//fstream = new FileWriter(path+"/"+name+".text");
		
		fstream = new FileWriter(path);
		BufferedWriter out = new BufferedWriter(fstream);
		out.write(text);
		out.flush();
		System.out.println("File "+ path + " with assertions is created in folder");
	} catch (IOException e) {
		// TODO Auto-generated catch block
		 System.exit(1);
		e.printStackTrace();
	}
	
	
}

}
