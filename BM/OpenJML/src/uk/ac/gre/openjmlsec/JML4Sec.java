package uk.ac.gre.openjmlsec;

import com.github.javaparser.StaticJavaParser;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.*;

import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;


import greenwich.ensuresec.vistor.JavaCodeVistor;
import greenwich.ensuresec.vistor.FileHandler;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;


public class JML4Sec {
    
    public void typeCheck(String filePath) {
        int errors = 0;

        try {
            
        JML4Sec main = new JML4Sec();
        IAPI api = Factory.makeAPI(null);
        JmlCompilationUnit unit = api.parseSingleFile(filePath); 
        
        ArrayList<JmlCompilationUnit> units = new ArrayList<JmlCompilationUnit>();
        units.add(unit);
        
     //   JmlCompilationUnit unit1 = api.parseSingleFile("/Users/drijazahmed/runtime-EclipseApplication/EComJsp/src/utility/com/greenwich/JMLUtilityFunctions.java"); 
    //    units.add(unit1);
        
        System.out.println(unit);
        errors = api.typecheck(units);        
        
        }catch(Throwable th) {th.printStackTrace();}
        finally {
            if(errors > 0)
                System.out.println("Type checking failed!");
            else
                System.out.println("Type checked successfully!");
        }

    }
    
    public static void generateAssertions(String file) {
     
      
        try {
            com.github.javaparser.ast.CompilationUnit cu = StaticJavaParser.parse(new FileInputStream(file));
            cu.accept(new JavaCodeVistor(), null);
         //   System.out.println(cu.toString());
         //   System.out.println("save"+ cu.toString());
            FileHandler.createFile(file, cu.toString());
            
            } 
        
        catch (FileNotFoundException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        

    }
    
   

    public static void main(String[] args) {
        // TODO Auto-generated method stub
        JML4Sec sec = new JML4Sec();
     //   sec.typeCheck("src/uk/ac/gre/openjmlsec/A.java");
     //   sec.typeCheck("src/uk/ac/gre/openjmlsec/B.java");
        
     //   sec.typeCheck("/Users/drijazahmed/runtime-EclipseApplication/EComJsp/src/utility/com/greenwich/Student.java");
    //  sec.generateAssertions("/Users/drijazahmed/runtime-EclipseApplication/EComJsp/src/utility/com/greenwich/Student.java");
   //    sec.generateAssertions("/Users/drijazahmed/runtime-EclipseApplication/EComJsp/src/db/com/greenwich/DbBridge.java");
      
      ArrayList<File> files= new ArrayList<File>();
      generateAssertionsForProject("/Users/drijazahmed/runtime-EclipseApplication/EComJsp",files);
        
        //sec.typeCheck("src/uk/ac/gre/openjmlsec/Balance.java");
        

    }
    
    public static void generateAssertionsForProject(String directoryName, List<File> files) {
        
        File directory = new File(directoryName);
        File[] fList = directory.listFiles();
        if(fList != null)
            for (File file : fList) {      
                if (file.isFile()) {
                    files.add(file);
                    
                    if (file.toString().contains(".java")) {
                        
                        System.out.println("Parsing File: "+file.toString());
                        generateAssertions(file.toString());
                        System.out.println("Generated assertions for File: "+file.toString());
                    }
                    
                } else if (file.isDirectory()) {
                    generateAssertionsForProject(file.getAbsolutePath(), files);
                }
            }
    }

}
