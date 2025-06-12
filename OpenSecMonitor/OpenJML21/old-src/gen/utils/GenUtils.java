package uk.gre.ac.openjmlsec.gen.utils;

import java.util.StringJoiner;

import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.util.Context;

public class GenUtils {
    
    public static final String FILE_DIR = "/Home/workvm/Documents/git-ug-out/";
    
    public static final String SMT_VERIFY_CODE_GEN_FACTORY_KEY = "smt_verify_code_generator";
    //public static final String COMPILETIME_ESC_VERIFY_CODE_GEN_FACTORY_KEY = "compiletime_esc_verify_code_generator";

    public static String getFileName(JmlMethodDecl decl) {
        StringJoiner joiner = new StringJoiner("_");
        String className = decl.sym.owner.toString().replaceAll("\\.", "_");
        joiner.add("verify");
        joiner.add(className);
        joiner.add(decl.name.toString());
        return joiner.toString();
    }

}

