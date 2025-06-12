package uk.gre.ac.openjmlsec.gen.utils;

import java.nio.file.Paths;

import org.smtlib.ICommand;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.SMT;
import org.smtlib.impl.Factory;

public class SMTSolver {
    public static boolean verify(String smtFileName) {
        SMT smt = new SMT();

        String proverToUse = "z3_4_3";
        String exec = getProverExec();

        ISolver solver = smt.startSolver(smt.smtConfig, proverToUse, exec);
        Factory.initFactories(smt.smtConfig);
        IStringLiteral fileName = smt.smtConfig.exprFactory
                .unquotedString(smtFileName + ".smt");
        ICommand.IScript script = smt.smtConfig.exprFactory.script(fileName,
                null);

        // Run prover
        IResponse solverResponse = null;
        try {
            solverResponse = script.execute(solver);
        } catch (Exception e) {
            solver.exit();
            e.printStackTrace();
            solver = null;
            return false;
        }

        String res = smt.smtConfig.defaultPrinter.toString(solverResponse);

        solver.exit();

        return res.equalsIgnoreCase("sat");
    }

    public static String getProverExec() {
    	System.out.println("If this codes runs, please change 'solversRoot' to path for solvers, I belive it won't run");
        String solversRoot = "/home/workvm/Documents/openjml/";
        String os = System.getProperty("os.name");
        os = os.contains("Mac") ? "macos" : os;
        // Absolute path of the prover executable
        return Paths.get(solversRoot, "Solvers-" + os, "z3-4.3.1").toString();
    }
}
