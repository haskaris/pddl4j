package fr.uga.pddl4j.satplanner;

import fr.uga.pddl4j.encoding.CodedProblem;
import fr.uga.pddl4j.heuristics.relaxation.Heuristic;
import fr.uga.pddl4j.heuristics.relaxation.HeuristicToolKit;
import fr.uga.pddl4j.parser.ErrorManager;
import fr.uga.pddl4j.planners.Planner;
import fr.uga.pddl4j.planners.ProblemFactory;
import fr.uga.pddl4j.planners.Statistics;
import fr.uga.pddl4j.planners.statespace.StateSpacePlanner;
import fr.uga.pddl4j.planners.statespace.search.strategy.AStar;
import fr.uga.pddl4j.planners.statespace.search.strategy.Node;
import fr.uga.pddl4j.planners.statespace.search.strategy.StateSpaceStrategy;
import fr.uga.pddl4j.util.BitOp;
import fr.uga.pddl4j.util.BitState;
import fr.uga.pddl4j.util.CondBitExp;
import fr.uga.pddl4j.util.MemoryAgent;
import fr.uga.pddl4j.util.Plan;
import fr.uga.pddl4j.util.SequentialPlan;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;

import java.io.File;
import java.io.IOException;

import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Properties;
import java.util.Set;

public final class SATPlanner {

    /*
    * The arguments of the planner.
    */
    private Properties arguments;

    /**
    * Creates a new SATPlanner planner with the default parameters.
    *
    * @param arguments the arguments of the planner.
    */
    public SATPlanner(final Properties arguments) {
        super();
        this.arguments = arguments;
    }

    /**
    * Parse the command line and return the planner's arguments.
    *
    * @param args the command line.
    * @return the planner arguments or null if an invalid argument is encountered.
    */
    private static Properties parseCommandLine(String[] args) {

        // Get the default arguments from the super class
        final Properties arguments = StateSpacePlanner.getDefaultArguments();

        // Parse the command line and update the default argument value
        for (int i = 0; i < args.length; i += 2) {
            if ("-o".equalsIgnoreCase(args[i]) && ((i + 1) < args.length)) {
                if (!new File(args[i + 1]).exists()) {
                    return null;
                }
                arguments.put(Planner.DOMAIN, new File(args[i + 1]));
            } else if ("-f".equalsIgnoreCase(args[i]) && ((i + 1) < args.length)) {
                if (!new File(args[i + 1]).exists()) {
                    return null;
                }
                arguments.put(Planner.PROBLEM, new File(args[i + 1]));
            } else if ("-t".equalsIgnoreCase(args[i]) && ((i + 1) < args.length)) {
                final int timeout = Integer.parseInt(args[i + 1]) * 1000;
                if (timeout < 0) {
                    return null;
                }
                arguments.put(Planner.TIMEOUT, timeout);
            } else if ("-w".equalsIgnoreCase(args[i]) && ((i + 1) < args.length)) {
                final double weight = Double.parseDouble(args[i + 1]);
                if (weight < 0) {
                    return null;
                }
                arguments.put(StateSpacePlanner.WEIGHT, weight);
            } else {
                return null;
            }
        }
        // Return null if the domain or the problem was not specified
        return (arguments.get(Planner.DOMAIN) == null
            || arguments.get(Planner.PROBLEM) == null) ? null : arguments;
    }

    /**
    * Print the usage of the SATPlanner planner.
    */
    private static void printUsage() {
        final StringBuilder strb = new StringBuilder();
        strb.append("\nusage of PDDL4J:\n")
            .append("OPTIONS   DESCRIPTIONS\n")
            .append("-o <str>    operator file name\n")
            .append("-f <str>    fact file name\n")
            .append("-w <num>    the weight used in the a star seach (preset: 1.0)\n")
            .append("-t <num>    specifies the maximum CPU-time in seconds (preset: 300)\n")
            .append("-h          print this message\n\n");
        Planner.getLogger().trace(strb.toString());
    }

    /**
    * Encode problem into a solver as a DIMACS DNF structure.
    *
    * @param problem the problem to be solved.
    * @return IProblem
    */
    public IProblem encodeToSAT(final CodedProblem problem) {
        ISolver solver = SolverFactory.newDefault();
        List<BitOp> listOperators = problem.getOperators();
        List<String> listPredicates = problem.getPredicates();
        int maxVar = listOperators.size();
        int nbClauses = listPredicates.size();
        solver.newVar(maxVar);
        solver.setExpectedNumberOfClauses(nbClauses);
        for (int i = 0; i < nbClauses; i++) {
            /*int clause[] = ???; // TODO - get clause
            solver.addClause(new VecInt(clause));*/
        }
        return (IProblem) solver;
    }

    /**
    * Extracts a search from a specified node.
    *
    * @param node the node.
    * @param problem the problem.
    * @return the search extracted from the specified node.
    */
    private Plan extractPlan(final Node node, final CodedProblem problem) {
        Node n = node;
        final Plan plan = new SequentialPlan();
        while (n.getOperator() != -1) {
            final BitOp op = problem.getOperators().get(n.getOperator());
            plan.add(0, op);
            n = n.getParent();
        }
        return plan;
    }

    /**
    * The main method of the <code>SATPlanner</code> example. The command line syntax is as
    * follow:
    * <p>
    * <pre>
    * usage of SATPlanner:
    *
    * OPTIONS   DESCRIPTIONS
    *
    * -o <i>str</i>   operator file name
    * -f <i>str</i>   fact file name
    * -w <i>num</i>   the weight used in the a star search (preset: 1)
    * -t <i>num</i>   specifies the maximum CPU-time in seconds (preset: 300)
    * -h              print this message
    *
    * </pre>
    * </p>
    *
    * @param args the arguments of the command line.
    */
    public static void main(String[] args) {
        final Properties arguments = SATPlanner.parseCommandLine(args);
        if (arguments == null) {
            SATPlanner.printUsage();
            System.exit(0);
        }
        final SATPlanner planner = new SATPlanner(arguments);

        final ProblemFactory factory = ProblemFactory.getInstance();
        File domain = (File) arguments.get(Planner.DOMAIN);
        File problem = (File) arguments.get(Planner.PROBLEM);
        ErrorManager errorManager = null;
        try {
            errorManager = factory.parse(domain, problem);
        } catch (IOException e) {
            Planner.getLogger().trace("\nunexpected error when parsing the PDDL planning problem description.");
            System.exit(0);
        }

        if (!errorManager.isEmpty()) {
            errorManager.printAll();
            System.exit(0);
        } else {
            Planner.getLogger().trace("\nparsing domain file done successfully");
            Planner.getLogger().trace("\nparsing problem file done successfully\n");
        }

        final CodedProblem pb = factory.encode();
        Planner.getLogger().trace("\nencoding problem done successfully ("
                    + pb.getOperators().size() + " ops, "
                    + pb.getRelevantFacts().size() + " facts)\n");
        if (!pb.isSolvable()) {
            Planner.getLogger().trace(String.format("goal can be simplified to FALSE."
                    +  "no search will solve it%n%n"));
            System.exit(0);
        }

        final IProblem pbSAT = planner.encodeToSAT(pb);
        if (pbSAT != null) {
            // TODO
        } else {
            // TODO
        }
    }
}
