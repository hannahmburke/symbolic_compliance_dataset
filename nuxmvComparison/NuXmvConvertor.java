package experiments.systems_compliance;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;

import compliance.obligations.ModelObligation;
import compliance.obligations.Obligation.ObligationConditionType;
import compliance.obligations.Obligation.ObligationTypes;
import datatypes.attributes.Attribute;
import datatypes.domain.DomainInstance;
import datatypes.functions.expressions.LambdaExpression;
import datatypes.types.DataType;
import datatypes.types.IntType;
import datatypes.values.Value;
import datatypes.values.Value.Operation;
import kotlin.jvm.internal.Lambda;
import model.Model;
import model.annotations.Annotation;
import model.annotations.Annotations.AnnotationIncompatibleWithStateException;
import model.annotations.AttributeAnnotation;
import model.annotations.ExpressionAnnotation;
import model.annotations.ValueAnnotation;
import model.executions.Execution;
import model.executions.ExecutionRestrictor;
import model.states.SimpleState;
import model.states.SimpleState.StateRetrievalException;
import nl.rug.ds.bpm.petrinet.interfaces.element.TransitionI;
import nl.rug.ds.bpm.petrinet.interfaces.marking.MarkingI;
import nl.rug.ds.bpm.petrinet.ptnet.PlaceTransitionNet;
import nl.rug.ds.bpm.petrinet.ptnet.element.Arc;
import nl.rug.ds.bpm.petrinet.ptnet.element.Place;
import nl.rug.ds.bpm.petrinet.ptnet.element.Transition;
import nl.rug.ds.bpm.petrinet.ptnet.marking.Marking;
import nl.rug.ds.bpm.util.exception.IllegalMarkingException;

import javax.xml.crypto.Data;

import static model.executions.Execution.id;

/*
converts the experiments to NuXmv files
 */
public class NuXmvConvertor {

	enum METHOD {
		BMC,
		SBMC_INC,
		IC3,
	}

	public static void main(String[] args) throws Exception {

		String testDataFile = "src/main/resources/experiments/batch.csv";
		String dir = "src/main/resources/experiments/";

		String row;

		BufferedReader csvReader = null;
		csvReader = new BufferedReader(new FileReader(testDataFile)); //Import each line of file into program
		csvReader.readLine();

		while ((row = csvReader.readLine()) != null) {

			String[] data = row.split(",");

			String model = data[1];
			model = model.replaceAll("\\./", dir);
			String annotations = data[2];
			annotations = annotations.replaceAll("\\./", dir);
			String obligations = data[3];
			obligations = obligations.replaceAll("\\./", dir);

			Model m = new Model(model, annotations, obligations);

			String experimentName = data[0].replace("./descriptions/", "").replace(".txt", "");

			String fileString = createFileString(m, experimentName);

			try (PrintWriter writer = new PrintWriter(new FileWriter("src/main/resources/nuxmv/models/"+experimentName+".smv"))) {
				writer.println(fileString);
			} catch (IOException e) {
				System.err.println("Error writing to the file: " + e.getMessage());
			}

			for (METHOD method: METHOD.values()) {

				String cmdString = "read_model\n"
						+ "flatten_hierarchy\n"
						+ "encode_variables\n"
						+ "go_msat\n";
				switch (method) {
					case BMC:
						cmdString += "msat_check_ltlspec_bmc -k "+m.getAllExecutions().stream().mapToInt(e->e.getAllTransitions().size()+1).max().getAsInt()+"\n";
						break;
					case SBMC_INC:
						cmdString += "msat_check_ltlspec_sbmc_inc -k "+m.getAllExecutions().stream().mapToInt(e->e.getAllTransitions().size()+1).max().getAsInt()+"\n";
						break;
					case IC3:
						cmdString += "check_ltlspec_ic3 -k "+m.getAllExecutions().stream().mapToInt(e->e.getAllTransitions().size()+1).max().getAsInt()+"\n";
						break;
				}
				cmdString += "quit";


				try (PrintWriter writer = new PrintWriter(new FileWriter("src/main/resources/nuxmv/commands/"+method.toString().toLowerCase()+"/"+experimentName+"_cmd.smv"))) {
					writer.println(cmdString);
				} catch (IOException e) {
					System.err.println("Error writing to the file: " + e.getMessage());
				}
			}
		}

		csvReader.close();

	}


	private static String createFileString(Model m, String name) throws StateRetrievalException, AnnotationIncompatibleWithStateException {

		String fileString = "MODULE main\n\n";

		fileString += "VAR\n\n";

		List<String> constants = new ArrayList<>();

		// reachability graph for petrinet. contains all possible markings in the graph, and their subsequent edges
		Map<String, List<Map.Entry<TransitionI, MarkingI>>> markings = buildReachabilityGraph(m.getPn());

		// get locations
		String locations = "location: {";
		for (String marking: markings.keySet()) {
			if (locations.equals("location: {"))
				locations += marking;
			else
				locations += ", " + marking;
		}
		locations += "};";

		fileString += "    " + locations + "\n";

		// get decision points. ie reachability nodes with multiple edges
		String decPoints = "";
		for (String marking : markings.keySet()) {
			if (markings.get(marking).size() > 1) {
				List<String> intList = new ArrayList<>();
				for (Integer i = 0; i < markings.get(marking).size(); i++) {
					intList.add(i.toString());
				}
				constants.add(marking + "_choice");
				decPoints += "    " + marking + "_choice: {" + String.join(", ", intList) + "};\n";
			}
		}
		fileString += decPoints;

		// get attributes
		String variables = "";
		Set<String> variableList = new HashSet<>();
		SimpleState initialState = m.getTAMap().getInitialState();
		for (String varName : initialState.getAllIDs()) {
			if (initialState.isInstancedVar(varName)) {
				for (Value instance : initialState.getAllInstancesOf(varName)) {
					if (initialState.get(varName, instance).getValType() == IntType.class) {
						variables += "    " + "var_" + SimpleState.getInstanceIdentifier(varName, instance) + ": Integer;\n";
						variableList.add(SimpleState.getInstanceIdentifier(varName, instance));
					} else {
						throw new RuntimeException("Shouldn't have non-integer variables: " + varName + "_" + instance);
					}
				}
			} else {
				if (initialState.get(varName, null).getValType() == IntType.class) {
					variables += "    var_" + varName + ": Integer;\n";
					variableList.add(SimpleState.getInstanceIdentifier(varName, null));
				} else {
					throw new RuntimeException("Shouldn't have non-integer variables: " + varName);
				}
			}
		}
		fileString += "\n\n" + variables + "\n\n";

		// get constants in annotations
		for (String t : m.getTAMap().getTransitions()) {
			if (m.getTAMap().getAnnotations(t).getAnnotations().size() == 0) continue;
			String annotationsT = "";
			for (Annotation a : m.getTAMap().getAnnotations(t).getAnnotations()) {
				if (a instanceof ValueAnnotation) {
					ValueAnnotation vA = (ValueAnnotation) a;
					String annotationVariable = SimpleState.getInstanceIdentifier(a.getVarID(), a.getIdentifier()) + "_" + t;
					annotationsT += "    " + annotationVariable + ": " + vA.getListVal() + ";\n";
					if (vA.getListVal().getList().size() < 1)
						constants.add(annotationVariable);
				} else if (a instanceof ExpressionAnnotation) {
					ExpressionAnnotation eA = (ExpressionAnnotation) a;
					for (Attribute c: eA.getConstants().keySet()){
						annotationsT += "    " + c.getName() + ": " + eA.getConstants().get(c) + ";\n";
						constants.add(c.getName());
					}
				}
			}
			fileString += annotationsT;
		}

		// initial values
		fileString += "\nASSIGN\n";
		String initVals = "    init(location) := " + id(m.getPn().getInitialMarking()) + ";\n";
		for (String varName : variableList) {
			initVals += "    init(var_" + varName + ") := " + varName + "_start;\n";
		}
		fileString += initVals + "\n";

		// constants
		String constantsString = "";
		for (String constant : constants) {
			constantsString += "    next(" + constant + ") := " + constant + ";\n";
		}
		fileString += "\n" + constantsString + "\n";

		// transitions
		fileString += "TRANS\n";
		String allTransitions = "(";
		for (String marking: markings.keySet()){
			int branchChoice = 0;
			for (Map.Entry<TransitionI, MarkingI> edge: markings.get(marking)){
				String transitionString = "\n    (";
				if (markings.get(marking).size() > 1) {
					transitionString += "    ((location = " + marking + ") & (" + marking + "_choice = " + branchChoice + ")) ->\n";
					branchChoice += 1;
				} else
					transitionString += "    (location = " + marking + ") ->\n";
				transitionString += "        (";
				transitionString += "\n        next(location) = " + id(edge.getValue()); // skip to next marking

				TransitionI t = edge.getKey();
				Set<String> annotatedVariables = new HashSet<>();
				for (Annotation a : m.getTAMap().getAnnotations(t).getAnnotations()) {
					String annotationVariable = SimpleState.getInstanceIdentifier(a.getVarID(), a.getIdentifier());
					annotatedVariables.add(annotationVariable);
					transitionString += " &\n        "+annotationToString(a, annotationVariable, t);
				}
				for (String variable : variableList) {
					if (!annotatedVariables.contains(variable)) {
						transitionString += " &\n        next(var_" + variable + ") = var_" + variable;
					}
				}
				transitionString += "\n        )\n    )\n";
				if (allTransitions.equals("("))
					allTransitions += transitionString;
				else
					allTransitions += "&\n" + transitionString;
			}

			if(markings.get(marking).size()==0){ // sink
				String transitionString = "\n    (";
				transitionString += "    (location = " + marking + ") ->\n";
				transitionString += "        (";
				transitionString += "\n        next(location) = " + marking;
				for (String variable : variableList) {
					transitionString += " &\n        next(var_" + variable + ") = var_" + variable;
				}
				transitionString += "\n        )\n    )\n";

				if (allTransitions.equals("("))
					allTransitions += transitionString;
				else
					allTransitions += "&\n" + transitionString;
			}
		}
		allTransitions += ")\n";
		fileString += allTransitions;

		// convert obligations into LTL
		String obligationString = "";
		for (ModelObligation o : m.getObligations()) {
			for (DomainInstance instance : o.getCodomain(m.getTAMap().getInitialState())) {
				String trig = subAttrs(o.getCondition(ObligationConditionType.TRIGGER)).toString(instance);
				String req = subAttrs(o.getCondition(ObligationConditionType.REQUIREMENT)).toString(instance);
				String dead = subAttrs(o.getCondition(ObligationConditionType.DEADLINE)).toString(instance);

				String result;
				if (o.getType() == ObligationTypes.ACHIEVEMENT)
					result = "LTLSPEC G((" + trig + ")->!(" + dead + ") U (" + req + "));";
				else
					result = "LTLSPEC G((" + trig + ")->(" + dead + ") V (" + req + "));";
				result = result.replaceAll("&&", "&");
				result = result.replaceAll("\\|\\|", "|");
				result = result.replaceAll("==", "=");
				result = result.replaceAll("true", "1>0");
				result = result.replaceAll("false", "1<0");
				obligationString += result + "\n";
			}
		}
		fileString += "\n\n" + obligationString;

		return fileString;
	}

	private static DataType subAttrs(DataType input) {
		if (input instanceof LambdaExpression){
			LambdaExpression subbed = (LambdaExpression) input;
			for (Attribute attr: input.getRelatedAttributes()){
				try {
					subbed = subbed.substitute(attr, LambdaExpression.generateSimpleExpression(
							Attribute.createFromDatatype("var_"+attr.getName(), attr)));
				} catch (Attribute.AttributeConstructionException e) {
					throw new RuntimeException(e);
				}
			}
			return subbed;
		}
		return input;
	}

	private static String annotationToString(Annotation a, String annotationVariable, TransitionI t) {
		if (a instanceof ValueAnnotation) {
			if (a.getOperation() == Operation.EQUALS)
				return "next(var_" + annotationVariable + ") = " + annotationVariable + "_" + t.getId();
			else if (a.getOperation() == Operation.PLUS)
				return "next(var_" + annotationVariable + ") = var_" + annotationVariable + " + " + annotationVariable + "_" + t.getId();
			else if (a.getOperation() == Operation.MINUS)
				return "next(var_" + annotationVariable + ") = var_" + annotationVariable + " - " + annotationVariable + "_" + t.getId();
			else
				throw new RuntimeException("Unsupported annotation operation");
		} else if (a instanceof AttributeAnnotation){
			AttributeAnnotation aA = (AttributeAnnotation) a;
			if (a.getOperation() == Operation.EQUALS)
				return "next(var_" + annotationVariable + ") = var_" + aA.getAttr();
			else if (a.getOperation() == Operation.PLUS)
				return "next(var_" + annotationVariable + ") = var_" + annotationVariable + " + var_" + aA.getAttr();
			else if (a.getOperation() == Operation.MINUS)
				return "next(var_" + annotationVariable + ") = var_" + annotationVariable + " - var_" + aA.getAttr();
			else
				throw new RuntimeException("Unsupported annotation operation");
		} else if (a instanceof ExpressionAnnotation){
			ExpressionAnnotation eA = (ExpressionAnnotation) a;
			LambdaExpression expr = eA.getExpression();
			LambdaExpression subbed = expr;
			for (Attribute attr: expr.getRelatedAttributes()){
				if (!eA.getConstants().containsKey(attr)){
					// for attributes that aren't constants, just sub in with var_
					try {
						Attribute substitute = Attribute.createFromDatatype("var_"+attr.getName(), attr);
						subbed = subbed.substitute(attr, LambdaExpression.generateSimpleExpression(substitute));
					} catch (Attribute.AttributeConstructionException e) {
						throw new RuntimeException(e);
					}
				}
			}
			return "next(var_" + annotationVariable + ") = "+subbed.toString();
		}
		throw new RuntimeException("Unsupported annotation");
	}

	// assumes no loops
	private static Map<String, List<Map.Entry<TransitionI, MarkingI>>> buildReachabilityGraph(PlaceTransitionNet pn) {
		Map<String, List<Map.Entry<TransitionI, MarkingI>>> markings = new LinkedHashMap<>();
		recurser(pn, pn.getInitialMarking(), markings);
		return markings;
	}

	static void recurser(PlaceTransitionNet pn, MarkingI m, Map<String, List<Map.Entry<TransitionI, MarkingI>>> markings) {
		// check if already done this marking
		for (String existing: markings.keySet()) { // hashcode not properly implemented for MarkingI, so do like this
			if (id(m).equals(existing)) return;
		}

		List<Map.Entry<TransitionI, MarkingI>> next = new ArrayList<>();
		markings.put(id(m), next);

		for (TransitionI t: pn.getEnabledTransitions(m)){
			MarkingI nextM = pn.fire(t, m);
			next.add(Map.entry(t, nextM));
		}

		// once finished this marking, recurse
		for (Map.Entry<TransitionI,MarkingI> entry: next){
			recurser(pn, entry.getValue(), markings);
		}
	}
}
