package inference;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import checkreducedform.RFChecker;
import concepts.AtomicConcept;
import connectives.*;
import formula.Formula;
import individual.Individual;
import simplification.Simplifier;
public class Skolemisation_C {
	static int nominalsCnt = 0;
public List<Formula> Skolemisation_C_Positive(AtomicConcept concept,
		List<Formula> pivot_list_normalised)throws CloneNotSupportedException {
	List<Formula> result = new ArrayList<>();
	Simplifier simp = new Simplifier();
	RFChecker rfc = new RFChecker();
	for(Formula formula1 : pivot_list_normalised) {
		Formula formula = formula1.clone();
		List<Formula> temp = Skolemisation_C_Positive(concept, formula);
		if(!rfc.isAReducedFormPositive(concept, temp)) {
			Surfacing_C surfacing_C = new Surfacing_C();
			temp = surfacing_C.Surfacing_C_Positive(concept, temp);
		}
		result.addAll(temp);
	}
	return simp.getCNF(result);
}
public List<Formula> Skolemisation_C_Positive(AtomicConcept concept, Formula formula) throws CloneNotSupportedException {
	RFChecker rfc = new RFChecker();
	List<Formula> result = new ArrayList<>();
	if(!rfc.isAReducedFormPositive(concept, Collections.singletonList(formula))) {
		List<Formula> subFormulas = formula.getSubFormulas();
	if(subFormulas.size() != 2) {
			
		}else if((subFormulas.get(0) instanceof Negation) && (subFormulas.get(1) instanceof Exists) && subFormulas.get(0).getSubFormulas().get(0) instanceof Individual) {
			List<Formula> temp = new ArrayList<>();
			temp.add(subFormulas.get(0));
			Formula role = subFormulas.get(1).getSubFormulas().get(0);
			temp.add(new Exists(role, new Individual("n" + nominalsCnt)));
			result.add(new Or(temp));
			temp.clear();
			temp.add(new Negation(new Individual("n" + nominalsCnt++)));
			temp.add(subFormulas.get(1).getSubFormulas().get(1));
			Simplifier simp = new Simplifier();
			result.addAll(Skolemisation_C_Positive(concept, simp.getCNF(simp.simplified_1(new Or(temp)))));
			return result;
		}else if(subFormulas.get(0) instanceof Exists && subFormulas.get(1) instanceof Negation && subFormulas.get(1).getSubFormulas().get(0) instanceof Individual) {
			List<Formula> temp = new ArrayList<>();
			temp.add(subFormulas.get(1));
			Formula role = subFormulas.get(0).getSubFormulas().get(0);
			temp.add(new Exists(role, new Individual("n" + nominalsCnt)));
			result.add(new Or(temp));
			temp.clear();
			temp.add(new Negation(new Individual("n" + nominalsCnt++)));
			temp.add(subFormulas.get(0).getSubFormulas().get(1));
			Simplifier simp = new Simplifier();
			result.addAll(Skolemisation_C_Positive(concept, simp.getCNF(simp.simplified_1(new Or(temp)))));
			return result;
		}
	}
	return Collections.singletonList(formula);
}
public List<Formula> Skolemisation_C_Negative(AtomicConcept concept, List<Formula> pivot_list_normalised) throws CloneNotSupportedException {
	
	List<Formula> result = new ArrayList<>();
	Simplifier simp = new Simplifier();
	RFChecker rfc = new RFChecker();
	for(Formula formula1 : pivot_list_normalised) {
		Formula formula = formula1.clone();
		List<Formula> temp = Skolemisation_C_Negative(concept, formula);
		if(!rfc.isAReducedFormNegative(concept, temp)) {
			Surfacing_C surfacing_C = new Surfacing_C();
			temp = surfacing_C.Surfacing_C_Negative(concept, temp);
		}
		result.addAll(temp);
	}
	return simp.getCNF(result);
}
public List<Formula> Skolemisation_C_Negative(AtomicConcept concept, Formula formula) throws CloneNotSupportedException {
	RFChecker rfc = new RFChecker();
	List<Formula> result = new ArrayList<>();
	if(!rfc.isAReducedFormNegative(concept, Collections.singletonList(formula))) {
		List<Formula> subFormulas = formula.getSubFormulas();
		if(subFormulas.size() != 2) {
			
		}else if((subFormulas.get(0) instanceof Negation) && (subFormulas.get(1) instanceof Exists) && subFormulas.get(0).getSubFormulas().get(0) instanceof Individual) {
			List<Formula> temp = new ArrayList<>();
			temp.add(subFormulas.get(0));
			Formula role = subFormulas.get(1).getSubFormulas().get(0);
			temp.add(new Exists(role, new Individual("n" + nominalsCnt)));
			result.add(new Or(temp));
			temp.clear();
			temp.add(new Negation(new Individual("n" + nominalsCnt++)));
			temp.add(subFormulas.get(1).getSubFormulas().get(1));
			Simplifier simp = new Simplifier();
			result.addAll(Skolemisation_C_Negative(concept, simp.getCNF( simp.simplified_1(new Or(temp)))));
			return result;
		}else if(subFormulas.get(0) instanceof Exists && subFormulas.get(1) instanceof Negation && subFormulas.get(1).getSubFormulas().get(0) instanceof Individual) {
			List<Formula> temp = new ArrayList<>();
			temp.add(subFormulas.get(1));
			Formula role = subFormulas.get(0).getSubFormulas().get(0);
			temp.add(new Exists(role, new Individual("n" + nominalsCnt)));
			result.add(new Or(temp));
			temp.clear();
			temp.add(new Negation(new Individual("n" + nominalsCnt++)));
			temp.add(subFormulas.get(0).getSubFormulas().get(1));
			Simplifier simp = new Simplifier();
			result.addAll(Skolemisation_C_Negative(concept, simp.getCNF( simp.simplified_1(new Or(temp)))));
			return result;
		}
	}
	return Collections.singletonList(formula);
}
}
