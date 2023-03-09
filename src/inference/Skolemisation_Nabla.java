package inference;

import java.util.ArrayList;
import java.util.List;

import checkfrequency.FChecker;
import concepts.AtomicConcept;
import connectives.Exists;
import formula.Formula;
import individual.Individual;
import connectives.*;
import roles.TopRole;

public class Skolemisation_Nabla {
	static int cnt = 1; 
public List<Formula> Skolemisation_nabla_Positive(AtomicConcept concept, List<Formula> pivot_list_normalised)
		throws CloneNotSupportedException{
	List<Formula> output = new ArrayList<>();
	for(Formula formula: pivot_list_normalised) {
		Formula newFormula = formula.clone();
		Formula oldFormula = new Formula();
		Surfacing_C surfacing_C = new Surfacing_C();
		while(!newFormula.equals(oldFormula)) {
			oldFormula = newFormula.clone();
			newFormula = Skolemisation_nabla_Positive(concept, newFormula);
			newFormula = surfacing_C.Surfacing_C_Positive(concept, newFormula);
		}
		output.add(newFormula);
	}
	return output;
}
public Formula Skolemisation_nabla_Positive(AtomicConcept concept, Formula formula) 
		throws CloneNotSupportedException {
	for(Formula f : formula.getSubFormulas()) {
		if(f instanceof Exists && f.getSubFormulas().get(0) instanceof TopRole) {
			FChecker fc = new FChecker();
			if(fc.positive(concept, f.getSubFormulas().get(1)) > 0) {
				List<Formula> C = new ArrayList<>();
				List<Formula> orList = new ArrayList<>(); 
				C = formula.clone().getSubFormulas();
				C.remove(f);
				if(C.size() > 1) {
					orList.add(new Forall(new TopRole(), new Or(C)));
				}
				else if(C.size() == 1){
					orList.add(new Forall(new TopRole(), C.get(0)));
				}
				orList.add(f.getSubFormulas().get(1));
				orList.add(new Negation(new Individual("na" + cnt++)));
				return Skolemisation_nabla_Positive(concept, new Or(orList));
			}
		}
	}
	return formula;
}
public List<Formula> Skolemisation_nabla_Negative(AtomicConcept concept, List<Formula> pivot_list_normalised)
		throws CloneNotSupportedException{
	List<Formula> output = new ArrayList<>();
	for(Formula formula: pivot_list_normalised) {
		Formula newFormula = formula.clone();
		Formula oldFormula = new Formula();
		Surfacing_C surfacing_C = new Surfacing_C();
		while(!newFormula.equals(oldFormula)) {
			oldFormula = newFormula.clone();
			newFormula = Skolemisation_nabla_Negative(concept, newFormula);
			newFormula = surfacing_C.Surfacing_C_Negative(concept, newFormula);
		}
		output.add(newFormula);
	}
	return output;
}
public Formula Skolemisation_nabla_Negative(AtomicConcept concept, Formula formula) 
		throws CloneNotSupportedException {
	for(Formula f : formula.getSubFormulas()) {
		if(f instanceof Exists && f.getSubFormulas().get(0) instanceof TopRole) {
			FChecker fc = new FChecker();
			if(fc.positive(concept, f.getSubFormulas().get(1)) > 0) {
				List<Formula> C = new ArrayList<>();
				List<Formula> orList = new ArrayList<>(); 
				C = formula.clone().getSubFormulas();
				C.remove(f);
				if(C.size() > 1) {
					orList.add(new Forall(new TopRole(), new Or(C)));
				}
				else if(C.size() == 1){
					orList.add(new Forall(new TopRole(), C.get(0)));
				}
				orList.add(f.getSubFormulas().get(1));
				orList.add(new Negation(new Individual("na" + cnt++)));
				return Skolemisation_nabla_Negative(concept, new Or(orList));
			}
		}
	}
	return formula;
}
}
