package inference;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import checkexistence.EChecker;
import concepts.AtomicConcept;
import concepts.BottomConcept;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import simplification.Simplifier;

public class SubstitutionWithDefiner {
	static int definerCnt = 1;
	public List<AtomicConcept> definer = new ArrayList<>();
	public List<Formula> Substitution(List<Formula> input) {
		return SubstitutionOfC(SubstitutionOfD(input));
	}
	public List<Formula> SubstitutionOfC(List<Formula> input){
		List<Formula> output = new ArrayList<>();
		for(Formula formula : input) {
			output.addAll(SubstitutionOfC(formula));
		}
		return output;
	}
	public List<Formula> SubstitutionOfC(Formula formula){
		List<Formula> output = new ArrayList<>();
		for(Formula f : formula.getSubFormulas()) {
			if(f instanceof Exists || f instanceof Forall) {
				List<Formula> orList = new ArrayList<>();
				EChecker ec = new EChecker();
				orList.addAll(formula.getSubFormulas());
				orList.remove(f);
				if(!ec.hasRoleRestriction(new Or(orList)))
					break;
				AtomicConcept atomicConcept = new AtomicConcept("D" + definerCnt++);
				definer.add(atomicConcept);
				orList.add(new Negation(atomicConcept));
				output.addAll(SubstitutionOfC(new Or(orList)));
				orList.clear();
				orList.add(atomicConcept);
				orList.add(f);
				output.add(new Or(orList));
				
				return output;
			}
		}
		return Collections.singletonList(formula);
	}
	public List<Formula> SubstitutionOfD(List<Formula> input){
		List<Formula> output = new ArrayList<>();
		for(Formula formula : input) {
			output.addAll(SubstitutionOfD(formula));
		}
		return output;
	}
	public List<Formula> SubstitutionOfD(Formula formula){
		List<Formula> output = new ArrayList<>();
		Simplifier simp = new Simplifier();
		if(!(formula instanceof Or) && !(formula instanceof And)) {
			List<Formula> orList = new ArrayList<Formula>();
			orList.add(formula);
			orList.add(new BottomConcept());
			formula = new Or(orList);
		}
		for(Formula f : formula.getSubFormulas()) {
			if(f instanceof Exists || f instanceof Forall) {
				EChecker ec = new EChecker();
				if(!ec.hasRoleRestriction(f.getSubFormulas().get(1)))
					break;
				AtomicConcept atomicConcept = new AtomicConcept("D" + definerCnt++);
				definer.add(atomicConcept);
				List<Formula> orList = new ArrayList<>();
				orList.add(new Negation(atomicConcept));
				orList.add(f.getSubFormulas().get(1));
				output.addAll(SubstitutionOfD(simp.getCNF(new Or(orList))));
				orList.clear();
				orList.addAll(formula.getSubFormulas());
				orList.remove(f);
				f.getSubFormulas().set(1, atomicConcept);
				orList.add(f);
				output.add(new Or(orList));			
				return output;
			}
		}
		return Collections.singletonList(formula);
	}
}
