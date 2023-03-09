package checkreducedform;

import java.util.List;
import checkfrequency.FChecker;
import concepts.AtomicConcept;
import connectives.Exists;
import connectives.Forall;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import roles.AtomicRole;
import roles.InverseRole;

public class RFChecker {

	public RFChecker() {

	}
	//在normal form的基础上判断是否为r-reduced form
	public boolean isAReducedForm(AtomicRole role, List<Formula> formula_list) {
		for(Formula formula : formula_list) {
			if(!isAReducedForm(role, formula))
				return false;
		}
		return true;
	}
	public boolean isAReducedForm(AtomicRole role, Formula formula) {
		for(Formula f : formula.getSubFormulas()) {
			if(f instanceof Forall || f instanceof Exists) {
				if(f.getSubFormulas().get(0) instanceof InverseRole 
						&& f.getSubFormulas().get(0).equals(new InverseRole(role.toString()))) {
					return false;
				}
			}else if(f instanceof InverseRole && f.equals(new InverseRole(role.toString()))) {
				return false;
			}
		}
		return true;
	}
	public boolean isAReducedFormPositive(AtomicConcept concept, List<Formula> formula_list) {

		FChecker fc = new FChecker();

		for (Formula formula : formula_list) {
			if (fc.positive(concept, formula) == 0) {

			} else if (formula.equals(concept) || (formula instanceof Or
					&& fc.positive(concept, formula) == 1
					&& fc.negative(concept, formula) == 0
					&& formula.getSubFormulas().contains(concept))) {

			} else {
				return false;
			}
		}

		return true;
	}

	public boolean isAReducedFormNegative(AtomicConcept concept, List<Formula> formula_list) {

		FChecker fc = new FChecker();

		for (Formula formula : formula_list) {
			if (fc.negative(concept, formula) == 0) {

			} else if (formula.equals(new Negation(concept)) || (formula instanceof Or
				 && fc.negative(concept, formula) == 1 
				 && fc.positive(concept, formula) == 0
				 && formula.getSubFormulas().contains(new Negation(concept)))) {

			} else {
				return false;
			}
		}

		return true;
	}

}
