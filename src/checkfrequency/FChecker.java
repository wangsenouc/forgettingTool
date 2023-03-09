package checkfrequency;

import java.util.List;
import concepts.AtomicConcept;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import connectives.Inclusion;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import roles.AtomicRole;
import roles.InverseRole;

public class FChecker {

	public FChecker() {

	}
	
	public int positiveExistsRestrict(AtomicConcept concept, List<Formula> formula_list) {

		int positive = 0;

		for (Formula formula : formula_list) {
			positive = positive + positiveExistsRestrict(concept, formula, 0);
		}

		return positive;
	}

	public int positiveExistsRestrict(AtomicConcept concept, Formula formula, int depth) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept) ? depth * (depth + 1) / 2 : 0;
		} else if (formula instanceof Negation) {
			return negativeExistsRestrict(concept, formula.getSubFormulas().get(0), depth);
		} else if (formula instanceof Exists) {
			return positiveExistsRestrict(concept, formula.getSubFormulas().get(1), depth + 1);
		}else if(formula instanceof Forall) {
			return positiveExistsRestrict(concept, formula.getSubFormulas().get(1), depth);
		}else if (formula instanceof Inclusion) {
			return negativeExistsRestrict(concept, formula.getSubFormulas().get(0), depth)
					+ positiveExistsRestrict(concept, formula.getSubFormulas().get(1), depth);
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				sum = sum + positiveExistsRestrict(concept, operand, depth);
			}
			return sum;
		}

		return 0;
	}

	public int negativeExistsRestrict(AtomicConcept concept, List<Formula> formula_list) {

		int negative = 0;

		for (Formula formula : formula_list) {
			negative = negative + negativeExistsRestrict(concept, formula, 0);
		}

		return negative;
	}

	public int negativeExistsRestrict(AtomicConcept concept, Formula formula, int depth) {

		if (formula instanceof Negation) {
			return positiveExistsRestrict(concept, formula.getSubFormulas().get(0),depth);
		} else if (formula instanceof Exists) {
			return negativeExistsRestrict(concept, formula.getSubFormulas().get(1), depth + 1);
		} else if(formula instanceof Forall) {
			return negativeExistsRestrict(concept, formula.getSubFormulas().get(1), depth);
		}else if (formula instanceof Inclusion) {
			return positiveExistsRestrict(concept, formula.getSubFormulas().get(0), depth)
					+ negativeExistsRestrict(concept, formula.getSubFormulas().get(1), depth);
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				sum = sum + negativeExistsRestrict(concept, operand, depth);
			}
			return sum;
		}

		return 0;
	}
	
	public int positiveRestrict(AtomicConcept concept, List<Formula> formula_list) {

		int positive = 0;

		for (Formula formula : formula_list) {
			positive = positive + positiveRestrict(concept, formula, 0);
		}

		return positive;
	}

	public int positiveRestrict(AtomicConcept concept, Formula formula, int depth) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept) ? depth * (depth + 1) / 2 : 0;
		} else if (formula instanceof Negation) {
			return negativeRestrict(concept, formula.getSubFormulas().get(0), depth);
		} else if (formula instanceof Exists) {
			return positiveRestrict(concept, formula.getSubFormulas().get(1), depth + 1);
		}else if(formula instanceof Forall) {
			return positiveRestrict(concept, formula.getSubFormulas().get(1), depth + 1);
		}else if (formula instanceof Inclusion) {
			return negativeRestrict(concept, formula.getSubFormulas().get(0), depth)
					+ positiveRestrict(concept, formula.getSubFormulas().get(1), depth);
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				sum = sum + positiveRestrict(concept, operand, depth);
			}
			return sum;
		}

		return 0;
	}

	public int negativeRestrict(AtomicConcept concept, List<Formula> formula_list) {

		int negative = 0;

		for (Formula formula : formula_list) {
			negative = negative + negativeRestrict(concept, formula, 0);
		}

		return negative;
	}

	public int negativeRestrict(AtomicConcept concept, Formula formula, int depth) {

		if (formula instanceof Negation) {
			return positiveRestrict(concept, formula.getSubFormulas().get(0),depth);
		} else if (formula instanceof Exists) {
			return negativeRestrict(concept, formula.getSubFormulas().get(1), depth + 1);
		} else if(formula instanceof Forall) {
			return negativeRestrict(concept, formula.getSubFormulas().get(1), depth + 1);
		}else if (formula instanceof Inclusion) {
			return positiveRestrict(concept, formula.getSubFormulas().get(0), depth)
					+ negativeRestrict(concept, formula.getSubFormulas().get(1), depth);
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				sum = sum + negativeRestrict(concept, operand, depth);
			}
			return sum;
		}

		return 0;
	}
	
	public int positive(AtomicConcept concept, List<Formula> formula_list) {

		int positive = 0;

		for (Formula formula : formula_list) {
			positive = positive + positive(concept, formula);
		}

		return positive;
	}

	public int positive(AtomicConcept concept, Formula formula) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept) ? 1 : 0;
		} else if (formula instanceof Negation) {
			return negative(concept, formula.getSubFormulas().get(0));
		} else if (formula instanceof Exists || formula instanceof Forall) {
			return positive(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return negative(concept, formula.getSubFormulas().get(0))
					+ positive(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				sum = sum + positive(concept, operand);
			}
			return sum;
		}

		return 0;
	}

	public int negative(AtomicConcept concept, List<Formula> formula_list) {

		int negative = 0;

		for (Formula formula : formula_list) {
			negative = negative + negative(concept, formula);
		}

		return negative;
	}

	public int negative(AtomicConcept concept, Formula formula) {

		if (formula instanceof Negation) {
			return positive(concept, formula.getSubFormulas().get(0));
		} else if (formula instanceof Exists || formula instanceof Forall) {
			return negative(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return positive(concept, formula.getSubFormulas().get(0))
					+ negative(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				sum = sum + negative(concept, operand);
			}
			return sum;
		}

		return 0;
	}
	
	public int positive(AtomicRole role, List<Formula> formula_list) {
		
		int positive = 0;
		
		for (Formula formula : formula_list) {
			positive = positive + positive(role, formula);
		}
		
		return positive;		
	}
		
	public int positive(AtomicRole role, Formula formula) {

		if (formula instanceof AtomicRole) {
			return formula.equals(role) ? 1 : 0;
		}else if(formula instanceof InverseRole) {
			return formula.equals(new InverseRole(role.toString())) ? 1 : 0;
		}else if (formula instanceof Negation) {
			return negative(role, formula.getSubFormulas().get(0));
		} else if (formula instanceof Exists) {
			return positive(role, formula.getSubFormulas().get(0)) + positive(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof Forall) {
			return negative(role, formula.getSubFormulas().get(0)) + positive(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return negative(role, formula.getSubFormulas().get(0)) + positive(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				sum = sum + positive(role, operand);
			}
			return sum;
		}

		return 0;
	}
	
	public int negative(AtomicRole role, List<Formula> formula_list) {

		int negative = 0;

		for (Formula formula : formula_list) {
			negative = negative + negative(role, formula);
		}

		return negative;
	}
	
	public int negative(AtomicRole role, Formula formula) {

		if (formula instanceof Negation) {
			return positive(role, formula.getSubFormulas().get(0));
		} else if (formula instanceof Exists) {
			return negative(role, formula.getSubFormulas().get(0)) + negative(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof Forall) {
			return positive(role, formula.getSubFormulas().get(0)) + negative(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return positive(role, formula.getSubFormulas().get(0))
					+ negative(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof And || formula instanceof Or) {
			int sum = 0;
			List<Formula> operand_list = formula.getSubFormulas(); 
			for (Formula operand : operand_list) {
				sum = sum + negative(role, operand);
			}
			return sum;
		}

		return 0;
	}
	
}
