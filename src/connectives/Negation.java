package connectives;

import concepts.ConceptExpression;
import formula.Formula;

public class Negation extends ConceptExpression {

	public Negation() {
		super();
	}
	
	public Negation(Formula formula) {
		super(formula);
	}

	@Override
	public String toString() {
		Formula formula = this.getSubFormulas().get(0);

		if (formula instanceof And || formula instanceof Or) {
			return "\u00AC(" + formula + ")";
		} else {
			return "\u00AC" + formula;
		}
	}

}
