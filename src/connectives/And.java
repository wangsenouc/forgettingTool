package connectives;

import concepts.ConceptExpression;
import formula.Formula;
import individual.Individual;
import roles.AtomicRole;
import roles.InverseRole;
import roles.RoleExpression;

import java.util.List;

public class And extends Formula {

	public And() {
		super();
	}
	
	public And(List<Formula> list) {
		super(list.size());
		this.setSubFormulas(list);
	}

	@Override
	public String toString() {
		if (this.getSubFormulas().size() == 1) {
			return this.getSubFormulas().get(0).toString();
		}
		String str = "";
		for (int i = 0; i < this.getSubFormulas().size(); i++) {
			if (i == 0) {
				if (this.getSubFormulas().get(i) instanceof ConceptExpression
						|| this.getSubFormulas().get(i) instanceof RoleExpression
						|| this.getSubFormulas().get(i) instanceof Individual
						|| this.getSubFormulas().get(i) instanceof Negation
						|| this.getSubFormulas().get(i) instanceof Exists
						|| this.getSubFormulas().get(i) instanceof Forall
						) {
					str = str + this.getSubFormulas().get(i);
					continue;
				}
				str = str + "(" + this.getSubFormulas().get(i) + ")";
				continue;
			}
			if (this.getSubFormulas().get(i) instanceof ConceptExpression
					|| this.getSubFormulas().get(i) instanceof RoleExpression
					|| this.getSubFormulas().get(i) instanceof Individual
					|| this.getSubFormulas().get(i) instanceof Negation
					|| this.getSubFormulas().get(i) instanceof Exists
					|| this.getSubFormulas().get(i) instanceof Forall
					) {
				str = str + " \u2293 " + this.getSubFormulas().get(i);
				continue;
			}
			str = str + " \u2293 " + "(" + this.getSubFormulas().get(i) + ")";
		}
		if(this.getSubFormulas().size() > 1 && 
				(this.getSubFormulas().get(0) instanceof AtomicRole || this.getSubFormulas().get(0) instanceof InverseRole)){
			str = "(" + str + ")";
		}
		return str + "";
	}
}
