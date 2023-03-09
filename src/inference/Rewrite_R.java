package inference;

import java.util.ArrayList;
import java.util.List;
import checkexistence.EChecker;
import concepts.BottomConcept;
import connectives.And;
import connectives.Forall;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import roles.AtomicRole;
import roles.InverseRole;

public class Rewrite_R {
	public List<Formula> Surfacing_R(List<Formula> pivot_list_normalised){
		List<Formula> output = new ArrayList<>();
		for(Formula formula : pivot_list_normalised) {
			output.add(Surfacing_R(formula));
		}
		return output;
	}
	public Formula Surfacing_R(Formula formula){
		
		if(!(formula instanceof Or) && !(formula instanceof And)) {
			List<Formula> orList = new ArrayList<Formula>();
			orList.add(formula);
			orList.add(new BottomConcept());
			formula = new Or(orList);
		}
		for(Formula f : formula.getSubFormulas()) {
			
			if(f instanceof Forall) {
				if(f.getSubFormulas().get(0) instanceof InverseRole) {
					List<Formula> orList = new ArrayList<>();
					Formula C;
					orList = formula.getSubFormulas();
					orList.remove(f);
					if(orList.size() > 1)
						C = new Or(orList);
					else 
						C = orList.get(0);
					orList.clear();
					orList.add(new Forall(new AtomicRole(f.getSubFormulas().get(0).getText()), C));
					orList.add(f.getSubFormulas().get(1));
					return new Or(orList);
				}
			}
		}
		return formula;
	}
	//判断r和S相等时，转换失败
	public List<Formula> Inverting_R(AtomicRole role, List<Formula> pivot_list_normalised){
		List<Formula> output = new ArrayList<>();
		EChecker ec = new EChecker();
		for(Formula formula : pivot_list_normalised) {
			if(!ec.hasRoleRestriction(formula)) {
				output.add(Inverting_R(role, formula));
			}else {
				output.add(formula);
			}
		}
		return output;
	}
	public Formula Inverting_R(AtomicRole role, Formula formula) {
		List<Formula> subFormulas = formula.getSubFormulas();
		if(subFormulas.contains(new InverseRole(role.toString()))
				|| subFormulas.contains(new Negation(new InverseRole(role.toString())))) {
			subFormulas.set(0, InvertingRole(subFormulas.get(0)));
			subFormulas.set(1, InvertingRole(subFormulas.get(1)));
				return new Or(subFormulas);
		}
		return formula;
	}
	public Formula InvertingRole(Formula formula) {
		if(formula instanceof Negation) {
			if(formula.getSubFormulas().get(0) instanceof AtomicRole) {
				AtomicRole atomicRole = (AtomicRole) formula.getSubFormulas().get(0);
				return new Negation(new InverseRole(atomicRole.toString()));	
			}
			else {
				InverseRole inverseRole = (InverseRole) formula.getSubFormulas().get(0);
				return new Negation(new AtomicRole(inverseRole.getText()));
			}
		}
		else if(formula instanceof AtomicRole) {
			AtomicRole atomicRole = (AtomicRole) formula;
			return new InverseRole(atomicRole.toString());
		}
		else if(formula instanceof InverseRole){
			InverseRole inverseRole = (InverseRole) formula;
			return new AtomicRole(inverseRole.getText());
		}
		return formula;
	}
}
