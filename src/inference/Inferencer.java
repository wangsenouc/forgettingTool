package inference;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.apache.commons.collections.CollectionUtils; 
import checkexistence.EChecker;
import checkfrequency.FChecker;
import concepts.AtomicConcept;
import concepts.BottomConcept;
import concepts.TopConcept;
import roles.AtomicRole;
import roles.BottomRole;
import roles.InverseRole;
import roles.TopRole;
import simplification.Simplifier;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import individual.Individual;

public class Inferencer {
	
	public Inferencer() {

	}
	
	public List<Formula> Ackermann_R(AtomicRole role, List<Formula> formula_list)
			throws CloneNotSupportedException {
		
		List<Formula> output_list = new ArrayList<>();
		List<Formula> positive_RBox_premises = new ArrayList<>();
		List<Formula> negative_RBox_premises = new ArrayList<>();
		List<Formula> positive_TBox_premises = new ArrayList<>();
		List<Formula> negative_TBox_premises = new ArrayList<>();

		EChecker ec = new EChecker();
		FChecker fc = new FChecker();

		for (Formula formula : formula_list) {
			if (fc.positive(role, formula) + fc.negative(role, formula) > 1) {//role出现了不止一次，遗忘失败
				return formula_list;
						
			} else if (!ec.isPresent(role, formula)) {//formula中没有role
				output_list.add(formula);

			} else if (formula.equals(role)) {//有这种可能吗
				positive_RBox_premises.add(formula);

			} else if (formula.equals(new Negation(role))) {
				negative_RBox_premises.add(formula);

			} else if (formula instanceof Exists && formula.getSubFormulas().get(0).equals(role)) {
				positive_TBox_premises.add(formula);

			} else if (formula instanceof Forall && formula.getSubFormulas().get(0).equals(role)) {
				negative_TBox_premises.add(formula);

			} else if (formula instanceof Or) {
				List<Formula> disjunct_list = formula.getSubFormulas();

				if (disjunct_list.contains(role)) {
					positive_RBox_premises.add(formula);

				} else if (disjunct_list.contains(new Negation(role))) {
					negative_RBox_premises.add(formula);

				} else {
					for (Formula disjunct : disjunct_list) {
						if (disjunct instanceof Exists && disjunct.getSubFormulas().get(0).equals(role)) {
							positive_TBox_premises.add(formula);
							break;
						} else if (disjunct instanceof Forall && disjunct.getSubFormulas().get(0).equals(role)) {
							negative_TBox_premises.add(formula);
							break;
						}
					}
				}
			}
		}
		for(Formula formula : positive_TBox_premises) {
			Formula roleConjunction = new TopRole();
			Formula C = new Formula();
			C = formula.clone();
			Formula D = new Formula();
			Formula exist = new Formula();
			for(Formula f : formula.getSubFormulas()) {
				if(f instanceof Exists) {
					exist = f.clone();
					D = exist.getSubFormulas().get(1).clone();
					C.getSubFormulas().remove(f);
					if(C.getSubFormulas().size() == 1) {
						C = C.getSubFormulas().get(0);
					}else if(C.getSubFormulas().size() == 0) {
						C = new BottomConcept();
					}
				}
			}
			if(!negative_RBox_premises.isEmpty()) {
				List<Formula> roleList = new ArrayList<>();
				for(Formula roleExp : negative_RBox_premises) {
					if(roleExp.getSubFormulas().get(0) instanceof Negation) {
						roleList.add(roleExp.getSubFormulas().get(1));
					}else {
						roleList.add(roleExp.getSubFormulas().get(0));
					}
				}
				roleConjunction = new And(roleList);
			}
			
			output_list.add(AckermannReplace(role, formula, roleConjunction));
			if(!negative_TBox_premises.isEmpty()) {
				
				exist = AckermannReplace(role, exist, roleConjunction);
				List<Formula> EList = new ArrayList<>();
				List<Formula> FList = new ArrayList<>();
				for(Formula ntp : negative_TBox_premises) {
					for(Formula f : ntp.getSubFormulas()) {
						if(f instanceof Forall) {
							FList.add(f.getSubFormulas().get(1));
							List<Formula> tempEList = ntp.clone().getSubFormulas();
							tempEList.remove(f);
							if(tempEList.size() == 1) {
								EList.add(tempEList.get(0));
							}else if(tempEList.size() == 0) {
								EList.add(new BottomConcept());
							}else {
								EList.add(new Or(tempEList));
							}
							break;
						}
					}
				}
				
				int n = EList.size();
				List<Formula> E = new ArrayList<Formula>();
				List<Formula> F = new ArrayList<Formula>();
				E.add(C);
				F.add(D);
				Block(E, F, 0, output_list, n, EList, FList, roleConjunction);
			}
		}
		
		for(Formula formula: positive_RBox_premises ) {
			Formula role_sk = formula.clone();
			role_sk.getSubFormulas().remove(role);
			role_sk = role_sk.getSubFormulas().get(0).getSubFormulas().get(0);
			for(Formula ntp : negative_TBox_premises) {
				Formula tempFormula = ntp.clone();
				output_list.add(AckermannReplace(role, tempFormula, role_sk));
			}
			for(Formula nrp : negative_RBox_premises) {
				List<Formula> orList = new ArrayList<>();
				orList.addAll(formula.clone().getSubFormulas());
				orList.addAll(nrp.clone().getSubFormulas());
				orList.remove(role);
				orList.remove(new Negation(role));
				output_list.add(new Or(orList));
			}
		}
		
		return output_list;
	}
	
	public void Block(List<Formula> E, List<Formula> F, int start, List<Formula> output_list,  int n, 
			List<Formula> EList, List<Formula> FList, Formula roleExp)  {
		
		Simplifier simp = new Simplifier();
		
		for(int i = start; i < n; i++) {
			List<Formula> newE = new ArrayList<Formula>();
			List<Formula> newF = new ArrayList<Formula>();
			CollectionUtils.addAll(newE, new Object[E.size()]);
			Collections.copy(newE, E);
			CollectionUtils.addAll(newF, new Object[F.size()]);
			Collections.copy(newF,  F);
			newE.add(EList.get(i));
			newF.add(FList.get(i));
			Formula orNewE = simp.simplified_1( new Or(newE));
			Formula andNewF = simp.simplified_1( new And(newF));
			Exists exist  = new Exists(roleExp, new And(newF));
			List<Formula> orList = new ArrayList<Formula>(newE);
			orList.add(exist);
			output_list.add(new Or(orList));
			
			if(simp.ObviousSimpOr(orNewE) instanceof TopConcept
					|| simp.ObviousSimpAnd(andNewF) instanceof BottomConcept) {
				continue;
			}
			Block(newE, newF, i + 1, output_list, n, EList, FList, roleExp);
			
		}
	}
	
	public List<Formula> AckermannPositive(AtomicConcept concept, List<Formula> input_list) throws CloneNotSupportedException {

		List<Formula> output_list = new ArrayList<>();
		List<Formula> toBeReplaced_list = new ArrayList<>();
		List<Formula> toReplace_list = new ArrayList<>();

		FChecker cf = new FChecker();
		//input_list中存放的是pivot-reduced form
		for (Formula formula : input_list) {
			if (cf.positive(concept, formula) == 0) {//this formula is negative w.r.t. concept
				toBeReplaced_list.add(formula);

			} else {
				toReplace_list.add(formula);
			}
		}

		Formula definition = null;
		List<Formula> disjunct_list = new ArrayList<>();

		for (Formula toReplace : toReplace_list) {
			if (toReplace.equals(concept)) {
				definition = TopConcept.getInstance();
				break;
				
			} else {
				List<Formula> other_list = new ArrayList<>(toReplace.getSubFormulas());
				other_list.remove(concept);
				if(other_list.size() ==0) {
					
				}else if (other_list.size() == 1) {
					disjunct_list.add(new Negation(other_list.get(0)));
					continue;
				} else {
					disjunct_list.add(new Negation(new Or(other_list)));
					continue;
				}
			}
		}

		if (definition != TopConcept.getInstance()) {
			if (disjunct_list.size() == 1) {
				definition = disjunct_list.get(0);
			} else {
				definition = new Or(disjunct_list);
			}
		}

		for (Formula toBeReplaced : toBeReplaced_list) {
			output_list.add(AckermannReplace(concept, toBeReplaced, definition));
		}

		return output_list;
	}
	
	public List<Formula> AckermannNegative(AtomicConcept concept, List<Formula> input_list)
			throws CloneNotSupportedException {
		
		List<Formula> output_list = new ArrayList<>();
		List<Formula> toBeReplaced_list = new ArrayList<>();
		List<Formula> toReplace_list = new ArrayList<>();

		FChecker cf = new FChecker();

		for (Formula formula : input_list) {
			if (cf.negative(concept, formula) == 0) {
				toBeReplaced_list.add(formula);

			} else {
				toReplace_list.add(formula);
			}
		}

		Formula definition = null;
		List<Formula> disjunct_list = new ArrayList<>();

		for (Formula toReplace : toReplace_list) {
			if (toReplace.equals(new Negation(concept))) {//考虑只有negative pivot的情况
				definition = BottomConcept.getInstance();
				break;
				
			} else {
				List<Formula> other_list = new ArrayList<>(toReplace.getSubFormulas());
				other_list.remove(new Negation(concept));
				if (other_list.size() == 1) {
					disjunct_list.add(other_list.get(0));
					continue;
				} else {
					disjunct_list.add(new Or(other_list));
					continue;
				}
			}
		}

		if (definition != BottomConcept.getInstance()) {
			if (disjunct_list.size() == 1) {
				definition = disjunct_list.get(0);
			} else {
				definition = new And(disjunct_list);
			}
		}

		for (Formula toBeReplaced : toBeReplaced_list) {
			output_list.add(AckermannReplace(concept, toBeReplaced, definition));
		}

		return output_list;
	}

	public List<Formula> PurifyPositive(AtomicRole role, List<Formula> input_list)
			throws CloneNotSupportedException {
		FChecker cf = new FChecker();

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			if (cf.positive(role, formula) == 0) {
				output_list.add(formula);
			} else {
				output_list.add(PurifyPositive(role, formula));
			}
		}

		return output_list;
	}

	public List<Formula> PurifyPositive(AtomicConcept concept, List<Formula> input_list)
			throws CloneNotSupportedException {

		FChecker cf = new FChecker();

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			if (cf.positive(concept, formula) == 0) {//如果concept正出现的频率为0，则说明concept已经被遗忘掉了，因为这是在PurifyPositive中
				output_list.add(formula);
			} else {
				output_list.add(PurifyPositive(concept, formula));
			}
		}

		return output_list;
	}

	public List<Formula> PurifyNegative(AtomicRole role, List<Formula> input_list)
			throws CloneNotSupportedException {

		FChecker cf = new FChecker();

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			if (cf.negative(role, formula) == 0) {
				output_list.add(formula);
			} else {
				output_list.add(PurifyNegative(role, formula));
			}
		}

		return output_list;
	}

	public List<Formula> PurifyNegative(AtomicConcept concept, List<Formula> inputList)
			throws CloneNotSupportedException {

		FChecker cf = new FChecker();

		List<Formula> outputList = new ArrayList<>();

		for (Formula formula : inputList) {
			if (cf.negative(concept, formula) == 0) {
				outputList.add(formula);
			} else {
				outputList.add(PurifyNegative(concept, formula));
			}
		}

		return outputList;
	}

	public Formula AckermannReplace(AtomicRole role, Formula toBeReplaced, Formula definition) {

		if (toBeReplaced instanceof AtomicConcept) {
			return new AtomicConcept(toBeReplaced.getText());

		} else if (toBeReplaced instanceof AtomicRole) {
			return toBeReplaced.equals(role) ? definition : new AtomicRole(toBeReplaced.getText());

		} else if (toBeReplaced instanceof Individual) {
			return new Individual(toBeReplaced.getText());
		
		} else if (toBeReplaced instanceof Negation) {
			return new Negation(AckermannReplace(role, toBeReplaced.getSubFormulas().get(0), definition));

		} else if (toBeReplaced instanceof Exists) {
			return new Exists(AckermannReplace(role, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(role, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof Forall) {
			return new Forall(AckermannReplace(role, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(role, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof And) {
			List<Formula> conjunct_list = toBeReplaced.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(AckermannReplace(role, conjunct, definition));
			}
			return new And(new_conjunct_list);

		} else if (toBeReplaced instanceof Or) {
			List<Formula> disjunct_list = toBeReplaced.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(AckermannReplace(role, disjunct, definition));
			}
			return new Or(new_disjunct_list);

		}

		return toBeReplaced;
	}
	/**
	 * 用definition替换ToBeReplaced中的concept
	 * @param concept
	 * @param toBeReplaced
	 * @param definition
	 * @return
	 */
	public Formula AckermannReplace(AtomicConcept concept, Formula toBeReplaced, Formula definition) {

		if (toBeReplaced instanceof AtomicConcept) {
			return toBeReplaced.equals(concept) ? definition : new AtomicConcept(toBeReplaced.getText());
			
		} else if (toBeReplaced instanceof AtomicRole) {
			return new AtomicRole(toBeReplaced.getText());

		} else if (toBeReplaced instanceof Individual) {
			return new Individual(toBeReplaced.getText());
		
		} else if (toBeReplaced instanceof Negation) {
			return new Negation(AckermannReplace(concept, toBeReplaced.getSubFormulas().get(0), definition));
			
		} else if (toBeReplaced instanceof Exists) {
			return new Exists(AckermannReplace(concept, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(concept, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof Forall) {
			return new Forall(AckermannReplace(concept, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(concept, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof And) {
			List<Formula> conjunct_list = toBeReplaced.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(AckermannReplace(concept, conjunct, definition));
			}
			return new And(new_conjunct_list);
			
		} else if (toBeReplaced instanceof Or) {
			List<Formula> disjunct_list = toBeReplaced.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(AckermannReplace(concept, disjunct, definition));
			}
			return new Or(new_disjunct_list);
			
		}
		
		return toBeReplaced;
	}
	
	public Formula PurifyPositive(AtomicRole role, Formula formula) {
		
		if (formula instanceof AtomicConcept) {
			return new AtomicConcept(formula.getText());
		
		} else if (formula instanceof AtomicRole) {
			return formula.equals(role) ? TopRole.getInstance() : new AtomicRole(formula.getText());
		
		} else if(formula instanceof InverseRole) {
			return formula.equals(new AtomicRole(formula.getText())) ? TopRole.getInstance() : new InverseRole(formula.getText());
		
		}else if (formula instanceof Individual) {
			return new Individual(formula.getText());
		
		} else if (formula instanceof Negation) {
			return new Negation(PurifyPositive(role, formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Exists) {
			return new Exists(PurifyPositive(role, formula.getSubFormulas().get(0)),
					PurifyPositive(role, formula.getSubFormulas().get(1)));
		
		} else if (formula instanceof Forall) {
			return new Forall(PurifyPositive(role, formula.getSubFormulas().get(0)),
					PurifyPositive(role, formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(PurifyPositive(role, conjunct));
			}
			return new And(new_conjunct_list);
			
		} else if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(PurifyPositive(role, disjunct));
			}
			return new Or(new_disjunct_list);
		}

		return formula;
	}
	
	public Formula PurifyNegative(AtomicRole role, Formula formula) {
		
		if (formula instanceof AtomicConcept) {
			return new AtomicConcept(formula.getText());
		
		} else if (formula instanceof AtomicRole) {
			return formula.equals(role) ? BottomRole.getInstance() : new AtomicRole(formula.getText());
		
		}else if(formula instanceof InverseRole) {
			return formula.equals(new AtomicRole(formula.getText())) ? TopRole.getInstance() : new InverseRole(formula.getText());
		
		}else if (formula instanceof Individual) {
			return new Individual(formula.getText());
		
		} else if (formula instanceof Negation) {
			return new Negation(PurifyNegative(role, formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Exists) {
			return new Exists(PurifyNegative(role, formula.getSubFormulas().get(0)),
					PurifyNegative(role, formula.getSubFormulas().get(1)));
		
		} else if (formula instanceof Forall) {
			return new Forall(PurifyNegative(role, formula.getSubFormulas().get(0)),
					PurifyNegative(role, formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(PurifyNegative(role, conjunct));
			}
			return new And(new_conjunct_list);
			
		} else if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(PurifyNegative(role, disjunct));
			}
			return new Or(new_disjunct_list);
		}

		return formula;
	}
	
	public Formula PurifyPositive(AtomicConcept concept, Formula formula) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept) ? TopConcept.getInstance() : new AtomicConcept(formula.getText());
			
		} else if (formula instanceof AtomicRole) {
			return new AtomicRole(formula.getText());

		} else if (formula instanceof Individual) {
			return new Individual(formula.getText());
		
		} else if (formula instanceof Negation) {
			return new Negation(PurifyPositive(concept, formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Exists) {
			return new Exists(PurifyPositive(concept, formula.getSubFormulas().get(0)),
					PurifyPositive(concept, formula.getSubFormulas().get(1)));
		
		} else if (formula instanceof Forall) {//猜测是全称变量
			return new Forall(PurifyPositive(concept, formula.getSubFormulas().get(0)),
					PurifyPositive(concept, formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(PurifyPositive(concept, conjunct));
			}
			return new And(new_conjunct_list);
			
		} else if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(PurifyPositive(concept, disjunct));
			}
			return new Or(new_disjunct_list);
		}

		return formula;
	}
			
	public Formula PurifyNegative(AtomicConcept concept, Formula formula) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept) ? BottomConcept.getInstance() : new AtomicConcept(formula.getText());

		} else if (formula instanceof AtomicRole) {
			return new AtomicRole(formula.getText());

		} else if (formula instanceof Individual) {
			return new Individual(formula.getText());
		
		} else if (formula instanceof Negation) {
			return new Negation(PurifyNegative(concept, formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Exists) {
			return new Exists(PurifyNegative(concept, formula.getSubFormulas().get(0)),
					PurifyNegative(concept, formula.getSubFormulas().get(1)));

		} else if (formula instanceof Forall) {
			return new Forall(PurifyNegative(concept, formula.getSubFormulas().get(0)),
					PurifyNegative(concept, formula.getSubFormulas().get(1)));

		} else if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(PurifyNegative(concept, conjunct));
			}
			return new And(new_conjunct_list);

		} else if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(PurifyNegative(concept, disjunct));
			}
			return new Or(new_disjunct_list);
		}

		return formula;
	}
	public List<Formula> AckermannCPositive(AtomicConcept concept, List<Formula> pivot_list_reduced)throws CloneNotSupportedException{
		List<Formula> output_list = new ArrayList<>();
		List<Formula> toBeReplaced_list = new ArrayList<>();
		List<Formula> toReplace_list = new ArrayList<>();

		FChecker cf = new FChecker();
		//input_list中存放的是pivot-reduced form
		for (Formula formula : pivot_list_reduced) {
			if (cf.positive(concept, formula) == 0) {//this formula is negative w.r.t. concept
				toBeReplaced_list.add(formula.clone());

			} else {
				toReplace_list.add(formula);
				
			}
		}

		Formula definition = null;
		List<Formula> disjunct_list = new ArrayList<>();

		for (Formula toReplace : toReplace_list) {
			if (toReplace.equals(concept)) {
				definition = TopConcept.getInstance();
				break;
				
			} else {
				List<Formula> other_list = new ArrayList<>(toReplace.getSubFormulas());
				other_list.remove(concept);
				if (other_list.size() == 1) {
					disjunct_list.add(other_list.get(0));
					continue;
				} else {
					disjunct_list.add(new Or(other_list));
					continue;
				}
			}
		}

		if (definition != TopConcept.getInstance()) {
			if (disjunct_list.size() == 1) {
				definition = new Negation(disjunct_list.get(0));
			} else {
				definition = new Negation(new And(disjunct_list));
			}
		}

		for (Formula toBeReplaced : toBeReplaced_list) {
			output_list.add(AckermannReplace(concept, toBeReplaced, definition));
		}
		
		return output_list;
	}
public List<Formula> AckermannCNegative(AtomicConcept concept, List<Formula> pivot_list_reduced){
	List<Formula> output_list = new ArrayList<>();
	List<Formula> toBeReplaced_list = new ArrayList<>();
	List<Formula> toReplace_list = new ArrayList<>();

	FChecker cf = new FChecker();

	for (Formula formula : pivot_list_reduced) {
		if (cf.negative(concept, formula) == 0) {
			toBeReplaced_list.add(formula);

		} else{
			toReplace_list.add(formula);
		}
	}

	Formula definition = null;
	List<Formula> disjunct_list = new ArrayList<>();

	for (Formula toReplace : toReplace_list) {
		if (toReplace.equals(new Negation(concept))) {//考虑只有negative pivot的情况
			definition = BottomConcept.getInstance();
			break;
			
		} else {
			List<Formula> other_list = new ArrayList<>(toReplace.getSubFormulas());
			other_list.remove(new Negation(concept));
			if (other_list.size() == 1) {
				disjunct_list.add(other_list.get(0));
				continue;
			} else {
				disjunct_list.add(new Or(other_list));
				continue;
			}
		}
	}

	if (definition != BottomConcept.getInstance()) {
		if (disjunct_list.size() == 1) {
			definition = disjunct_list.get(0);
		} else {
			definition = new And(disjunct_list);
		}
	}

	for (Formula toBeReplaced : toBeReplaced_list) {
		output_list.add(AckermannReplace(concept, toBeReplaced, definition));
	}

	return output_list;
}


	
}
