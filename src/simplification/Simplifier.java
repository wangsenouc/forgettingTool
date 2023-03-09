package simplification;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import com.google.common.collect.Lists;
import checkexistence.EChecker;
import concepts.BottomConcept;
import concepts.TopConcept;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import connectives.Inclusion;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import roles.AtomicRole;
import roles.BottomRole;
import roles.InverseRole;
import roles.RoleExpression;
import roles.TopRole;

public class Simplifier {

	public Simplifier() {

	}

	public List<Formula> roleSimplification(List<Formula> inputList) {
		EChecker ec = new EChecker();
		List<Formula> outputList = new ArrayList<>();

		for (Formula formula : inputList) {
			if (ec.hasRole(formula) && !ec.hasRoleRestriction(formula)) {
				if (formula.getSubFormulas().get(0) instanceof TopRole
						|| formula.getSubFormulas().get(1) instanceof TopRole) {
					continue;
				}
			}
			formula = simplified_1(formula);
			formula = ObviousSimpAnd(formula);
			formula = ObviousSimpOr(formula);
			if (!(formula instanceof TopConcept)) {
				outputList.add(formula);
			}
		}
		return outputList;
	}

	public List<Formula> getCNFandSimplify(List<Formula> inputList) throws CloneNotSupportedException {

		inputList = getSimplifiedForm1(inputList);
		inputList = getCNF(inputList);
		inputList = getSimplifiedForm2(inputList);
		boolean[] flag = new boolean[1];
		inputList = InverseSimp(inputList, flag);
		if (flag[0]) {
			inputList = getSimplifiedForm2(inputList);
		}
		return inputList;
	}

	public List<Formula> getSimplifiedForm2(List<Formula> input_list) throws CloneNotSupportedException {
		List<Formula> output_list = new ArrayList<>();

		for (Formula unsimplified : input_list) {
			Formula simplified = getSimplifiedForm2(unsimplified);
			if (!(simplified instanceof TopConcept))
				output_list.add(simplified);
		}
		return output_list;
	}

	public Formula getSimplifiedForm2(Formula formula) throws CloneNotSupportedException {
		Formula tempFormula;
		while (true) {
			tempFormula = simplifiedForm2(formula);
			if (formula.toString().equals(tempFormula.toString())) {
				break;
			}
			formula = tempFormula;
		}
		return formula;
	}

	public Formula simplifiedForm2(final Formula input) throws CloneNotSupportedException {

		Formula formula = input.clone();
		formula = AbsorptionSimplification2(formula);
		formula = DistributivitySimp(formula);
		formula = surfacingSimplification(formula);
		formula = InteractionSimp2(formula);
		formula = ObviousSimpOr(formula);
		return formula;
	}

	public List<Formula> getSimplifiedForm1(List<Formula> input_list) throws CloneNotSupportedException {
		List<Formula> output_list = new ArrayList<>();
		for (Formula unsimplified : input_list) {
			Formula simplified = getSimplifiedForm1(unsimplified);
			output_list.add(simplified);
		}
		return output_list;
	}

	public Formula getSimplifiedForm1(Formula formula) throws CloneNotSupportedException {
		// 当化简之后和化简之前的结果相同时，则停止化简操作
		Formula tempFormula;
		while (true) {
			tempFormula = simplifiedForm1(formula);
			if (formula.toString().equals(tempFormula.toString())) {
				break;
			}
			formula = tempFormula;
		}
		return formula;
	}

	public Formula simplifiedForm1(final Formula input) throws CloneNotSupportedException {
		Formula formula = input.clone();
		formula = getNNF(formula);// 得到否定范式
		formula = simplified_1(formula);
		formula = ObviousSimpAnd(formula);
		formula = AbsorptionSimplification1(formula);
		formula = additionalSimp(formula);
		formula = InteractionSimp1(formula);

		return formula;

	}

	// 反向分配率化简
	public List<Formula> InverseSimp(List<Formula> inputList, boolean[] flag) throws CloneNotSupportedException {
		List<Formula> outputList = new ArrayList<>();
		for (Formula formula : inputList) {
			Formula f = new Formula();
			f = InverseSimp(formula);
			if (!f.toString().equals(formula.toString())) {
				outputList.addAll(getCNF(f));
				flag[0] = true;
			} else {
				outputList.add(f);
			}
		}
		return outputList;
	}

	public Formula InverseSimp(final Formula input) throws CloneNotSupportedException {
		Formula formula = input.clone();
		if (formula.getSubFormulas().size() > 1) {
			for (int i = 0; i < formula.getSubFormulas().size(); i++) {
				formula.getSubFormulas().set(i, InverseSimp(formula.getSubFormulas().get(i)));
			}
		}
		if (formula instanceof Forall) {

			if (formula.getSubFormulas().get(1) instanceof And) {// 此处的化简疑似反向操作
				List<Formula> filler_conjunct_list = formula.getSubFormulas().get(1).getSubFormulas();
				List<Formula> new_conjunct_list = new ArrayList<>();
				for (Formula filler_conjunct : filler_conjunct_list) {
					new_conjunct_list.add(new Forall(formula.getSubFormulas().get(0), simplified_1(filler_conjunct)));
				}
				return new And(new_conjunct_list);
			}
		}
		return formula;
	}

	/*
	 * 主要解决AndInAnd和OrInOr的问题
	 */
	public Formula simplified_1(Formula formula) {

		if (formula instanceof Negation) {
			formula.getSubFormulas().set(0, simplified_1(formula.getSubFormulas().get(0)));
			return formula;

		} else if (formula instanceof Exists) {
			if (formula.getSubFormulas().get(1) == BottomConcept.getInstance()) {
				return BottomConcept.getInstance();

			} else {
				formula.getSubFormulas().set(1, simplified_1(formula.getSubFormulas().get(1)));
				return formula;
			}

		} else if (formula instanceof Forall) {
			if (formula.getSubFormulas().get(1) == TopConcept.getInstance()) {
				return TopConcept.getInstance();
			} else {
				formula.getSubFormulas().set(1, simplified_1(formula.getSubFormulas().get(1)));
				return formula;
			}

		} else if (formula instanceof And) {

			EChecker ec = new EChecker();

			if (formula.getSubFormulas().size() == 1) {
				return simplified_1(formula.getSubFormulas().get(0));

			} else if (ec.isAndInAnd(formula)) {
				List<Formula> conjunct_list = formula.getSubFormulas();
				List<Formula> new_conjunct_list = new ArrayList<>();

				for (Formula conjunct : conjunct_list) {
					if (conjunct instanceof And) {
						new_conjunct_list.addAll(conjunct.getSubFormulas());
					} else {
						new_conjunct_list.add(conjunct);
					}
				}
				formula.getSubFormulas().clear();
				formula.getSubFormulas().addAll(new_conjunct_list);
				return simplified_1(formula);

			} else {
				for (int i = 0; i < formula.getSubFormulas().size(); i++) {
					formula.getSubFormulas().set(i, simplified_1(formula.getSubFormulas().get(i)));
				}
				return formula;
			}

		} else if (formula instanceof Or) {

			EChecker ec = new EChecker();

			if (formula.getSubFormulas().size() == 1) {
				return simplified_1(formula.getSubFormulas().get(0));

			} else if (ec.isOrInOr(formula)) {
				List<Formula> disjunct_list = formula.getSubFormulas();
				List<Formula> new_disjunct_list = new ArrayList<>();

				for (Formula disjunct : disjunct_list) {
					if (disjunct instanceof Or) {
						new_disjunct_list.addAll(disjunct.getSubFormulas());
					} else {
						new_disjunct_list.add(disjunct);
					}
				}
				formula.getSubFormulas().clear();
				formula.getSubFormulas().addAll(new_disjunct_list);
				return simplified_1(formula);

			} else {
				for (int i = 0; i < formula.getSubFormulas().size(); i++) {
					formula.getSubFormulas().set(i, simplified_1(formula.getSubFormulas().get(i)));
				}
				return formula;
			}
		}

		return formula;
	}

	public List<Formula> subsumeSimplification(List<Formula> inputList) {

		for (int i = 0; i < inputList.size(); i++) {
			for (int j = i + 1; j < inputList.size(); j++) {
				List<Formula> list1 = new ArrayList<>();
				List<Formula> list2 = new ArrayList<>();
				list1 = inputList.get(i).getSubFormulas();
				list2 = inputList.get(j).getSubFormulas();
				if (list1.containsAll(list2)) {
					inputList.remove(i);
					i--;
					break;
				} else if (list2.containsAll(list1)) {
					inputList.remove(j);
					j--;
				}
			}
		}
		return inputList;
	}

	// 附加的化简规则
	public List<Formula> additionalSimp(List<Formula> input) {
		List<Formula> output = new ArrayList<>();
		for (Formula formula : input) {
			output.add(additionalSimp(formula));
		}
		return output;
	}

	public Formula additionalSimp(Formula formula) {
		EChecker ec = new EChecker();
		List<Formula> subFormulas = new ArrayList<>();
		if (ec.isOrInAnd(formula)) {
			for (Formula f : formula.getSubFormulas()) {
				subFormulas.add(additionalSimp(f));
			}
			for (int i = 0; i < subFormulas.size(); i++) {
				for (int j = i + 1; j < subFormulas.size(); j++) {
					if (subFormulas.get(i) instanceof Or) {
						if (isNegationSubFormula(subFormulas.get(j), subFormulas.get(i))) {
							subFormulas.get(i).getSubFormulas().remove(getNNF(new Negation(subFormulas.get(j))));
							if (subFormulas.get(i).getSubFormulas().size() == 1) {
								subFormulas.set(i, subFormulas.get(i).getSubFormulas().get(0));
							}
						}
					} else if (subFormulas.get(j) instanceof Or) {
						if (isNegationSubFormula(subFormulas.get(i), subFormulas.get(j))) {
							subFormulas.get(j).getSubFormulas().remove(getNNF(new Negation(subFormulas.get(i))));
							if (subFormulas.get(j).getSubFormulas().size() == 1) {
								subFormulas.set(j, subFormulas.get(j).getSubFormulas().get(0));
							}
						}
					}
				}
			}
			return new And(subFormulas);
		} else if (ec.isAndInOr(formula)) {
			for (Formula f : formula.getSubFormulas()) {
				subFormulas.add(additionalSimp(f));
			}
			for (int i = 0; i < subFormulas.size(); i++) {
				for (int j = i + 1; j < subFormulas.size(); j++) {
					if (subFormulas.get(i) instanceof And) {
						if (isNegationSubFormula(subFormulas.get(j), subFormulas.get(i))) {
							subFormulas.get(i).getSubFormulas().remove(getNNF(new Negation(subFormulas.get(j))));
							if (subFormulas.get(i).getSubFormulas().size() == 1) {
								subFormulas.set(i, subFormulas.get(i).getSubFormulas().get(0));
							}
						}
					} else if (subFormulas.get(j) instanceof And) {
						if (isNegationSubFormula(subFormulas.get(i), subFormulas.get(j))) {
							subFormulas.get(j).getSubFormulas().remove(getNNF(new Negation(subFormulas.get(i))));
							if (subFormulas.get(j).getSubFormulas().size() == 1) {
								subFormulas.set(j, subFormulas.get(j).getSubFormulas().get(0));
							}
						}
					}
				}
			}
			return new Or(subFormulas);
		} else if (formula.getSubFormulas().size() > 1) {
			for (int i = 0; i < formula.getSubFormulas().size(); i++)
				formula.getSubFormulas().set(i, additionalSimp(formula.getSubFormulas().get(i)));
		}
		return formula;
	}

	/*
	 * 判断formula1的否定形式是否为formula2的子formula
	 */
	public boolean isNegationSubFormula(Formula formula1, Formula formula2) {
		formula1 = getNNF(new Negation(formula1));
		return formula2.getSubFormulas().contains(formula1);
	}

	public boolean surfacingSimplificationJudge(Formula forAllFormula, List<RoleExpression> role_list, Formula formula,
			boolean isAtomicRole) {
		int i = role_list.size() - 1;
		if (isAtomicRole) {
			while (forAllFormula.getSubFormulas().size() > 0 && i >= 0
					&& forAllFormula.getSubFormulas().get(0) instanceof InverseRole) {
				InverseRole inverseRole = new InverseRole(role_list.get(i).toString());
				if (inverseRole.equals(forAllFormula.getSubFormulas().get(0))) {
					forAllFormula = forAllFormula.getSubFormulas().get(1);
					i--;
				} else {
					break;
				}
			}
		} else {
			while (forAllFormula.getSubFormulas().size() > 0 && i >= 0
					&& forAllFormula.getSubFormulas().get(0) instanceof AtomicRole) {
				InverseRole inverseRole = new InverseRole(forAllFormula.getSubFormulas().get(0).toString());
				if (inverseRole.equals(role_list.get(i))) {
					forAllFormula = forAllFormula.getSubFormulas().get(1);
					i--;
				} else {
					break;
				}
			}
		}
		Formula tempFormula = new Formula();
		if (formula.getSubFormulas().size() == 1) {
			tempFormula = formula.getSubFormulas().get(0);
		} else {
			tempFormula = formula;
		}
		if (i == -1 && tempFormula.equals(forAllFormula)) {
			return true;
		}
		return false;
	}

	public Formula surfacingSimplification(Formula formula) throws CloneNotSupportedException {
		List<Formula> forallList = new ArrayList<>();
		for (int i = 0; i < formula.getSubFormulas().size(); i++) {

			if (formula.getSubFormulas().get(i) instanceof Exists
					|| formula.getSubFormulas().get(i) instanceof Forall) {
				formula.getSubFormulas().get(i).getSubFormulas().set(1,
						surfacingSimplification(formula.getSubFormulas().get(i).getSubFormulas().get(1)));
			}
			if (formula.getSubFormulas().get(i) instanceof Forall)
				forallList.add(formula.getSubFormulas().get(i));
		}
		for (Formula forAllFormula : forallList) {
			List<RoleExpression> role_list = new ArrayList<>();
			Formula D = new Formula();
			Formula ff = forAllFormula;
			boolean isAtomicRole;
			if (forAllFormula.getSubFormulas().get(0) instanceof AtomicRole
					|| forAllFormula.getSubFormulas().get(0) instanceof InverseRole) {
				formula.getSubFormulas().remove(forAllFormula);

				if (forAllFormula.getSubFormulas().get(0) instanceof AtomicRole) {
					isAtomicRole = true;
					while (forAllFormula.getSubFormulas().size() > 0
							&& forAllFormula.getSubFormulas().get(0) instanceof AtomicRole) {
						role_list.add(((AtomicRole) forAllFormula.getSubFormulas().get((0))));
						forAllFormula = forAllFormula.getSubFormulas().get(1);
						if (!(forAllFormula instanceof Forall))
							break;
					}
				} else {
					isAtomicRole = false;
					while (forAllFormula.getSubFormulas().size() > 0
							&& forAllFormula.getSubFormulas().get(0) instanceof InverseRole) {
						role_list.add(((InverseRole) forAllFormula.getSubFormulas().get((0))));
						forAllFormula = forAllFormula.getSubFormulas().get(1);
						if (!(forAllFormula instanceof Forall))
							break;
					}
				}
				if (forAllFormula instanceof Or || forAllFormula instanceof Forall) {
					if (forAllFormula instanceof Forall) {
						List<Formula> or_list = new ArrayList<>();
						or_list.add(forAllFormula);
						or_list.add(new BottomConcept());
						forAllFormula = new Or(or_list);
					}
					for (Formula f : forAllFormula.getSubFormulas()) {
						if (f instanceof Forall) {
							if (surfacingSimplificationJudge(f, role_list, formula, isAtomicRole)) {
								Forall result = new Forall();
								Formula forAllFormulaCopy = forAllFormula.clone();
								forAllFormulaCopy.getSubFormulas().remove(f);
								D = forAllFormulaCopy;
								for (int j = role_list.size() - 1; j >= 0; j--) {
									result = new Forall(role_list.get(j), D);
									D = result;
								}
								formula.getSubFormulas().add(result);
								return formula;
							}
						}
					}
				}
				formula.getSubFormulas().add(ff);
			} else if (forAllFormula.getSubFormulas().get(0) instanceof InverseRole) {
				formula.getSubFormulas().remove(forAllFormula);
				while (forAllFormula.getSubFormulas().get(0) instanceof InverseRole) {
					role_list.add(((InverseRole) forAllFormula.getSubFormulas().get((0))));
					forAllFormula = forAllFormula.getSubFormulas().get(1);
				}
				if (forAllFormula instanceof Or) {
					if (forAllFormula.getSubFormulas().get(0) instanceof Forall) {
						D = forAllFormula.getSubFormulas().get(1);
						forAllFormula = forAllFormula.getSubFormulas().get(0);
					} else {
						D = forAllFormula.getSubFormulas().get(0);
						forAllFormula = forAllFormula.getSubFormulas().get(1);
					}
				} else {
					D = new BottomConcept();
				}
				int i = role_list.size() - 1;
				while (i >= 0 && forAllFormula.getSubFormulas().get(0) instanceof AtomicRole) {
					InverseRole inverseRole = new InverseRole(forAllFormula.getSubFormulas().get(0).toString());
					if (inverseRole.equals(role_list.get(i))) {
						forAllFormula = forAllFormula.getSubFormulas().get(1);
						i--;
					} else {
						break;
					}
				}
				Formula tempFormula = new Formula();
				if (formula.getSubFormulas().size() == 1) {
					tempFormula = formula.getSubFormulas().get(0);
				} else {
					tempFormula = formula;
				}
				if (i == -1 && tempFormula.equals(forAllFormula)) {
					Forall result = new Forall();
					for (int j = role_list.size() - 1; j >= 0; j--) {
						result = new Forall(role_list.get(j), D);
						D = result;
					}
					formula.getSubFormulas().add(result);
				} else {
					formula.getSubFormulas().add(ff);
				}
			}
		}
		return formula;
	}

//使用条件：simplify1之后，CNF之间 
// C and (C or D) = C; C or (C and D) = C
	public Formula AbsorptionSimplification1(Formula formula) {
		EChecker ec = new EChecker();
		if (ec.isAndInOr(formula) || ec.isOrInAnd(formula)) {
			boolean is_and_in_or = ec.isAndInOr(formula);
			List<Formula> new_subFormulas = new ArrayList<>();
			for (Formula f : formula.getSubFormulas()) {
				new_subFormulas.add(AbsorptionSimplification1(f));
			}
			List<Formula> result_subFormulas = new ArrayList<>(new_subFormulas);
			for (int i = 0; i < new_subFormulas.size(); i++) {
				if (is_and_in_or && ec.isOrInAnd(new_subFormulas.get(i))) {
					for (Formula f : new_subFormulas.get(i).getSubFormulas()) {
						if (f instanceof Or) {
							if (formula.getSubFormulas().containsAll(f.getSubFormulas())) {
								result_subFormulas.remove(new_subFormulas.get(i));
								continue;
							}
						}
					}
				} else if (!is_and_in_or && ec.isAndInOr(new_subFormulas.get(i))) {
					for (Formula f : new_subFormulas.get(i).getSubFormulas()) {
						if (f instanceof And) {
							if (formula.getSubFormulas().containsAll(f.getSubFormulas())) {
								result_subFormulas.remove(new_subFormulas.get(i));
								continue;
							}
						}
					}
				}
				for (int j = i + 1; j < new_subFormulas.size(); j++) {
					List<Formula> list1 = new ArrayList<>();
					List<Formula> list2 = new ArrayList<>();
					if (new_subFormulas.get(i).getSubFormulas().size() > 1)
						list1 = new_subFormulas.get(i).getSubFormulas();

					else {
						list1.add(new_subFormulas.get(i));
					}
					if (new_subFormulas.get(j).getSubFormulas().size() > 1)
						list2 = new_subFormulas.get(j).getSubFormulas();

					else {
						list2.add(new_subFormulas.get(j));
					}
					if (list2.containsAll(list1)) {
						result_subFormulas.remove(new_subFormulas.get(j));
					} else if (list1.containsAll(list2)) {
						result_subFormulas.remove(new_subFormulas.get(i));
					}
				}
			}
			formula.getSubFormulas().clear();
			formula.getSubFormulas().addAll(result_subFormulas);
		} else if (formula.getSubFormulas().size() > 1) {
			for (int i = 0; i < formula.getSubFormulas().size(); i++) {
				formula.getSubFormulas().set(i, AbsorptionSimplification1(formula.getSubFormulas().get(i)));
			}
		}
		if (formula.getSubFormulas().size() == 1) {
			if (formula instanceof And || formula instanceof Or)
				return formula.getSubFormulas().get(0);

		}
		return formula;
	}

	public Formula Absorption2Compare(Formula fi1, Formula fj1) throws CloneNotSupportedException {
		Formula fi = fi1.clone();
		Formula fj = fj1.clone();
		Formula savedFi = new Formula(), savedFj = new Formula();
		savedFi = fi;
		savedFj = fj;
		while (fi.getSubFormulas().get(0).equals(fj.getSubFormulas().get(0))) {
			fi = fi.getSubFormulas().get(1);
			fj = fj.getSubFormulas().get(1);
			if (!(fi instanceof Forall) || !(fj instanceof Forall)) {
				if (!(fi instanceof Forall) && !(fj instanceof Forall))
					break;
				else {
					return null;
				}
			}
		}
		List<Formula> fi_sub_listFormulas = new ArrayList<>();
		List<Formula> fj_sub_listFormulas = new ArrayList<>();
		if (fi.equals(fj)) {
			return savedFi;
		}
		if (fi.getSubFormulas().size() <= 1)
			fi_sub_listFormulas.add(fi);
		else {
			fi_sub_listFormulas = fi.getSubFormulas();
		}
		if (fj.getSubFormulas().size() <= 1)
			fj_sub_listFormulas.add(fj);
		else {
			fj_sub_listFormulas = fj.getSubFormulas();
		}
		if (fi_sub_listFormulas.containsAll(fj_sub_listFormulas) && fi instanceof And)
			return savedFi;
		else if (fj_sub_listFormulas.containsAll(fi_sub_listFormulas) && fj instanceof And)
			return savedFj;

		return null;
	}

//使用条件：CNF之后
	public Formula AbsorptionSimplification2(Formula formula) throws CloneNotSupportedException {

		List<Formula> forall_list = new ArrayList<>();
		for (int i = 0; i < formula.getSubFormulas().size(); i++) {
			if (formula.getSubFormulas().get(i) instanceof Forall) {
				formula.getSubFormulas().get(i).getSubFormulas().set(1,
						AbsorptionSimplification2(formula.getSubFormulas().get(i).getSubFormulas().get(1)));
				forall_list.add(formula.getSubFormulas().get(i));
			} else if (formula.getSubFormulas().get(i) instanceof Exists) {
				formula.getSubFormulas().get(i).getSubFormulas().set(1,
						AbsorptionSimplification2(formula.getSubFormulas().get(i).getSubFormulas().get(1)));
			}
		}
		formula = DistributivitySimp(formula);
		formula = AbsorptionSimplification1(formula);
		for (int i = 0; i < forall_list.size(); i++) {
			for (int j = i + 1; j < forall_list.size(); j++) {
				Formula removeFormula = Absorption2Compare(forall_list.get(i), forall_list.get(j));
				if (removeFormula != null)
					formula.getSubFormulas().remove(removeFormula);
			}
		}
		return formula;
	}

//使用条件，CNF之后
	public Formula DistributivitySimp(Formula formula) {

		List<Formula> existList = new ArrayList<>();
		List<Formula> otherList = new ArrayList<>();
		for (Formula f : formula.getSubFormulas()) {
			if (f instanceof Exists)
				existList.add(f);
			else {
				otherList.add(f);
			}
		}

		for (int i = 0; i < existList.size(); i++) {
			for (int j = i + 1; j < existList.size(); j++) {
				Formula fi = existList.get(i);
				Formula fj = existList.get(j);
				if (fi.getSubFormulas().get(0).equals(fj.getSubFormulas().get(0))) {
					List<Formula> or_list = new ArrayList<>();
					if (fi.getSubFormulas().get(1) instanceof Or)
						or_list.addAll(fi.getSubFormulas().get(1).getSubFormulas());
					else {
						or_list.add(fi.getSubFormulas().get(1));
					}
					if (fj.getSubFormulas().get(1) instanceof Or)
						or_list.addAll(fj.getSubFormulas().get(1).getSubFormulas());
					else {
						or_list.add(fj.getSubFormulas().get(1));
					}

					existList.get(i).getSubFormulas().set(1, DistributivitySimp(new Or(or_list)));

					existList.remove(j);
					j--;
				}
			}
		}
		formula.getSubFormulas().clear();
		formula.getSubFormulas().addAll(otherList);
		formula.getSubFormulas().addAll(existList);
		if (formula.getSubFormulas().size() == 1 && formula instanceof Or)
			formula = formula.getSubFormulas().get(0);
		return formula;
	}

	public boolean ComplementJudge(Formula formula1, Formula formula2) {

		if (formula1.equals(getNNF(new Negation(formula2))))
			return true;
		else
			return false;
	}

//使用条件：simplified之后，CNF之前 ¬A ⊔ (∀r2.∃r1.C ⊓ ∀r2.∀r1.¬C)
//∃R.C ⊓ ∀R.¬C == 
	public Formula InteractionSimp1(Formula formula) {
		if (formula instanceof And) {
			List<Formula> existList = new ArrayList<>();
			List<Formula> forallList = new ArrayList<>();
			for (Formula f : formula.getSubFormulas()) {
				if (f instanceof Exists) {
					existList.add(InteractionSimp1(f));
				} else if (f instanceof Forall) {
					forallList.add(InteractionSimp1(f));
				}
			}
			for (int i = 0; i < existList.size(); i++) {
				for (int j = 0; j < forallList.size(); j++) {
					if (existList.get(i).getSubFormulas().get(0).equals(forallList.get(j).getSubFormulas().get(0))) {
						if (ComplementJudge(existList.get(i).getSubFormulas().get(1),
								forallList.get(j).getSubFormulas().get(1))) {
							return new BottomConcept();
						}
					}
				}
			}
		} else if (formula.getSubFormulas().size() > 1) {
			for (int i = 0; i < formula.getSubFormulas().size(); i++) {
				// Formula f = formula.getSubFormulas().get(i);
				Formula f = InteractionSimp1(formula.getSubFormulas().get(i));
				if (f.getSubFormulas().size() == 1 && (f instanceof Or || f instanceof And)) {
					f = f.getSubFormulas().get(0);
				}
				formula.getSubFormulas().set(i, f);
			}
		}
		return formula;
	}

//使用条件：CNF之后  
//∃R.C ⊔ ∀R.¬C == T
	public Formula InteractionSimp2(Formula formula) {
		if (formula instanceof Or) {
			List<Formula> existList = new ArrayList<>();
			List<Formula> forallList = new ArrayList<>();
			for (Formula f : formula.getSubFormulas()) {
				if (f instanceof Exists)
					existList.add(InteractionSimp2(f));
				else if (f instanceof Forall)
					forallList.add(InteractionSimp2(f));
			}
			for (int i = 0; i < existList.size(); i++) {
				for (int j = 0; j < forallList.size(); j++) {
					if (existList.get(i).getSubFormulas().get(0).equals(forallList.get(j).getSubFormulas().get(0))) {
						if (ComplementJudge(existList.get(i).getSubFormulas().get(1),
								forallList.get(j).getSubFormulas().get(1))) {
							return new TopConcept();
						}
					}
				}
			}
		} else if (formula.getSubFormulas().size() > 1) {
			for (int i = 0; i < formula.getSubFormulas().size(); i++) {
				// Formula f = formula.getSubFormulas().get(i);
				Formula f = InteractionSimp2(formula.getSubFormulas().get(i));
				if (f.getSubFormulas().size() == 1 && (f instanceof Or || f instanceof And)) {
					f = f.getSubFormulas().get(0);
				}
				formula.getSubFormulas().set(i, f);
			}
		}
		return formula;
	}

	public Formula ObviousSimpOr(Formula formula) {
		if (formula instanceof Or) {
			for (int i = 0; i < formula.getSubFormulas().size(); i++) {
				formula.getSubFormulas().set(i, ObviousSimpOr(formula.getSubFormulas().get(i)));
				if (formula.getSubFormulas().get(i) instanceof TopConcept) {
					return new TopConcept();
				} else if (formula.getSubFormulas().get(i) instanceof BottomConcept) {
					formula.getSubFormulas().remove(i);
					i--;
				}
			}
			Set<Formula> formulaSet = new HashSet<>(formula.getSubFormulas());// 去掉重复
			formula.getSubFormulas().clear();
			formula.getSubFormulas().addAll(formulaSet);
			for (int i = 0; i < formula.getSubFormulas().size(); i++) {
				for (int j = i + 1; j < formula.getSubFormulas().size(); j++) {
					if (ComplementJudge(formula.getSubFormulas().get(i), formula.getSubFormulas().get(j))) {
						return new TopConcept();
					}
				}
			}
		} else if (formula instanceof Forall) {
			if (formula.getSubFormulas().get(1) instanceof TopConcept)
				return new TopConcept();
			if (formula.getSubFormulas().get(0) instanceof TopRole
					&& formula.getSubFormulas().get(1) instanceof BottomConcept)
				return new BottomConcept();
		} else if (formula instanceof Exists) {
			if (formula.getSubFormulas().get(1) instanceof BottomConcept)
				return new BottomConcept();
			if (formula.getSubFormulas().get(0) instanceof TopRole
					&& formula.getSubFormulas().get(1) instanceof TopConcept)
				return new TopConcept();
		}
		if (formula.getSubFormulas().size() > 1) {
			for (int i = 0; i < formula.getSubFormulas().size(); i++) {
				formula.getSubFormulas().set(i, ObviousSimpOr(formula.getSubFormulas().get(i)));
			}
		}
		if (formula.getSubFormulas().size() == 1 && (formula instanceof Or || formula instanceof And))
			formula = formula.getSubFormulas().get(0);
		return formula;
	}

	public Formula ObviousSimpAnd(Formula formula) {
		if (formula instanceof And) {
			for (int i = 0; i < formula.getSubFormulas().size(); i++) {
				formula.getSubFormulas().set(i, ObviousSimpAnd(formula.getSubFormulas().get(i)));
				if (formula.getSubFormulas().get(i) instanceof BottomConcept) {
					return new BottomConcept();
				} else if (formula.getSubFormulas().get(i) instanceof TopConcept) {
					formula.getSubFormulas().remove(i);
					i--;
				}
			}
			Set<Formula> formulaSet = new HashSet<>(formula.getSubFormulas());// 去掉重复
			formula.getSubFormulas().clear();
			formula.getSubFormulas().addAll(formulaSet);
			for (int i = 0; i < formula.getSubFormulas().size(); i++) {
				for (int j = i + 1; j < formula.getSubFormulas().size(); j++) {
					if (ComplementJudge(formula.getSubFormulas().get(i), formula.getSubFormulas().get(j))) {
						return new BottomConcept();
					}
				}
			}

		} else if (formula.getSubFormulas().size() > 1) {
			for (int i = 0; i < formula.getSubFormulas().size(); i++) {
				formula.getSubFormulas().set(i, ObviousSimpAnd(formula.getSubFormulas().get(i)));
			}
		}
		if (formula.getSubFormulas().size() == 1 && (formula instanceof Or || formula instanceof And))
			formula = formula.getSubFormulas().get(0);
		return formula;
	}

	public List<Formula> getNNF(List<Formula> input_list) {

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			output_list.add(getNNF(formula));
		}

		return output_list;
	}

	public Formula getNNF(Formula formula) {// 猜测是不是否定范式

		if (formula instanceof Negation) {
			Formula operand = formula.getSubFormulas().get(0);

			if (operand == TopConcept.getInstance()) {
				return BottomConcept.getInstance();

			} else if (operand == BottomConcept.getInstance()) {
				return TopConcept.getInstance();

			} else if (operand instanceof Negation) {
				return getNNF(operand.getSubFormulas().get(0));

			} else if (operand instanceof Exists) {
				return new Forall(getNNF(operand.getSubFormulas().get(0)),
						getNNF(new Negation(operand.getSubFormulas().get(1))));

			} else if (operand instanceof Forall) {
				return new Exists(getNNF(operand.getSubFormulas().get(0)),
						getNNF(new Negation(operand.getSubFormulas().get(1))));

			} else if (operand instanceof And) {
				List<Formula> conjunct_list = operand.getSubFormulas();
				List<Formula> new_conjunct_list = new ArrayList<>();
				for (Formula conjunct : conjunct_list) {
					new_conjunct_list.add(getNNF(new Negation(conjunct)));
				}
				return new Or(new_conjunct_list);

			} else if (operand instanceof Or) {
				List<Formula> disjunct_list = operand.getSubFormulas();
				List<Formula> new_disjunct_list = new ArrayList<>();
				for (Formula disjunct : disjunct_list) {
					new_disjunct_list.add(getNNF(new Negation(disjunct)));
				}
				return new And(new_disjunct_list);

			} else {
				return formula;
			}

		} else if (formula instanceof Exists || formula instanceof Forall) {
			formula.getSubFormulas().set(0, getNNF(formula.getSubFormulas().get(0)));
			formula.getSubFormulas().set(1, getNNF(formula.getSubFormulas().get(1)));
			return formula;

		} else if (formula instanceof And || formula instanceof Or) {
			for (int i = 0; i < formula.getSubFormulas().size(); i++) {
				formula.getSubFormulas().set(i, getNNF(formula.getSubFormulas().get(i)));
			}
			return formula;
		}

		return formula;
	}

	public List<Formula> getCNF(List<Formula> input_list) {

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			output_list.addAll(getCNF(simplified_1(formula)));
		}

		for (int i = 0; i < output_list.size(); i++) {
			output_list.set(i, simplified_1(output_list.get(i)));
		}
		return output_list;
	}

	static int i = 0;

	public List<Formula> getCNF(Formula formula) {

		EChecker ec = new EChecker();
		List<Formula> output_list = new ArrayList<>();
		if (ec.isAndInOr(formula)) {
			i++;
			// System.out.println("i = " + i);
			List<List<Formula>> list_list = new ArrayList<>();
			List<Formula> disjunct_list = formula.getSubFormulas();
			for (int i = 0; i < disjunct_list.size(); i++) {
				list_list.add(i, new ArrayList<>());
				if (disjunct_list.get(i) instanceof And) {
					list_list.get(i).addAll(disjunct_list.get(i).getSubFormulas());
				} else {
					list_list.get(i).add(disjunct_list.get(i));
				}
			}

			List<List<Formula>> cp_list = Lists.cartesianProduct(list_list);

			for (List<Formula> list : cp_list) {
				output_list.add(new Or(list));
			}

			return getCNF(output_list);
		} else if (formula instanceof And) {
			for (Formula f : formula.getSubFormulas()) {
				output_list.add(f);

			}
			return getCNF(output_list);
		}

		return Collections.singletonList(formula);
	}

	public Formula getDNF(Formula formula) {

		EChecker ec = new EChecker();

		if (ec.isOrInAnd(formula)) {

			List<List<Formula>> list_list = new ArrayList<>();
			List<Formula> conjunct_list = formula.getSubFormulas();

			for (int i = 0; i < conjunct_list.size(); i++) {
				list_list.add(i, new ArrayList<>());
				if (conjunct_list.get(i) instanceof Or) {
					list_list.get(i).addAll(conjunct_list.get(i).getSubFormulas());
				} else {
					list_list.get(i).add(conjunct_list.get(i));
				}
			}

			List<Formula> output_list = new ArrayList<>();
			List<List<Formula>> cp_list = Lists.cartesianProduct(list_list);

			for (List<Formula> list : cp_list) {
				output_list.add(new And(list));
			}

			Formula output = new Or(output_list);
			return output;
		}

		return formula;
	}

	public Formula removeDoubleNegations(Formula formula) {

		if (formula instanceof Negation) {
			Formula operand = formula.getSubFormulas().get(0);

			if (operand == TopConcept.getInstance()) {
				return BottomConcept.getInstance();

			} else if (operand == BottomConcept.getInstance()) {
				return TopConcept.getInstance();

			} else if (operand == TopRole.getInstance()) {
				return BottomRole.getInstance();

			} else if (operand == BottomRole.getInstance()) {
				return TopRole.getInstance();

			} else if (operand instanceof Negation) {
				return removeDoubleNegations(operand.getSubFormulas().get(0));

			} else {
				formula.getSubFormulas().set(0, removeDoubleNegations(operand));
				return formula;
			}

		} else if (formula instanceof Exists || formula instanceof Forall) {
			formula.getSubFormulas().set(0, removeDoubleNegations(formula.getSubFormulas().get(0)));
			formula.getSubFormulas().set(1, removeDoubleNegations(formula.getSubFormulas().get(1)));
			return formula;

		} else if (formula instanceof And || formula instanceof Or) {
			for (int i = 0; i < formula.getSubFormulas().size(); i++) {
				formula.getSubFormulas().set(i, removeDoubleNegations(formula.getSubFormulas().get(i)));
			}
			return formula;
		}

		return formula;
	}

	public List<Formula> getClauses(List<Formula> input_list) {

		List<Formula> output_list = new ArrayList<>();

		for (Formula axiom : input_list) {
			output_list.add(getClause(axiom));
		}
		return output_list;
	}

	private Formula getClause(Formula formula) {

		if (formula instanceof Inclusion) {
			List<Formula> disjunct_list = new ArrayList<>();

			Formula subsumee = formula.getSubFormulas().get(0);
			Formula subsumer = formula.getSubFormulas().get(1);

			if (subsumee instanceof Negation) {
				disjunct_list.add(subsumee.getSubFormulas().get(0));
			} else {
				disjunct_list.add(new Negation(subsumee));
			}

			disjunct_list.add(subsumer);

			Formula clause = new Or(disjunct_list);
			return clause;

		}

		return null;
	}

}
