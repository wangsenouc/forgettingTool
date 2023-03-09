package inference;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import checkfrequency.FChecker;
import connectives.*;
import simplification.*;
import formula.Formula;
import roles.AtomicRole;
import roles.InverseRole;
import checkreducedform.*;
import concepts.*;
public class Surfacing_C {
	
public boolean CheckCyclic(AtomicConcept concept, Formula formula) {
		FChecker fc = new FChecker();
		int cnt = 0;
		for(Formula subFormula : formula.getSubFormulas()) {
			if(fc.positive(concept, subFormula) + fc.negative(concept, subFormula) > 0)
				cnt++;
		}
		if(cnt > 1)
			return true;
	return false;
	}
public List<Formula> Surfacing_C_Positive(AtomicConcept concept,
		List<Formula> pivot_list_normalised)throws CloneNotSupportedException{
	Simplifier simp = new Simplifier();
	List<Formula> result = new ArrayList<>();
	for(Formula formula1 : pivot_list_normalised) {
		Formula formula = formula1.clone();
		if(formula instanceof Forall) {
			List<Formula> orList = new ArrayList<Formula>();
			orList.add(formula);
			orList.add(new BottomConcept());
			formula = new Or(orList);
		}
		Formula temp = Surfacing_C_Positive(concept, formula);
		result.add(temp);
	}
	return simp.getCNF(result);
}
Formula Surfacing_C_Positive(AtomicConcept concept, Formula formula) throws CloneNotSupportedException{
	RFChecker rfc = new RFChecker();
	FChecker fc = new FChecker();
	if(CheckCyclic(concept, formula) == true) {
		Simplifier simp = new Simplifier();
		formula = simp.surfacingSimplification(formula);
		if(CheckCyclic(concept, formula) == true)
			return formula;
	}
	if(!rfc.isAReducedFormPositive(concept, Collections.singletonList(formula))) {	
		List<Formula> subFormulasList = formula.getSubFormulas();
		for(Formula ele : subFormulasList) {
			if(ele instanceof Forall && fc.positive(concept, ele) != 0) {
				subFormulasList.remove(ele);
				Forall forall;
				if(ele.getSubFormulas().get(0) instanceof InverseRole) {
					InverseRole iRole = (InverseRole) ele.getSubFormulas().get(0);
					AtomicRole atomicRole = new AtomicRole(iRole.getRoleStr());
					if(subFormulasList.size() > 1)
						forall = new Forall(atomicRole, new Or(subFormulasList));
					else 
						forall = new Forall(atomicRole, subFormulasList.get(0));
					
				}else {
					AtomicRole atomicRole = (AtomicRole) ele.getSubFormulas().get(0);
					InverseRole iRole = new InverseRole(atomicRole.toString());
					if(subFormulasList.size() > 1)
						forall = new Forall(iRole, new Or(subFormulasList));
					else
						forall = new Forall(iRole, subFormulasList.get(0));
				}							
				subFormulasList.clear();
				subFormulasList.add(forall);
				if(ele.getSubFormulas().get(1) instanceof Or) {
					subFormulasList.addAll(ele.getSubFormulas().get(1).getSubFormulas());
				}
				else
					subFormulasList.add(ele.getSubFormulas().get(1));
				Or or = new Or(subFormulasList);	
				return Surfacing_C_Positive(concept, (Formula) or);			
			}
		}
		
	}
		
	return formula;
}
public List<Formula> Surfacing_C_Negative(AtomicConcept concept, List<Formula> pivot_list_normalised) throws CloneNotSupportedException{
	Simplifier simp = new Simplifier();
	List<Formula> result = new ArrayList<>();
	for(Formula formula1 : pivot_list_normalised) {
		Formula formula = formula1.clone();
		if(formula instanceof Forall) {
			List<Formula> orList = new ArrayList<Formula>();
			orList.add(formula);
			orList.add(new BottomConcept());
			formula = new Or(orList);
		}
		Formula temp = Surfacing_C_Negative(concept, formula);
		result.add(temp);
	}
	return simp.getCNF(result);
}
//如果能应用Surfacing，则应用，否则将formula原路返回
Formula Surfacing_C_Negative(AtomicConcept concept, Formula formula) throws CloneNotSupportedException{
	RFChecker rfc = new RFChecker();
	FChecker fc = new FChecker();
	if(CheckCyclic(concept, formula) == true) {
		Simplifier simp = new Simplifier();
		formula = simp.surfacingSimplification(formula);
		if(CheckCyclic(concept, formula) == true)
			return formula;
		}
	else if(!rfc.isAReducedFormNegative(concept, Collections.singletonList(formula))) {	
		List<Formula> subFormulasList = formula.getSubFormulas();
		for(Formula ele : subFormulasList) {
			if(ele instanceof Forall && fc.negative(concept, ele) != 0) {
				subFormulasList.remove(ele);
				Forall forall;
				if(ele.getSubFormulas().get(0) instanceof InverseRole) {
					InverseRole iRole = (InverseRole) ele.getSubFormulas().get(0);
					AtomicRole atomicRole = new AtomicRole(iRole.getRoleStr());
					if(subFormulasList.size() > 1)
						forall = new Forall(atomicRole, new Or(subFormulasList));
					else 
						forall = new Forall(atomicRole, subFormulasList.get(0));
					
				}else {
					AtomicRole atomicRole = (AtomicRole) ele.getSubFormulas().get(0);
					InverseRole iRole = new InverseRole(atomicRole.toString());
					if(subFormulasList.size() > 1)
						forall = new Forall(iRole, new Or(subFormulasList));
					else
						forall = new Forall(iRole, subFormulasList.get(0));
				}							
				subFormulasList.clear();
				subFormulasList.add(forall);
				if(ele.getSubFormulas().get(1) instanceof Or) {
					subFormulasList.addAll(ele.getSubFormulas().get(1).getSubFormulas());
				}
				else
					subFormulasList.add(ele.getSubFormulas().get(1));
				Or or = new Or(subFormulasList);	
				return Surfacing_C_Negative(concept, (Formula) or);			
			}
		}
		
		
	}
		
	return formula;
}
}
