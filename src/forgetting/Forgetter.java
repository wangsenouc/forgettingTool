package forgetting;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import com.google.common.collect.Sets;
import checkfrequency.FChecker;
import checkreducedform.RFChecker;
import concepts.AtomicConcept;
import convertion.BackConverter;
import convertion.Converter;
import extraction.SubsetExtractor;
import formula.Formula;
import inference.Inferencer;
import inference.Rewrite_R;
import inference.Skolemisation_C;
import inference.Skolemisation_Nabla;
import inference.SubstitutionWithDefiner;
import inference.Surfacing_C;
import roles.AtomicRole;
import simplification.Simplifier;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;

public class Forgetter {

	public OWLOntology Forgetting(Set<OWLClass> c_sig_owl, Set<OWLObjectProperty> r_sig_owl, OWLOntology onto,
			BufferedWriter bf, String filePath) throws CloneNotSupportedException, OWLOntologyCreationException, IOException, InterruptedException {

		

		Converter ct = new Converter();
		BackConverter bc = new BackConverter();
		Inferencer inf = new Inferencer();
		Simplifier simp = new Simplifier();
		SubsetExtractor se = new SubsetExtractor();
		FChecker fc = new FChecker();
		SubstitutionWithDefiner swd = new SubstitutionWithDefiner();
		int ontoSize = 0;
		
		OWLOntology onto_subclassof = ct.toOWLSubClassOfAxiom(onto);
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		OWLOntology result = manager.createOntology(IRI.generateDocumentIRI());
		SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager, onto_subclassof,
				ModuleType.BOT);
		Set<OWLClass> c_sig_owl_m = Sets.difference(onto_subclassof.getClassesInSignature(), c_sig_owl);
		Set<OWLEntity> c_sig_owl_m_entity = new HashSet<>(c_sig_owl_m);

		bf.write("c_sig_owl = " + c_sig_owl.size() + "\n");
		bf.write("r_sig_owl = " + r_sig_owl.size() + "\n");
		bf.write("onto = " + onto_subclassof.getLogicalAxiomCount() + "\n");
		
		Set<OWLObjectProperty> r_sig_owl_m = Sets.difference(onto_subclassof.getObjectPropertiesInSignature(),
				r_sig_owl);
		Set<OWLEntity> r_sig_owl_m_entity = new HashSet<>(r_sig_owl_m);
		Set<OWLEntity> sig_owl_m_entity = Sets.union(c_sig_owl_m_entity, r_sig_owl_m_entity);
		OWLOntology module = extractor.extractAsOntology(sig_owl_m_entity, IRI.generateDocumentIRI());
		ontoSize = onto_subclassof.getLogicalAxiomCount() - module.getLogicalAxiomCount();
		if(ontoSize >= 0) {
			BufferedWriter bw = new BufferedWriter(new FileWriter("F:\\Clauses\\extra40.txt",true));
			bw.write(filePath + "\n");
			bw.write(ontoSize + "\n");
			bw.close();
			return null;
		}
		List<Formula> clause_list = simp.getClauses(ct.OntologyConverter(module));

		Set<AtomicConcept> c_sig = ct.getConceptsfromClasses(c_sig_owl);
		Set<AtomicRole> r_sig = ct.getRolesfromObjectProperties(r_sig_owl);
		List<AtomicConcept> list_c_sig = new ArrayList<>(c_sig);
		List<AtomicRole> list_r_sig = new ArrayList<>(r_sig);
		List<AtomicConcept> remained_list_c_sig = new ArrayList<>();
		List<AtomicRole> unforgetted_r_sig = new ArrayList<>();
		List<AtomicConcept> unforgetted_c_sig = new ArrayList<>();
		List<Formula> canPurifySig = new ArrayList<>();
		List<Formula> c_sig_clause_list = se.getConceptSubset(c_sig, clause_list);
		List<Formula> r_sig_clause_list = se.getRoleSubset(r_sig, clause_list);
		List<Formula> sig_clause_list = new ArrayList<>();
		sig_clause_list.addAll(c_sig_clause_list);
		sig_clause_list.addAll(r_sig_clause_list);
		List<Formula> pivot_list_normalised = null;
		boolean conceptSuccess = true;
		boolean roleSuccess = true;

		//将所有可以purify的symbols分离出来
		List<Formula> pivot_list = new ArrayList<>();
		for(AtomicConcept concept:c_sig) {
			if(fc.positive(concept, sig_clause_list) == 0) {
				pivot_list = se.getConceptSubset(concept, sig_clause_list);
				sig_clause_list.addAll(inf.PurifyPositive(concept, pivot_list));
				
			}else if(fc.negative(concept, sig_clause_list) == 0) {
				pivot_list = se.getConceptSubset(concept, sig_clause_list);
				sig_clause_list.addAll(inf.PurifyNegative(concept, pivot_list));
			}else {
				list_c_sig.add(concept);
			}
		}
		for(AtomicRole role : r_sig) {
			if(fc.positive(role, sig_clause_list) == 0) {
				pivot_list = se.getRoleSubset(role, sig_clause_list);
				sig_clause_list.addAll(inf.PurifyPositive(role, pivot_list));
				
			}else if(fc.negative(role, sig_clause_list) == 0) {
				pivot_list = se.getRoleSubset(role, sig_clause_list);
				sig_clause_list.addAll(inf.PurifyNegative(role, pivot_list));
			}else {
				list_r_sig.add(role);
			}
		}		
		//将所有可以Purifiable的进行遗忘
		for(Formula sig : canPurifySig) {
			
			if(sig instanceof AtomicConcept) {
				AtomicConcept concept = (AtomicConcept) sig;
				pivot_list = se.getConceptSubset(concept, sig_clause_list);
				if(fc.positive(concept, pivot_list) == 0) {
					pivot_list = inf.PurifyPositive(concept, pivot_list);
					
				}else {
					pivot_list = inf.PurifyNegative(concept, pivot_list);
				}
			}else {
				AtomicRole role = (AtomicRole) sig;
				pivot_list = se.getRoleSubset(role, sig_clause_list);
				if(fc.positive(role, sig_clause_list) == 0) {
					pivot_list = inf.PurifyPositive(role, pivot_list);
				}else {
					pivot_list = inf.PurifyNegative(role, pivot_list);
				}
			}
			sig_clause_list.addAll(pivot_list);
		}
		sig_clause_list = simp.getCNFandSimplify(sig_clause_list);

		// 首先遗忘role symbols
		Runtime r = Runtime.getRuntime();
		r.gc();
		Thread.sleep(100);
		long roleStartMem = r.freeMemory();
		long roleEndMem = roleStartMem;
		long roleStart = System.currentTimeMillis();
		
		for (AtomicRole role : list_r_sig) {
			List<Formula> getRoleSubList = se.getRoleSubset(role, sig_clause_list);
			List<Formula> getNNFList = simp.getNNF(getRoleSubList);
			List<Formula> getCNFList = simp.getCNF(getNNFList);
			List<Formula> list_normalised = swd.Substitution(getCNFList);
			pivot_list_normalised = se.getRoleSubset(role, list_normalised);// 正规化会引入新的不含role的axiom，
			sig_clause_list.addAll(list_normalised);
			List<Formula> forgetted_list = null;
			if (pivot_list_normalised.isEmpty()) {
				continue;
			}
			try {
				forgetted_list = forgettingRole(role, pivot_list_normalised);
				roleEndMem = Math.min(roleEndMem, r.freeMemory());
			} catch (OutOfMemoryError e) {
				roleSuccess = false;
				bf.write(e.getMessage() + "\n");
				break;

			} catch (IllegalArgumentException e) {
				roleSuccess = false;
				bf.write(e.getMessage() + "\n");
				break;
			}

			if (forgetted_list == null) {//遗忘失败
				forgetted_list = pivot_list_normalised;
				roleSuccess = false;
				unforgetted_r_sig.add(role);
			}
			sig_clause_list.addAll(forgetted_list);

		}
		long roleEnd = System.currentTimeMillis();
		
		// 对concepts进行排序
		list_c_sig.addAll(swd.definer);
		for (AtomicConcept concept : list_c_sig) {
			int pr = fc.positiveRestrict(concept, sig_clause_list);
			int nr = fc.negativeRestrict(concept, sig_clause_list);
			int p = fc.positive(concept, sig_clause_list);
			int n = fc.negative(concept, sig_clause_list);
			if(pr < nr) {
				concept.restrictionTimes = pr;
				concept.isPositive = true;
			}else if(pr > nr) {
				concept.restrictionTimes = nr;
				concept.isPositive = false;
			}else {
				concept.restrictionTimes = pr;
				if(p < n) {
					concept.occurenceTimes = p;
					concept.isPositive = true;
				}else {
					concept.occurenceTimes = n;
					concept.isPositive = false;
				}
			}

		}
		Collections.sort(list_c_sig);
		
		// 然后遗忘concept symbols
		r.gc();
		Thread.sleep(100);
		long conceptStartMen = r.freeMemory();
		long conceptEndMen = conceptStartMen;
		long conceptStart = System.currentTimeMillis();
		for (AtomicConcept concept : list_c_sig) {
			List<Formula> forgetted_list = null;
			try {
				pivot_list_normalised = simp.getCNFandSimplify(se.getConceptSubset(concept, sig_clause_list));
				if (pivot_list_normalised.isEmpty()) {
					continue;
				}
				forgetted_list = FrogettingConcept(concept, pivot_list_normalised);
				conceptEndMen = Math.min(conceptEndMen, r.freeMemory());
				
			} catch (OutOfMemoryError e) {
				bf.write("异常" + e.getMessage() + "\n");
				conceptSuccess = false;
				break;
			} catch (IllegalArgumentException e) {
				bf.write("异常" + e.getMessage() + "\n");
				conceptSuccess = false;
				break;
			}catch (Exception e) {
				bf.write("异常" + e.getMessage() + "\n");
				conceptSuccess = false;
				break;
			}

			if (forgetted_list == null) {// 遗忘失败
				forgetted_list = pivot_list_normalised;
				remained_list_c_sig.add(concept);
			} else {
				swd.definer.remove(concept);
			}
			sig_clause_list.addAll(forgetted_list);
		}
		// 开始遗忘上一次遗忘过程中不能遗忘的符号
		for (AtomicConcept concept : remained_list_c_sig) {
			List<Formula> forgetted_list = null;
			try {
				pivot_list_normalised = simp.getCNFandSimplify(se.getConceptSubset(concept, sig_clause_list));
				forgetted_list = FrogettingConcept(concept, pivot_list_normalised);
			}catch (OutOfMemoryError e) {
				bf.write("异常" + e.getMessage() + "\n");
				conceptSuccess = false;
				break;
			} catch (IllegalArgumentException e) {
				bf.write("异常" + e.getMessage() + "\n");
				conceptSuccess = false;
				break;
			}catch (Exception e) {
				bf.write("异常" + e.getMessage() + "\n");
				conceptSuccess = false;
				break;
			}

			if (forgetted_list == null) {// 遗忘失败
				forgetted_list = pivot_list_normalised;
				conceptSuccess = false;
				unforgetted_c_sig.add(concept);
				
			}else{
				swd.definer.remove(concept);
			}
			sig_clause_list.addAll(forgetted_list);
		}
		long conceptEnd = System.currentTimeMillis();

		// 输出遗忘结果
		clause_list.addAll(simp.getCNFandSimplify(sig_clause_list));
		if (conceptSuccess) {
			System.out.println("Concept Forgetting Successful!");
			bf.write("Concept Forgetting Successful!\n");
		} else {
			System.out.println("Concept Forgetting Unsuccessful");
			bf.write("Concept Forgetting Unsuccessful\n");
		}
		if (roleSuccess) {
			System.out.println("Role Forgetting Successful!");
			bf.write("Role Forgetting Successful!\n");
		} else {
			System.out.println("Role Forgetting Unsuccseeful!");
			bf.write("Role Forgetting Unsuccseeful!\n");
		}
		manager.addAxioms(result, bc.toOWLAxioms(bc.toAxioms(clause_list)));
		bf.write("Duration of concept forgetting: " + (conceptEnd - conceptStart) + "ms\n");
		bf.write("Duration of role forgetting: " + (roleEnd - roleStart)  + "ms\n");
		bf.write("Memory consumption of concept forgetting:" + (conceptStartMen - conceptEndMen) / 1024 + "KB\n");
		bf.write("Memory consumption of role forgetting:" + (roleStartMem - roleEndMem) /1024 + "KB\n");
		bf.write("The number of lefted definer: " + swd.definer.size() + "\n");
		bf.write("The size of new ontology：" + (result.getLogicalAxiomCount() + ontoSize) + "\n\n");
		bf.write("\n");
		return result;
		
	}

	public List<Formula> FrogettingConcept(AtomicConcept concept, List<Formula> pivot_list_normalised)
			throws CloneNotSupportedException, OWLOntologyCreationException {
		Simplifier simp = new Simplifier();
		Inferencer inf = new Inferencer();
		FChecker fc = new FChecker();
		RFChecker rfc = new RFChecker();
		Surfacing_C surfacing_C = new Surfacing_C();
		Skolemisation_C skolemisation_C = new Skolemisation_C();
		Skolemisation_Nabla skolemisation_Nabla = new Skolemisation_Nabla();
		if (concept.isPositive) {
			if (pivot_list_normalised.isEmpty()) {
				return pivot_list_normalised;
			} else if (fc.negative(concept, pivot_list_normalised) == 0) {// 没有负的
				return simp.getCNFandSimplify(inf.PurifyPositive(concept, pivot_list_normalised));

			} else if (fc.positive(concept, pivot_list_normalised) == 0) {// 没有正的
				return simp.getCNFandSimplify(inf.PurifyNegative(concept, pivot_list_normalised));
			
			} else if (rfc.isAReducedFormPositive(concept, pivot_list_normalised)) {// pivot+-reduced form
				return simp.getCNFandSimplify(inf.AckermannCPositive(concept, pivot_list_normalised));
			
			} else if (rfc.isAReducedFormNegative(concept, pivot_list_normalised)) {// pivot--reduced form
				return simp.getCNFandSimplify(inf.AckermannCNegative(concept, pivot_list_normalised));
			
			} else {// 非pivot-reduced form
				List<Formula> pivot_list_reduced = new ArrayList<>();
				if (rfc.isAReducedFormPositive(concept,
						pivot_list_reduced = surfacing_C.Surfacing_C_Positive(concept, pivot_list_normalised))) {
					return simp.getCNFandSimplify(inf.AckermannCPositive(concept, pivot_list_reduced));
				
				} else if (rfc.isAReducedFormNegative(concept,
						pivot_list_reduced = surfacing_C.Surfacing_C_Negative(concept, pivot_list_normalised))) {
					return simp.getCNFandSimplify(inf.AckermannCNegative(concept, pivot_list_reduced));
				
				} else if (rfc.isAReducedFormPositive(concept, pivot_list_reduced = skolemisation_C
						.Skolemisation_C_Positive(concept, pivot_list_normalised))) {
					return simp.getCNFandSimplify(inf.AckermannCPositive(concept, pivot_list_reduced));
				
				} else if (rfc.isAReducedFormNegative(concept, pivot_list_reduced = skolemisation_C
						.Skolemisation_C_Negative(concept, pivot_list_normalised))) {
					return simp.getCNFandSimplify(inf.AckermannCNegative(concept, pivot_list_reduced));
				
				} else if (rfc.isAReducedFormPositive(concept, pivot_list_reduced = skolemisation_Nabla
						.Skolemisation_nabla_Positive(concept, pivot_list_normalised))) {
					return simp.getCNFandSimplify(inf.AckermannCPositive(concept, pivot_list_reduced));
				
				} else if (rfc.isAReducedFormNegative(concept, pivot_list_reduced = skolemisation_Nabla
						.Skolemisation_nabla_Negative(concept, pivot_list_normalised))) {
					return simp.getCNFandSimplify(inf.AckermannCNegative(concept, pivot_list_reduced));
				
				} else {// 目前暂时无法遗忘

				}
			}
		} else {
			if (pivot_list_normalised.isEmpty()) {
				return pivot_list_normalised;
			} else if (fc.positive(concept, pivot_list_normalised) == 0) {// 没有正的
				return simp.getCNFandSimplify(inf.PurifyNegative(concept, pivot_list_normalised));

			} else if (fc.negative(concept, pivot_list_normalised) == 0) {// 没有负的
				return simp.getCNFandSimplify(inf.PurifyPositive(concept, pivot_list_normalised));

			} else if (rfc.isAReducedFormNegative(concept, pivot_list_normalised)) {// pivot--reduced form
				return simp.getCNFandSimplify(inf.AckermannCNegative(concept, pivot_list_normalised));

			} else if (rfc.isAReducedFormPositive(concept, pivot_list_normalised)) {// pivot+-reduced form
				return simp.getCNFandSimplify(inf.AckermannCPositive(concept, pivot_list_normalised));

			} else {// 非pivot-reduced form
				List<Formula> pivot_list_reduced = new ArrayList<>();
				if (rfc.isAReducedFormNegative(concept,
						pivot_list_reduced = surfacing_C.Surfacing_C_Negative(concept, pivot_list_normalised))) {
					return simp.getCNFandSimplify(inf.AckermannCNegative(concept, pivot_list_reduced));

				} else if (rfc.isAReducedFormPositive(concept,
						pivot_list_reduced = surfacing_C.Surfacing_C_Positive(concept, pivot_list_normalised))) {
					return simp.getCNFandSimplify(inf.AckermannCPositive(concept, pivot_list_reduced));

				} else if (rfc.isAReducedFormNegative(concept, pivot_list_reduced = skolemisation_C
						.Skolemisation_C_Negative(concept, pivot_list_normalised))) {
					return simp.getCNFandSimplify(inf.AckermannCNegative(concept, pivot_list_reduced));

				} else if (rfc.isAReducedFormPositive(concept, pivot_list_reduced = skolemisation_C
						.Skolemisation_C_Positive(concept, pivot_list_normalised))) {
					return simp.getCNFandSimplify(inf.AckermannCPositive(concept, pivot_list_reduced));

				} else if (rfc.isAReducedFormNegative(concept, pivot_list_reduced = skolemisation_Nabla
						.Skolemisation_nabla_Negative(concept, pivot_list_normalised))) {
					return simp.getCNFandSimplify(inf.AckermannCNegative(concept, pivot_list_reduced));

				} else if (rfc.isAReducedFormPositive(concept, pivot_list_reduced = skolemisation_Nabla
						.Skolemisation_nabla_Positive(concept, pivot_list_normalised))) {
					return simp.getCNFandSimplify(inf.AckermannCPositive(concept, pivot_list_reduced));

				} else {// 目前暂时无法遗忘

				}
			}
		}
		return null;
	}

	public List<Formula> forgettingRole(AtomicRole role, List<Formula> pivot_list_normalised)
			throws CloneNotSupportedException, OWLOntologyCreationException {
		List<Formula> pivot_list_normalised2 = new ArrayList<>();
		Simplifier simp = new Simplifier();
		FChecker fc = new FChecker();
		for (Formula formula : pivot_list_normalised)
			pivot_list_normalised2.add(formula.clone());

		RFChecker rfc = new RFChecker();
		Inferencer inf = new Inferencer();
		Rewrite_R rewrite_R = new Rewrite_R();
		if (fc.positive(role, pivot_list_normalised2) == 0) {
			return new ArrayList<>();
			
		} else if (fc.negative(role, pivot_list_normalised2) == 0) {
			return simp.roleSimplification(inf.PurifyPositive(role, pivot_list_normalised2));

		} else if (rfc.isAReducedForm(role, pivot_list_normalised2)) {
			return simp.roleSimplification(inf.Ackermann_R(role, pivot_list_normalised2));

		} else if (rfc.isAReducedForm(role, 
				pivot_list_normalised2 = rewrite_R.Surfacing_R(pivot_list_normalised2))) {
			return simp.roleSimplification(inf.Ackermann_R(role, pivot_list_normalised2));

		} else if (rfc.isAReducedForm(role,
				pivot_list_normalised2 = rewrite_R.Inverting_R(role, pivot_list_normalised2))) {
			return simp.roleSimplification(inf.Ackermann_R(role, pivot_list_normalised2));
		}
		return null;
	}

}
