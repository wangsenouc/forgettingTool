package convertion;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.EntityType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import checkexistence.EChecker;
import concepts.AtomicConcept;
import concepts.BottomConcept;
import concepts.TopConcept;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import connectives.Inclusion;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import individual.Individual;
import roles.AtomicRole;
import roles.BottomRole;
import roles.InverseRole;
import roles.TopRole;


public class BackConverter {

	public BackConverter() {

	}
	
	private OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	private OWLDataFactory factory = manager.getOWLDataFactory();
	
	public OWLEntity getClassfromConcept(AtomicConcept concept) {
				
		OWLEntity owlentity = factory.getOWLEntity(EntityType.OBJECT_PROPERTY, IRI.create(concept.getText()));
		return owlentity;
	}
	
	public Set<Formula> toAxioms(List<Formula> input_list) throws CloneNotSupportedException {
		
		Set<Formula> output_set = new HashSet<>();
		for (Formula clause : input_list) {
			if (clause == BottomConcept.getInstance() || clause == BottomRole.getInstance()) {									
				return Collections.singleton(toInclusion(BottomConcept.getInstance()));
				
			} else if (clause != TopConcept.getInstance() && clause != TopRole.getInstance()) {
				Formula axiom = toInclusion(clause);
				output_set.add(axiom);
			}
		}
				
		return output_set;
	}
	
	
	private Formula toInclusion(Formula formula) {

		if (formula instanceof Inclusion) {
			return formula;

		} else if (formula instanceof Or) {
			List<Formula> negative_list = new ArrayList<>();
			List<Formula> positive_list = new ArrayList<>();
			List<Formula> disjunct_list = formula.getSubFormulas();
			for (Formula disjunct : disjunct_list) {
				if (disjunct instanceof Negation) {
					negative_list.add(disjunct.getSubFormulas().get(0));
				} else {
					positive_list.add(disjunct);
				}
			}

			Formula lefthand = null;
			if (negative_list.isEmpty()) {
				lefthand = TopConcept.getInstance();
			} else if (negative_list.size() == 1) {
				lefthand = negative_list.get(0);
			} else {
				lefthand = new And(negative_list);
			}

			Formula righthand = null;
			if (positive_list.isEmpty()) {
				righthand = BottomConcept.getInstance();
			} else if (positive_list.size() == 1) {
				righthand = positive_list.get(0);
			} else {
				righthand = new Or(positive_list);
			}

			return new Inclusion(lefthand, righthand);

		} else if (formula instanceof Negation) {
			return new Inclusion(formula.getSubFormulas().get(0), BottomConcept.getInstance());

		} else {
			return new Inclusion(TopConcept.getInstance(), formula);
		}

	}

	public OWLOntology toOWLSubClassOfAxiomOntology(List<Formula> formula_list) throws OWLOntologyCreationException {

		OWLOntology ontology = manager.createOntology(IRI.generateDocumentIRI());

		for (Formula formula : formula_list) {
			manager.addAxiom(ontology, toOWLSubClassOfAxiom(formula));
		}

		return ontology;
	}


	public OWLOntology toOWLOntology(List<Formula> formula_list) throws OWLOntologyCreationException {

		OWLOntology ontology = manager.createOntology();

		for (Formula formula : formula_list) {
			manager.addAxiom(ontology, toOWLAxiom(formula));
		}

		return ontology;
	}
	
	public Set<OWLAxiom> toOWLAxioms(Set<Formula> formula_set) {

		Set<OWLAxiom> output_set = new HashSet<>();
		
		for (Formula formula : formula_set) {
			output_set.add(toOWLAxiom(formula));
		}

		return output_set;
	}
	
	
	public OWLAxiom toOWLSubClassOfAxiom(Formula inclusion) {
		
		OWLSubClassOfAxiom scoa = factory.getOWLSubClassOfAxiom(toOWLClassExpression(inclusion.getSubFormulas().get(0)),
					toOWLClassExpression(inclusion.getSubFormulas().get(1)));
		
		return scoa;
	}

	public OWLAxiom toOWLAxiom(Formula inclusion) {

		EChecker ec = new EChecker();
		//RBox
		if (ec.hasRole(inclusion) && !ec.hasRoleRestriction(inclusion)) {
			return factory.getOWLSubObjectPropertyOfAxiom(
					toOWLObjectPropertyExpression(inclusion.getSubFormulas().get(0)),
					toOWLObjectPropertyExpression(inclusion.getSubFormulas().get(1)));
		//ABox
		} else if (inclusion.getSubFormulas().get(0) instanceof Individual) {
			if (inclusion.getSubFormulas().get(1) instanceof Exists
					&& inclusion.getSubFormulas().get(1).getSubFormulas().get(1) instanceof Individual) {
				return factory.getOWLObjectPropertyAssertionAxiom(
						toOWLObjectPropertyExpression(inclusion.getSubFormulas().get(1).getSubFormulas().get(0)),
						toOWLNamedIndividual(inclusion.getSubFormulas().get(0)),
						toOWLNamedIndividual(inclusion.getSubFormulas().get(1).getSubFormulas().get(1)));
			} else {
				return factory.getOWLClassAssertionAxiom(toOWLClassExpression(inclusion.getSubFormulas().get(1)),
						toOWLNamedIndividual(inclusion.getSubFormulas().get(0)));
			}
		//TBox
		} else {
			try {
			return factory.getOWLSubClassOfAxiom(toOWLClassExpression(inclusion.getSubFormulas().get(0)),
					toOWLClassExpression(inclusion.getSubFormulas().get(1)));
			}catch (Exception e) {
				System.out.println(ec.hasRole(inclusion));
				System.out.println(ec.hasRoleRestriction(inclusion));
			}
		}
		return null;
	}
	
	public OWLClassExpression toOWLClassExpression(Formula formula) {

		if (formula instanceof TopConcept) {
			return factory.getOWLThing();
		} else if (formula instanceof BottomConcept) {
			return factory.getOWLNothing();
		} else if (formula instanceof AtomicConcept) {
			OWLClass owlClass = factory.getOWLClass(IRI.create(formula.getText()));
			return owlClass;
		} else if(formula instanceof Individual) {
			return  factory.getOWLObjectOneOf(toOWLNamedIndividual(formula));
		}
		else if (formula instanceof Negation) {
			return factory.getOWLObjectComplementOf(toOWLClassExpression(formula.getSubFormulas().get(0)));
		} else if (formula instanceof Exists) {
			return factory.getOWLObjectSomeValuesFrom(
					toOWLObjectPropertyExpression(formula.getSubFormulas().get(0)),
					toOWLClassExpression(formula.getSubFormulas().get(1)));
		} else if (formula instanceof Forall) {
			return factory.getOWLObjectAllValuesFrom(
					toOWLObjectPropertyExpression(formula.getSubFormulas().get(0)),
					toOWLClassExpression(formula.getSubFormulas().get(1)));
		} else if (formula instanceof And) {
			Set<OWLClassExpression> conjunct_set = new HashSet<>();
			List<Formula> conjunct_list = formula.getSubFormulas();
			for (Formula conjunct : conjunct_list) {
				conjunct_set.add(toOWLClassExpression(conjunct));
			}
			return factory.getOWLObjectIntersectionOf(conjunct_set);
		} else if (formula instanceof Or) {
			Set<OWLClassExpression> disjunct_set = new HashSet<>();
			List<Formula> disjunct_list = formula.getSubFormulas();
			for (Formula disjunct : disjunct_list) {
				disjunct_set.add(toOWLClassExpression(disjunct));
			}
			return factory.getOWLObjectUnionOf(disjunct_set);
		}

		assert false : "Unsupported ClassExpression: " + formula;
		return null;
	}

	public OWLObjectPropertyExpression toOWLObjectPropertyExpression(Formula role) {
		
		if (role instanceof TopRole) {
			return factory.getOWLTopObjectProperty();
		} else if (role instanceof BottomRole) {
			return factory.getOWLBottomObjectProperty();
		} else if (role instanceof AtomicRole) {
		    return factory.getOWLObjectProperty(IRI.create(role.getText()));
		} else if(role instanceof InverseRole) {
			return factory.getOWLObjectInverseOf(
					factory.getOWLObjectProperty(IRI.create(role.getText())));
		} else if(role instanceof And) {//先暂时这样处理
			return factory.getOWLTopObjectProperty();
		}

		assert false : "Unsupported ObjectPropertyExpression: " + role;
		return null;
	}
	
	public OWLNamedIndividual toOWLNamedIndividual(Formula Indi) {

		if (Indi instanceof Individual) {
			return factory.getOWLNamedIndividual(IRI.create(Indi.getText()));
		}

		assert false : "Unsupported ObjectPropertyExpression: " + Indi;
		return null;
	}

}
