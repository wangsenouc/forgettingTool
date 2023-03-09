package convertion;

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
import roles.RoleExpression;
import roles.TopRole;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointUnionAxiom;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectInverseOf;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;

import com.google.common.collect.Sets;

public class Converter {
		
	public AtomicConcept getConceptfromClass(OWLEntity owlClass) {
		return new AtomicConcept(owlClass.getIRI().toString());
	}
	
	public AtomicRole getRoleFromObjectProperty(OWLEntity owlObjectProperty) {		
		return new AtomicRole(owlObjectProperty.getIRI().toString());
	}
	
	public Individual getIndividualFromNamedIndividual(OWLNamedIndividual owlNamedIndividual) {		
		return new Individual(owlNamedIndividual.getIRI().toString());
	}
	
	public Set<AtomicConcept> getConceptsfromClasses(Set<OWLClass> class_set) {

		Set<AtomicConcept> concept_set = new HashSet<>();
		for (OWLClass owlClass : class_set) {
			concept_set.add(getConceptfromClass(owlClass));
		}

		return concept_set;
	}
		
	public Set<AtomicRole> getRolesfromObjectProperties(Set<OWLObjectProperty> op_set) {

		Set<AtomicRole> role_set = new HashSet<>();

		for (OWLObjectProperty owlObjectProperty : op_set) {
			role_set.add(getRoleFromObjectProperty(owlObjectProperty));
		}

		return role_set;
	}
				
	public List<AtomicConcept> getConceptsInSignature(OWLOntology ontology) {

		List<AtomicConcept> concept_list = new ArrayList<>();
		Set<OWLClass> class_set = ontology.getClassesInSignature();

		for (OWLClass owlClass : class_set) {
			concept_list.add(getConceptfromClass(owlClass));
		}

		return concept_list;
	}
		
	public List<AtomicRole> getRolesInSignature(OWLOntology ontology) {

		List<AtomicRole> role_list = new ArrayList<>();
		Set<OWLObjectProperty> op_set = ontology.getObjectPropertiesInSignature();

		for (OWLObjectProperty owlObjectProperty : op_set) {
			role_list.add(getRoleFromObjectProperty(owlObjectProperty));
		}

		return role_list;
	}
	
	public List<Formula> OntologyConverter(OWLOntology ontology) {

		List<Formula> formula_list = new ArrayList<>();		
		Set<OWLLogicalAxiom> owlAxiom_set = ontology.getLogicalAxioms();

		for (OWLAxiom owlAxiom : owlAxiom_set) {
			formula_list.addAll(AxiomConverter(owlAxiom));
		}

		return formula_list;
	}
	
	public List<Formula> AxiomsConverter(Set<OWLAxiom> owlAxiom_set) {

		List<Formula> formula_list = new ArrayList<>();

		for (OWLAxiom owlAxiom : owlAxiom_set) {
			formula_list.addAll(AxiomConverter(owlAxiom));
		}

		return formula_list;
	}
		
	public List<Formula> AxiomConverter(OWLAxiom axiom) {

		if(axiom instanceof OWLSubObjectPropertyOfAxiom) {
			OWLSubObjectPropertyOfAxiom owlSOPOA = (OWLSubObjectPropertyOfAxiom) axiom;
			Formula converted = new Inclusion(RoleExpressionConverter(owlSOPOA.getSubProperty()),
					RoleExpressionConverter(owlSOPOA.getSuperProperty()));
			return Collections.singletonList(converted);
		}
		else if (axiom instanceof OWLSubClassOfAxiom) {
			OWLSubClassOfAxiom owlSCOA = (OWLSubClassOfAxiom) axiom;
			Formula param1 = ClassExpressionConverter(owlSCOA.getSubClass());
			OWLClassExpression tempOwlClassExpression  = owlSCOA.getSuperClass();
			Formula param2 = ClassExpressionConverter(tempOwlClassExpression);
			Formula converted = new Inclusion(param1, 
					param2);
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLEquivalentClassesAxiom) {
			OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
			Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlECA.asOWLSubClassOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
				converted.addAll(AxiomConverter(owlSCOA));
			}
			return converted;

		} else if (axiom instanceof OWLDisjointClassesAxiom) {
			OWLDisjointClassesAxiom owlDCA = (OWLDisjointClassesAxiom) axiom;
			Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlDCA.asOWLSubClassOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
				converted.addAll(AxiomConverter(owlSCOA));
			}
			return converted;

		} else if (axiom instanceof OWLDisjointUnionAxiom) {
			OWLDisjointUnionAxiom owlDUA = (OWLDisjointUnionAxiom) axiom;
			OWLEquivalentClassesAxiom owlECA = owlDUA.getOWLEquivalentClassesAxiom();
			OWLDisjointClassesAxiom owlDCA = owlDUA.getOWLDisjointClassesAxiom();
			List<Formula> converted = new ArrayList<>();
			converted.addAll(AxiomConverter(owlECA));
			converted.addAll(AxiomConverter(owlDCA));
			return converted;

		} else if (axiom instanceof OWLObjectPropertyDomainAxiom) {
			OWLObjectPropertyDomainAxiom owlOPDA = (OWLObjectPropertyDomainAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlOPDA.asOWLSubClassOfAxiom();
			return AxiomConverter(owlSCOA);

		} else if (axiom instanceof OWLObjectPropertyRangeAxiom) {
			OWLObjectPropertyRangeAxiom owlOPRA = (OWLObjectPropertyRangeAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlOPRA.asOWLSubClassOfAxiom();
			return AxiomConverter(owlSCOA);

		} 

		return Collections.emptyList();
	}
	
	
	private Formula ClassExpressionConverter(OWLClassExpression concept) {
	
		if (concept.isTopEntity()) {
			return TopConcept.getInstance();

		} else if (concept.isBottomEntity()) {
			return BottomConcept.getInstance();

		} else if (concept instanceof OWLClass) {
			OWLClass owlClass = (OWLClass) concept;
			String str = owlClass.getIRI().toString();
			return new AtomicConcept(str);

		} else if (concept instanceof OWLObjectComplementOf) {
			OWLObjectComplementOf owlOCO = (OWLObjectComplementOf) concept;
			return new Negation(ClassExpressionConverter(owlOCO.getOperand()));

		} else if (concept instanceof OWLObjectSomeValuesFrom) {
			OWLObjectSomeValuesFrom owlOSVF = (OWLObjectSomeValuesFrom) concept;
			return new Exists(RoleExpressionConverter(owlOSVF.getProperty()),
					ClassExpressionConverter(owlOSVF.getFiller()));

		} else if (concept instanceof OWLObjectAllValuesFrom) {
			OWLObjectAllValuesFrom owlOAVF = (OWLObjectAllValuesFrom) concept;
			OWLObjectPropertyExpression temExpression1 = owlOAVF.getProperty();
			RoleExpression tempRoleExpression = RoleExpressionConverter(temExpression1);
			OWLClassExpression tempClassExpression = owlOAVF.getFiller();
			Formula tempFormula = ClassExpressionConverter(tempClassExpression);
			return new Forall(tempRoleExpression,
					tempFormula);

		} else if (concept instanceof OWLObjectIntersectionOf) {
			OWLObjectIntersectionOf owlOIO = (OWLObjectIntersectionOf) concept;
			List<Formula> conjunct_list = new ArrayList<>();
			for (OWLClassExpression conjunct : owlOIO.getOperands()) {
				conjunct_list.add(ClassExpressionConverter(conjunct));
			}
			return new And(conjunct_list);

		} else if (concept instanceof OWLObjectUnionOf) {
			OWLObjectUnionOf owlOUO = (OWLObjectUnionOf) concept;
			List<Formula> disjunct_list = new ArrayList<>();
			for (OWLClassExpression disjunct : owlOUO.getOperands()) {
				disjunct_list.add(ClassExpressionConverter(disjunct));
			}
			return new Or(disjunct_list);
		}else if(concept instanceof OWLObjectOneOf) {//新加方法
			OWLObjectOneOf owlOO = (OWLObjectOneOf) concept;
			Set<OWLNamedIndividual> set_owlNI= owlOO.getIndividualsInSignature();
			for(OWLNamedIndividual individual : set_owlNI) {
				String str = individual.getIRI().toString();
				return new Individual( str);	
			}
		}

		return TopConcept.getInstance();
	}
	
	private RoleExpression RoleExpressionConverter(OWLObjectPropertyExpression role) {

		if (role.isTopEntity()) {
			return TopRole.getInstance();
			
		} else if (role.isBottomEntity()) {
			return BottomRole.getInstance();
			
		} else if (role instanceof OWLObjectProperty) {
			OWLObjectProperty owlOP = (OWLObjectProperty) role;	
			String str = owlOP.getIRI().toString();
			return new AtomicRole(str);
			
		}else if(role instanceof OWLObjectInverseOf) {//新加方法			
			OWLObjectInverseOf owlOI = (OWLObjectInverseOf) role;	
			OWLObjectProperty owlOP = (OWLObjectProperty) owlOI.getInverse();
			String str = owlOP.getIRI().toString();
			return new InverseRole(str);
			
		}

		return TopRole.getInstance();
		
	}
	
	public OWLOntology toOWLSubClassOfAxiom(OWLOntology onto) throws OWLOntologyCreationException {

		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		OWLOntology onto_prime = manager.createOntology(IRI.generateDocumentIRI());
		for (OWLLogicalAxiom axiom : onto.getLogicalAxioms()) {
			manager.addAxioms(onto_prime, toOWLSubClassOfAxiom(axiom));
			manager.addAxioms(onto_prime, toOWLSubObjectPropertyOfAxiom(axiom));
		}

		return onto_prime;
	}
	public Set<OWLSubObjectPropertyOfAxiom> toOWLSubObjectPropertyOfAxiom(OWLLogicalAxiom axiom) {
		if(axiom instanceof OWLSubObjectPropertyOfAxiom) {
			OWLSubObjectPropertyOfAxiom owlSOPOA = (OWLSubObjectPropertyOfAxiom) axiom;
			return Collections.singleton(owlSOPOA);
		}else if(axiom instanceof OWLEquivalentObjectPropertiesAxiom) {
			OWLEquivalentObjectPropertiesAxiom owlEOPA = (OWLEquivalentObjectPropertiesAxiom) axiom;
			return owlEOPA.asSubObjectPropertyOfAxioms();
		}
		
		return Collections.emptySet();
	}
	
	public Set<OWLSubClassOfAxiom> toOWLSubClassOfAxiom(OWLLogicalAxiom axiom) {
		if (axiom instanceof OWLSubClassOfAxiom) {
			OWLSubClassOfAxiom owlSCOA = (OWLSubClassOfAxiom) axiom;
			return Collections.singleton(owlSCOA);

		} else if (axiom instanceof OWLEquivalentClassesAxiom) {
			OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
			return owlECA.asOWLSubClassOfAxioms();

		} else if (axiom instanceof OWLDisjointClassesAxiom) {
			OWLDisjointClassesAxiom owlDCA = (OWLDisjointClassesAxiom) axiom;
			return owlDCA.asOWLSubClassOfAxioms();

		} else if (axiom instanceof OWLDisjointUnionAxiom) {
			OWLDisjointUnionAxiom owlDUA = (OWLDisjointUnionAxiom) axiom;
			return Sets.union(owlDUA.getOWLEquivalentClassesAxiom().asOWLSubClassOfAxioms(),
					owlDUA.getOWLDisjointClassesAxiom().asOWLSubClassOfAxioms());

		} else if (axiom instanceof OWLObjectPropertyDomainAxiom) {
			OWLObjectPropertyDomainAxiom owlOPDA = (OWLObjectPropertyDomainAxiom) axiom;
			return Collections.singleton(owlOPDA.asOWLSubClassOfAxiom());

		} else if (axiom instanceof OWLObjectPropertyRangeAxiom) {
			OWLObjectPropertyRangeAxiom owlOPRA = (OWLObjectPropertyRangeAxiom) axiom;
			return Collections.singleton(owlOPRA.asOWLSubClassOfAxiom());
			
		} else if(axiom instanceof OWLClassAssertionAxiom) {//新加方法
			OWLClassAssertionAxiom owlacc = (OWLClassAssertionAxiom) axiom;
			return Collections.singleton(owlacc.asOWLSubClassOfAxiom());
		} else if(axiom instanceof OWLObjectPropertyAssertionAxiom) {//新加方法
			OWLObjectPropertyAssertionAxiom owlOPA = (OWLObjectPropertyAssertionAxiom)axiom;
			return Collections.singleton(owlOPA.asOWLSubClassOfAxiom());
			
		}

		return Collections.emptySet();
	}
}
