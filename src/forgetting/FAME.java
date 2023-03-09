package forgetting;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashSet;
import java.util.Set;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.IRIDocumentSource;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyLoaderConfiguration;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;


public class FAME {

	public static void compute_diff(OWLOntology signature, OWLOntology ontology, BufferedWriter bf, int conceptPercent, int rolePercent, String filePath)
			throws OWLOntologyCreationException, CloneNotSupportedException, OWLOntologyStorageException, IOException, InterruptedException {
//随机方式1
//		List<OWLClass> c_sig_all = new ArrayList<OWLClass>(signature.getClassesInSignature());
//		Set<OWLObjectProperty> r_sig_all = signature.getObjectPropertiesInSignature();
//		Collections.shuffle(c_sig_all);
//		int range = (int)Math.round(c_sig_all.size() * 0.1);
//		Set<OWLClass> c_sig = new HashSet<>(c_sig_all.subList(0, range));
//		Set<OWLObjectProperty> r_sig = new HashSet<>();
//随机方式1	
		
//随机方式2	
		Set<OWLClass> c_sig_all = new HashSet<OWLClass>();
		Set<OWLClass> c_sig = new HashSet<OWLClass>();
		c_sig_all.addAll(signature.getClassesInSignature());
		Set<OWLObjectProperty> r_sig_all = new HashSet<OWLObjectProperty>();
		Set<OWLObjectProperty> r_sig = new HashSet<OWLObjectProperty>();
		r_sig_all.addAll(signature.getObjectPropertiesInSignature());
		int c_sig_size = (int) Math.round(c_sig_all.size() * conceptPercent / 100.0);
		int r_sig_size = (int) Math.round(r_sig_all.size() * rolePercent / 100.0);

		for (OWLClass concept : c_sig_all) {
			c_sig_size--;
			if(c_sig_size < 0)
				break;
			c_sig.add(concept);
		}
		for (OWLObjectProperty role : r_sig_all) {
		r_sig_size--;
		if(r_sig_size < 0)
			break;
		r_sig.add(role);
		}
//随机方式2
		Forgetter forgetter = new Forgetter();
		forgetter.Forgetting(c_sig, r_sig, ontology, bf, filePath);
		
	}


	public static void main(String[] args)
			throws OWLOntologyCreationException, CloneNotSupportedException, OWLOntologyStorageException, IOException, InterruptedException {
		String filePath1 = "F:\\我的大学\\毕业论文\\BioPortal\\BioPortal\\PARTIII\\icps.international-classification-for-patient-safety.7.owl.xml";
		int conceptPercent = 0;
		int rolePercent = 40;
		if(args.length > 0) {
			filePath1 = args[0];
		}
		if(args.length > 1) {
			conceptPercent = Integer.valueOf(args[1]);
		}
		if(args.length > 2) {
			rolePercent = Integer.valueOf(args[2]);
		}
		OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
		File file1 = new File(filePath1);
		IRI iri1 = IRI.create(file1);
		OWLOntology onto_1 = manager1.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri1),
				new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(false));
		String logsPath = "F:\\logs\\";
		if(conceptPercent == 0) {
			logsPath += "Role" + rolePercent + ".txt";
		}else {
			logsPath += "Concept" + conceptPercent + ".txt";
		}
		BufferedWriter bf = new BufferedWriter(new FileWriter(logsPath, true));
		bf.write(filePath1 + "\n");
		compute_diff(onto_1, onto_1, bf, conceptPercent, rolePercent, filePath1);	
		bf.close();
		
	}

}
