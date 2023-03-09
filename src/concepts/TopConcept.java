package concepts;

import org.apache.commons.lang3.builder.HashCodeBuilder;

public class TopConcept extends ConceptExpression {

	private static final TopConcept TC = new TopConcept();

	public TopConcept() {
		super("\u22A4");
	}

	public static TopConcept getInstance() {
		return TC;
	}

	@Override
	public String toString() {
		return this.getText();
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(17, 37).append(this.getClass()).toHashCode();
	}
}
