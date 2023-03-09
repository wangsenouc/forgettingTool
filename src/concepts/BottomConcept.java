package concepts;

import org.apache.commons.lang3.builder.HashCodeBuilder;

public class BottomConcept extends ConceptExpression {

	private static final BottomConcept BC = new BottomConcept();

	public BottomConcept() {
		super("\u22A5");
	}

	public static BottomConcept getInstance() {
		return BC;
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
