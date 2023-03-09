package concepts;

import org.apache.commons.lang3.builder.HashCodeBuilder;

public class AtomicConcept extends ConceptExpression implements Comparable<AtomicConcept> {
		
	private static int definer_index = 1;
	public int occurenceTimes = 0;//此概念在本体中正出现和负出现的最小值
	public boolean isPositive = false;
	public int restrictionTimes = 0;//关系限制的最小值
	public AtomicConcept() {
		super();
	}

	public AtomicConcept(String str) {
		super(str);
	}

	@Override
	public String toString() {
		return this.getText();
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(17, 37).append(this.getText()).toHashCode();
	}

	@Override
	public int compareTo(AtomicConcept concept) {
		//int i = this.getText().compareTo(concept.getText());
		int i = 0;
		if(this.restrictionTimes == concept.restrictionTimes) {
			if(this.occurenceTimes > concept.occurenceTimes)
				i = 1;
			else if(this.occurenceTimes < concept.occurenceTimes)
				i= -1;
			else 
				i= 0;	
		}else if(this.restrictionTimes > concept.restrictionTimes) {
			i = 1;
		}else {
			i = -1;
		}
		
		return i;
	}

	public static int getDefiner_index() {
		return definer_index;
	}

	public static void setDefiner_index(int definer_index) {
		AtomicConcept.definer_index = definer_index;
	}

}
