package roles;
import org.apache.commons.lang3.builder.HashCodeBuilder;

public class AtomicRole extends RoleExpression implements Comparable<AtomicRole> {
	
	public AtomicRole() {
		super();
	}

	public AtomicRole(String str) {
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
	public int compareTo(AtomicRole atomicRole) {
		int i = this.getText().compareTo(atomicRole.getText());
		return i;
	}

}
