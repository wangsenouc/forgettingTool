package roles;
import org.apache.commons.lang3.builder.HashCodeBuilder;

public class BottomRole extends RoleExpression {

	private static final BottomRole BR = new BottomRole();

	public BottomRole() {
		super("\u25B3");
	}

	public static BottomRole getInstance() {
		return BR;
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
