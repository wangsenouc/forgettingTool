package roles;

public class InverseRole extends RoleExpression {
	public InverseRole() {
		super();
	}
	public InverseRole(String str) {
		super(str);
	}
	@Override
	public String toString() {
		return this.getText() + "\u207B";
	}
	public String getRoleStr() {
		return this.getText();
	}
}
