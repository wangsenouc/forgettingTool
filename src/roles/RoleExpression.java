package roles;
import java.util.List;
import formula.Formula;

public class RoleExpression extends Formula {

	public RoleExpression() {
		super();
	}

	public RoleExpression(String str) {
		super(str);
	}
	
	public RoleExpression(Formula formula) {
		super(1);
		this.setSubFormulas(formula);
	}
		
	public RoleExpression(List<Formula> list) {
		super(list.size());
		this.setSubFormulas(list);
	}

}
