//update: 22/07/2014

package bkool.checker
import bkool.utils._

trait Kind
case object Class extends Kind {
	override def toString = "Class"
}
case object SpecialMethod extends Kind {
	override def toString = "Method"
}

case object Method extends Kind {
	override def toString = "Method"
}

case object Parameter extends Kind {
	override def toString = "Parameter"
}
case object Constant extends Kind {
	override def toString = "Constant"
}
case object Variable extends Kind {
	override def toString = "Variable"
}
case object Identifier extends Kind {
	override def toString = "Identifier"
}
case object Attribute extends Kind {
	override def toString = "Attribute"
}

/* These exception classes are used to throw when an error is detected */

/* 
//    k: the kind of the redeclared identifnier; it must be one of the eight above kinds
//    n: the name of the redeclared identifier; 
*/
case class Undeclared(k: Kind, n: String) extends Exception
case class Redeclared(k: Kind, n: String) extends Exception
case class CannotAssignToConstant(s: Assign) extends Exception
case class TypeMismatchInExpression(exp: Expr) extends Exception
case class TypeMismatchInStatement(stmt: Stmt) extends Exception 
case class TypeMismatchInConstant(cons: ConstDecl) extends Exception

/* These exception classes are used by KSTN only */
case class CannotAccessPrivateAttribute(cName: String, attr: String) extends Exception
case class MethodNotReturn(m: String) extends Exception
case class BreakNotInLoop(line:Int) extends Exception
case class ContinueNotInLoop(line:Int) extends Exception
case class NotConstantExpression(exp: Expr) extends Exception

