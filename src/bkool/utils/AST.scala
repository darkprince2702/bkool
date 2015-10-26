package bkool.utils

/**
 * @author nhphung
 */

trait Context
trait AST {
        def accept(v: Visitor, param: Context) =  v.visit(this,param)
}

case class Program(val decl: List[ClassDecl]) extends AST {
        override def toString = "Program(" + decl.mkString("[",",","]") + ")"
        override def accept(v: Visitor, param: Context) = v.visitProgram(this,param)
}


trait Decl extends AST 
case class VarDecl(val variable: Id, val varType: Type) extends Decl {
        override def toString = "VarDecl(" + variable + "," + varType + ")"
        override def accept(v: Visitor, param: Context) = v.visitVarDecl(this,param)
}
case class ConstDecl(val id: Id, val constType: Type, val const: Expr) extends Decl {
        override def toString = "ConstDecl(" + id + "," + constType + "," + const + ")"
        override def accept(v: Visitor, param: Context) = v.visitConstDecl(this,param)
}
case class ParamDecl(val id: Id, val paramType: Type) extends Decl {
        override def toString = "param(" + id + "," + paramType + ")"
        override def accept(v: Visitor, param: Context) = v.visitParamDecl(this,param)
}
case class ClassDecl(val name: Id, val parent: Id, val decl: List[MemDecl]) extends AST {
        override def toString = "ClassDecl(" + name + "," + (if (parent != null) parent + "," else "") + decl.mkString("[",",","]") +")"
        override def accept(v: Visitor, param: Context) = v.visitClassDecl(this,param)
}

trait MemDecl extends AST
trait SIKind extends AST
object Instance extends SIKind {
  override def toString = "Instance"
  override def accept(v: Visitor, param: Context) = v.visitInstance(this,param)
}
object Static extends SIKind {
  override def toString = "Static"
  override def accept(v: Visitor, param: Context) = v.visitStatic(this,param)
}



case class MethodDecl(val kind: SIKind, val name: Id, val param: List[ParamDecl], val returnType: Type,val body: Stmt) extends MemDecl {
        override def toString = "MethodDecl(" + name + "," + kind +"," + param.mkString("[",",","]")  + "," + (if (returnType != null) returnType + "," else "") + body + ")"
        override def accept(v: Visitor, param: Context) = v.visitMethodDecl(this,param)
}

//method implement
case class AttributeDecl(val kind: SIKind, val decl: Decl) extends MemDecl {
        override def toString = "AttributeDecl(" + kind + "," + decl + ")"
        override def accept(v: Visitor, param: Context) = v.visitAttributeDecl(this,param)
}


/*        TYPE        */
trait Type extends AST
object IntType extends Type {
        override def toString = "IntType"
        override def accept(v: Visitor, param: Context) = v.visitIntType(this,param)
}
object FloatType extends Type {
        override def toString = "FloatType"
        override def accept(v: Visitor, param: Context) = v.visitFloatType(this,param)
}
object BoolType extends Type {
        override def toString = "BoolType"
        override def accept(v: Visitor, param: Context) = v.visitBoolType(this,param)
}
object StringType extends Type {
        override def toString = "StringType"
        override def accept(v: Visitor, param: Context) = v.visitStringType(this,param)
}
object VoidType extends Type {
        override def toString = "VoidType"
        override def accept(v: Visitor, param: Context) = v.visitVoidType(this,param)
}
case class ArrayType(val dimen: IntLiteral, val eleType: Type) extends Type {
        override def toString = "ArrayType(" + eleType.toString() + "," + dimen + ")"
        override def accept(v: Visitor, param: Context) = v.visitArrayType(this,param)
}
case class ClassType(val classType: String) extends Type {
        override def toString = "ClassType(" + classType + ")"
        override def accept(v: Visitor, param: Context) = v.visitClassType(this,param)
}


/*        expr        */
trait Expr extends AST 
case class BinaryOp(op: String, left: Expr, right: Expr) extends Expr {
        override def toString = "BinaryOp(" + op + "," + left + "," + right + ")"
        override def accept(v: Visitor, param: Context) = v.visitBinaryOp(this,param)
}
case class UnaryOp(op: String, body: Expr) extends Expr {
        override def toString = "UnaryOp(" + op + "," + body + ")"
        override def accept(v: Visitor, param: Context) = v.visitUnaryOp(this,param)
}
case class NewExpr(val name: Id, val exprs: List[Expr]) extends Expr {
        override def toString = "NewExp(" + name + "," + exprs.mkString("[",",","]") + ")"
        override def accept(v: Visitor, param: Context) = v.visitNewExpr(this,param)
}
case class CallExpr(val cName: Expr, val method: Id, val params: List[Expr]) extends LHS {
        override def toString = "CallExp(" + (if (cName == null) "self" else cName) + "," + method + "," + params.mkString("[",",","]")+ ")"
        override def accept(v: Visitor, param: Context) = v.visitCallExpr(this,param)
}


//LHS ------------------------
trait LHS extends Expr
case class Id(val name: String) extends LHS {
        override def toString = name
        override def accept(v: Visitor, param: Context) = v.visitId(this,param)
}
// element access
case class ArrayCell(arr: Expr, idx: Expr) extends LHS {
        override def toString = "ArrayCell(" + arr + "," + idx + ")"
        override def accept(v: Visitor, param: Context) = v.visitArrayCell(this,param)
}

case class FieldAccess(name: Expr, field: Id) extends LHS {
        override def toString = "FieldAccess(" + name + "," + field + ")"
        override def accept(v: Visitor, param: Context) = v.visitFieldAccess(this,param)
}
/*        STMT        */
trait Stmt extends AST
case class Block(val decl: List[Decl], val stmt: List[Stmt]) extends Stmt {
        override def toString = "Block(" +  decl.mkString("[",",","]") + "," + stmt.mkString("[",",","]") + ")"
        override def accept(v: Visitor, param: Context) = v.visitBlock(this,param)
}
case class Assign(val leftHandSide: LHS, val expr: Expr) extends Stmt {
        override def toString = "Assign(" + leftHandSide + "," + expr + ")"
        override def accept(v: Visitor, param: Context) = v.visitAssign(this,param)
}
case class If(val expr: Expr, val thenStmt: Stmt, val elseStmt: Option[Stmt]) extends Stmt {
        override def toString = "If(" + expr + "," + thenStmt + "," + (if (elseStmt == None) "" else elseStmt.get) + ")"
        override def accept(v: Visitor, param: Context) = v.visitIf(this,param)
}
case class Call(val parent: Expr, val method: Id, val params: List[Expr]) extends Stmt {
        override def toString = "Call(" + parent + "," + method + "," + params.mkString("[",",","]") + ")"
        override def accept(v: Visitor, param: Context) = v.visitCall(this,param)
}
case class While(val expr: Expr, val loop: Stmt) extends Stmt {
        override def toString = "While(" + expr + "," + loop + ")"
        override def accept(v: Visitor, param: Context) = v.visitWhile(this,param)
}

object Break extends Stmt {
        override def toString = "Break()"
        override def accept(v: Visitor, param: Context) = v.visitBreak(this,param)
}
object Continue extends Stmt {
        override def toString = "Continue()"
        override def accept(v: Visitor, param: Context) = v.visitContinue(this,param)
}
case class Return(val expr: Expr) extends Stmt {
        override def toString = "Return(" + expr + ")"
        override def accept(v: Visitor, param: Context) = v.visitReturn(this,param)
}


/*        LITERAL        */
trait Literal extends Expr
case class IntLiteral(val value: Int) extends Literal {
        override def toString = "IntLit(" + value.toString + ")"
        override def accept(v: Visitor, param: Context) = v.visitIntLiteral(this,param)
}
case class FloatLiteral(val value: Float) extends Literal {
        override def toString = "FloatLit(" + value.toString + ")"
        override def accept(v: Visitor, param: Context) = v.visitFloatLiteral(this,param)
}
case class StringLiteral(val value: String) extends Literal {
        override def toString = "StringLit(" + value + ")"
        override def accept(v: Visitor, param: Context) = v.visitStringLiteral(this,param)

}
case class BooleanLiteral(val value: Boolean) extends Literal {
        override def toString = "BoolLit(" + value.toString() + ")"
        override def accept(v: Visitor, param: Context) = v.visitBooleanLiteral(this,param)
}
object NullLiteral extends Literal {
        override def toString = "Null()"
        override def accept(v: Visitor, param: Context) = v.visitNullLiteral(this,param)
}
object SelfLiteral extends Literal {
        override def toString = "Self()"
        override def accept(v: Visitor, param: Context) = v.visitSelfLiteral(this,param)
}

