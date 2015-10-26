package bkool.checker

/**
 * @author nhphung
 */

import bkool.parser._
import bkool.utils._
import java.io.{ PrintWriter, File }
import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree._
import scala.collection.JavaConverters._

class StaticChecker(ast: AST) {
  def check() = {
    val bldecls = new GlobalEnvironment()
    val env = bldecls.visit(ast, null).asInstanceOf[SymbolList]
    val ce = new ClassEnvironment();
    val clenv = ce.visit(ast, null).asInstanceOf[GlobalSymbolList]
    val tc = new TypeChecking(clenv)
    tc.visit(ast, null)
  }
}

class GlobalEnvironment extends CheckingVisitor {
  override def visitProgram(ast: Program, c: Context) = ast.decl.foldLeft(SymbolList(List[(String, Type, Kind)](("io", ClassType("io"), Class))))((x, y) => visit(y, x).asInstanceOf[SymbolList])

  override def visitVarDecl(ast: VarDecl, c: Context) = {
    val env = c.asInstanceOf[SymbolList].list
    val newenv = if (env.exists(x => x._1 == ast.variable.toString())) throw Redeclared(Attribute, ast.variable.toString()) else (ast.variable.toString(), ast.varType, Variable) :: env
    SymbolList(newenv)
  }

  override def visitConstDecl(ast: ConstDecl, c: Context) = {
    val env = c.asInstanceOf[SymbolList].list
    val newenv = if (env.exists(x => x._1 == ast.id.toString())) throw Redeclared(Attribute, ast.id.toString()) else (ast.id.toString(), ast.constType, Constant) :: env
    SymbolList(newenv)
  }

  override def visitClassDecl(ast: ClassDecl, c: Context) = {
    val env = c.asInstanceOf[SymbolList].list
    val newenv = if (env.exists(x => x._1 == ast.name.toString())) throw Redeclared(Class, ast.name.toString()) else (ast.name.toString(), ClassType(ast.name.toString()), Class) :: env
    ast.decl.foldLeft(SymbolList(List[(String, Type, Kind)]()).asInstanceOf[Context])((x, y) => visit(y, x).asInstanceOf[SymbolList])
    SymbolList(newenv)
  }

  override def visitMethodDecl(ast: MethodDecl, c: Context) = {
    val env = c.asInstanceOf[SymbolList].list
    if (env.exists(x => x._1 == ast.name.toString())) throw Redeclared(Method, ast.name.name)
    val newenv = if (env.exists(x => x._1 == ast.name.toString())) throw Redeclared(Method, ast.name.name) else (ast.name.toString(), ast.returnType, if (ast.returnType != null) Method else SpecialMethod) :: env
    SymbolList(newenv)
  }

  override def visitAttributeDecl(ast: AttributeDecl, c: Context) = visit(ast.decl, c)
}

class ClassEnvironment extends CheckingVisitor {
  override def visitProgram(ast: Program, c: Context) = ast.decl.foldLeft(GlobalSymbolList(List(ClassSymbolList("io", "", SymbolList(List(("writeStrLn", VoidType, Method), ("writeStr", VoidType, Method), ("readStr", StringType, Method), ("writeBoolLn", VoidType, Method), ("writeBool", VoidType, Method), ("readBool", BoolType, Method), ("writeFloatLn", VoidType, Method), ("writeFloat", VoidType, Method), ("readFloat", FloatType, Method), ("writeIntLn", VoidType, Method), ("writeInt", VoidType, Method), ("readInt", IntType, Method)))))))((x, y) => visit(y, x).asInstanceOf[GlobalSymbolList])

  override def visitVarDecl(ast: VarDecl, c: Context) = {
    val env = c.asInstanceOf[SymbolList].list
    val newenv = if (env.exists(x => x._1 == ast.variable.toString())) throw Redeclared(Attribute, ast.variable.toString()) else (ast.variable.toString(), ast.varType, Attribute) :: env
    SymbolList(newenv)
  }

  override def visitConstDecl(ast: ConstDecl, c: Context) = {
    val env = c.asInstanceOf[SymbolList].list
    val newenv = if (env.exists(x => x._1 == ast.id.toString())) throw Redeclared(Attribute, ast.id.toString()) else (ast.id.toString(), ast.constType, Attribute) :: env
    SymbolList(newenv)
  }

  override def visitClassDecl(ast: ClassDecl, c: Context) = {
    val globalList = c.asInstanceOf[GlobalSymbolList].list
    if (globalList.exists(x => x.name == ast.name.toString())) throw Redeclared(Class, ast.name.toString())
    val attributeList = ast.decl.foldLeft(SymbolList(List[(String, Type, Kind)]()).asInstanceOf[Context])((x, y) => visit(y, x).asInstanceOf[SymbolList]).asInstanceOf[SymbolList]
    GlobalSymbolList(ClassSymbolList(ast.name.name, ast.parent.name, attributeList) :: globalList)
  }

  override def visitMethodDecl(ast: MethodDecl, c: Context) = {
    val env = c.asInstanceOf[SymbolList].list
    if (env.exists(x => x._1 == ast.name.toString())) throw Redeclared(Method, ast.name.name)
    val newenv = if (env.exists(x => x._1 == ast.name.toString())) throw Redeclared(Method, ast.name.name) else (ast.name.toString(), ast.returnType, if (ast.returnType != null) Method else SpecialMethod) :: env
    SymbolList(newenv)
  }

  override def visitAttributeDecl(ast: AttributeDecl, c: Context) = visit(ast.decl, c)
}

class TypeChecking(clenv: GlobalSymbolList) extends CheckingVisitor with Utils {
  var parammeterFlag = false;
  var memberAccessFlag = false;

  override def visitProgram(ast: Program, c: Context) = ast.decl.map(visit(_, null))

  override def visitClassDecl(ast: ClassDecl, c: Context) = {
    if (!ast.parent.name.isEmpty()) {
      val parentClass = lookup(ast.parent.name, clenv.list, (x: ClassSymbolList) => x.name)
      parentClass match {
        case None => throw Undeclared(Class, ast.parent.name)
        case Some(_) =>
      }
    }
    val newenv = ClassSymbolList(ast.name.name, ast.parent.name, SymbolList(List[(String, Type, Kind)]()))
    ast.decl.filter(_.isInstanceOf[AttributeDecl]).foldLeft(newenv)((x, y) => visit(y, x).asInstanceOf[ClassSymbolList])
    ast.decl.filter(_.isInstanceOf[MethodDecl]).map(visit(_, newenv))
  }

  override def visitAttributeDecl(ast: AttributeDecl, c: Context) = visit(ast.decl, c)

  override def visitMethodDecl(ast: MethodDecl, c: Context) = {
    if (ast.returnType != null) visit(ast.returnType, c)
    val classenv = c.asInstanceOf[ClassSymbolList]
    val locenv = ast.param.foldLeft(ClassSymbolList(classenv.name, classenv.parent, SymbolList(List[(String, Type, Kind)]())).asInstanceOf[Context])((x, y) => visit(y, x).asInstanceOf[ClassSymbolList])
    parammeterFlag = true
    visit(ast.body, locenv)
  }

  override def visitParamDecl(ast: ParamDecl, c: Context): Object = {
    if (ast.paramType.isInstanceOf[ClassType])
      visit(ast.paramType, c)
    val classenv = c.asInstanceOf[ClassSymbolList]
    val oldenv = classenv.symlst.list
    val newenv = if (oldenv.exists(x => x._1 == ast.id.toString())) throw Redeclared(Parameter, ast.id.toString()) else (ast.id.toString(), ast.paramType, Parameter) :: oldenv
    ClassSymbolList(classenv.name, classenv.parent, SymbolList(newenv))
  }

  override def visitVarDecl(ast: VarDecl, c: Context) = {
    visit(ast.varType, c)
    val classenv = c.asInstanceOf[ClassSymbolList]
    val oldenv = classenv.symlst.list
    val newenv = if (oldenv.exists(x => x._1 == ast.variable.toString())) throw Redeclared(Variable, ast.variable.toString()) else (ast.variable.toString(), ast.varType, Variable) :: oldenv
    ClassSymbolList(classenv.name, classenv.parent, SymbolList(newenv))
  }

  override def visitConstDecl(ast: ConstDecl, c: Context) = {
    visit(ast.constType, c)
    visit(ast.const, c)
    val classenv = c.asInstanceOf[ClassSymbolList]
    val oldenv = classenv.symlst.list
    val newenv = if (oldenv.exists(x => x._1 == ast.id.toString())) throw Redeclared(Constant, ast.id.toString()) else (ast.id.toString(), ast.constType, Constant) :: oldenv
    ClassSymbolList(classenv.name, classenv.parent, SymbolList(newenv))
  }

  override def visitArrayType(ast: ArrayType, c: Context) = {
    visit(ast.eleType, c)
  }

  override def visitClassType(ast: ClassType, c: Context) = {
    val findClass = lookup(ast.classType, clenv.list, (x: ClassSymbolList) => x.name)
    findClass match {
      case None => throw Undeclared(Class, ast.classType)
      case Some(t) => c
    }
  }

  override def visitBinaryOp(ast: BinaryOp, c: Context) = {
    val typeOfLeft = visit(ast.left, c)
    val typeOfRight = visit(ast.right, c)
    typeOfRight
  }

  override def visitUnaryOp(ast: UnaryOp, c: Context) = {
    visit(ast.body, c)
  }

  override def visitNewExpr(ast: NewExpr, c: Context) = {
    ast.exprs.map(visit(_, c))
    val findClass = lookup(ast.name.name, clenv.list, (x: ClassSymbolList) => x.name)
    findClass match {
      case None => throw Undeclared(Class, ast.name.name)
      case Some(t) => ClassType(t.name)
    }
  }

  override def visitCallExpr(ast: CallExpr, c: Context) = {
    ast.params.map(visit(_, c))
    if (ast.cName.isInstanceOf[Id]) memberAccessFlag = true
    val callType = visit(ast.cName, c)
    callType match {
      case ClassType(name) => {
        val findClass = lookup(name, clenv.list, (x: ClassSymbolList) => x.name)
        findClass match {
          case None => throw Undeclared(Class, name)
          case Some(t) => {
            val method = lookupInClass(ast.method.name, t, clenv.list)
            method match {
              case None => throw Undeclared(Method, ast.method.name)
              case Some(t) => if (t._3 != Method) throw Undeclared(Method, ast.method.name) else {
                t._2
              }
            }
          }
        }
      }
      case _ => callType
    }
  }

  override def visitId(ast: Id, c: Context) = {
    val env = c.asInstanceOf[ClassSymbolList].symlst.list
    val id = lookup(ast.name, env, (x: (String, Type, Kind)) => x._1)
    id match {
      case None => {
        memberAccessFlag match {
          case true => {
            val findClass = lookup(ast.name, clenv.list, (x: ClassSymbolList) => x.name)
            findClass match {
              case None => throw Undeclared(Identifier, ast.name)
              case Some(t) => {
                memberAccessFlag = false;
                ClassType(ast.name)
              }
            }
          }
          case false => throw Undeclared(Identifier, ast.name)
        }
      }
      case Some(t) => t._2
    }
  }

  override def visitArrayCell(ast: ArrayCell, c: Context) = {
    visit(ast.idx, c)
    val arrayType = visit(ast.arr, c)
    arrayType match {
      case ArrayType(_, t) => t
      case _ => arrayType
    }
  }

  override def visitFieldAccess(ast: FieldAccess, c: Context) = {
    if (ast.name.isInstanceOf[Id]) memberAccessFlag = true
    val fieldType = visit(ast.name, c)
    fieldType match {
      case ClassType(name) => {
        val findClass = lookup(name, clenv.list, (x: ClassSymbolList) => x.name)
        findClass match {
          case None => throw Undeclared(Class, name)
          case Some(t) => {
            val field = lookupInClass(ast.field.name, t, clenv.list)
            field match {
              case None => throw Undeclared(Attribute, ast.field.name)
              case Some(t) => if (t._3 != Attribute) throw Undeclared(Attribute, ast.field.name) else {
                t._2
              }
            }
          }
        }
      }
      case _ => fieldType
    }
  }

  override def visitBlock(ast: Block, c: Context) = {
    val classenv = c.asInstanceOf[ClassSymbolList]
    val env = if (parammeterFlag == true) {
      parammeterFlag = false
      c.asInstanceOf[ClassSymbolList]
    } else ClassSymbolList(classenv.name, classenv.parent, SymbolList(List[(String, Type, Kind)]()))
    val newenv = ast.decl.foldLeft(env)((x, y) => visit(y, x).asInstanceOf[ClassSymbolList])
    ast.stmt.map(visit(_, ClassSymbolList(classenv.name, classenv.parent, SymbolList(classenv.symlst.list ++ newenv.symlst.list))))
    c
  }

  override def visitAssign(ast: Assign, c: Context) = {
    visit(ast.leftHandSide, c)
    visit(ast.expr, c)
    c
  }

  override def visitIf(ast: If, c: Context) = {
    visit(ast.expr, c)
    visit(ast.thenStmt, c)
    ast.elseStmt match {
      case None =>
      case Some(t) => visit(t, c)
    }
    c
  }

  override def visitCall(ast: Call, c: Context) = {
    ast.params.map(visit(_, c))
    if (ast.parent.isInstanceOf[Id]) memberAccessFlag = true
    val callType = visit(ast.parent, c)
    callType match {
      case ClassType(name) => {
        val findClass = lookup(name, clenv.list, (x: ClassSymbolList) => x.name)
        findClass match {
          case None => throw Undeclared(Class, name)
          case Some(t) => {
            val method = lookupInClass(ast.method.name, t, clenv.list)
            method match {
              case None => throw Undeclared(Method, ast.method.name)
              case Some(t) => if (t._3 != Method) throw Undeclared(Method, ast.method.name) else c
            }
          }
        }
      }
      case _ => c
    }
  }
  override def visitWhile(ast: While, c: Context) = {
    visit(ast.expr, c)
    visit(ast.loop, c)
    c
  }

  override def visitReturn(ast: Return, c: Context) = {
    visit(ast.expr, c)
    c
  }

  override def visitIntLiteral(ast: IntLiteral, c: Context) = IntType

  override def visitFloatLiteral(ast: FloatLiteral, c: Context) = FloatType

  override def visitStringLiteral(ast: StringLiteral, c: Context) = StringType

  override def visitBooleanLiteral(ast: BooleanLiteral, c: Context) = BoolType

  override def visitNullLiteral(ast: NullLiteral.type, c: Context) = NullType

  override def visitSelfLiteral(ast: SelfLiteral.type, c: Context) = {
    ClassType(c.asInstanceOf[ClassSymbolList].name)
  }
}

class CheckingVisitor extends Visitor {
  override def visit(ast: AST, c: Context): Object = ast.accept(this, c)
  override def visitProgram(ast: Program, c: Context): Object = c
  override def visitVarDecl(ast: VarDecl, c: Context): Object = c
  override def visitConstDecl(ast: ConstDecl, c: Context): Object = c
  override def visitParamDecl(ast: ParamDecl, c: Context): Object = c
  override def visitClassDecl(ast: ClassDecl, c: Context): Object = c
  override def visitMethodDecl(ast: MethodDecl, c: Context): Object = c
  override def visitAttributeDecl(ast: AttributeDecl, c: Context): Object = c
  override def visitInstance(ast: Instance.type, c: Context): Object = c
  override def visitStatic(ast: Static.type, c: Context): Object = c
  override def visitIntType(ast: IntType.type, c: Context): Object = c
  override def visitFloatType(ast: FloatType.type, c: Context): Object = c
  override def visitBoolType(ast: BoolType.type, c: Context): Object = c
  override def visitStringType(ast: StringType.type, c: Context): Object = c
  override def visitVoidType(ast: VoidType.type, c: Context): Object = c
  override def visitArrayType(ast: ArrayType, c: Context): Object = c
  override def visitClassType(ast: ClassType, c: Context): Object = c
  override def visitBinaryOp(ast: BinaryOp, c: Context): Object = c
  override def visitUnaryOp(ast: UnaryOp, c: Context): Object = c
  override def visitNewExpr(ast: NewExpr, c: Context): Object = c
  override def visitCallExpr(ast: CallExpr, c: Context): Object = c
  override def visitId(ast: Id, c: Context): Object = c
  override def visitArrayCell(ast: ArrayCell, c: Context): Object = c
  override def visitFieldAccess(ast: FieldAccess, c: Context): Object = c
  override def visitBlock(ast: Block, c: Context): Object = c
  override def visitAssign(ast: Assign, c: Context): Object = c
  override def visitIf(ast: If, c: Context): Object = c
  override def visitCall(ast: Call, c: Context): Object = c
  override def visitWhile(ast: While, c: Context): Object = c
  override def visitBreak(ast: Break.type, c: Context): Object = c
  override def visitContinue(ast: Continue.type, c: Context): Object = c
  override def visitReturn(ast: Return, c: Context): Object = c
  override def visitIntLiteral(ast: IntLiteral, c: Context): Object = c
  override def visitFloatLiteral(ast: FloatLiteral, c: Context): Object = c
  override def visitStringLiteral(ast: StringLiteral, c: Context): Object = c
  override def visitBooleanLiteral(ast: BooleanLiteral, c: Context): Object = c
  override def visitNullLiteral(ast: NullLiteral.type, c: Context): Object = c
  override def visitSelfLiteral(ast: SelfLiteral.type, c: Context): Object = c
}

case class SymbolList(list: List[(String, Type, Kind)]) extends Context
case class ClassSymbolList(name: String, parent: String, symlst: SymbolList) extends Context
case class GlobalSymbolList(list: List[ClassSymbolList]) extends Context

object NullType extends Type

trait Utils {
  def lookup[T](name: String, lst: List[T], func: T => String): Option[T] = lst match {
    case List() => None
    case head :: tail => if (func(head) == name) Some(head) else lookup(name, tail, func)
  }

  def lookupInClass(name: String, currentClass: ClassSymbolList, lst: List[ClassSymbolList]): Option[(String, Type, Kind)] = {
    val inCurrentClass = lookup(name, currentClass.symlst.list, (x: (String, Type, Kind)) => x._1)
    inCurrentClass match {
      case None => currentClass.parent match {
        case "" => None
        case _ => {
          val parentClass = lookup(currentClass.parent, lst, (x: ClassSymbolList) => x.name)
          parentClass match {
            case None => None
            case Some(t) => lookupInClass(name, t, lst)
          }
        }
      }
      case Some(t) => Some(t)
    }
  }
}
