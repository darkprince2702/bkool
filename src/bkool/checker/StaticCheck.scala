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
  override def visitProgram(ast: Program, c: Context) = ast.decl.foldLeft(SymbolList(List[(String, Type, Kind, SIKind)](("io", ClassType("io"), Class, Static))))((x, y) => visit(y, x).asInstanceOf[SymbolList])

  override def visitClassDecl(ast: ClassDecl, c: Context) = {
    val env = c.asInstanceOf[SymbolList].list
    val newenv = if (env.exists(x => x._1 == ast.name.toString())) throw Redeclared(Class, ast.name.toString()) else (ast.name.toString(), ClassType(ast.name.toString()), Class, null) :: env
    ast.decl.foldLeft(SymbolList(List[(String, Type, Kind, SIKind)]()).asInstanceOf[Context])((x, y) => visit(y, x).asInstanceOf[SymbolList])
    SymbolList(newenv)
  }

  override def visitMethodDecl(ast: MethodDecl, c: Context) = {
    val env = c.asInstanceOf[SymbolList].list
    if (env.exists(x => x._1 == ast.name.toString())) throw Redeclared(Method, ast.name.name)
    val newenv = if (env.exists(x => x._1 == ast.name.toString())) throw Redeclared(Method, ast.name.name) else (ast.name.toString(), ast.returnType, if (ast.returnType != null) Method else SpecialMethod, ast.kind) :: env
    SymbolList(newenv)
  }

  override def visitAttributeDecl(ast: AttributeDecl, c: Context) = {
    val decl = ast.decl
    val env = c.asInstanceOf[SymbolList].list
    decl match {
      case VarDecl(a, b) => {
        val newenv = if (env.exists(x => x._1 == a.toString())) throw Redeclared(Attribute, a.toString()) else (a.toString(), b, Variable, ast.kind) :: env
        SymbolList(newenv)
      }
      case ConstDecl(a, b, _) => {
        val newenv = if (env.exists(x => x._1 == a.toString())) throw Redeclared(Attribute, a.toString()) else (a.toString(), b, Constant, ast.kind) :: env
        SymbolList(newenv)
      }
    }
  }
}

class ClassEnvironment extends CheckingVisitor {
  override def visitProgram(ast: Program, c: Context) = ast.decl.foldLeft(GlobalSymbolList(List(ClassSymbolList("io", "", SymbolList(List(("writeStrLn", VoidType, Method, Static), ("writeStr", VoidType, Method, Static), ("readStr", StringType, Method, Static), ("writeBoolLn", VoidType, Method, Static), ("writeBool", VoidType, Method, Static), ("readBool", BoolType, Method, Static), ("writeFloatLn", VoidType, Method, Static), ("writeFloat", VoidType, Method, Static), ("readFloat", FloatType, Method, Static), ("writeIntLn", VoidType, Method, Static), ("writeInt", VoidType, Method, Static), ("readInt", IntType, Method, Static)))))))((x, y) => visit(y, x).asInstanceOf[GlobalSymbolList])

  override def visitClassDecl(ast: ClassDecl, c: Context) = {
    val globalList = c.asInstanceOf[GlobalSymbolList].list
    if (globalList.exists(x => x.name == ast.name.toString())) throw Redeclared(Class, ast.name.toString())
    val attributeList = ast.decl.foldLeft(SymbolList(List[(String, Type, Kind, SIKind)]()).asInstanceOf[Context])((x, y) => visit(y, x).asInstanceOf[SymbolList]).asInstanceOf[SymbolList]
    GlobalSymbolList(ClassSymbolList(ast.name.name, ast.parent.name, attributeList) :: globalList)
  }

  override def visitParamDecl(ast: ParamDecl, c: Context): Object = {
    val oldenv = c.asInstanceOf[SymbolList].list
    val newenv = if (oldenv.exists(x => x._1 == ast.id.toString())) throw Redeclared(Parameter, ast.id.toString()) else (ast.id.toString(), ast.paramType, Parameter, Instance) :: oldenv
    SymbolList(newenv)
  }

  override def visitMethodDecl(ast: MethodDecl, c: Context) = {
    val env = c.asInstanceOf[SymbolList].list
    if (env.exists(x => x._1 == ast.name.toString())) throw Redeclared(Method, ast.name.name)
    val paramenv = ast.param.foldLeft(SymbolList(List[(String, Type, Kind, SIKind)]()))((x, y) => visit(y, x).asInstanceOf[SymbolList])
    val newenv = if (env.exists(x => x._1 == ast.name.toString())) throw Redeclared(Method, ast.name.name) else (ast.name.toString(), MethodType(ast.returnType, paramenv), if (ast.returnType != null) Method else SpecialMethod, ast.kind) :: env
    SymbolList(newenv)
  }

  override def visitAttributeDecl(ast: AttributeDecl, c: Context) = {
    val decl = ast.decl
    val env = c.asInstanceOf[SymbolList].list
    decl match {
      case VarDecl(a, b) => {
        val newenv = if (env.exists(x => x._1 == a.toString())) throw Redeclared(Attribute, a.toString()) else (a.toString(), b, Variable, ast.kind) :: env
        SymbolList(newenv)
      }
      case ConstDecl(a, b, _) => {
        val newenv = if (env.exists(x => x._1 == a.toString())) throw Redeclared(Attribute, a.toString()) else (a.toString(), b, Constant, ast.kind) :: env
        SymbolList(newenv)
      }
    }
  }
}

class TypeChecking(clenv: GlobalSymbolList) extends CheckingVisitor with Utils {
  var parammeterFlag = false;
  var memberAccessFlag = false;
  var assignmentFlag = false;

  override def visitProgram(ast: Program, c: Context) = ast.decl.map(visit(_, null))

  override def visitClassDecl(ast: ClassDecl, c: Context) = {
    if (!ast.parent.name.isEmpty()) {
      val parentClass = lookup(ast.parent.name, clenv.list, (x: ClassSymbolList) => x.name)
      parentClass match {
        case None => throw Undeclared(Class, ast.parent.name)
        case Some(_) =>
      }
    }
    val newenv = ClassSymbolList(ast.name.name, ast.parent.name, SymbolList(List[(String, Type, Kind, SIKind)]()))
    ast.decl.filter(_.isInstanceOf[AttributeDecl]).foldLeft(newenv)((x, y) => visit(y, x).asInstanceOf[ClassSymbolList])
    ast.decl.filter(_.isInstanceOf[MethodDecl]).map(visit(_, newenv))
  }

  override def visitAttributeDecl(ast: AttributeDecl, c: Context) = visit(ast.decl, c)

  override def visitMethodDecl(ast: MethodDecl, c: Context) = {
    if (ast.returnType != null) visit(ast.returnType, c)
    val classenv = c.asInstanceOf[ClassSymbolList]
    val locenv = ast.param.foldLeft(ClassSymbolList(classenv.name, classenv.parent, SymbolList(List[(String, Type, Kind, SIKind)]())).asInstanceOf[Context])((x, y) => visit(y, x).asInstanceOf[ClassSymbolList])
    parammeterFlag = true
    visit(ast.body, locenv)
  }

  override def visitParamDecl(ast: ParamDecl, c: Context): Object = {
    if (ast.paramType.isInstanceOf[ClassType])
      visit(ast.paramType, c)
    val classenv = c.asInstanceOf[ClassSymbolList]
    val oldenv = classenv.symlst.list
    val newenv = if (oldenv.exists(x => x._1 == ast.id.toString())) throw Redeclared(Parameter, ast.id.toString()) else (ast.id.toString(), ast.paramType, Parameter, Instance) :: oldenv
    ClassSymbolList(classenv.name, classenv.parent, SymbolList(newenv))
  }

  override def visitVarDecl(ast: VarDecl, c: Context) = {
    visit(ast.varType, c)
    val classenv = c.asInstanceOf[ClassSymbolList]
    val oldenv = classenv.symlst.list
    val newenv = if (oldenv.exists(x => x._1 == ast.variable.toString())) throw Redeclared(Variable, ast.variable.toString()) else (ast.variable.toString(), ast.varType, Variable, Instance) :: oldenv
    ClassSymbolList(classenv.name, classenv.parent, SymbolList(newenv))
  }

  override def visitConstDecl(ast: ConstDecl, c: Context) = {
    visit(ast.constType, c)
    visit(ast.const, c)
    val classenv = c.asInstanceOf[ClassSymbolList]
    val oldenv = classenv.symlst.list
    val newenv = if (oldenv.exists(x => x._1 == ast.id.toString())) throw Redeclared(Constant, ast.id.toString()) else (ast.id.toString(), ast.constType, Constant, Instance) :: oldenv
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
    val typeOfLeft = visit(ast.left, c).asInstanceOf[(Type, Kind)]
    val typeOfRight = visit(ast.right, c).asInstanceOf[(Type, Kind)]
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
      case Some(t) => (ClassType(t.name), Variable)
    }
  }

  override def visitCallExpr(ast: CallExpr, c: Context) = {
    ast.params.map(visit(_, c))
    if (ast.cName.isInstanceOf[Id]) memberAccessFlag = true
    val callType = visit(ast.cName, c).asInstanceOf[(Type, Kind)]
    callType._1 match {
      case ClassType(name) => {
        val findClass = lookup(name, clenv.list, (x: ClassSymbolList) => x.name)
        findClass match {
          case None => throw Undeclared(Class, name)
          case Some(t) => {
            val method = lookupInClass(ast.method.name, t, clenv.list)
            method match {
              case None => throw Undeclared(Method, ast.method.name)
              case Some(t) => if (t._3 != Method) throw Undeclared(Method, ast.method.name) else {
                (t._2, t._3)
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
    val id = lookup(ast.name, env, (x: (String, Type, Kind, SIKind)) => x._1)
    id match {
      case None => {
        memberAccessFlag match {
          case true => {
            val findClass = lookup(ast.name, clenv.list, (x: ClassSymbolList) => x.name)
            findClass match {
              case None => throw Undeclared(Identifier, ast.name)
              case Some(t) => {
                memberAccessFlag = false;
                (ClassType(ast.name), Variable)
              }
            }
          }
          case false => throw Undeclared(Identifier, ast.name)
        }
      }
      case Some(t) => (t._2, t._3)
    }
  }

  override def visitArrayCell(ast: ArrayCell, c: Context) = {
    visit(ast.idx, c)
    val arrayType = visit(ast.arr, c).asInstanceOf[(Type, Kind)]
    arrayType._1 match {
      case ArrayType(_, t) => (t, arrayType._2)
      case _ => arrayType
    }
  }

  override def visitFieldAccess(ast: FieldAccess, c: Context) = {
    if (ast.name.isInstanceOf[Id]) memberAccessFlag = true
    val fieldType = visit(ast.name, c).asInstanceOf[(Type, Kind)]
    fieldType._1 match {
      case ClassType(name) => {
        val findClass = lookup(name, clenv.list, (x: ClassSymbolList) => x.name)
        findClass match {
          case None => throw Undeclared(Class, name)
          case Some(t) => {
            val field = lookupInClass(ast.field.name, t, clenv.list)
            field match {
              case None => throw Undeclared(Attribute, ast.field.name)
              case Some(t) => if (t._3 != Constant && t._3 != Variable) throw Undeclared(Attribute, ast.field.name) else {
                (t._2, t._3)
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
    } else ClassSymbolList(classenv.name, classenv.parent, SymbolList(List[(String, Type, Kind, SIKind)]()))
    val newenv = ast.decl.foldLeft(env)((x, y) => visit(y, x).asInstanceOf[ClassSymbolList])
    ast.stmt.map(visit(_, ClassSymbolList(classenv.name, classenv.parent, SymbolList(classenv.symlst.list ++ newenv.symlst.list))))
    c
  }

  override def visitAssign(ast: Assign, c: Context) = {
    val lhs = visit(ast.leftHandSide, c).asInstanceOf[(Type, Kind)]
    if (lhs._2 == Constant) throw CannotAssignToConstant(ast)
    val rhs = visit(ast.expr, c).asInstanceOf[(Type, Kind)]
    if (checkType(lhs._1, rhs._1, clenv.list) == false) throw TypeMismatchInStatement(ast)
    c
  }

  override def visitIf(ast: If, c: Context) = {
    val ifExpr = visit(ast.expr, c)
    //if (ifExpr != BoolType) throw TypeMismatchInStatement(ast)
    visit(ast.thenStmt, c)
    ast.elseStmt match {
      case None =>
      case Some(t) => visit(t, c)
    }
    c
  }

  override def visitCall(ast: Call, c: Context) = {
    if (ast.parent.isInstanceOf[Id]) memberAccessFlag = true
    val callType = visit(ast.parent, c).asInstanceOf[(Type, Kind)]
    callType._1 match {
      case ClassType(name) => {
        val findClass = lookup(name, clenv.list, (x: ClassSymbolList) => x.name)
        findClass match {
          case None => throw Undeclared(Class, name)
          case Some(t) => {
            val method = lookupInClass(ast.method.name, t, clenv.list)
            method match {
              case None => throw Undeclared(Method, ast.method.name)
              case Some(t) => {
                if (t._3 != Method) throw Undeclared(Method, ast.method.name)
                else if (t._2.asInstanceOf[MethodType].returnType != VoidType) throw TypeMismatchInStatement(ast)
                else {
                  val param = ast.params.foldLeft(List[Type]())((x,y) => visit(y, c).asInstanceOf[(Type, Kind)]._1 :: x)
                  val protypeparam = t._2.asInstanceOf[MethodType].param.list.map(x => x._2)
                  if (param.size == protypeparam.size) {
                    val check = protypeparam.zip(param).foldLeft(true)((x, y) => checkType(y._1, y._2, clenv.list) && x)
                    if (check == true) c
                    else throw TypeMismatchInStatement(ast)
                  }
                  else throw TypeMismatchInStatement(ast)
                }
              }
            }
          }
        }
      }
      case _ => throw TypeMismatchInStatement(ast)
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

  override def visitIntLiteral(ast: IntLiteral, c: Context) = (IntType, Constant)

  override def visitFloatLiteral(ast: FloatLiteral, c: Context) = (FloatType, Constant)

  override def visitStringLiteral(ast: StringLiteral, c: Context) = (StringType, Constant)

  override def visitBooleanLiteral(ast: BooleanLiteral, c: Context) = (BoolType, Constant)

  override def visitNullLiteral(ast: NullLiteral.type, c: Context) = (NullType, Constant)

  override def visitSelfLiteral(ast: SelfLiteral.type, c: Context) = {
    (ClassType(c.asInstanceOf[ClassSymbolList].name), Variable)
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

case class Property(Type: Type, kind: Kind) extends Context
case class SymbolList(list: List[(String, Type, Kind, SIKind)]) extends Context
case class ClassSymbolList(name: String, parent: String, symlst: SymbolList) extends Context
case class MethodEnvironment(name: String, returnType: Type, locenv: ClassSymbolList) extends Context
case class GlobalSymbolList(list: List[ClassSymbolList]) extends Context
case class MethodType(returnType: Type, param: SymbolList) extends Type
object NullType extends Type

trait Utils {
  def lookup[T](name: String, lst: List[T], func: T => String): Option[T] = lst match {
    case List() => None
    case head :: tail => if (func(head) == name) Some(head) else lookup(name, tail, func)
  }

  def lookupInClass(name: String, currentClass: ClassSymbolList, lst: List[ClassSymbolList]): Option[(String, Type, Kind, SIKind)] = {
    val inCurrentClass = lookup(name, currentClass.symlst.list, (x: (String, Type, Kind, SIKind)) => x._1)
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

  def checkType(lhs: Type, rhs: Type, lst: List[ClassSymbolList]): Boolean = {
    lhs match {
      case VoidType => false
      case ClassType(t) => {
        rhs match {
          case ClassType(r) => {
            if (r == t) true
            else {
              val currentClass = lookup(r, lst, (x: ClassSymbolList) => x.name)
              currentClass match {
                case None => false
                case Some(x) => checkType(lhs, ClassType(x.parent), lst)
              }
            }
          }
          case NullType => true
          case _ => false
        }

      }
      case ArrayType(ldim, ltype) => {
        rhs match {
          case ArrayType(rdim, rtype) => {
            if (checkType(ltype, rtype, lst) == true && ldim == rdim) true
            else false
          }
          case _ => false
        }
      }
      case FloatType => {
        if (rhs == FloatType || rhs == IntType) true
        else false
      }
      case _ => {
        if (rhs == lhs) true
        else false
      }
    }
  }
}
