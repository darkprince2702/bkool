package bkool.checker

/**
 * @author nhphung
 */

import bkool.parser._
import bkool.utils._
import java.io.{ PrintWriter, File }
import org.antlr.v4.runtime.ANTLRFileStream
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.tree._
import scala.collection.JavaConverters._

class StaticChecker(ast: AST) {
  def check() = {
    try {
      val bldecls = new GlobalEnvironment()
      val env = bldecls.visit(ast, null).asInstanceOf[SymbolList]
      val ce = new ClassEnvironment();
      val clenv = ce.visit(ast, null).asInstanceOf[GlobalSymbolList]
      val tc = new TypeChecking(clenv)
      tc.visit(ast, null)

    } catch {
      case Undeclared(k, n) => throw Undeclared(k, n)
      case Redeclared(k, n) => throw Redeclared(k, n)
      case CannotAssignToConstant(s) => throw CannotAssignToConstant(s)
      case TypeMismatchInExpression(exp) => throw TypeMismatchInExpression(exp)
      case TypeMismatchInStatement(stmt) => throw TypeMismatchInStatement(stmt)
      case TypeMismatchInConstant(cons) => throw TypeMismatchInConstant(cons)
      case CannotAccessPrivateAttribute(cName, attr) => throw CannotAccessPrivateAttribute(cName, attr)
      case MethodNotReturn(m) => throw MethodNotReturn(m)
      case BreakNotInLoop(line) => throw BreakNotInLoop(line)
      case ContinueNotInLoop(line) => throw ContinueNotInLoop(line)
      case NotConstantExpression(exp) => throw NotConstantExpression(exp)
      //case _: Throwable => throw BreakNotInLoop(0)
    }
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
  override def visitProgram(ast: Program, c: Context) = ast.decl.foldLeft(GlobalSymbolList(List(ClassSymbolList("io", "", SymbolList(List(("writeStrLn", MethodType(VoidType, SymbolList(List(("anArg", StringType, Parameter, Instance)))), Method, Static), ("writeStr", MethodType(VoidType, SymbolList(List(("anArg", StringType, Parameter, Instance)))), Method, Static), ("readStr", MethodType(StringType, SymbolList(List())), Method, Static), ("writeBoolLn", MethodType(VoidType, SymbolList(List(("anArg", BoolType, Parameter, Instance)))), Method, Static), ("writeBool", MethodType(VoidType, SymbolList(List(("anArg", BoolType, Parameter, Instance)))), Method, Static), ("readBool", MethodType(BoolType, SymbolList(List())), Method, Static), ("writeFloatLn", MethodType(VoidType, SymbolList(List(("anArg", FloatType, Parameter, Instance)))), Method, Static), ("writeFloat", MethodType(VoidType, SymbolList(List(("anArg", FloatType, Parameter, Instance)))), Method, Static), ("readFloat", MethodType(FloatType, SymbolList(List())), Method, Static), ("writeIntLn", MethodType(VoidType, SymbolList(List(("anArg", IntType, Parameter, Instance)))), Method, Static), ("writeInt", MethodType(VoidType, SymbolList(List(("anArg", IntType, Parameter, Instance)))), Method, Static), ("readInt", MethodType(IntType, SymbolList(List())), Method, Static)))))))((x, y) => visit(y, x).asInstanceOf[GlobalSymbolList])

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
  var parammeterFlag = false
  var memberAccessFlag = false
  var assignmentFlag = false
  var constantExprFlag = false
  var methodReturnType:Type = VoidType
  var loopLevel = 0

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
    methodReturnType = ast.returnType
    val body = visit(ast.body, locenv).asInstanceOf[Statement]
    if (body.isReturn == false && ast.returnType != VoidType && ast.returnType != null) throw MethodNotReturn(ast.name.name)
    else c
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
    val env = if (c.isInstanceOf[MethodEnvironment]) c.asInstanceOf[MethodEnvironment].locenv else c.asInstanceOf[ClassSymbolList]
    visit(ast.varType, env)
    val oldenv = env.symlst.list
    val newenv = if (oldenv.exists(x => x._1 == ast.variable.toString())) throw Redeclared(Variable, ast.variable.toString()) else (ast.variable.toString(), ast.varType, Variable, Instance) :: oldenv
    val locenv = ClassSymbolList(env.name, env.parent, SymbolList(newenv))
    if (c.isInstanceOf[MethodEnvironment]) MethodEnvironment(c.asInstanceOf[MethodEnvironment].name, c.asInstanceOf[MethodEnvironment].returnType, locenv) else locenv
  }

  override def visitConstDecl(ast: ConstDecl, c: Context) = {
    val env = if (c.isInstanceOf[MethodEnvironment]) c.asInstanceOf[MethodEnvironment].locenv else c.asInstanceOf[ClassSymbolList]
    val oldenv = env.symlst.list
    val newenv = if (oldenv.exists(x => x._1 == ast.id.toString())) throw Redeclared(Constant, ast.id.toString()) else (ast.id.toString(), ast.constType, Constant, Instance) :: oldenv
    // 2.10
    constantExprFlag = true
    val exprType = visit(ast.const, c).asInstanceOf[(Type, Kind)]
    if (exprType._2 != Constant) throw NotConstantExpression(ast.const)
    constantExprFlag = false
    // 2.6
    if (checkType(ast.constType, exprType._1, clenv.list) == false) throw TypeMismatchInConstant(ast)
    val locenv = ClassSymbolList(env.name, env.parent, SymbolList(newenv))
    if (c.isInstanceOf[MethodEnvironment]) MethodEnvironment(c.asInstanceOf[MethodEnvironment].name, c.asInstanceOf[MethodEnvironment].returnType, locenv) else locenv
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
    val left = visit(ast.left, c).asInstanceOf[(Type, Kind)]
    val right = visit(ast.right, c).asInstanceOf[(Type, Kind)]
    val lt = left._1
    val rt = right._1
    val sikind = if (left._2 != Constant || right._2 != Constant) Variable else Constant
    ast.op match {
      case "+" => {
        if ((lt == IntType || lt == FloatType) && (rt == IntType || rt == FloatType))
          if (lt == FloatType || rt == FloatType) (FloatType, sikind)
          else (IntType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
      case "-" => {
        if ((lt == IntType || lt == FloatType) && (rt == IntType || rt == FloatType))
          if (lt == FloatType || rt == FloatType) (FloatType, sikind)
          else (IntType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
      case "*" => {
        if ((lt == IntType || lt == FloatType) && (rt == IntType || rt == FloatType))
          if (lt == FloatType || rt == FloatType) (FloatType, sikind)
          else (IntType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
      case "/" => {
        if ((lt == IntType || lt == FloatType) && (rt == IntType || rt == FloatType)) (FloatType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
      case "\\" => {
        if (lt == IntType && rt == IntType) (IntType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
      case "%" => {
        if (lt == IntType && rt == IntType) (IntType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
      case "&&" => {
        if (lt == BoolType && rt == BoolType) (BoolType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
      case "||" => {
        if (lt == BoolType && rt == BoolType) (BoolType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
      case "==" => {
        if (lt != VoidType && rt != VoidType && ((lt == rt) || (lt == NullType) || (rt == NullType))) (BoolType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
      case "<>" => {
        if (lt != VoidType && rt != VoidType && ((lt == rt) || (lt == NullType) || (rt == NullType))) (BoolType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
      case ">" => {
        if ((lt == IntType || lt == FloatType) && (rt == IntType || rt == FloatType)) (BoolType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
      case "<" => {
        if ((lt == IntType || lt == FloatType) && (rt == IntType || rt == FloatType)) (BoolType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
      case ">=" => {
        if ((lt == IntType || lt == FloatType) && (rt == IntType || rt == FloatType)) (BoolType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
      case "<=" => {
        if ((lt == IntType || lt == FloatType) && (rt == IntType || rt == FloatType)) (BoolType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
      case "^" => {
        if (lt == StringType && rt == StringType) (StringType, sikind)
        else throw TypeMismatchInExpression(ast)
      }
    }
  }

  override def visitUnaryOp(ast: UnaryOp, c: Context) = {
    val expr = visit(ast.body, c).asInstanceOf[(Type, Kind)]
    val rt = expr._1
    ast.op match {
      case "+" => {
        if (rt == IntType || rt == FloatType) (rt, expr._2)
        else throw TypeMismatchInExpression(ast)
      }
      case "-" => {
        if (rt == IntType || rt == FloatType) (rt, expr._2)
        else throw TypeMismatchInExpression(ast)
      }
      case "!" => {
        if (rt == BoolType) (rt, expr._2)
        else throw TypeMismatchInExpression(ast)
      }
    }
  }

  override def visitNewExpr(ast: NewExpr, c: Context) = {
    //if (constantExprFlag == true) throw NotConstantExpression(ast)
    val findClass = lookup(ast.name.name, clenv.list, (x: ClassSymbolList) => x.name)
    findClass match {
      case None => throw Undeclared(Class, ast.name.name)
      case Some(t) => {
        val constructor = lookupInClass(ast.name.name, t, clenv.list)
        val protypeparam = constructor match {
          case None => List[Type]()
          case Some(x) => {
            x._2.asInstanceOf[MethodType].param.list.map(x => x._2)
          }
        }
        val param = ast.exprs.foldLeft(List[Type]())((x, y) => visit(y, c).asInstanceOf[(Type, Kind)]._1 :: x)
        if (param.size == protypeparam.size) {
          val check = protypeparam.zip(param).foldLeft(true)((x, y) => checkType(y._1, y._2, clenv.list) && x)
          if (check == true) (ClassType(t.name), Variable)
          else throw TypeMismatchInExpression(ast)
        } else throw TypeMismatchInExpression(ast)
      }
    }
  }

  override def visitCallExpr(ast: CallExpr, c: Context) = {
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
              case Some(t) => {
                if (t._3 != Method) throw TypeMismatchInExpression(ast)
                else if (t._2.asInstanceOf[MethodType].returnType == VoidType) throw TypeMismatchInExpression(ast)
                else {
                  val param = ast.params.foldLeft(List[Type]())((x, y) => visit(y, c).asInstanceOf[(Type, Kind)]._1 :: x)
                  val protypeparam = t._2.asInstanceOf[MethodType].param.list.map(x => x._2)
                  if (param.size == protypeparam.size) {
                    val check = protypeparam.zip(param).foldLeft(true)((x, y) => checkType(y._1, y._2, clenv.list) && x)
                    if (check == true) (t._2.asInstanceOf[MethodType].returnType, t._3)
                    else throw TypeMismatchInExpression(ast)
                  } else throw TypeMismatchInExpression(ast)
                }
              }
            }
          }
        }
      }
      case _ => throw TypeMismatchInExpression(ast)
    }
  }
  
  override def visitId(ast: Id, c: Context) = {
    val env = c match {
      case MethodEnvironment(_, _, t) => t.symlst.list
      case ClassSymbolList(_, _, t) => t.list
    }

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
      case Some(t) => {
        (t._2, t._3)
      }
    }
  }

  override def visitArrayCell(ast: ArrayCell, c: Context) = {
    val idx = visit(ast.idx, c).asInstanceOf[(Type, Kind)]
    val arr = visit(ast.arr, c).asInstanceOf[(Type, Kind)]
    if (arr._1.isInstanceOf[ArrayType] && idx._1 == IntType) {
      //if (constantExprFlag == true && arr._2 != Constant) throw NotConstantExpression(ast)
      (arr._1.asInstanceOf[ArrayType].eleType, arr._2)
    } else throw TypeMismatchInExpression(ast)
  }

  override def visitFieldAccess(ast: FieldAccess, c: Context) = {
    val currentClass = if (c.isInstanceOf[MethodEnvironment]) c.asInstanceOf[MethodEnvironment].locenv else c.asInstanceOf[ClassSymbolList]
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
              case Some(x) => {
                if (x._3 != Constant && x._3 != Variable) throw TypeMismatchInExpression(ast)
                else if (x._4 != Static && checkSuperclass(currentClass, t.name, clenv.list) == false) throw CannotAccessPrivateAttribute(x._5, x._1)
                else {
                  //if (constantExprFlag == true && x._3 != Constant) throw NotConstantExpression(ast)
                  (x._2, x._3)
                }
              }
            }
          }
        }
      }
      case _ => throw TypeMismatchInExpression(ast)
    }
  }

  override def visitBlock(ast: Block, c: Context) = {
    //val methodenv = c.asInstanceOf[MethodEnvironment]
    val classenv = c.asInstanceOf[ClassSymbolList]
    val env = if (parammeterFlag == true) {
      parammeterFlag = false
      classenv
    } else ClassSymbolList(classenv.name, classenv.parent, SymbolList(List[(String, Type, Kind, SIKind)]()))
    val newenv = ast.decl.foldLeft(env)((x, y) => visit(y, x).asInstanceOf[ClassSymbolList])
    val context = ClassSymbolList(classenv.name, classenv.parent, SymbolList(classenv.symlst.list ++ newenv.symlst.list))
    val isReturn = ast.stmt.foldLeft(false)((x, y) => visit(y, context).asInstanceOf[Statement].isReturn || x)
    Statement(isReturn)
  }

  override def visitAssign(ast: Assign, c: Context) = {
    val lhs = visit(ast.leftHandSide, c).asInstanceOf[(Type, Kind)]
    if (lhs._2 == Constant) throw CannotAssignToConstant(ast)
    val rhs = visit(ast.expr, c).asInstanceOf[(Type, Kind)]
    if (checkType(lhs._1, rhs._1, clenv.list) == false) throw TypeMismatchInStatement(ast)
    Statement(false)
  }

  override def visitIf(ast: If, c: Context) = {
    val ifExpr = visit(ast.expr, c).asInstanceOf[(Type, Kind)]
    if (ifExpr._1 != BoolType) throw TypeMismatchInStatement(ast)
    val thenReturn = visit(ast.thenStmt, c).asInstanceOf[Statement]
    val elseReturn = ast.elseStmt match {
      case None => Statement(false)
      case Some(t) => visit(t, c).asInstanceOf[Statement]
    }
    Statement(thenReturn.isReturn && elseReturn.isReturn)
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
                if (t._3 != Method) throw TypeMismatchInStatement(ast)
                else if (t._2.asInstanceOf[MethodType].returnType != VoidType) throw TypeMismatchInStatement(ast)
                else {
                  val param = ast.params.foldLeft(List[Type]())((x, y) => visit(y, c).asInstanceOf[(Type, Kind)]._1 :: x)
                  val protypeparam = t._2.asInstanceOf[MethodType].param.list.map(x => x._2)
                  if (param.size == protypeparam.size) {
                    val check = protypeparam.zip(param).foldLeft(true)((x, y) => checkType(y._1, y._2, clenv.list) && x)
                    if (check == true) Statement(false)
                    else throw TypeMismatchInStatement(ast)
                  } else throw TypeMismatchInStatement(ast) // Change to UndeclMethod
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
    val expr = visit(ast.expr, c).asInstanceOf[(Type, Kind)]
    if (expr._1 != BoolType) throw TypeMismatchInStatement(ast)
    loopLevel = loopLevel + 1
    visit(ast.loop, c)
    loopLevel = loopLevel - 1
    Statement(false)
  }

  override def visitBreak(ast: Break.type, c: Context) = if (loopLevel == 0) throw BreakNotInLoop(0) else Statement(false)

  override def visitContinue(ast: Continue.type, c: Context) = if (loopLevel == 0) throw ContinueNotInLoop(0) else Statement(false)

  override def visitReturn(ast: Return, c: Context) = {
    val rttype = visit(ast.expr, c).asInstanceOf[(Type, Kind)]
    if (checkType(methodReturnType, rttype._1, clenv.list) == false) throw TypeMismatchInStatement(ast)
    Statement(true)
  }

  override def visitIntLiteral(ast: IntLiteral, c: Context) = (IntType, Constant)

  override def visitFloatLiteral(ast: FloatLiteral, c: Context) = (FloatType, Constant)

  override def visitStringLiteral(ast: StringLiteral, c: Context) = (StringType, Constant)

  override def visitBooleanLiteral(ast: BooleanLiteral, c: Context) = (BoolType, Constant)

  override def visitNullLiteral(ast: NullLiteral.type, c: Context) = (NullType, Constant)

  override def visitSelfLiteral(ast: SelfLiteral.type, c: Context) = {
    if (c.isInstanceOf[MethodEnvironment]) (ClassType(c.asInstanceOf[MethodEnvironment].locenv.name), Variable)
    else (ClassType(c.asInstanceOf[ClassSymbolList].name), Variable)
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

case class Statement(isReturn: Boolean) extends Context
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

  def lookupInClass(name: String, currentClass: ClassSymbolList, lst: List[ClassSymbolList]): Option[(String, Type, Kind, SIKind, String)] = {
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
      case Some(t) => Some((t._1, t._2, t._3, t._4, currentClass.name))
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

  def checkSuperclass(current: ClassSymbolList, that: String, lst: List[ClassSymbolList]): Boolean = {
    if (current.name == that) true
    else {
      if (current.parent == "") false
      else {
        val parentClass = lookup(current.parent, lst, (x: ClassSymbolList) => x.name)
        parentClass match {
          case None => false
          case Some(t) => checkSuperclass(t, that, lst)
        }
      }
    }
  }
}
