package bkool.parser
import org.antlr.v4.runtime.Token
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.ParserRuleContext
import java.io.{ PrintWriter, File }
import org.antlr.v4.runtime.ANTLRFileStream
import bkool.utils._
import scala.collection.JavaConverters._
import org.antlr.v4.runtime.tree._

class ASTGeneration extends BKOOLBaseVisitor[Object] {
  def flatten(ls: List[Any]): List[Any] = ls flatMap {
    case i: List[_] => flatten(i)
    case e => List(e)
  }

  override def visitProgram(ctx: BKOOLParser.ProgramContext) = {
    val decl = ctx.classDecl().asScala.map(visit).toList.asInstanceOf[List[ClassDecl]]
    Program(decl)
  }

  override def visitClassDecl(ctx: BKOOLParser.ClassDeclContext) = {
    //val name = visit(ctx.ID(0)).asInstanceOf[Id]
    val name = Id(ctx.ID(0).getText)
    val parent = if (ctx.ID(1) != null) Id(ctx.ID(1).getText) else Id("")
    val decl2 = visit(ctx.listMembers()).asInstanceOf[List[MemDecl]]
    //val decl = ctx.listMembers().member().asScala.map(visit).toList.asInstanceOf[List[MemDecl]]
    ClassDecl(name, parent, decl2)
  }

  override def visitListMembers(ctx: BKOOLParser.ListMembersContext) = {
    flatten(ctx.member().asScala.map(visit).toList)
  }

  override def visitMember(ctx: BKOOLParser.MemberContext) = {
    visit(ctx.getChild(0))
  }

  override def visitAttribute(ctx: BKOOLParser.AttributeContext) = {
    visit(ctx.getChild(0))
  }

  override def visitConstantDecl(ctx: BKOOLParser.ConstantDeclContext) = {
    val id = Id(ctx.ID().getText)
    val constType = visit(ctx.`type`()).asInstanceOf[Type]
    val const = visit(ctx.exp).asInstanceOf[Expr]
    val decl = ConstDecl(id, constType, const)
    val kind = if (ctx.STATIC() != null) Static else Instance
    AttributeDecl(kind, decl)
  }

  override def visitVaribleDecl(ctx: BKOOLParser.VaribleDeclContext) = {
    val kind = if (ctx.STATIC() != null) Static else Instance
    val varType = visit(ctx.`type`()).asInstanceOf[Type]
    val varList = visit(ctx.listIDs()).asInstanceOf[List[Id]]
    val varDeclList = varList.map(i => VarDecl(i, varType))
    val attributeList = varDeclList.map(i => AttributeDecl(kind, i))
    attributeList
  }

  override def visitMethodDecl(ctx: BKOOLParser.MethodDeclContext) = {
    visit(ctx.getChild(0))
  }

  override def visitNormalMethod(ctx: BKOOLParser.NormalMethodContext) = {
    val kind = if (ctx.STATIC() != null) Static else Instance
    val name = Id(ctx.ID().getText)
    val param = if (ctx.listPara() != null) visit(ctx.listPara()).asInstanceOf[List[ParamDecl]] else List()
    val returnType = visit(ctx.returnType()).asInstanceOf[Type]
    val body = visit(ctx.blockStat()).asInstanceOf[Stmt]
    MethodDecl(kind, name, param, returnType, body)
  }

  override def visitReturnType(ctx: BKOOLParser.ReturnTypeContext) = {
    visit(ctx.getChild(0))
  }

  override def visitConstructor(ctx: BKOOLParser.ConstructorContext) = {
    val kind = Instance
    val name = Id(ctx.ID().getText)
    val param = if (ctx.listPara() != null) visit(ctx.listPara()).asInstanceOf[List[ParamDecl]] else List()
    val returnType = null
    val body = visit(ctx.blockStat()).asInstanceOf[Stmt]
    MethodDecl(kind, name, param, returnType, body)
  }

  override def visitPara(ctx: BKOOLParser.ParaContext) = {
    val idList = visit(ctx.listIDs()).asInstanceOf[List[Id]]
    val paramType = visit(ctx.`type`()).asInstanceOf[Type]
    val paramDeclList = idList.map(x => new ParamDecl(x, paramType))
    paramDeclList
  }

  override def visitListPara(ctx: BKOOLParser.ListParaContext) = {
    val paramList = ctx.para().asScala.map(visit).toList.asInstanceOf[List[List[ParamDecl]]]
    val paramDeclList = paramList.flatten
    paramDeclList
  }

  override def visitListIDs(ctx: BKOOLParser.ListIDsContext) = {
    val ids = ctx.ID().asScala
    val idList = ids.map(x => Id(x.getText)).toList
    idList
  }

  override def visitType(ctx: BKOOLParser.TypeContext) = {
    visit(ctx.getChild(0))
  }

  override def visitPrimitiveType(ctx: BKOOLParser.PrimitiveTypeContext) = {
    visit(ctx.getChild(0))
  }

  override def visitIntegerType(ctx: BKOOLParser.IntegerTypeContext) = IntType

  override def visitFloatType(ctx: BKOOLParser.FloatTypeContext) = FloatType

  override def visitBooleanType(ctx: BKOOLParser.BooleanTypeContext) = BoolType

  override def visitStringType(ctx: BKOOLParser.StringTypeContext) = StringType

  override def visitVoidType(ctx: BKOOLParser.VoidTypeContext) = VoidType

  override def visitArrayType(ctx: BKOOLParser.ArrayTypeContext) = {
    val dimen = visit(ctx.size()).asInstanceOf[IntLiteral]
    val eleType = visit(ctx.getChild(0)).asInstanceOf[Type]
    ArrayType(dimen, eleType)
  }

  override def visitSize(ctx: BKOOLParser.SizeContext) = IntLiteral(ctx.INTLIT().toString().toInt)

  override def visitClassType(ctx: BKOOLParser.ClassTypeContext) = ClassType(ctx.ID().toString())

  override def visitBinExpr1(ctx: BKOOLParser.BinExpr1Context) = {
    val op = ctx.getChild(1).toString()
    val left = visit(ctx.exp(0)).asInstanceOf[Expr]
    val right = visit(ctx.exp(1)).asInstanceOf[Expr]
    BinaryOp(op, left, right)
  }

  override def visitSelfExpr(ctx: BKOOLParser.SelfExprContext) = SelfLiteral

  override def visitBinExpr3(ctx: BKOOLParser.BinExpr3Context) = {
    val op = ctx.getChild(1).toString()
    val left = visit(ctx.exp(0)).asInstanceOf[Expr]
    val right = visit(ctx.exp(1)).asInstanceOf[Expr]
    BinaryOp(op, left, right)
  }

  override def visitBinExpr2(ctx: BKOOLParser.BinExpr2Context) = {
    val op = ctx.getChild(1).toString()
    val left = visit(ctx.exp(0)).asInstanceOf[Expr]
    val right = visit(ctx.exp(1)).asInstanceOf[Expr]
    BinaryOp(op, left, right)
  }

  override def visitUnaExpr1(ctx: BKOOLParser.UnaExpr1Context) = {
    val op = ctx.getChild(0).toString()
    val body = visit(ctx.exp()).asInstanceOf[Expr]
    UnaryOp(op, body)
  }

  override def visitUnaExpr2(ctx: BKOOLParser.UnaExpr2Context) = {
    val op = ctx.getChild(0).toString()
    val body = visit(ctx.exp()).asInstanceOf[Expr]
    UnaryOp(op, body)
  }

  override def visitMethodInvocation(ctx: BKOOLParser.MethodInvocationContext) = {
    val cName = visit(ctx.exp()).asInstanceOf[Expr]
    val method = Id(ctx.ID().getText)
    val params = if (ctx.listExp() != null) visit(ctx.listExp()).asInstanceOf[List[Expr]] else List()
    CallExpr(cName, method, params)
  }

  override def visitAttributeAccess(ctx: BKOOLParser.AttributeAccessContext) = {
    val name = visit(ctx.exp()).asInstanceOf[Expr]
    val field = Id(ctx.ID().getText)
    FieldAccess(name, field)
  }

  override def visitBinExpr5(ctx: BKOOLParser.BinExpr5Context) = {
    val op = ctx.getChild(1).toString()
    val left = visit(ctx.exp(0)).asInstanceOf[Expr]
    val right = visit(ctx.exp(1)).asInstanceOf[Expr]
    BinaryOp(op, left, right)
  }

  override def visitBinExpr4(ctx: BKOOLParser.BinExpr4Context) = {
    val op = ctx.getChild(1).toString()
    val left = visit(ctx.exp(0)).asInstanceOf[Expr]
    val right = visit(ctx.exp(1)).asInstanceOf[Expr]
    BinaryOp(op, left, right)
  }

  override def visitIndexExpr(ctx: BKOOLParser.IndexExprContext) = {
    val arr = visit(ctx.exp(0)).asInstanceOf[Expr]
    val idx = visit(ctx.exp(1)).asInstanceOf[Expr]
    ArrayCell(arr, idx)
  }

  override def visitBraceExpr(ctx: BKOOLParser.BraceExprContext) = {
    visit(ctx.exp())
  }

  override def visitNullExpr(ctx: BKOOLParser.NullExprContext) = NullLiteral

  override def visitBinExpr6(ctx: BKOOLParser.BinExpr6Context) = {
    val op = ctx.getChild(1).toString()
    val left = visit(ctx.exp(0)).asInstanceOf[Expr]
    val right = visit(ctx.exp(1)).asInstanceOf[Expr]
    BinaryOp(op, left, right)
  }

  override def visitIdentifier(ctx: BKOOLParser.IdentifierContext) = Id(ctx.ID().getText)

  override def visitNewExpr(ctx: BKOOLParser.NewExprContext) = {
    val name = Id(ctx.ID().getText)
    val exprs = if (ctx.listExp() != null) visit(ctx.listExp()).asInstanceOf[List[Expr]] else List()
    NewExpr(name, exprs)
  }

  override def visitLiterals(ctx: BKOOLParser.LiteralsContext) = {
    visit(ctx.literal())
  }

  override def visitListExp(ctx: BKOOLParser.ListExpContext) = {
    ctx.exp().asScala.map(visit).toList
  }

  override def visitLiteral(ctx: BKOOLParser.LiteralContext) = {
    val literal = {
      if (ctx.INTLIT() != null)
        IntLiteral(ctx.INTLIT().toString().toInt)
      else if (ctx.FLOATLIT() != null)
        FloatLiteral(ctx.FLOATLIT().toString().toFloat)
      else if (ctx.STRINGLIT() != null)
        StringLiteral(ctx.STRINGLIT().toString())
      else
        BooleanLiteral(ctx.BOOLLIT().toString().toBoolean)
    }

    literal
  }

  override def visitStat(ctx: BKOOLParser.StatContext) = {
    visit(ctx.getChild(0))
  }

  override def visitListStat(ctx: BKOOLParser.ListStatContext) = {
    ctx.stat().asScala.map(visit).toList
  }

  override def visitListDecl(ctx: BKOOLParser.ListDeclContext) = {
    val attributeList = flatten(ctx.attribute().asScala.map(visit).toList)
    val declList = attributeList.map(x => x.asInstanceOf[AttributeDecl].decl)
    declList
  }

  override def visitBlockStat(ctx: BKOOLParser.BlockStatContext) = {
    val decl = if (ctx.listDecl() != null) visit(ctx.listDecl()).asInstanceOf[List[Decl]] else List()
    val stmt = if (ctx.listStat() != null) visit(ctx.listStat()).asInstanceOf[List[Stmt]] else List()
    Block(decl, stmt)
  }

  override def visitAssignmentStat(ctx: BKOOLParser.AssignmentStatContext) = {
    val leftHandSide = visit(ctx.exp(0)).asInstanceOf[LHS]
    val expr = visit(ctx.exp(1)).asInstanceOf[Expr]
    Assign(leftHandSide, expr)
  }

  override def visitIfStat(ctx: BKOOLParser.IfStatContext) = {
    val expr = visit(ctx.exp()).asInstanceOf[Expr]
    val thenStmt = visit(ctx.stat(0)).asInstanceOf[Stmt]

    val elseStmt = if (ctx.stat(1) != null) Option(visit(ctx.stat(1)).asInstanceOf[Stmt]) else None
    If(expr, thenStmt, elseStmt)
  }

  override def visitWhileStat(ctx: BKOOLParser.WhileStatContext) = {
    val expr = visit(ctx.exp()).asInstanceOf[Expr]
    val loop = visit(ctx.stat()).asInstanceOf[Stmt]
    While(expr, loop)
  }

  override def visitBreakStat(ctx: BKOOLParser.BreakStatContext) = Break

  override def visitContinueStat(ctx: BKOOLParser.ContinueStatContext) = Continue

  override def visitReturnStat(ctx: BKOOLParser.ReturnStatContext) = {
    val expr = visit(ctx.exp()).asInstanceOf[Expr]
    Return(expr)
  }

  override def visitMethodInvocationStat(ctx: BKOOLParser.MethodInvocationStatContext) = {
    val parent = visit(ctx.exp()).asInstanceOf[Expr]
    val method = Id(ctx.ID().getText)
    val params = if (ctx.listExp() != null) visit(ctx.listExp()).asInstanceOf[List[Expr]] else List()
    Call(parent, method, params)
  }
}