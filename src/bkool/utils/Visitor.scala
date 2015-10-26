package bkool.utils

/**
 * @author nhphung
 */
trait Visitor {
  def visit(ast: AST, c: Context): Object = ast.accept(this,c)
  def visitProgram(ast: Program, c: Context): Object
  def visitVarDecl(ast: VarDecl, c: Context): Object
  def visitConstDecl(ast: ConstDecl, c: Context): Object
  def visitParamDecl(ast: ParamDecl, c: Context): Object
  def visitClassDecl(ast: ClassDecl, c: Context): Object
  def visitMethodDecl(ast: MethodDecl, c: Context): Object
  def visitAttributeDecl(ast: AttributeDecl, c: Context): Object
  def visitInstance(ast: Instance.type, c: Context): Object
  def visitStatic(ast: Static.type, c: Context): Object
  def visitIntType(ast: IntType.type, c: Context): Object 
  def visitFloatType(ast: FloatType.type, c: Context): Object
  def visitBoolType(ast: BoolType.type, c: Context): Object
  def visitStringType(ast: StringType.type, c: Context): Object
  def visitVoidType(ast: VoidType.type, c: Context): Object
  def visitArrayType(ast: ArrayType, c: Context): Object
  def visitClassType(ast: ClassType, c: Context): Object
  def visitBinaryOp(ast: BinaryOp, c: Context): Object
  def visitUnaryOp(ast: UnaryOp, c: Context): Object
  def visitNewExpr(ast: NewExpr, c: Context): Object
  def visitCallExpr(ast: CallExpr, c: Context): Object
  def visitId(ast: Id, c: Context): Object
  def visitArrayCell(ast: ArrayCell, c: Context): Object
  def visitFieldAccess(ast: FieldAccess, c: Context): Object
  def visitBlock(ast: Block, c: Context): Object
  def visitAssign(ast: Assign, c: Context): Object
  def visitIf(ast: If, c: Context): Object
  def visitCall(ast: Call, c: Context): Object
  def visitWhile(ast: While, c: Context): Object
  def visitBreak(ast: Break.type, c: Context): Object
  def visitContinue(ast: Continue.type, c: Context): Object
  def visitReturn(ast: Return, c: Context): Object
  def visitIntLiteral(ast: IntLiteral, c: Context): Object
  def visitFloatLiteral(ast: FloatLiteral, c: Context): Object
  def visitStringLiteral(ast: StringLiteral, c: Context): Object
  def visitBooleanLiteral(ast: BooleanLiteral, c: Context): Object
  def visitNullLiteral(ast: NullLiteral.type, c: Context): Object
  def visitSelfLiteral(ast: SelfLiteral.type, c: Context): Object
}
