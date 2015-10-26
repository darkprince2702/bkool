package bkool.checker

/**
 * @author nhphung
 */


import bkool.parser._
import bkool.utils._
import java.io.{PrintWriter,File}
import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree._


object TestChecker {
  def test(infile:ANTLRFileStream,outfile:PrintWriter) = {
    val lexer = new BKOOLLexer(infile);
    val tokens = new CommonTokenStream(lexer);
    val parser = new BKOOLParser(tokens);
    val progtree = parser.program()
    
    val astbuild = new ASTGeneration()
    val ast = astbuild.visit(progtree).asInstanceOf[Program]
    //val ast = null
    try {
      val checker = new StaticChecker(ast)
      checker.check()
    } catch {
      case Undeclared(k, n)  => outfile.println("Undeclared "+k+": "+n)
      case Redeclared(k, n)  => outfile.println("Redeclared "+k+": "+n)
      case CannotAssignToConstant(s) => outfile.println("Cannot Assign To Constant: "+s)
      case TypeMismatchInExpression(exp) => outfile.println("Type Mismatch In Expression: "+exp)
      case TypeMismatchInStatement(stmt) => outfile.println("Type Mismatch In Statement: "+stmt)
      case TypeMismatchInConstant(cons) => outfile.println("Type Mismatch In Constant: "+cons)

      /* These exception classes are used by KSTN only */
      case CannotAccessPrivateAttribute(cName, attr) => outfile.println("Cannot Access Private Attribute: "+attr+" of class "+cName)
      case MethodNotReturn(m) => outfile.println("Method Not Return: "+m)
      case BreakNotInLoop(line) => outfile.println("Break Not In Loop: "+line)
      case ContinueNotInLoop(line) => outfile.println("Continue Not In Loop: "+line)
      case NotConstantExpression(exp) => outfile.println("Not Constant Expression: "+exp)
    }
  }
  
}