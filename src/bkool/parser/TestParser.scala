

/**
 * @author nhphung
 */
package bkool.parser

import java.io.{PrintWriter,File}
import org.antlr.v4.runtime.ANTLRFileStream
import org.antlr.v4.runtime.CommonTokenStream




//import ProgramContext;

object TestParser extends ProcessError {
    

  def main(args:List[String]) {
    if (args.length == 2) {
      val inputFile = new ANTLRFileStream(args(0))
      val out = new PrintWriter(new File(args(1)));
      try {
        test(inputFile,out);
      }    
      catch  {
        case e:Exception => out.println(e.getMessage());
      }
      finally {
        out.close()
      }
    } 
    else 
        println("Usage: scala TestParser <input file> <output file>")
  }

    /**
     * Parses an expression into an integer result.
     * @param expression the expression to part
     * @return and integer result
     */

    def test(fileName:ANTLRFileStream,outFile:PrintWriter) = {
        /*
         * Create a lexer that reads from our expression string
         */
        val lexer = new BKOOLLexer(fileName); // ANTLRInputStream
        val _listener = createErrorListener();
        

        /*
         * The lexer reads characters and lexes them into token stream. The
         * tokens are consumed by the parser that then builds an Abstract
         * Syntax Tree.
         */
        val tokens = new CommonTokenStream(lexer);

        val parser = new BKOOLParser(tokens);
        parser.removeErrorListeners();
        parser.addErrorListener(_listener);
    try {
      parser.program();
      outFile.println("sucessful");
    } catch {
      case e:Exception => outFile.println(e.getMessage());
    }
    
    }
}