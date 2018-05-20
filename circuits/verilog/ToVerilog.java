import java.io.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import antlrgallinaparser.*;
import antlrgallinaparser.GallinaParser.*;
import java.util.*;
import java.time.format.*;
import java.text.SimpleDateFormat;

public class ToVerilog {

  static class GallinaVisitor extends GallinaBaseVisitor<String> {

    private static Map<String, Record> records = new HashMap<>();

    static class Record {
      static String name;
      static Map<String, String> fields = new HashMap<>();
      Record(String name) {
        this.name = name;
      }
    }

    @Override
    public String visitRequireImport (GallinaParser.RequireImportContext ctx) {
      return "";
    }

    @Override
    public String visitSentences(GallinaParser.SentencesContext ctx) {
      String out = "";
      for (SentenceContext sc : ctx.sentence()) {
        out += this.visit(sc);
      }
      return out;
    }

    @Override
    public String visitNotation(GallinaParser.NotationContext ctx) {
      System.out.println("Visiting notation...");
      this.visitChildren(ctx);
      System.out.println("Notation " + ctx.STRING_LITERAL().getText());
      return "";
    }

    @Override
    public String visitRecord(GallinaParser.RecordContext ctx) {
      System.out.println("Visiting record...");
      this.visitChildren(ctx);
      String recName = ctx.ID().getText();
      System.out.println("Record " + recName);
      Record rec = new Record(recName);
      for (FieldContext fc : ctx.fields().field()) {
        String fieldType = fc.term().getText();
        if (!fieldType.equals("bit")) {
          throw new RuntimeException("Unsupported field type: " + fieldType
              + "; only supporting bit for now.");
        }
        rec.fields.put(fc.name().getText(), fieldType);
      }
      this.records.put(recName, rec);
      return "";
    }

    @Override
    public String visitDefinition(GallinaParser.DefinitionContext ctx) {
      System.out.println("Visiting definition...");
      this.visitChildren(ctx);

      // INPUTS
      List<String> inputs = new ArrayList<String>();
      for (BinderContext bc : ctx.binders().binder()) {
        String type = bc.term().getText();
        if (!type.equals("bit")) {
          throw new RuntimeException("Unsupported binder type: " + type
              + "; only supporting bit for now.");
        }
        for (TerminalNode id : bc.ID()) {
          inputs.add(id.getText());
        }
      }

      // OUTPUTS
      String defnType = ctx.ty.getText();
      Record outRec = this.records.get(defnType);
      Set<String> outputs = outRec.fields.keySet();

      // ASSIGNMENTS
      Map<String, String> assgmts = new HashMap<>();
      // Expects a record instance in definition body for now.
      for (FieldAssgmtContext fac :
          ((TermRecordInstanceContext) ctx.body).fieldAssgmt()) {
        String outputName = fac.ID().getText();
        String outputExpr = this.visit(fac.term());
        System.out.println("Output name: " + outputName);
        System.out.println("Output expr: " + outputExpr);
        assgmts.put(outputName, outputExpr);
      }

      // *** VERILOG OUTPUT *****************************************/
      SimpleDateFormat sdfDate = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");
      Date now = new Date();
      String verilog = "/**************************************************\n"
                     + " * COQ-TO-VERILOG DESCRIPTION FILE\n"
                     + " * GENERATED " + sdfDate.format(new Date()) + "\n"
                     + " **************************************************/\n";
      verilog += "module " + ctx.ID().getText();
      verilog += "\n  (\n    input ";
      for (String in : inputs) {
        verilog += in + ", ";
      }
      verilog += "\n    output ";
      Iterator<String> outit = outputs.iterator();
      while (outit.hasNext()) {
        verilog += outit.next();
        // Last output shouldn't have a trailing comma.
        if (outit.hasNext()) {
          verilog += ", ";
        }
      }
      verilog += "\n  );\n\n";
      for (Map.Entry<String, String> entry : assgmts.entrySet()) {
        verilog += "  assign " + entry.getKey() + " = " + entry.getValue() + ";\n";
      }
      verilog += "\nendmodule";
      return verilog;
    }

    @Override
    public String visitTermInfixFuncCall(
        GallinaParser.TermInfixFuncCallContext ctx) {
      System.out.println("Visiting infix func call...");
      String lhs = this.visit(ctx.lhs);
      String op = ctx.op.getText();
      String rhs = this.visit(ctx.rhs);
      System.out.println("OP: " + op);
      // TODO: Eventually link into notation definitions before xlating.
      switch (op) {
        case "|":
        case "&":
          return lhs + " " + op + " " + rhs;
        case "XOR":
          return lhs + " ^ " + rhs;
        default:
          throw new RuntimeException("Unexpected infix operation: " + op);
      }
    }

    @Override
    public String visitTermId(GallinaParser.TermIdContext ctx) {
      return ctx.ID().getText();
    }

    @Override
    public String visitTermParenthesized(
        GallinaParser.TermParenthesizedContext ctx) {
      return "(" + this.visit(ctx.term()) + ")";
    }
  }

  public static void main(String[] args) throws IOException {

    if(args.length != 2) {
      System.out.println("Usage: java ToVerilog "
          + "<input_path_to_Coq_file> <output_path_for_Verilog_file>");
      System.exit(1);
    }

    CharStream charStream = CharStreams.fromPath(Paths.get(args[0]));
    GallinaLexer lexer = new GallinaLexer(charStream);
    CommonTokenStream tokens = new CommonTokenStream(lexer);
    tokens.fill();  // Get all tokens until EOF.
    System.out.println("Tokens: " + tokens.size());
    GallinaParser parser = new GallinaParser(tokens);
    final ParseTree parseTree = parser.sentences();
    final GallinaVisitor gallinaVisitor = new GallinaVisitor();
    String verilogCode = gallinaVisitor.visit(parseTree);

    System.out.println(verilogCode);

    BufferedWriter out = new BufferedWriter(new FileWriter(args[1]));
    out.write(verilogCode);
    out.close();
  }
}
