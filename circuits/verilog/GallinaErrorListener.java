import java.util.Collections;
import java.util.List;
import org.antlr.v4.runtime.DiagnosticErrorListener;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;

/**
 * This listener does not tolerate ANTLR errors of any kind,
 * including ambiguous grammar alternatives (unless explicitly exempted
 * below). Every exception received
 * here is wrapped as a untime exception and bubbled up.
 */
public class GallinaErrorListener extends DiagnosticErrorListener {

  /**
   * Default, no-args constructor.
   */
  public GallinaErrorListener() {}

  @Override
  public void syntaxError(final Recognizer<?, ?> recognizer,
      final Object offendingSymbol, final int line,
      final int charPositionInLine, final String msg,
      final RecognitionException ex) {

    // If ANTLR reports that it is switching from SLL(*) to ALL(*)
    // parsing, that is not an error; no need to throw an exception here.
    if (msg.startsWith("reportAttemptingFullContext")) {
      return;
    }

    // If ANTLR reports that a full-context prediction returned a
    // unique result, that is not an error; no need to throw an
    // exception here.
    if (msg.startsWith("reportContextSensitivity")) {
      return;
    }

    final List<String> stack = ((Parser) recognizer).getRuleInvocationStack();
    Collections.reverse(stack);
    final StringBuilder builder = new StringBuilder();
    builder.append("line ").append(line);
    builder.append(':').append(charPositionInLine);
    builder.append(" at ").append(offendingSymbol);
    builder.append(": ").append(msg);
    builder.append(". Rule stack: ").append(stack);
    throw new RuntimeException(builder.toString(), ex);
  }
}
