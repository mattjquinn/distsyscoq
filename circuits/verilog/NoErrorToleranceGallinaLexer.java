import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.LexerNoViableAltException;
import antlrgallinaparser.GallinaLexer;

/**
 * This lexer does not recover from lexer errors; it fails
 * irrecoverably instead.
 */
public class NoErrorToleranceGallinaLexer extends GallinaLexer {

  /**
   * @param input the CharStream to lex
   */
  public NoErrorToleranceGallinaLexer(final CharStream input) {
    super(input);
  }

  @Override
  public void recover(final LexerNoViableAltException e) {
    throw new RuntimeException(e.getMessage(), e);
  }
}
