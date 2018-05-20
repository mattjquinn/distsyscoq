import org.antlr.v4.runtime.DefaultErrorStrategy;
import org.antlr.v4.runtime.InputMismatchException;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Token;

/**
 * This error strategy bails out upon encountering the
 * first syntax error; no recovery is attempted.
 */
public class GallinaErrorStrategy extends DefaultErrorStrategy {

  /**
   * Default no-args constructor.
   */
  public GallinaErrorStrategy() {}

  @Override
  public void recover(final Parser recognizer,
      final RecognitionException e) {
    throw new RuntimeException(e.getMessage(), e);
  }

  // Prevents recovery from inline errors.
  @Override
  public Token recoverInline(final Parser recognizer) {
    final InputMismatchException ime = new InputMismatchException(recognizer);
    throw new RuntimeException(ime.getMessage(), ime);
  }

  // Prevents recovery from errors in subrules.
  @Override
  public void sync(final Parser recognizer) { }
}
