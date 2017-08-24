import java.util.function.Supplier;
import aeminium.runtime.futures.*;

class F {
   public static <T> Future<T> future(Supplier<T> f) {
      return new Future<T>((t) -> f.get());
   }
   public static <T> T get(Future<T> f) {
      return f.get();
   }
}
