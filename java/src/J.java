import java.util.function.Supplier;

class J {

   public static <T> T iif(boolean c, Supplier<T> a, Supplier<T> b) {
      if (c)
         return a.get();
      else
         return b.get();
   }

   public static Integer out(Integer i) {
      System.out.println("" + i);
      return i;
   }

   public static void noop(Object o) {
      // Do nothing
   }

}
