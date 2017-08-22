import java.util.function.Supplier;

class J {
   
   public static <T> T iif(boolean c, Supplier<T> a, Supplier<T> b) {
      if (c)
         return a.get();
      else
         return b.get();
   }
   
   public static void out(Integer i) {
      System.out.println("" + i);
   }
   
}