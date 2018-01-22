import java.util.function.Supplier;

class J {

   public static <T> T iif(boolean c, Supplier<T> a, Supplier<T> b) {
      if (c)
         return a.get();
      else
         return b.get();
   }

   public static Object out(Object i) {
      System.out.println("" + i);
      return i;
   }

   public static void noop(Object o) {
      // Do nothing
   }
   
   public static <T> T timeit(Supplier<T> lambda) {
	   long init = System.nanoTime();
	   T a = lambda.get();
	   long time = System.nanoTime() - init;
	   System.out.println("Timer: " + (time / 1000000000.0) );
	   return a;
   }

}
