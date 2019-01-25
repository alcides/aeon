
public class E {

  public static void forIndex(Integer n, java.util.function.Consumer<Integer> f) {
    java.util.ArrayList<Integer> a = A.range(Integer.valueOf(0), n);
    J.noop(A.forEach(a, f));
  }

  public static void swap(java.util.ArrayList<Integer> a, Integer x, Integer y) {
    Integer x_v = A.get(a, x);
    Integer y_v = A.get(a, y);
    J.noop(A.set(a, x, y_v));
    J.noop(A.set(a, y, x_v));
  }

  public static java.util.ArrayList<Integer> reverse(java.util.ArrayList<Integer> in) {
    return A.map(
        A.range(Integer.valueOf(0), A.size(in)),
        (Integer i) -> {
          return A.get(in, ((A.size(in) - i) - Integer.valueOf(1)));
        });
  }

  public static void main(String[] underscore1) {
    aeminium.runtime.futures.RuntimeManager.init();
    java.util.ArrayList<Integer> a = A.range(Integer.valueOf(0), Integer.valueOf(32));
    java.util.ArrayList<Integer> r = reverse(a);
    J.noop(J.out(A.get(r, Integer.valueOf(0))));
    aeminium.runtime.futures.RuntimeManager.shutdown();
  }
}
