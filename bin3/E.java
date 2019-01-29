
public class E {

  public static Integer three(Integer i) {
    return (Integer.valueOf(3) * i);
  }

  public static void main(String[] underscore1) {
    aeminium.runtime.futures.RuntimeManager.init();
    J.noop(J.out(three(Integer.valueOf(3))));
    aeminium.runtime.futures.RuntimeManager.shutdown();
  }
}
