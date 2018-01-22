import java.util.ArrayList;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Consumer;

public class A {
	public static <T> ArrayList<T> array(int size) {
		return new ArrayList<>(size);
	}
  
	public static ArrayList<Integer> range(int mi, int ma) {
		ArrayList<Integer> ar = new ArrayList<>(ma-mi);
    for (int i=mi; i<ma; i++)
      ar.add((Integer)i);
    return ar;
	}

	public static <T> T get(ArrayList<T> a, int i) {
		return a.get(i);
	}

	public static <T> ArrayList<T> set(ArrayList<T> a, int i, T v) {
		a.set(i, (T) v);
		return a;
	}
  
  public static <T> Integer size(ArrayList<T> a) {
    return a.size();
  }
  
  public static <T> ArrayList<T> forEach(ArrayList<T> a, Consumer<T> c) {
    a.forEach(c);
    return a;
  }
  

	public static <T,I> ArrayList<I> map(ArrayList<T> a, Function<T,I> f) {
		ArrayList<I> n = new ArrayList<>();
		for (T e : a) {
			n.add(f.apply(e));
		}
		return n;
	}

	public static <T> T reduce(ArrayList<T> a, BiFunction<T,T,T> f) {
		T i = null;
		for (T e : a) {
			if (i == null) {
				i = e;
			} else {
				i = f.apply(i, e);
			}
		}
		return i;
	}
}
