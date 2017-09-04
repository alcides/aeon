import java.util.ArrayList;
import java.util.function.BiFunction;
import java.util.function.Function;

public class A {
	public static <T> ArrayList<T> array(int size) {
		return new ArrayList<>();
	}

	public static <T> T get(ArrayList<T> a, int i) {
		return a.get(i);
	}

	public static <T> ArrayList<T> set(ArrayList<T> a, int i, T v) {
		a.set(i, v);
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
