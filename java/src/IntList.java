import java.util.ArrayList;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Consumer;
import java.util.Random;

public class IntList extends ArrayList<Integer> {
  
	public static IntList range(int mi, int ma) {
		IntList ar = new IntList();
		for (int i=mi; i<ma; i++)
			ar.add((Integer)i);
		return ar;
	}

	public static Integer get(IntList a, int i) {
		return a.get(i);
	}

	public static IntList set(IntList a, int i, Integer v) {
		a.set(i, v);
		return a;
	}
  
	public static  Integer size(IntList a) {
		return a.size();
	}
  
	public static IntList forEach(IntList a, Consumer c) {
		a.forEach(c);
		return a;
	}
  
	public static IntList forEachIndex(IntList a, BiFunction<Integer, Integer, Void> c) {
		int i = 0;
		for (Integer e : a) {
			c.apply(i++,e);
		}
		return a;
	}
  
	public static  Boolean forall(IntList a, Function<Integer, Boolean> f) {
		boolean b = true;
		for (Integer v : a) {
			b = b && f.apply(v);
		}
		return b;
	}
  

	public static IntList map(IntList a, Function<Integer,Integer> f) {
		IntList n = new IntList();
		for (Integer e : a) {
			n.add(f.apply(e));
		}
		return n;
	}

	public static  Integer reduce(IntList a, BiFunction<Integer,Integer,Integer> f) {
		Integer i = null;
		for (Integer e : a) {
			if (i == null) {
				i = e;
			} else {
				i = f.apply(i, e);
			}
		}
		return i;
	}
	
	public static IntList copy(IntList a) {
		return IntList.map(a, (Integer i) -> i);
	}
	
	public static  IntList append(IntList a, Integer e) {
		IntList t = IntList.copy(a);
		t.add(e);
		return t;
	}
	
	public static IntList randomIntArray() {
		Random r = new Random();
		IntList arr = new IntList();
		for (int i=0; i<r.nextInt(); i++){
			arr.add(r.nextInt());
		}
		return arr;
	}
	
}
