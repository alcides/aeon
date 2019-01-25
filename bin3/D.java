import java.util.HashMap;

public class D {
	public static <K,V> HashMap<K,V> dict() {
		return new HashMap<>();
	}
	
	public static <K,V> V get(HashMap<K,V> a, K i) {
		return a.get(i);
	}
	
	public static <K,V> V del(HashMap<K,V> a, K i) {
		return a.remove(i);
	}
	
	public static <K,V> HashMap<K,V> set(HashMap<K,V> a, K i, V v) {
		a.put(i, v);
		return a;
	}
}
