import java.util.ArrayList;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Consumer;

public class P<K,V> {
	public K _0;
	public V _1;
	
	public P(K a, V b) {
		this._0 = a;
		this._1 = b;
	}
	
	public static <A,B> P<A,B> pair(A a, B b) {
		return new P<A,B>(a,b);
	}
	
	public static <A,B> A fst(P<A,B> p) {
		return p._0;
	}
	
	public static <A,B> B snd(P<A,B> p) {
		return p._1;
	}
}
