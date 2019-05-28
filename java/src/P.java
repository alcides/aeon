public class P<K,V> {
	public K _0;
	public V _1;
	
	public P(K a, V b) {
		this._0 = a;
		this._1 = b;
	}
	
	public static <TA,TB> P<TA,TB> pair(TA a, TB b) {
		return new P<TA,TB>(a,b);
	}
	
	public static <TA,TB> TA fst(P<TA,TB> p) {
		return p._0;
	}
	
	public static <TA,TB> TB snd(P<TA,TB> p) {
		return p._1;
	}
}
