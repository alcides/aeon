import java.util.Random;
import java.util.ArrayList;

public class R {
  
  private static Random r = new Random(1L);
  
	public static ArrayList<Integer> randomInts(int size) {
		ArrayList<Integer> arr = new ArrayList<>(size);
    for (int i = 0; i<size; i++)
      arr.add(r.nextInt(100));
    return arr;
	}
  
	public static ArrayList<Double> randoms(int size) {
		ArrayList<Double> arr = new ArrayList<>(size);
    for (int i = 0; i<size; i++)
      arr.add(r.nextDouble());
    return arr;
	}
  
}
