import java.util.ArrayList;
import java.util.HashMap;
import java.util.Random;
import java.util.function.Predicate;
import java.util.function.Consumer;

public class GA {
  public static HashMap<Integer,ArrayList<Double>> fitnesses = new HashMap<>();
  
  public static Double addFitness(Integer i, Double v) {
    if (!fitnesses.containsKey(i)) {
      fitnesses.put(i, new ArrayList<>());
    }
    fitnesses.get(i).add(v);
    return v;
  }
  
  public static Double getFitness() {
    if (fitnesses.isEmpty()) return 1000.0;
    double fitness = 0;
    for (int k : fitnesses.keySet()) {
      double subfitness = 0;
      double subvalues = 0;
      for (double d : fitnesses.get(k)) {
        subfitness += d;
        subvalues += 1;
      }
      if (subvalues > 0) {
          subfitness /= subvalues;
          fitness += subfitness;
      }
    }
    return fitness / fitnesses.size();
  }
  
  
  public static void genInteger(Integer size, Integer seed, Predicate<Integer> pred, Consumer<Integer> c) {
    Random r = new Random(seed);
    int i = 0;
    while (i < size) {
      Integer t = r.nextInt(100)-50;
      if (pred.test(t)) {
        c.accept(t);
        i++;
      }
    }
  }
  
  public static <T> void genObject(Integer size, T object, Predicate<T> pred, Consumer<T> c) {
    int i = 0;
    while (i < size) {
      if (pred.test(object)) {
        c.accept(object);
        i++;
      }
    }
  }
  
  public static void genTests(Integer size, Runnable c) {
    int i = 0;
    while (i < size) {
        c.run();
        i++;
    }
  }
  
}