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
    int values = 0;
    for (int k : fitnesses.keySet()) {
      for (double d : fitnesses.get(k)) {
        fitness += d;
        values += 1;
      }
    }
    return fitness / values;
  }
  
  public static void genInteger(Integer size, Integer seed, Predicate<Integer> pred, Consumer<Integer> c) {
    Random r = new Random(seed);
    int i = 0;
    while (i < size) {
      Integer t = r.nextInt();
      if (pred.test(t)) {
        c.accept(t);
        i++;
      }
    }
  }
  
}