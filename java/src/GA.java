import java.util.ArrayList;
import java.util.HashMap;

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
  
  
}