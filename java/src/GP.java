import java.util.ArrayList;
import java.util.HashMap;
import java.util.Random;
import java.util.function.Predicate;
import java.util.function.Consumer;

public class GP {

    // Atributos
    public static HashMap<Integer,ArrayList<Double>> fitnesses = new HashMap<>();

    public static Double addFitness(Integer i, Double v) {
        if (!fitnesses.containsKey(i)) {
            fitnesses.put(i, new ArrayList<>());
        }
        fitnesses.get(i).add(v);
        return v;
    }

    public static Double getFitness() {
        if (fitnesses.isEmpty())
            return 1000.0;

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
            try {
                if (pred.test(t)) {
                    c.accept(t);
                    i++;
                }
            } catch (Exception e) {
                i++;
            }
        }
    }

    public static void genDouble(Integer size, Integer seed, Predicate<Double> pred, Consumer<Double> c) {
        Random r = new Random(seed);
        int i = 0;
        while (i < size) {
            Double t = -50.0 + (100.0 - (-50.0)) * r.nextDouble();
            try {
                if (pred.test(t)) {
                    c.accept(t);
                    i++;
                }
            } catch (Exception e) {
                i++;
            }
        }
    }

    public static void genBoolean(Integer size, Integer seed, Predicate<Boolean> pred, Consumer<Boolean> c) {
        Random r = new Random(seed);
        int i = 0;
        while (i < size) {
            Boolean t = r.nextBoolean();
            try {
                if (pred.test(t)) {
                    c.accept(t);
                    i++;
                }
            } catch (Exception e) {
                i++;
            }
        }
    }

    public static void genFloat(Integer size, Integer seed, Predicate<Float> pred, Consumer<Float> c) {
        Random r = new Random(seed);
        int i = 0;
        while (i < size) {
            Float t = -50.0f + (100.0f - (-50f)) * r.nextFloat();
            try {
                if (pred.test(t)) {
                    c.accept(t);
                    i++;
                }
            } catch (Exception e) {
                i++;
            }
        }
    }

    public static void genString(Integer size, Integer seed, Predicate<String> pred, Consumer<String> c) {
        Random r = new Random(seed);
        int i = 0;
        while (i < size) {
            String t = "x" + r.nextInt(1000000);
            try {
                if (pred.test(t)) {
                    c.accept(t);
                    i++;
                }
            } catch (Exception e) {
                i++;
            }
        }
    }

    public static <T> void genObject(Integer size, T object, Predicate<T> pred, Consumer<T> c) {
        int i = 0;
        while (i < size) {
            try {
                if (pred.test(object)) {
                    c.accept(object);
                    i++;
                }
            } catch (Exception e) {
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
