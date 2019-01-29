
        public class FitnessEvaluator {
            



























 public static void test0(Integer __argument_0, Integer __return_0) { J.noop(
            GA.addFitness(Integer.valueOf(0), 
            Math.abs((Double.valueOf(1.0) * (__return_0 - (Integer.valueOf(3) * __argument_0))))
        )
        ); }

 public static void main(String[] args) { aeminium.runtime.futures.RuntimeManager.init();

            GA.genInteger(Integer.valueOf(100), Integer.valueOf(680), (Integer __return_0) -> { return (true); }, (Integer __argument_0) -> { Integer __return_0 = 
            Candidate.three(__argument_0)
        ;

            test0(__argument_0, __return_0)
        ; })
        ;

            System.out.println(
            GA.getFitness()
        )
        ;
aeminium.runtime.futures.RuntimeManager.shutdown(); }
        }
        