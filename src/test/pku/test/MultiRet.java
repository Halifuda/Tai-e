package test;

import benchmark.internal.Benchmark;
import benchmark.objects.B;

public class MultiRet {
    public static B rets(B x, B y, String[] args) {
        if (args.length > 1) {
            return x;
        } else {
            return y;
        }
    }

    public static void main(String[] args) {
        Benchmark.alloc(1);
        B a = new B();
        Benchmark.alloc(2);
        B b = new B();
        B c = rets(a, b, args);
        Benchmark.test(1, c);
    }
}
