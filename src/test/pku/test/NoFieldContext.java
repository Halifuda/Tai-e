package test;

import benchmark.internal.Benchmark;
import benchmark.objects.A;
import benchmark.objects.B;

public class NoFieldContext {
    public static A assign(A x, A y) {
        return x;
    }

    public static void main(String[] args) {
        Benchmark.alloc(1);
        A a = new A();
        Benchmark.alloc(2);
        A b = new A();
        a = assign(b, a);
        Benchmark.test(1, a); // expected: 2
    }
}
