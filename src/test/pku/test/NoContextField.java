package test;

import benchmark.internal.Benchmark;
import benchmark.objects.A;
import benchmark.objects.B;

public class NoContextField {
    public static void main(String[] args) {
        Benchmark.alloc(1);
        B b = new B();
        Benchmark.alloc(2);
        A a = new A();
        a.f = b;
        B d = a.f;
        Benchmark.test(1, d); // expected: 1
    }
}
