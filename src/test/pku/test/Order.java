package test;

import benchmark.internal.Benchmark;
import benchmark.objects.A;

/**
 * Order is important.
 */
public class Order {
  public static void main(String[] args) {
    A a = null;
    Benchmark.alloc(1);
    A b = new A();
    Benchmark.alloc(2);
    A c = new A();
    a = b;
    b = c;
    Benchmark.test(1, a); // expect 1
    Benchmark.test(2, b); // expect 2
  }
}
