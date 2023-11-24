package test;

import benchmark.internal.Benchmark;
import benchmark.objects.A;
import benchmark.objects.B;

/*
 * @testcase FieldSensitivity2
 * 
 * @version 1.0
 * 
 * @author Johannes Späth, Nguyen Quang Do Lisa (Secure Software Engineering Group, Fraunhofer
 * Institute SIT)
 * 
 * @description Field Sensitivity without static method
 */
public class Field {

  public Field() {}

  private void test() {	  
    Benchmark.alloc(1);
    B b = new B();
    Benchmark.alloc(2);
    A a = new A(b);

    Benchmark.test(1, a.f); // expected: 1
    Benchmark.test(2, a);   // expected: 2
  }

  public static void main(String[] args) {
    Field fs = new Field();
    fs.test();
  }
}
