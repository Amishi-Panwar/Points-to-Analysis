class Main {
	public static void main (String [] args) {
		A a = new A ();
		a.f = new F();
		
		B b = new B();

		a.foo();

		C c = new C();
		c.fooBar(a);
	}
}

class A {
	F f;
	void foo () { System.out.println("hello from A foo");} 
}

class B extends A {
	@Override
	void foo () { System.out.println("hello from B foo"); }
}

class D extends B { 
	void foo () { System.out.println("hello from D foo"); }
}
class C {
	void fooBar(A p) { 
		p.foo(); 
	}
}

class F {}
