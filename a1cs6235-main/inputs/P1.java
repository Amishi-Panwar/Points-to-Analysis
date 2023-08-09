// only a1 and a5 are not alias. Everything else becomes bottom
class T26{
	public static void main(String[] args){
		A26 a1;
		A26 a2;
		A26 a3;
		A26 a4;
		A26 a5;
		A26 a6;
		A26 a7;
		A26 a8;
		A26 a9;
		A26 a10;

		a1 = new A26();
		a2 = new A26();
		a1.f1 = a2;
		a3 = new A26();
		a1.f2 = a3;
		a4 = new A26();
		a1.f3 = a4;
		
		a5 = new A26();
		a6 = new A26();
		a5.f1 = a6;
		a7 = new A26();
		a5.f2 = a7;

		a8 = new A26();
		a2.f1 = a8;
		a9 = new A26();
		a2.f2 = a9;

		
		a10 = a1.foo(a5);
		a2 = a1.f1;
		a8 = a2.f1;
		a9 = a2.f2;
		a3 = a1.f2;
		a6 = a5.f1;
		a7 = a5.f2;
	}
}

class A26{
	A26 f1;
	A26 f2;
	A26 f3;
	public A26 foo(A26 p1){
		A26 a;
		a = this;
		return a;
	}
}
class P1{
	
}