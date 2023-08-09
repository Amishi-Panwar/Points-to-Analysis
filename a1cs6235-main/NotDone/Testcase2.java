class Testcase2 {
  void m1() {
	T2A x,y,z;
	x = new T2A();
	y = new T2A();
	x.a= new T2B();
	y.a= new T2B();
	z=y; 
	if(true)
	{
		y.a=x.a;
		y=x;
	}
 }
}

class T2A{
	T2B a;
}

class T2B{
	int c;
}