class D: pass
class E: pass
class H: pass

class B(D, E): pass
class A(E, H): pass
class C(B, A): pass

# Print the MRO for class C
print(C.__mro__)

