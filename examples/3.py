class D: pass
class E: pass
class H: pass
class F: pass
class B(E,D): pass
class C(F,D): pass
class G(H,D): pass
class A(B,C,G): pass
# Print the MRO for class A
print(A.__mro__)