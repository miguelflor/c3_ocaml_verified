class O: pass
class A (O): pass
class B (O): pass
class C (O): pass
class D (O) : pass
class E (O) : pass
class K1 (C, A, B) : pass
class K3 (A, D) : pass
class K2 (B, D, E) : pass
class Z (K1, K3, K2) : pass

print(Z.__mro__)