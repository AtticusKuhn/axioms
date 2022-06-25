# Axioms

We wrote up some of the proofs from our number theory course in lean

##Commutative Rings Axioms

* (commutative addition) a+b=b+a
* (commutative multiplication) ab=ba
* (associative addtion) a+(b+c) = (a+b)+c
* (associative multiplication) a(bc)= (ab)c
* (zero) a+0=a
* (negatives) a+(-a) = 0
* (one) a(1) = a

##Ordered Ring Axioms

* There is a nonempty subset of the ring, which we will call P, representing numbers that are positive
* P is implemented in lean as the proposition `is_positive`
* (closed multiplication) if a is an element of P and b is an element of P then a * b is an element of P
* (closed addition) if a is an element of P and b is an element of P then a + b is an element of P
* (nontriviality) 0 is not an element of P
* (trichotomy) For every element of the ring, it is in P, or it is zero, or its inverse is in P

##Misc

* (less than) a < b is defined to mean that there exists a positive number p such that b = a + p 
