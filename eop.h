// eop.h

// Copyright (c) 2009 Alexander Stepanov and Paul McJones
//
// Permission to use, copy, modify, distribute and sell this software
// and its documentation for any purpose is hereby granted without
// fee, provided that the above copyright notice appear in all copies
// and that both that copyright notice and this permission notice
// appear in supporting documentation. The authors make no
// representations about the suitability of this software for any
// purpose. It is provided "as is" without express or implied
// warranty.


// Algorithms from
// Elements of Programming
// by Alexander Stepanov and Paul McJones
// Addison-Wesley Professional, 2009


#ifndef EOP_EOP
#define EOP_EOP

#include "assertions.h"
#include "intrinsics.h"
#include "type_functions.h"
#include "pointers.h"
#include "integers.h"

#include <cstdlib> // malloc, free
#include <cmath> // sqrt


// 
//  Chapter 1. Foundations
// 


int plus_0(int a, int b)
{
    return a + b;
}

int plus_1(const int& a, const int& b)
{
    return a + b;
}

void plus_2(int* a, int* b, int* c)
{
    *c = *a + *b;
}

int square(int n) { return n * n; }

template<typename Op>
    requires(BinaryOperation(Op))
EOPDomain(Op) square(EOPDomain(Op) const& x, Op op)
{
    return op(x, x);
}


// Function object for equality

template<typename T>
    requires(Regular(T))
struct equal
{
    typedef T input_type_0;
    typedef T input_type_1;
    typedef bool codomain_type;

    bool operator()(T const& x, T const& y)
    {
        return x == y;
    }
};


// type pair (see chapter 12 of Elements of Programming)
// model Regular(Pair)

template<typename T0, typename T1>
    requires(Regular(T0) && Regular(T1))
struct pair
{
    T0 m0;
    T1 m1;
};

template<typename T0, typename T1>
    requires(Regular(T0) && Regular(T1))
inline pair<T0, T1> make_pair(const T0& m0, const T1& m1)
{
  pair<T0, T1> tmp = {m0, m1};
  return tmp ;
}

template<typename T0, typename T1>
    requires(Regular(T0) && Regular(T1))
struct underlying_type< pair<T0, T1> >
{
    typedef pair<UnderlyingType(T0), UnderlyingType(T1)> type;
};

template<typename T0, typename T1>
    requires(Regular(T0) && Regular(T1))
bool operator==(const pair<T0, T1>& x, const pair<T0, T1>& y)
{
    return x.m0 == y.m0 && x.m1 == y.m1;
}

template<typename T0, typename T1>
    requires(TotallyOrdered(T0) && TotallyOrdered(T1))
bool operator<(const pair<T0, T1>& x, const pair<T0, T1>& y)
{
    return x.m0 < y.m0 || (!(y.m0 < x.m0) && x.m1 < y.m1);
}


// type triple (see Exercise 12.2 of Elements of Programming)
// model Regular(triple)

template<typename T0, typename T1, typename T2>
    requires(Regular(T0) && Regular(T1) && Regular(T2))
struct triple
{
    T0 m0;
    T1 m1;
    T2 m2;
};

template<typename T0, typename T1, typename T2>
    requires(Regular(T0) && Regular(T1) && Regular(T2))
inline triple<T0, T1, T2> make_triple( T0 const& x, T1 const& y, T2 const& z)
{
  triple<T0, T1, T2> tmp = {x, y, z};
  return tmp;
}

template<typename T0, typename T1, typename T2>
    requires(Regular(T0) && Regular(T1) && Regular(T2))
struct underlying_type< triple<T0, T1, T2> >
{
    typedef triple<UnderlyingType(T0), UnderlyingType(T1), UnderlyingType(T2)> type;
};

template<typename T0, typename T1, typename T2>
    requires(Regular(T0) && Regular(T1) && Regular(T2))
bool operator==(const triple<T0, T1, T2>& x, const triple<T0, T1, T2>& y)
{
    return x.m0 == y.m0 && x.m1 == y.m1 && x.m2 == y.m2;
}

template<typename T0, typename T1, typename T2>
    requires(Regular(T0) && Regular(T1) && Regular(T2))
bool operator<(const triple<T0, T1, T2>& x, const triple<T0, T1, T2>& y)
{
    return x.m0 < y.m0 ||
           (!(y.m0 < x.m0) && x.m1 < y.m1) ||
           (!(y.m1 < x.m1) && x.m2 < y.m2);
}


// 
//  Chapter 2. Transformations and their orbits
// 


//int abs(int x) {
//    if (x < 0) return -x; else return x;
//} // unary operation

double euclidean_norm(double x, double y) {
    return sqrt(x * x + y * y);
} // binary operation

double euclidean_norm(double x, double y, double z) {
    return sqrt(x * x + y * y + z * z);
} // ternary operation

template<typename F, typename N>
    requires(Transformation(F) && Integer(N))
EOPDomain(F) power_unary(EOPDomain(F) x, N n, F f)
{                  
    // Precondition:
    // $n \geq 0 \wedge (\forall i \in N)\,0 < i \leq n \Rightarrow f^i(x)$ is defined
    while (n != N(0)) {
        n = n - N(1);
        x = f(x);
    }
    return x;
}

template<typename F>
    requires(Transformation(F))
EOPDistanceType(F) distance(EOPDomain(F) x, EOPDomain(F) y, F f)
{
    // Precondition: $y$ is reachable from $x$ under $f$
    typedef EOPDistanceType(F) N;
    N n(0);
    while (x != y) {
        x = f(x);
        n = n + N(1);
    }
    return n;
}

template<typename F, typename P>
    requires(Transformation(F) && UnaryPredicate(P) &&
        EOPDomain(F) == EOPDomain(P))
EOPDomain(F) collision_point(const EOPDomain(F)& x, F f, P p)
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    if (!p(x)) return x;
    EOPDomain(F) slow = x;        // $slow = f^0(x)$
    EOPDomain(F) fast = f(x);     // $fast = f^1(x)$
                               // $n \gets 0$ (completed iterations)
    while (fast != slow) {     // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
        slow = f(slow);        // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 1}(x)$
        if (!p(fast)) return fast;
        fast = f(fast);        // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 2}(x)$
        if (!p(fast)) return fast;
        fast = f(fast);        // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 3}(x)$
                               // $n \gets n + 1$
    }
    return fast;               // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
    // Postcondition: return value is terminal point or collision point
}

template<typename F, typename P>
    requires(Transformation(F) && UnaryPredicate(P) && 
        EOPDomain(F) == EOPDomain(P))
bool terminating(const EOPDomain(F)& x, F f, P p)
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    return !p(collision_point(x, f, p));
}

template<typename F>
    requires(Transformation(F))
EOPDomain(F)
collision_point_nonterminating_orbit(const EOPDomain(F)& x, F f)
{
    EOPDomain(F) slow = x;        // $slow = f^0(x)$
    EOPDomain(F) fast = f(x);     // $fast = f^1(x)$
                               // $n \gets 0$ (completed iterations)
    while (fast != slow) {     // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
        slow = f(slow);        // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 1}(x)$
        fast = f(fast);        // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 2}(x)$
        fast = f(fast);        // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 3}(x)$
                               // $n \gets n + 1$
    }
    return fast;               // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
    // Postcondition: return value is collision point
}

template<typename F>
    requires(Transformation(F))
bool circular_nonterminating_orbit(const EOPDomain(F)& x, F f)
{
    return x == f(collision_point_nonterminating_orbit(x, f));
}

template<typename F, typename P>
    requires(Transformation(F) && UnaryPredicate(P) &&
        EOPDomain(F) == EOPDomain(P))
bool circular(const EOPDomain(F)& x, F f, P p)
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    EOPDomain(F) y = collision_point(x, f, p);
    return p(y) && x == f(y);
}

template<typename F>
    requires(Transformation(F))
EOPDomain(F) convergent_point(EOPDomain(F) x0, EOPDomain(F) x1, F f)
{
    // Precondition: $(\exists n \in \func{EOPDistanceType}(F))\,n \geq 0 \wedge f^n(x0) = f^n(x1)$
    while (x0 != x1) {
        x0 = f(x0);
        x1 = f(x1);
    }
    return x0;
}

template<typename F>
    requires(Transformation(F))
EOPDomain(F)
connection_point_nonterminating_orbit(const EOPDomain(F)& x, F f)
{
    return convergent_point(
        x,
        f(collision_point_nonterminating_orbit(x, f)),
        f);
}

template<typename F, typename P>
    requires(Transformation(F) && UnaryPredicate(P) &&
        EOPDomain(F) == EOPDomain(P))
EOPDomain(F) connection_point(const EOPDomain(F)& x, F f, P p)
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    EOPDomain(F) y = collision_point(x, f, p);
    if (!p(y)) return y;
    return convergent_point(x, f(y), f);
}

// Exercise 2.3:

template<typename F>
    requires(Transformation(F))
EOPDomain(F) convergent_point_guarded(EOPDomain(F) x0,
                                   EOPDomain(F) x1,
                                   EOPDomain(F) y, F f)
{
    // Precondition: $\func{reachable}(x0, y, f) \wedge \func{reachable}(x1, y, f)$
    typedef EOPDistanceType(F) N;
    N d0 = distance(x0, y, f);
    N d1 = distance(x1, y, f);
    if      (d0 < d1) x1 = power_unary(x1, d1 - d0, f);
    else if (d1 < d0) x0 = power_unary(x0, d0 - d1, f);
    return convergent_point(x0, x1, f);
}

template<typename F>
    requires(Transformation(F))
triple<EOPDistanceType(F), EOPDistanceType(F), EOPDomain(F)>
orbit_structure_nonterminating_orbit(const EOPDomain(F)& x, F f)
{
    typedef EOPDistanceType(F) N;
    EOPDomain(F) y = connection_point_nonterminating_orbit(x, f);
    return make_triple(distance(x, y, f),
                       distance(f(y), y, f),
                       y);
}

template<typename F, typename P>
    requires(Transformation(F) &&
        UnaryPredicate(P) && EOPDomain(F) == EOPDomain(P))
triple<EOPDistanceType(F), EOPDistanceType(F), EOPDomain(F)>
orbit_structure(const EOPDomain(F)& x, F f, P p)
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    typedef EOPDistanceType(F) N;
    EOPDomain(F) y = connection_point(x, f, p);
    N m = distance(x, y, f);
    N n(0);
    if (p(y)) n = distance(f(y), y, f);
    // Terminating: $m = h - 1 \wedge n = 0$
    // Otherwise:   $m = h \wedge n = c - 1$
    return make_triple(m, n, y);
}


// 
//  Chapter 3. Associative operations
// 


template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_left_associated(EOPDomain(Op) a, I n, Op op)
{
    // Precondition: $n > 0$
    if (n == I(1)) return a;
    return op(power_left_associated(a, n - I(1), op), a);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_right_associated(EOPDomain(Op) a, I n, Op op)
{
    // Precondition: $n > 0$
    if (n == I(1)) return a;
    return op(a, power_right_associated(a, n - I(1), op));
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_0(EOPDomain(Op) a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    if (n == I(1)) return a;
    if (n % I(2) == I(0))
        return power_0(op(a, a), n / I(2), op);
    return op(power_0(op(a, a), n / I(2), op), a);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_1(EOPDomain(Op) a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    if (n == I(1)) return a;
    EOPDomain(Op) r = power_1(op(a, a), n / I(2), op);
    if (n % I(2) != I(0)) r = op(r, a);
    return r;
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_accumulate_0(EOPDomain(Op) r, EOPDomain(Op) a, I n,
                              Op op)
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if (n == I(0)) return r;
    if (n % I(2) != I(0)) r = op(r, a);
    return power_accumulate_0(r, op(a, a), n / I(2), op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_accumulate_1(EOPDomain(Op) r, EOPDomain(Op) a, I n,
                              Op op)
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if (n == I(0)) return r;
    if (n == I(1)) return op(r, a);
    if (n % I(2) != I(0)) r = op(r, a);
    return power_accumulate_1(r, op(a, a), n / I(2), op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_accumulate_2(EOPDomain(Op) r, EOPDomain(Op) a, I n,
                              Op op)
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if (n % I(2) != I(0)) {
        r = op(r, a);
        if (n == I(1)) return r;
    } else if (n == I(0)) return r;
    return power_accumulate_2(r, op(a, a), n / I(2), op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_accumulate_3(EOPDomain(Op) r, EOPDomain(Op) a, I n,
                              Op op)
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if (n % I(2) != I(0)) {
        r = op(r, a);
        if (n == I(1)) return r;
    } else if (n == I(0)) return r;
    a = op(a, a);
    n = n / I(2);
    return power_accumulate_3(r, a, n, op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_accumulate_4(EOPDomain(Op) r, EOPDomain(Op) a, I n,
                              Op op)
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    while (true) {
        if (n % I(2) != I(0)) {
            r = op(r, a);
            if (n == I(1)) return r;
        } else if (n == I(0)) return r;
        a = op(a, a);
        n = n / I(2);
    }
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_accumulate_positive_0(EOPDomain(Op) r,
                                       EOPDomain(Op) a, I n,
                                       Op op)
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    while (true) {
        if (n % I(2) != I(0)) {
            r = op(r, a);
            if (n == I(1)) return r;
        }
        a = op(a, a);
        n = n / I(2);
    }
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_accumulate_5(EOPDomain(Op) r, EOPDomain(Op) a, I n,
                              Op op)
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if (n == I(0)) return r;
    return power_accumulate_positive_0(r, a, n, op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_2(EOPDomain(Op) a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    return power_accumulate_5(a, a, n - I(1), op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_3(EOPDomain(Op) a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    while (n % I(2) == I(0)) {
        a = op(a, a);
        n = n / I(2);
    }
    n = n / I(2);
    if (n == I(0)) return a;
    return power_accumulate_positive_0(a, op(a, a), n, op);
}


template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_accumulate_positive(EOPDomain(Op) r,
                                     EOPDomain(Op) a, I n,
                                     Op op)
{
    // Precondition: $\func{associative}(op) \wedge \func{positive}(n)$
    while (true) {
      if (odd(n)) {
          r = op(r, a);
          if (one(n)) return r;
      }
      a = op(a, a);
      n = half_nonnegative(n);
    }
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power_accumulate(EOPDomain(Op) r, EOPDomain(Op) a, I n,
                            Op op)
{
    // Precondition: $\func{associative}(op) \wedge \neg \func{negative}(n)$
    if (zero(n)) return r;
    return power_accumulate_positive(r, a, n, op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power(EOPDomain(Op) a, I n, Op op)
{
    // Precondition: $\func{associative}(op) \wedge \func{positive}(n)$
    while (even(n)) {
        a = op(a, a);
        n = half_nonnegative(n);
    }
    n = half_nonnegative(n);
    if (zero(n)) return a;
    return power_accumulate_positive(a, op(a, a), n, op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
EOPDomain(Op) power(EOPDomain(Op) a, I n, Op op, EOPDomain(Op) id)
{
    // Precondition: $\func{associative}(op) \wedge \neg \func{negative}(n)$
    if (zero(n)) return id;
    return power(a, n, op);
}

template<typename I>
    requires(Integer(I))
pair<I, I> fibonacci_matrix_multiply(const pair<I, I>& x,
                                     const pair<I, I>& y)
{
    return make_pair(
        x.m0 * (y.m1 + y.m0) + x.m1 * y.m0,
        x.m0 * y.m0 + x.m1 * y.m1);
}

template<typename I>
    requires(Integer(I))
I fibonacci(I n)
{
    // Precondition: $n \geq 0$
    if (n == I(0)) return I(0);
    return power(make_pair(I(1), I(0)),
                 n,
                 fibonacci_matrix_multiply<I>).m0;
}

template<typename I>
    requires(Integer(I))
void fibonacci_next(I& n, I& nMinus1)
{
  I tmp = n + nMinus1;
  nMinus1 = n;
  n = tmp;
}

template<typename I>
    requires(Integer(I))
void fibonacci_previous(I& n, I& nMinus1)
{
  I tmp = n - nMinus1;
  n = nMinus1;
  nMinus1 = tmp;
}


// 
//  Chapter 4. Linear orderings
// 


// Exercise 4.1: Give an example of a relation that is neither strict nor reflexive
// Exercise 4.2: Give an example of a symmetric relation that is not transitive
// Exercise 4.3: Give an example of a symmetric relation that is not reflexive


template<typename R>
    requires(Relation(R))
struct complement
{
    typedef EOPDomain(R) T;
    typedef T input_type_0;
    typedef T input_type_1;
    typedef bool codomain_type;

    R r;
    bool operator()(T const& x, T const& y)
    {
        return !r(x, y);
    }
};

template<typename R>
    requires(Relation(R))
inline complement<R> make_complement(const R& r)
{
    complement<R> tmp = {r};
    return tmp;
}

template<typename R>
    requires(Relation(R))
struct converse
{
    typedef EOPDomain(R) T;
    typedef T input_type_0;
    typedef T input_type_1;
    typedef bool codomain_type;

    R r;
    bool operator()(T const& x, T const& y)
    {
        return r(y, x);
    }
};

template<typename R>
    requires(Relation(R))
inline converse<R> make_converse(const R& r)
{
    converse<R> tmp = {r};
    return tmp ;
}

template<typename R>
    requires(Relation(R))
struct complement_of_converse
{
    typedef EOPDomain(R) T;
    typedef T input_type_0;
    typedef T input_type_1;
    typedef bool codomain_type;

    R r;
    bool operator()(T const& a, T const& b)
    {
        return !r(b, a);
    }
};

template<typename R>
    requires(Relation(R))
inline complement_of_converse<R> make_complement_of_converse(const R& r)
{
    complement_of_converse<R> tmp = {r};
    return tmp ;
}

template<typename R>
   requires(Relation(R))
struct symmetric_complement
{
    typedef EOPDomain(R) T;
    typedef T input_type_0;
    typedef T input_type_1;
    typedef bool codomain_type;

    R r;
    bool operator()(T const& a, T const& b)
    {
        return !r(a, b) && !r(b, a);
    }
};

template<typename R>
   requires(Relation(R))
inline symmetric_complement<R> make_symmetric_complement(const R& r)
{
    symmetric_complement<R> tmp = {r};
    return tmp;
}

template<typename R>
    requires(Relation(R))
const EOPDomain(R)& select_0_2(const EOPDomain(R)& a,
                            const EOPDomain(R)& b, R r)
{
    // Precondition: $\func{weak\_ordering}(r)$
    if (r(b, a)) return b;
    return a;
}

template<typename R>
    requires(Relation(R))
const EOPDomain(R)& select_1_2(const EOPDomain(R)& a,
                            const EOPDomain(R)& b, R r)
{
    // Precondition: $\func{weak\_ordering}(r)$
    if (r(b, a)) return a;
    return b;
}

template<typename R>
    requires(Relation(R))
const EOPDomain(R)& select_0_3(const EOPDomain(R)& a,
                            const EOPDomain(R)& b,
                            const EOPDomain(R)& c, R r)
{
    return select_0_2(select_0_2(a, b, r), c, r);
}

template<typename R>
    requires(Relation(R))
const EOPDomain(R)& select_2_3(const EOPDomain(R)& a,
                            const EOPDomain(R)& b,
                            const EOPDomain(R)& c, R r)
{
    return select_1_2(select_1_2(a, b, r), c, r);
}

template<typename R>
    requires(Relation(R))
const EOPDomain(R)& select_1_3_ab(const EOPDomain(R)& a,
                               const EOPDomain(R)& b,
                               const EOPDomain(R)& c, R r)
{
    if (!r(c, b)) return b;     // $a$, $b$, $c$ are sorted
    return select_1_2(a, c, r); // $b$ is not the median
}

template<typename R>
    requires(Relation(R))
const EOPDomain(R)& select_1_3(const EOPDomain(R)& a,
                            const EOPDomain(R)& b,
                            const EOPDomain(R)& c, R r)
{
    if (r(b, a)) return select_1_3_ab(b, a, c, r);
    return              select_1_3_ab(a, b, c, r);
}

template<typename R>
    requires(Relation(R))
const EOPDomain(R)& select_1_4_ab_cd(const EOPDomain(R)& a,
                                  const EOPDomain(R)& b,
                                  const EOPDomain(R)& c,
                                  const EOPDomain(R)& d, R r) {
    if (r(c, a)) return select_0_2(a, d, r);
    return              select_0_2(b, c, r);
}

template<typename R>
    requires(Relation(R))
const EOPDomain(R)& select_1_4_ab(const EOPDomain(R)& a,
                               const EOPDomain(R)& b,
                               const EOPDomain(R)& c,
                               const EOPDomain(R)& d, R r) {
    if (r(d, c)) return select_1_4_ab_cd(a, b, d, c, r);
    return              select_1_4_ab_cd(a, b, c, d, r);
}

template<typename R>
    requires(Relation(R))
const EOPDomain(R)& select_1_4(const EOPDomain(R)& a,
                            const EOPDomain(R)& b,
                            const EOPDomain(R)& c,
                            const EOPDomain(R)& d, R r) {
    if (r(b, a)) return select_1_4_ab(b, a, c, d, r);
    return              select_1_4_ab(a, b, c, d, r);
}

// Exercise 4.4: select_2_4


// Order selection procedures with stability indices

template<bool strict, typename R>
    requires(Relation(R))
struct compare_strict_or_reflexive;

template<typename R>
    requires(Relation(R))
struct compare_strict_or_reflexive<true, R> // strict
{
    typedef EOPDomain(R) T;
    typedef T input_type_0;
    typedef T input_type_1;
    typedef bool codomain_type;

    bool operator()(T const& a,
                    T const& b, R r)
    {
        return r(a, b);
    }
};

template<typename R>
    requires(Relation(R))
struct compare_strict_or_reflexive<false, R> // reflexive
{
    typedef EOPDomain(R) T;
    typedef T input_type_0;
    typedef T input_type_1;
    typedef R input_type_2;
    typedef bool codomain_type;

    bool operator()(T const& a,
                    T const& b, R r)
    {
        return !r(b, a); // $\func{complement\_of\_converse}_r(a, b)$
    }
};

template<int ia, int ib, typename R>
    requires(Relation(R))
const EOPDomain(R)& select_0_2(const EOPDomain(R)& a,
                            const EOPDomain(R)& b, R r)
{
    compare_strict_or_reflexive<(ia < ib), R> cmp;
    if (cmp(b, a, r)) return b;
    return a;
}

template<int ia, int ib, typename R>
    requires(Relation(R))
const EOPDomain(R)& select_1_2(const EOPDomain(R)& a,
                            const EOPDomain(R)& b, R r)
{
    compare_strict_or_reflexive<(ia < ib), R> cmp;
    if (cmp(b, a, r)) return a;
    return b;
}

template<int ia, int ib, int ic, int id, typename R>
    requires(Relation(R))
const EOPDomain(R)& select_1_4_ab_cd(const EOPDomain(R)& a,
                                  const EOPDomain(R)& b,
                                  const EOPDomain(R)& c,
                                  const EOPDomain(R)& d, R r)
{
    compare_strict_or_reflexive<(ia < ic), R> cmp;
    if (cmp(c, a, r)) return
        select_0_2<ia,id>(a, d, r);
    return
        select_0_2<ib,ic>(b, c, r);
}

template<int ia, int ib, int ic, int id, typename R>
    requires(Relation(R))
const EOPDomain(R)& select_1_4_ab(const EOPDomain(R)& a,
                            const EOPDomain(R)& b,
                            const EOPDomain(R)& c,
                            const EOPDomain(R)& d, R r)
{
    compare_strict_or_reflexive<(ic < id), R> cmp;
    if (cmp(d, c, r)) return
        select_1_4_ab_cd<ia,ib,id,ic>(a, b, d, c, r);
    return
        select_1_4_ab_cd<ia,ib,ic,id>(a, b, c, d, r);
}

template<int ia, int ib, int ic, int id, typename R>
    requires(Relation(R))
const EOPDomain(R)& select_1_4(const EOPDomain(R)& a,
                            const EOPDomain(R)& b,
                            const EOPDomain(R)& c,
                            const EOPDomain(R)& d, R r)
{
    compare_strict_or_reflexive<(ia < ib), R> cmp;
    if (cmp(b, a, r)) return
        select_1_4_ab<ib,ia,ic,id>(b, a, c, d, r);
    return
        select_1_4_ab<ia,ib,ic,id>(a, b, c, d, r);
}

template<int ia, int ib, int ic, int id, int ie, typename R>
    requires(Relation(R))
const EOPDomain(R)& select_2_5_ab_cd(const EOPDomain(R)& a,
                                  const EOPDomain(R)& b,
                                  const EOPDomain(R)& c,
                                  const EOPDomain(R)& d,
                                  const EOPDomain(R)& e, R r)
{
    compare_strict_or_reflexive<(ia < ic), R> cmp;
    if (cmp(c, a, r)) return
        select_1_4_ab<ia,ib,id,ie>(a, b, d, e, r);
    return
        select_1_4_ab<ic,id,ib,ie>(c, d, b, e, r);
}

template<int ia, int ib, int ic, int id, int ie, typename R>
    requires(Relation(R))
const EOPDomain(R)& select_2_5_ab(const EOPDomain(R)& a,
                               const EOPDomain(R)& b,
                               const EOPDomain(R)& c,
                               const EOPDomain(R)& d,
                               const EOPDomain(R)& e, R r)
{
    compare_strict_or_reflexive<(ic < id), R> cmp;
    if (cmp(d, c, r)) return
        select_2_5_ab_cd<ia,ib,id,ic,ie>(
                          a, b, d, c, e, r);
    return
        select_2_5_ab_cd<ia,ib,ic,id,ie>(
                          a, b, c, d, e, r);
}

template<int ia, int ib, int ic, int id, int ie, typename R>
    requires(Relation(R))
const EOPDomain(R)& select_2_5(const EOPDomain(R)& a,
                            const EOPDomain(R)& b,
                            const EOPDomain(R)& c,
                            const EOPDomain(R)& d,
                            const EOPDomain(R)& e, R r)
{
    compare_strict_or_reflexive<(ia < ib), R> cmp;
    if (cmp(b, a, r)) return
        select_2_5_ab<ib,ia,ic,id,ie>(b, a, c, d, e, r);
    return
        select_2_5_ab<ia,ib,ic,id,ie>(a, b, c, d, e, r);
}

// Exercise 4.5. Find an algorithm for median of 5 that does slightly fewer comparisons
// on average


template<typename R>
    requires(Relation(R))
const EOPDomain(R)& median_5(const EOPDomain(R)& a,
                          const EOPDomain(R)& b,
                          const EOPDomain(R)& c,
                          const EOPDomain(R)& d,
                          const EOPDomain(R)& e, R r)
{
    return select_2_5<0,1,2,3,4>(a, b, c, d, e, r);
}


// Exercise 4.6. Prove the stability of every order selection procedure in this section
// Exercise 4.7. Verify the correctness and stability of every order selection procedure
// in this section by exhaustive testing


// Natural total ordering

template<typename T>
    requires(TotallyOrdered(T))
struct less
{
    typedef T input_type_0;
    typedef T input_type_1;
    typedef bool codomain_type;

    bool operator()(T const& x, T const& y)
    {
        return x < y;
    }
};

template<typename T>
    requires(TotallyOrdered(T))
const T& min(const T& a, const T& b)
{
    return select_0_2(a, b, less<T>());
}

template<typename T>
    requires(TotallyOrdered(T))
const T& max(const T& a, const T& b)
{
    return select_1_2(a, b, less<T>());
}


// Clusters of related procedures: equality and ordering

template<typename T>
    requires(Regular(T))
bool operator!=(const T& x, const T& y)
{
    return !(x==y);
}

template<typename T>
    requires(TotallyOrdered(T))
bool operator>(const T& x, const T& y)
{
    return y < x;
}

template<typename T>
    requires(TotallyOrdered(T))
bool operator<=(const T& x, const T& y)
{
    return !(y < x);
}

template<typename T>
    requires(TotallyOrdered(T))
bool operator>=(const T& x, const T& y)
{
    return !(x < y);
}


// Exercise 4.8: Rewrite the algorithms in this chapter using three-valued comparison


// 
//  Chapter 5. Ordered algebraic structures
// 


template<typename T>
    requires(AdditiveSemigroup(T))
struct plus
{
    typedef T input_type_0;
    typedef T input_type_1;
    typedef T codomain_type;

    T operator()(T const& x, T const& y)
    {
        return x + y;
    }
};

template<typename T>
    requires(MultiplicativeSemigroup(T))
struct multiplies
{
    typedef T input_type_0;
    typedef T input_type_1;
    typedef T codomain_type;

    T operator()(T const& x, T const& y)
    {
        return x * y;
    }
};

template<typename Op>
    requires(SemigroupOperation(Op)) // ***** or MultiplicativeSemigroup ?????
struct multiplies_transformation
{
    typedef EOPDomain(Op) T;
    typedef T input_type_0;
    typedef T codomain_type;

    T x;
    Op op;
    T operator()(T const& y)
    {
        return op(x, y);
    }
};

template<typename Op>
    requires(SemigroupOperation(Op)) // ***** or MultiplicativeSemigroup ?????
inline multiplies_transformation<Op> make_multiplies_transformation(const EOPDomain(Op)& x, const Op& op)
{
    multiplies_transformation<Op> tmp = {x, op};
    return tmp;
}

template<typename T>
    requires(AdditiveGroup(T))
struct negate
{
    typedef T input_type_0;
    typedef T codomain_type;

    T operator()(T const& x)
    {
        return -x;
    }
};

template<typename T>
    requires(OrderedAdditiveGroup(T))
T abs(const T& a)
{
    if (a < T(0)) return -a;
    else          return  a;
}

template<typename T>
    requires(CancellableMonoid(T))
T slow_remainder(T a, T b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    while (b <= a) a = a - b;
    return a;
}

template<typename T>
    requires(ArchimedeanMonoid(T))
EOPQuotientType(T) slow_quotient(T a, T b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    EOPQuotientType(T) n(0);
    while (b <= a) {
        a = a - b;
        n = successor(n);
    }
    return n;
}

template<typename T>
    requires(ArchimedeanMonoid(T))
T remainder_recursive(T a, T b)
{
    // Precondition: $a \geq b > 0$
    if (a - b >= b) {
        a = remainder_recursive(a, b + b);
        if (a < b) return a;
    }
    return a - b;
}

template<typename T>
    requires(ArchimedeanMonoid(T))
T remainder_nonnegative(T a, T b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    if (a < b) return a;
    return remainder_recursive(a, b);
}

/* The next function is due to:
    Robert W. Floyd and Donald E. Knuth.
    Addition machines.
    \emph{SIAM Journal on Computing},
    Volume 19, Number 2, 1990, pages 329--340.
*/

template<typename T>
    requires(ArchimedeanMonoid(T))
T remainder_nonnegative_fibonacci(T a, T b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    if (a < b) return a;
    T c = b;
    do {
      fibonacci_next(c, b);
    } while (a >= c);
    do {
        if (a >= b) a = a - b;
        fibonacci_previous(c, b);
    } while (b < c);
    return a;
}

template<typename T>
    requires(ArchimedeanMonoid(T))
T largest_doubling(T a, T b)
{
    // Precondition: $a \geq b > 0$
    while (b <= a - b) b = b + b;
    return b;
}

template<typename T>
    requires(HalvableMonoid(T))
T remainder_nonnegative_iterative(T a, T b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    if (a < b) return a;
    T c = largest_doubling(a, b);
    a = a - c;
    while (c != b) {
        c = half(c);
        if (c <= a) a = a - c;
    }
    return a;
}

// Jon Brandt suggested this algorithm (it is not mentioned in chapter 5):

template<typename T>
    requires(ArchimedeanMonoid(T))
T remainder_nonnegative_with_largest_doubling(T a, T b)
{
    // Precondition: $a \geq T(0) \wedge b > T(0)$
    while (b <= a)
        a = a - largest_doubling(a, b);
    return a;
}

template<typename T>
    requires(ArchimedeanMonoid(T))
T subtractive_gcd_nonzero(T a, T b)
{
    // Precondition: $a > 0 \wedge b > 0$
    while (true) {
        if (b < a)      a = a - b;
        else if (a < b) b = b - a;
        else            return a;
    }
}

template<typename T>
    requires(EuclideanMonoid(T))
T subtractive_gcd(T a, T b)
{
    // Precondition: $a \geq 0 \wedge b \geq 0 \wedge \neg(a = 0 \wedge b = 0)$
    while (true) {
        if (b == T(0)) return a; 
        while (b <= a) a = a - b;
        if (a == T(0)) return b;
        while (a <= b) b = b - a;
    }
}

template<typename T>
    requires(EuclideanMonoid(T))
T fast_subtractive_gcd(T a, T b)
{
    // Precondition: $a \geq 0 \wedge b \geq 0 \wedge \neg(a = 0 \wedge b = 0)$
    while (true) {
        if (b == T(0)) return a; 
        a = remainder_nonnegative(a, b);
        if (a == T(0)) return b;
        b = remainder_nonnegative(b, a);
    }
}

template<typename T>
    requires(EuclideanSemiring(T))
T gcd(T a, T b)
{
    // Precondition: $\neg(a = 0 \wedge b = 0)$
    while (true) {
        if (b == T(0)) return a; 
        a = remainder(a, b);
        if (a == T(0)) return b;
        b = remainder(b, a);
    }
}

template<typename T, typename S>
    requires(EuclideanSemimodule(T, S))
T gcd(T a, T b)
{
    // Precondition: $\neg(a = 0 \wedge b = 0)$
    while (true) {
        if (b == T(0)) return a; 
        a = remainder(a, b);
        if (a == T(0)) return b;
        b = remainder(b, a);
    }
}


// Exercise 5.3:

template<typename T>
    requires(Integer(T))
T stein_gcd_nonnegative(T a, T b)
{
    // Precondition: $a \geq 0 \wedge b \geq 0 \wedge \neg(a = 0 \wedge b = 0)$
    if (zero(a)) return b;
    if (zero(b)) return a;
    int d = 0;
    while (even(a) && even(b)) {
        a = half_nonnegative(a);
        b = half_nonnegative(b);
        d = d + 1;
    }
    while (even(a)) a = half_nonnegative(a);
    while (even(b)) b = half_nonnegative(b);
    while (true) 
        if (a < b) {
            b = b - a;
            do { b = half_nonnegative(b); } while (even(b));
        } else if (b < a) {
            a = a - b;
            do { a = half_nonnegative(a); } while (even(a));
        } else return binary_scale_up_nonnegative(a, d);
}

template<typename T>
    requires(ArchimedeanMonoid(T))
pair<EOPQuotientType(T), T>
quotient_remainder_nonnegative(T a, T b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    typedef EOPQuotientType(T) N;
    if (a < b) return make_pair(N(0), a);
    if (a - b < b) return make_pair(N(1), a - b);
    pair<N, T> q = quotient_remainder_nonnegative(a, b + b);
    N m = twice(q.m0);
    a = q.m1;
    if (a < b) return make_pair(m, a);
    else       return make_pair(successor(m), a - b);
}

/* The next function is due to:
    Robert W. Floyd and Donald E. Knuth.
    Addition machines.
    \emph{SIAM Journal on Computing},
    Volume 19, Number 2, 1990, pages 329--340.
*/

template<typename T>
    requires(ArchimedeanMonoid(T))
pair<EOPQuotientType(T), T>
quotient_remainder_nonnegative_fibonacci(T a, T b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    typedef EOPQuotientType(T) N;
    if (a < b) return make_pair(N(0), a);
    T c = b;
    N nMinus1 = N(0);
    N n = N(1);
    do {
        fibonacci_next(c, b);
        fibonacci_next(n, nMinus1);
    } while (a >= c);
    N quotient = N(0);
    do {
        if (a >= b) {
            a = a - b;
            quotient = quotient + n;
        }
        fibonacci_previous(n, nMinus1);
        fibonacci_previous(c, b);
    } while (b < c);
    return make_pair(quotient, a);
}

template<typename T>
    requires(HalvableMonoid(T))
pair<EOPQuotientType(T), T>
quotient_remainder_nonnegative_iterative(T a, T b)
{
    // Precondition: $a \geq 0 \wedge b > 0$
    typedef EOPQuotientType(T) N;
    if (a < b) return make_pair(N(0), a);
    T c = largest_doubling(a, b);
    a = a - c;
    N n(1);
    while (c != b) {
        n = twice(n);
        c = half(c);
        if (c <= a) {
            a = a - c;
            n = successor(n);
        }
    }
    return make_pair(n, a);
}

template<typename Op>
    requires(BinaryOperation(Op) &&
        ArchimedeanGroup(EOPDomain(Op)))
EOPDomain(Op) remainder(EOPDomain(Op) a, EOPDomain(Op) b, Op rem)
{
    // Precondition: $b \neq 0$
    typedef EOPDomain(Op) T;
    T r;
    if (a < T(0))
        if (b < T(0)) {
            r = -rem(-a, -b);
        } else {
            r =  rem(-a,  b); if (r != T(0)) r = b - r;
        }
    else
        if (b < T(0)) { 
            r =  rem(a, -b);  if (r != T(0)) r = b + r;
        } else {
            r =  rem(a,  b);
        }
    return r;
}

template<typename F>
    requires(HomogeneousFunction(F) && Arity(F) == 2 &&
        ArchimedeanGroup(EOPDomain(F)) &&
        EOPCodomain(F) == pair<EOPQuotientType(EOPDomain(F)),
                            EOPDomain(F)>)
pair<EOPQuotientType(EOPDomain(F)), EOPDomain(F)>
quotient_remainder(EOPDomain(F) a, EOPDomain(F) b, F quo_rem) 
{
    // Precondition: $b \neq 0$
    typedef EOPDomain(F) T;
    pair<EOPQuotientType(T), T> q_r;
    if (a < T(0)) {
        if (b < T(0)) {
            q_r = quo_rem(-a, -b); q_r.m1 = -q_r.m1;
        } else {
            q_r = quo_rem(-a,  b);
            if (q_r.m1 != T(0)) {
                q_r.m1 = b - q_r.m1; q_r.m0 = successor(q_r.m0);
            }
            q_r.m0 = -q_r.m0;
        }
    } else {
        if (b < T(0)) {
            q_r = quo_rem( a, -b);
            if (q_r.m1 != T(0)) {
                q_r.m1 = b + q_r.m1; q_r.m0 = successor(q_r.m0);
            }
            q_r.m0 = -q_r.m0;
        }
        else 
            q_r = quo_rem( a,  b);
    }
    return q_r;
}


// 
//  Chapter 6. Iterators
// 


template<typename I>
    requires(Iterator(I))
void increment(I& x)
{
    // Precondition: $\func{successor}(x)$ is defined
    x = successor(x);
}


template<typename I>
    requires(Iterator(I))
I operator+(I f, EOPDistanceType(I) n)
{
    // Precondition: $n \geq 0 \wedge \property{weak\_range}(f, n)$
    while (!zero(n)) {
        n = predecessor(n);
        f = successor(f);
    }
    return f;
}


template<typename I>
    requires(Iterator(I))
EOPDistanceType(I) operator-(I l, I f)
{
    // Precondition: $\property{bounded\_range}(f, l)$
    EOPDistanceType(I) n(0);
    while (f != l) {
        n = successor(n);
        f = successor(f);
    }
    return n;
}

template<typename I, typename Proc>
    requires(Readable(I) && Iterator(I) &&
        Procedure(Proc) && Arity(Proc) == 1 &&
        EOPValueType(I) == EOPInputType(Proc, 0))
Proc for_each(I f, I l, Proc proc)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l) {
        proc(source(f));
        f = successor(f); 
    }
    return proc;
}

template<typename I>
    requires(Readable(I) && Iterator(I))
I find(I f, I l, const EOPValueType(I)& x)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l && source(f) != x) f = successor(f);
    return f;
}

template<typename I>
    requires(Readable(I) && Iterator(I))
I find_not(I f, I l, const EOPValueType(I)& x)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l && source(f) == x) f = successor(f);
    return f;
}

template<typename I, typename P>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I find_if(I f, I l, P p)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l && !p(source(f))) f = successor(f);
    return f;
}

template<typename I,  typename P>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I find_if_not(I f, I l, P p)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l && p(source(f)))
        f = successor(f);
    return f;
}

// Exercise 6.1: quantifier functions

template<typename I,  typename P>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
bool all(I f, I l, P p)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return l == find_if_not(f, l, p);
}

template<typename I,  typename P>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
bool none(I f, I l, P p)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return l == find_if(f, l, p);
}

template<typename I,  typename P>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
bool not_all(I f, I l, P p)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return !all(f, l, p);
}

template<typename I,  typename P>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
bool some(I f, I l, P p)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return !none(f, l, p);
}

template<typename I, typename P, typename J>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && Iterator(J) &&
        EOPValueType(I) == EOPDomain(P))
J count_if(I f, I l, P p, J j)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l) {
        if (p(source(f))) j = successor(j);
        f = successor(f);
    }
    return j;
}


// Exercise 6.2: implement count_if using for_each


template<typename I, typename P>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
EOPDistanceType(I) count_if(I f, I l, P p) {
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return count_if(f, l, p, EOPDistanceType(I)(0));
}

template<typename I, typename J>
    requires(Readable(I) && Iterator(I) &&
        Iterator(J))
J count(I f, I l, const EOPValueType(I)& x, J j)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l) {
        if (source(f) == x) j = successor(j);
        f = successor(f);
    }
    return j;
}

template<typename I>
    requires(Readable(I) && Iterator(I))
EOPDistanceType(I) count(I f, I l, const EOPValueType(I)& x)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
  return count(f, l, x, EOPDistanceType(I)(0));
}

template<typename I, typename J>
    requires(Readable(I) && Iterator(I) &&
        Iterator(J))
J count_not(I f, I l, const EOPValueType(I)& x, J j)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l) {
        if (source(f) != x) j = successor(j);
        f = successor(f);
    }
    return j;
}

template<typename I>
    requires(Readable(I) && Iterator(I))
EOPDistanceType(I) count_not(I f, I l, const EOPValueType(I)& x)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
  return count_not(f, l, x, EOPDistanceType(I)(0));
}

template<typename I, typename P, typename J>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && EOPDomain(P) == EOPValueType(I) &&
        Iterator(J))
J count_if_not(I f, I l, P p, J j)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while (f != l) {
        if (!p(source(f))) j = successor(j);
        f = successor(f);
    }
    return j;
}
template<typename I, typename P>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && EOPDomain(P) == EOPValueType(I))
EOPDistanceType(I) count_if_not(I f, I l, P p)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return count_if_not(f, l, p, EOPDistanceType(I)(0));
}

template<typename I, typename Op, typename F>
    requires(Iterator(I) && BinaryOperation(Op) && 
        UnaryFunction(F) &&
        I == EOPDomain(F) && EOPCodomain(F) == EOPDomain(Op))
EOPDomain(Op) reduce_nonempty(I f, I l, Op op, F fun)
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge f \neq l$
    // Precondition: $\property{partially\_associative}(op)$
    // Precondition: $(\forall x \in [f, l))\,fun(x)$ is defined
    EOPDomain(Op) r = fun(f);
    f = successor(f);
    while (f != l) {
        r = op(r, fun(f)); 
        f = successor(f);
    }
    return r;
}

template<typename I, typename Op>
    requires(Readable(I) && Iterator(I) && BinaryOperation(Op) && 
        EOPValueType(I) == EOPDomain(Op))
EOPDomain(Op) reduce_nonempty(I f, I l, Op op)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l) \wedge f \neq l$
    // Precondition: $\property{partially\_associative}(op)$
    EOPDomain(Op) r = source(f);
    f = successor(f);
    while (f != l) {
        r = op(r, source(f)); 
        f = successor(f);
    }
    return r;
}

template<typename I, typename Op, typename F>
    requires(Iterator(I) && BinaryOperation(Op) && 
        UnaryFunction(F) &&
        I == EOPDomain(F) && EOPCodomain(F) == EOPDomain(Op))
EOPDomain(Op) reduce(I f, I l, Op op, F fun, const EOPDomain(Op)& z)
{
    // Precondition: $\property{bounded\_range}(f, l)$
    // Precondition: $\property{partially\_associative}(op)$
    // Precondition: $(\forall x \in [f, l))\,fun(x)$ is defined
    if (f == l) return z;
    return reduce_nonempty(f, l, op, fun);
}

template<typename I, typename Op>
    requires(ReadableIterator(I) && BinaryOperation(Op) && 
        EOPValueType(I) == EOPDomain(Op))
EOPDomain(Op) reduce(I f, I l, Op op, const EOPDomain(Op)& z)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    // Precondition: $\property{partially\_associative}(op)$
    if (f == l) return z;
    return reduce_nonempty(f, l, op);
}

template<typename I, typename Op, typename F>
    requires(Iterator(I) && BinaryOperation(Op) && 
        UnaryFunction(F) &&
        I == EOPDomain(F) && EOPCodomain(F) == EOPDomain(Op))
EOPDomain(Op) reduce_nonzeroes(I f, I l,
                            Op op, F fun, const EOPDomain(Op)& z)
{
    // Precondition: $\property{bounded\_range}(f, l)$
    // Precondition: $\property{partially\_associative}(op)$
    // Precondition: $(\forall x \in [f, l))\,fun(x)$ is defined
    EOPDomain(Op) x;
    do {
        if (f == l) return z;
        x = fun(f);
        f = successor(f);
    } while (x == z);
    while (f != l) {
        EOPDomain(Op) y = fun(f);
        if (y != z) x = op(x, y); 
        f = successor(f);
    }
    return x;
}

template<typename I, typename Op>
    requires(ReadableIterator(I) && BinaryOperation(Op) && 
        EOPValueType(I) == EOPDomain(Op))
EOPDomain(Op) reduce_nonzeroes(I f, I l,
                            Op op, const EOPDomain(Op)& z)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    // Precondition: $\property{partially\_associative}(op)$
    EOPDomain(Op) x;
    do {
        if (f == l) return z;
        x = source(f);
        f = successor(f);
    } while (x == z);
    while (f != l) {
        EOPDomain(Op) y = source(f);
        if (y != z) x = op(x, y); 
        f = successor(f);
    }
    return x;
}

template<typename I>
    requires(Readable(I) && Iterator(I) &&
        AdditiveMonoid(EOPValueType(I)))
EOPValueType(I) reduce(I f, I l)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    typedef EOPValueType(I) T;
    return reduce(f, l, plus<T>(), T(0));
}

template<typename I, typename Proc>
    requires(Readable(I) && Iterator(I) &&
        Procedure(Proc) && Arity(Proc) == 1 &&
        EOPValueType(I) == EOPInputType(Proc, 0))
pair<Proc, I> for_each_n(I f, EOPDistanceType(I) n, Proc proc)
{
    // Precondition: $\property{readable\_weak\_range}(f, n)$
    while (!zero(n)) {
        n = predecessor(n);
        proc(source(f));
        f = successor(f);
    }
    return make_pair(proc, f);
}

template<typename I>
    requires(Readable(I) && Iterator(I))
pair<I, EOPDistanceType(I)> find_n(I f, EOPDistanceType(I) n,
                                const EOPValueType(I)& x)
{
    // Precondition: $\property{readable\_weak\_range}(f, n)$
    while (!zero(n) && source(f) != x) {
        n = predecessor(n);
        f = successor(f);
    }
    return make_pair(f, n);
}


// Exercise 6.3: implement variations taking a weak range instead of a bounded range
// of all the versions of find, quantifiers, count, and reduce


template<typename I, typename P>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I find_if_unguarded(I f, P p) {
    // Precondition:
    // $(\exists l)\,\func{readable\_bounded\_range}(f, l) \wedge \func{some}(f, l, p)$
    while (!p(source(f))) f = successor(f);
    return f;
    // Postcondition: $p(\func{source}(f))$
}

template<typename I,  typename P>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && EOPDomain(P) == EOPValueType(I))
I find_if_not_unguarded(I f, P p) {
    // Let $l$ be the end of the implied range starting with $f$
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{not\_all}(f, l, p)$
    while (p(source(f))) f = successor(f);
    return f;
}

template<typename I0, typename I1, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) && Relation(R) && 
        EOPValueType(I0) == EOPValueType(I1) &&
        EOPValueType(I0) == EOPDomain(R))
pair<I0, I1> find_mismatch(I0 f0, I0 l0, I1 f1, I1 l1, R r)
{
    // Precondition: $\func{readable\_bounded\_range}(f0, l0)$
    // Precondition: $\func{readable\_bounded\_range}(f1, l1)$
    while (f0 != l0 && f1 != l1 && r(source(f0), source(f1))) {
        f0 = successor(f0);
        f1 = successor(f1);
    }
    return make_pair(f0, f1);
}

template<typename I, typename R>
    requires(Readable(I) && Iterator(I) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
I find_adjacent_mismatch(I f, I l, R r)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    if (f == l) return l;
    EOPValueType(I) x = source(f);
    f = successor(f);
    while (f != l && r(x, source(f))) {
        x = source(f);
        f = successor(f);
    }
    return f;
}

template<typename I, typename R>
    requires(Readable(I) && Iterator(I) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
bool relation_preserving(I f, I l, R r)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return l == find_adjacent_mismatch(f, l, r);
}

template<typename I, typename R>
    requires(Readable(I) && Iterator(I) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
bool strictly_increasing_range(I f, I l, R r)
{
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{weak\_ordering}(r)$
    return relation_preserving(f, l, r);
}

template<typename I, typename R>
    requires(Readable(I) && Iterator(I) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
bool increasing_range(I f, I l, R r)
{
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{weak\_ordering}(r)$
    return relation_preserving(
        f, l,
        make_complement_of_converse(r));
}

template<typename I, typename P>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
bool partitioned(I f, I l, P p)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    return l == find_if_not(find_if(f, l, p), l, p);
}


// Exercise 6.6: partitioned_n


template<typename I, typename R>
    requires(Readable(I) && ForwardIterator(I) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
I find_adjacent_mismatch_forward(I f, I l, R r)
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    if (f == l) return l;
    I t;
    do {
        t = f;
        f = successor(f);
    } while (f != l && r(source(t), source(f)));
    return f;
}

template<typename I, typename P>
    requires(Readable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I partition_point_n(I f, EOPDistanceType(I) n, P p)
{
    // Precondition:
    // $\func{readable\_counted\_range}(f, n) \wedge \func{partitioned\_n}(f, n, p)$
    while (!zero(n)) {
        EOPDistanceType(I) h = half_nonnegative(n);
        I m = f + h;
        if (p(source(m))) {
            n = h;
        } else {
            n = n - successor(h); f = successor(m);
        }
    }
    return f;
}

template<typename I,  typename P>
    requires(Readable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I partition_point(I f, I l, P p)
{
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{partitioned}(f, l, p)$
    return partition_point_n(f, l - f, p);
}

template<typename R>
    requires(Relation(R))
struct lower_bound_predicate
{
    typedef EOPDomain(R) T;
    typedef T input_type_0;
    typedef bool codomain_type;

    const T& a;
    R r;
    bool operator()(T const& x) { return !r(x, a); }
};

template<typename R>
    requires(Relation(R))
inline lower_bound_predicate<R> make_lower_bound_predicate(const EOPDomain(R)& a, const R& r)
{
    lower_bound_predicate<R> tmp = {a, r};
    return tmp;
}

template<typename I, typename R>
    requires(Readable(I) && ForwardIterator(I) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
I lower_bound_n(I f, EOPDistanceType(I) n,
                const EOPValueType(I)& a, R r)
{
    // Precondition:
    // $\property{weak\_ordering(r)} \wedge \property{increasing\_counted\_range}(f, n, r)$
    return partition_point_n(f, n, make_lower_bound_predicate(a, r));
} 

template<typename R>
    requires(Relation(R))
struct upper_bound_predicate
{
    typedef EOPDomain(R) T;
    typedef T input_type_0;
    typedef bool codomain_type;

    const T& a;
    R r;
    bool operator()(T const& x) { return r(a, x); }
};

template<typename R>
    requires(Relation(R))
inline upper_bound_predicate<R> make_upper_bound_predicate(const EOPDomain(R)& a, const R& r)
{
    upper_bound_predicate<R> tmp = {a, r};
    return tmp;
}

template<typename I, typename R>
    requires(Readable(I) && ForwardIterator(I) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
I upper_bound_n(I f, EOPDistanceType(I) n,
                const EOPValueType(I)& a, R r)
{
    // Precondition:
    // $\property{weak\_ordering(r)} \wedge \property{increasing\_counted\_range}(f, n, r)$
    return partition_point_n(f, n, make_upper_bound_predicate(a, r));
} 


// Exercise 6.7: equal_range


template<typename I>
    requires(BidirectionalIterator(I))
I operator-(I l, EOPDistanceType(I) n)
{
    // Precondition: $n \geq 0 \wedge (\exists f \in I)\,(\func{weak\_range}(f, n) \wedge l = f+n)$
    while (!zero(n)) {
        n = predecessor(n);
        l = predecessor(l);
    }
    return l;
}

template<typename I, typename P>
    requires(Readable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I find_backward_if(I f, I l, P p)
{
    // Precondition: $(f, l] \text{ is a readable bounded half-open on left range}$
    while (l != f && !p(source(predecessor(l))))
        l = predecessor(l);
    return l;
}

template<typename I, typename P>
    requires(Readable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I find_backward_if_not(I f, I l, P p) {
    // Precondition: $(f, l] \text{ is a readable bounded half-open on left range}$
    while (l != f && p(source(predecessor(l))))
        l = predecessor(l);
    return l;
}


// Exercise 6.8: optimized find_backward_if


// Exercise 6.9: palindrome predicate


template<typename I, typename P>
    requires(Readable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I find_backward_if_unguarded(I l, P p)
{
    // Precondition:
    // $(\exists f \in I)\,\property{readable\_bounded\_range}(f, l) \wedge \property{some}(f, l, p)$
    do l = predecessor(l); while (!p(source(l)));
    return l;
    // Postcondition: $p(\func{source}(l))$
}

template<typename I, typename P>
    requires(Readable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I find_backward_if_not_unguarded(I l, P p)
{
    // Precondition:
    // $(\exists f \in I)\,\property{readable\_bounded\_range}(f, l) \wedge \property{not\_all}(f, l, p)$
    do l = predecessor(l); while (p(source(l)));
    return l;
    // Postcondition: $\neg p(\func{source}(l))$
}


// 
//  Chapter 7. Coordinate structures
// 


template<typename C>
    requires(BifurcateCoordinate(C))
EOPWeightType(C) weight_recursive(C c)
{
    // Precondition: $\property{tree}(c)$
    typedef EOPWeightType(C) N;
    if (empty(c)) return N(0);
    N l(0);
    N r(0);
    if (has_left_successor(c))
        l = weight_recursive(left_successor(c));
    if (has_right_successor(c))
        r = weight_recursive(right_successor(c));
    return successor(l + r);
}

template<typename C>
    requires(BifurcateCoordinate(C))
EOPWeightType(C) height_recursive(C c)
{
    // Precondition: $\property{tree}(c)$
    typedef EOPWeightType(C) N;
    if (empty(c)) return N(0);
    N l(0);
    N r(0);
    if (has_left_successor(c))
        l = height_recursive(left_successor(c));
    if (has_right_successor(c))
        r = height_recursive(right_successor(c));
    return successor(max(l, r));
}

enum visit { pre, in, post };

template<typename C, typename Proc>
    requires(BifurcateCoordinate(C) &&
        Procedure(Proc) && Arity(Proc) == 2 &&
        visit == EOPInputType(Proc, 0) &&
        C == EOPInputType(Proc, 1))
Proc traverse_nonempty(C c, Proc proc)
{
    // Precondition: $\property{tree}(c) \wedge \neg \func{empty}(c)$
    proc(pre, c);
    if (has_left_successor(c))
        proc = traverse_nonempty(left_successor(c), proc);
    proc(in, c);
    if (has_right_successor(c))
        proc = traverse_nonempty(right_successor(c), proc);
    proc(post, c);
    return proc;
}

template<typename T>
    requires(BidirectionalBifurcateCoordinate(T))
bool is_left_successor(T j)
{
    // Precondition: $\func{has\_predecessor}(j)$
    T i = predecessor(j);
    return has_left_successor(i) && left_successor(i) == j;
}

template<typename T>
    requires(BidirectionalBifurcateCoordinate(T))
bool is_right_successor(T j)
{
    // Precondition: $\func{has\_predecessor}(j)$
    T i = predecessor(j);
    return has_right_successor(i) && right_successor(i) == j;
}

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
int traverse_step(visit& v, C& c)
{
    // Precondition: $\func{has\_predecessor}(c) \vee v \neq post$
    switch (v) {
    case pre:
        if (has_left_successor(c))  {
                     c = left_successor(c);  return 1;
        }   v = in;                          return 0;
    case in:
        if (has_right_successor(c)) {
            v = pre; c = right_successor(c); return 1;
        }   v = post;                        return 0;
    case post:
        if (is_left_successor(c))
            v = in;
                     c = predecessor(c);     return -1;
    }
}

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
bool reachable(C x, C y)
{
    // Precondition: $\property{tree}(x)$
    if (empty(x)) return false;
    C root = x;
    visit v = pre;
    do {
        if (x == y) return true;
        traverse_step(v, x);
    } while (x != root || v != post);
    return false;
}

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
EOPWeightType(C) weight(C c)
{
    // Precondition: $\property{tree}(c)$
    typedef EOPWeightType(C) N;
    if (empty(c)) return N(0);
    C root = c;
    visit v = pre;
    N n(1); // Invariant: $n$ is count of $\type{pre}$ visits so far
    do {
        traverse_step(v, c);
        if (v == pre) n = successor(n);
    } while (c != root || v != post);
    return n;
}

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
EOPWeightType(C) height(C c)
{
    // Precondition: $\property{tree}(c)$
    typedef EOPWeightType(C) N;
    if (empty(c)) return N(0);
    C root = c;
    visit v = pre;
    N n(1); // Invariant: $n$ is max of height of $\type{pre}$ visits so far
    N m(1); // Invariant: $m$ is height of current $\type{pre}$ visit
    do {
        m = (m - N(1)) + N(traverse_step(v, c) + 1);
        n = max(n, m);
    } while (c != root || v != post);
    return n;
}

template<typename C, typename Proc>
    requires(BidirectionalBifurcateCoordinate(C) &&
        Procedure(Proc) && Arity(Proc) == 2 &&
        visit == EOPInputType(Proc, 0) &&
        C == EOPInputType(Proc, 1))
Proc traverse(C c, Proc proc)
{
    // Precondition: $\property{tree}(c)$
    if (empty(c)) return proc;
    C root = c;
    visit v = pre;
    proc(pre, c);
    do {
        traverse_step(v, c);
        proc(v, c);
    } while (c != root || v != post);
    return proc;
}


// Exercise 7.3: Use traverse_step and the procedures of Chapter 2 to determine
// whether the descendants of a bidirectional bifurcate coordinate form a DAG


template<typename C0, typename C1>
    requires(BifurcateCoordinate(C0) &&
        BifurcateCoordinate(C1))
bool bifurcate_isomorphic_nonempty(C0 c0, C1 c1)
{
    // Precondition:
    // $\property{tree}(c0) \wedge \property{tree}(c1) \wedge \neg \func{empty}(c0) \wedge \neg \func{empty}(c1)$
    if (has_left_successor(c0))
        if (has_left_successor(c1)) {
            if (!bifurcate_isomorphic_nonempty(
                    left_successor(c0), left_successor(c1)))
                return false;
        } else return false;
    else if (has_left_successor(c1)) return false;
    if (has_right_successor(c0))
        if (has_right_successor(c1)) {
            if (!bifurcate_isomorphic_nonempty(
                    right_successor(c0), right_successor(c1)))
                return false;
        } else return false;
    else if (has_right_successor(c1)) return false;
    return true;
}

template<typename C0, typename C1>
    requires(BidirectionalBifurcateCoordinate(C0) &&
        BidirectionalBifurcateCoordinate(C1))
bool bifurcate_isomorphic(C0 c0, C1 c1)
{
    // Precondition: $\property{tree}(c0) \wedge \property{tree}(c1)$
    if (empty(c0)) return empty(c1);
    if (empty(c1)) return false;
    C0 root0 = c0;
    visit v0 = pre;
    visit v1 = pre;
    while (true) {
        traverse_step(v0, c0);
        traverse_step(v1, c1);
        if (v0 != v1) return false;
        if (c0 == root0 && v0 == post) return true;
    }
}

template<typename I0, typename I1, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        EOPValueType(I0) == EOPValueType(I1) &&
        Relation(R) && EOPValueType(I0) == EOPDomain(R))
bool lexicographical_equivalent(I0 f0, I0 l0, I1 f1, I1 l1, R r)
{
    // Precondition: $\property{readable\_bounded\_range}(f0, l0)$
    // Precondition: $\property{readable\_bounded\_range}(f1, l1)$
    // Precondition: $\property{equivalence}(r)$
    pair<I0, I1> p = find_mismatch(f0, l0, f1, l1, r);
    return p.m0 == l0 && p.m1 == l1;
}

template<typename I0, typename I1>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        EOPValueType(I0) == EOPValueType(I1))
bool lexicographical_equal(I0 f0, I0 l0, I1 f1, I1 l1)
{
    return lexicographical_equivalent(f0, l0, f1, l1,
                                      equal<EOPValueType(I0)>());
}

// Could specialize to use lexicographic_equal for k > some cutoff
template<int k, typename I0, typename I1>
   requires(Readable(I0) && ForwardIterator(I0) &&
       Readable(I1) && ForwardIterator(I1) &&
       EOPValueType(I0) == EOPValueType(I1))
struct lexicographical_equal_k
{
    typedef I0 input_type_0;
    typedef I1 input_type_1;
    typedef bool codomain_type;

     bool operator()(I0 f0, I1 f1)
     {
         if (source(f0) != source(f1)) return false;
         return lexicographical_equal_k<k - 1, I0, I1>()(successor(f0), successor(f1)); 
     }
};

template<typename I0, typename I1>
struct lexicographical_equal_k<0, I0, I1>
{
    typedef I0 input_type_0;
    typedef I1 input_type_1;
    typedef bool codomain_type;

    bool operator()(I0, I1)
    {
       return true;
    }
};

template<typename C0, typename C1, typename R>
    requires(Readable(C0) && BifurcateCoordinate(C0) &&
        Readable(C1) && BifurcateCoordinate(C1) &&
        EOPValueType(C0) == EOPValueType(C1) &&
        Relation(R) && EOPValueType(C0) == EOPDomain(R))
bool bifurcate_equivalent_nonempty(C0 c0, C1 c1, R r)
{
    // Precondition: $\property{readable\_tree}(c0) \wedge \property{readable\_tree}(c1)$
    // Precondition: $\neg \func{empty}(c0) \wedge \neg \func{empty}(c1)$
    // Precondition: $\property{equivalence}(r)$
    if (!r(source(c0), source(c1))) return false;
    if (has_left_successor(c0))
        if (has_left_successor(c1)) {
            if (!bifurcate_equivalent_nonempty(
                  left_successor(c0), left_successor(c1), r))
                return false;
        } else return false;
    else if (has_left_successor(c1)) return false;
    if (has_right_successor(c0))
        if (has_right_successor(c1)) {
            if (!bifurcate_equivalent_nonempty(
                  right_successor(c0), right_successor(c1), r))
                return false;
        } else return false;
    else if (has_right_successor(c1)) return false;
    return true;
}

template<typename C0, typename C1, typename R>
    requires(Readable(C0) &&
        BidirectionalBifurcateCoordinate(C0) &&
        Readable(C1) && 
        BidirectionalBifurcateCoordinate(C1) &&
        EOPValueType(C0) == EOPValueType(C1) &&
        Relation(R) && EOPValueType(C0) == EOPDomain(R))
bool bifurcate_equivalent(C0 c0, C1 c1, R r)
{
    // Precondition: $\property{readable\_tree}(c0) \wedge \property{readable\_tree}(c1)$
    // Precondition: $\property{equivalence}(r)$
    if (empty(c0)) return empty(c1);
    if (empty(c1)) return false;
    C0 root0 = c0;
    visit v0 = pre;
    visit v1 = pre;
    while (true) {
        if (v0 == pre && !r(source(c0), source(c1)))
            return false;          
        traverse_step(v0, c0);
        traverse_step(v1, c1);
        if (v0 != v1) return false;
        if (c0 == root0 && v0 == post) return true;
    }
}

template<typename C0, typename C1>
    requires(Readable(C0) &&
        BidirectionalBifurcateCoordinate(C0) &&
        Readable(C1) && 
        BidirectionalBifurcateCoordinate(C1) &&
        EOPValueType(C0) == EOPValueType(C1))
bool bifurcate_equal(C0 c0, C1 c1)
{
    return bifurcate_equivalent(c0, c1, equal<EOPValueType(C0)>());
}

template<typename I0, typename I1, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        EOPValueType(I0) == EOPValueType(I1) &&
        Relation(R) && EOPValueType(I0) == EOPDomain(R))
bool lexicographical_compare(I0 f0, I0 l0, I1 f1, I1 l1, R r)
{
    // Precondition: $\property{readable\_bounded\_range}(f0, l0)$
    // Precondition: $\property{readable\_bounded\_range}(f1, l1)$
    // Precondition: $\property{weak\_ordering}(r)$
    while (true) {
        if (f1 == l1) return false;
        if (f0 == l0) return true;
        if (r(source(f0), source(f1))) return true;
        if (r(source(f1), source(f0))) return false;
        f0 = successor(f0);
        f1 = successor(f1);
    }
}

template<typename I0, typename I1>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        EOPValueType(I0) == EOPValueType(I1))
bool lexicographical_less(I0 f0, I0 l0, I1 f1, I1 l1)
{
    return lexicographical_compare(f0, l0, f1, l1,
                                   less<EOPValueType(I0)>());
}

template<int k, typename I0, typename I1>
   requires(Readable(I0) && ForwardIterator(I0) &&
       Readable(I1) && ForwardIterator(I1) &&
       EOPValueType(I0) == EOPValueType(I1))
struct lexicographical_less_k
{
    typedef I0 input_type_0;
    typedef I1 input_type_1;
    typedef bool codomain_type;

    bool operator()(I0 f0, I1 f1)
    {
        if (source(f0) < source(f1)) return true;
        if (source(f0) > source(f1)) return false;
        return lexicographical_less_k<k - 1, I0, I1>()(
            successor(f0),
            successor(f1)); 
    }
};

template<typename I0, typename I1>
struct lexicographical_less_k<0, I0, I1>
{
    typedef I0 input_type_0;
    typedef I1 input_type_1;
    typedef bool codomain_type;

    bool operator()(I0, I1)
    {
       return false;
    }
};


// Exercise 7.6: bifurcate_compare_nonempty (using 3-way comparsion)

// concept Comparator3Way(F) is
//     HomogeneousFunction(F)
//  /\ Arity(F) = 2
//  /\ EOPCodomain(F) = int

// property(F : Comparator3Way)
// three_way_compare : F
//  f |- (all a,b in EOPDomain(F)) f(a, b) in {-1, 0, 1}

//  Also need axioms equivalent to weak_order : transitivity, etc.
//  We could relax this to OrderedAdditiveGroup
//  (allowing subtraction as the comparator for numbers)
//  Should sense of positive/negative be flipped?

template<typename R>
    requires(Relation(R))
struct comparator_3_way
{
    typedef EOPDomain(R) T;
    typedef T input_type_0;
    typedef T input_type_1;
    typedef int codomain_type;

    R r;
    int operator()(T const& a, T const& b)
    {
        if (r(a, b)) return 1;
        if (r(b, a)) return -1;
        return 0;
    }
};

template<typename R>
    requires(Relation(R))
inline comparator_3_way<R> make_comparator_3_way(const R& r)
{
    comparator_3_way<R> tmp = {r};
    return tmp;
}

template<typename I0, typename I1, typename F>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        EOPValueType(I0) == EOPValueType(I1) &&
        Comparator3Way(F) && EOPValueType(I0) == EOPDomain(F))
int lexicographical_compare_3way(I0 f0, I0 l0, I1 f1, I1 l1, F comp)
{
    // Precondition: $\property{readable\_bounded\_range}(f0, l0)$
    // Precondition: $\property{readable\_bounded\_range}(f1, l1)$
    // Precondition: $\property{three\_way\_compare}(comp)$
    while (true) {
        if (f0 == l0) {
            if (f1 == l1) return 0;
            else return 1;
        }
        if (f1 == l1) return -1;
        int tmp = comp(source(f0), source(f1));
        if (tmp != 0) return tmp;
        f0 = successor(f0);
        f1 = successor(f1);
    }
}

template<typename C0, typename C1, typename F>
    requires(Readable(C0) && BifurcateCoordinate(C0) &&
        Readable(C1) && BifurcateCoordinate(C1) &&
        EOPValueType(C0) == EOPValueType(C1) &&
        Comparator3Way(F) && EOPValueType(I0) == EOPDomain(F))
int bifurcate_compare_nonempty(C0 c0, C1 c1, F comp)
{
    // Precondition: $\property{readable\_tree}(c0) \wedge \property{readable\_tree}(c1)$
    // Precondition: $\neg \func{empty}(c0) \wedge \neg \func{empty}(c1)$
    // Precondition: $\property{three\_way\_compare}(comp)$
    int tmp = comp(source(c0), source(c1));
    if (tmp != 0) return tmp;
    if (has_left_successor(c0))
        if (has_left_successor(c1)) {
            tmp = bifurcate_compare_nonempty(left_successor(c0), left_successor(c1),
                                             comp);
            if (tmp != 0) return tmp;
        } else return -1;
    else if (has_left_successor(c1)) return 1;
    if (has_right_successor(c0))
        if (has_right_successor(c1)) {
            tmp = bifurcate_compare_nonempty(right_successor(c0), right_successor(c1),
                                             comp);
            if (tmp != 0) return tmp;
        } else return -1;
    else if (has_right_successor(c1)) return 1;
    return 0;
}

template<typename C0, typename C1, typename R>
    requires(Readable(C0) &&
        BidirectionalBifurcateCoordinate(C0) &&
        Readable(C1) && 
        BidirectionalBifurcateCoordinate(C1) &&
        EOPValueType(C0) == EOPValueType(C1) &&
        Relation(R) && EOPValueType(C0) == EOPDomain(R))
bool bifurcate_compare(C0 c0, C1 c1, R r)
{
    // Precondition: $\property{readable\_tree}(c0) \wedge
    //                \property{readable\_tree}(c1) \wedge
    //                \property{weak\_ordering}(r)$
    if (empty(c1)) return false;
    if (empty(c0)) return true;
    C0 root0 = c0;
    visit v0 = pre;
    visit v1 = pre;
    while (true) {
        if (v0 == pre) {
            if (r(source(c0), source(c1))) return true;
            if (r(source(c1), source(c0))) return false;
        }
        traverse_step(v0, c0);
        traverse_step(v1, c1);
        if (v0 != v1) return v0 > v1;
        if (c0 == root0 && v0 == post) return false;
    }
}

template<typename C0, typename C1>
    requires(Readable(C0) &&
        BidirectionalBifurcateCoordinate(C0) &&
        Readable(C1) && 
        BidirectionalBifurcateCoordinate(C1))
bool bifurcate_less(C0 c0, C1 c1)
{
    // Precondition: $\property{readable\_tree}(c0) \wedge
    //                \property{readable\_tree}(c1)
    return bifurcate_compare(c0, c1, less<EOPValueType(C0)>());
}

template<typename T>
    requires(TotallyOrdered(T))
struct always_false
{
    typedef T input_type_0;
    typedef T input_type_1;
    typedef bool codomain_type;

    bool operator()(T const& x, T const& y) const
    {
        return false;
    }
};

template<typename C0, typename C1>
    requires(Readable(C0) &&
        BidirectionalBifurcateCoordinate(C0) &&
        Readable(C1) && 
        BidirectionalBifurcateCoordinate(C1))
bool bifurcate_shape_compare(C0 c0, C1 c1)
{
    // Precondition: $\property{readable\_tree}(c0) \wedge
    //                \property{readable\_tree}(c1)
    return bifurcate_compare(c0, c1, always_false<EOPValueType(C0)>());
}


// 
//  Chapter 8. Coordinates with mutable successors
// 


// Models of ForwardLinker, BackwardLinker, and BidirectionalLinker
// assuming a particular representation of links

template<typename I>
    requires(LinkedForwardIterator(I))
struct forward_linker
{
    typedef I input_type_0;
    typedef I input_type_1;
    typedef void codomain_type;

    void operator()(I x, I y)
    {
        sink(x.p).forward_link = y.p;
    }
};

template<typename I>
    requires(LinkableForwardIterator(I))
struct iterator_type< forward_linker<I> >
{
    typedef I type;
};

template<typename I>
    requires(LinkedBidirectionalIterator(I))
struct backward_linker
{
    typedef I input_type_0;
    typedef I input_type_1;
    typedef void codomain_type;

    void operator()(I x, I y)
    {
        sink(y.p).backward_link = x.p;
    }
};

template<typename I>
    requires(LinkedBidirectionalIterator(I))
struct iterator_type< backward_linker<I> >
{
    typedef I type;
};

template<typename I>
    requires(LinkedBidirectionalIterator(I))
struct bidirectional_linker
{
    typedef I input_type_0;
    typedef I input_type_1;
    typedef void codomain_type;

    void operator()(I x, I y)
    {
        sink(x.p).forward_link = y.p;
        sink(y.p).backward_link = x.p;
    }
};

template<typename I>
    requires(LinkedBidirectionalIterator(I))
struct iterator_type< bidirectional_linker<I> >
{
    typedef I type;
};

template<typename I>
    requires(ForwardIterator(I))
void advance_tail(I& t, I& f)
{
    // Precondition: $\func{successor}(f)\text{ is defined}$
    t = f;
    f = successor(f);
}

template<typename S>
    requires(ForwardLinker(S))
struct linker_to_tail
{
    typedef EOPIteratorType(S) I;
    typedef I& input_type_0;
    typedef I& input_type_1;
    typedef void codomain_type;

    S set_link;
    void operator()(I& t, I& f)
    {
        // Precondition: $\func{successor}(f)\text{ is defined}$
        set_link(t, f);
        advance_tail(t, f);
    }
};

template<typename S>
    requires(ForwardLinker(S))
inline linker_to_tail<S> make_linker_to_tail(const S& s)
{
    linker_to_tail<S> tmp = {s};
    return tmp;
}

template<typename I>
    requires(ForwardIterator(I))
I find_last(I f, I l)
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge f \neq l$
    I t;
    do
        advance_tail(t, f);
    while (f != l);
    return t;
}

template<typename I, typename S, typename Pred>
    requires(ForwardLinker(S) && I == EOPIteratorType(S) &&
        UnaryPseudoPredicate(Pred) && I == EOPDomain(Pred))
pair< pair<I, I>, pair<I, I> >
split_linked(I f, I l, Pred p, S set_link)
{
    // Precondition: $\property{bounded\_range}(f, l)$
    typedef pair<I, I> P;
    linker_to_tail<S> link_to_tail = {set_link};
    I h0 = l; I t0 = l;
    I h1 = l; I t1 = l; 
    if (f == l)                              goto s4; 
    if (p(f)) { h1 = f; advance_tail(t1, f); goto s1; }
    else      { h0 = f; advance_tail(t0, f); goto s0; }
s0: if (f == l)                              goto s4; 
    if (p(f)) { h1 = f; advance_tail(t1, f); goto s3; }
    else      {         advance_tail(t0, f); goto s0; }
s1: if (f == l)                              goto s4; 
    if (p(f)) {         advance_tail(t1, f); goto s1; }
    else      { h0 = f; advance_tail(t0, f); goto s2; }
s2: if (f == l)                              goto s4; 
    if (p(f)) {         link_to_tail(t1, f); goto s3; }
    else      {         advance_tail(t0, f); goto s2; }
s3: if (f == l)                              goto s4; 
    if (p(f)) {         advance_tail(t1, f); goto s3; }  
    else      {         link_to_tail(t0, f); goto s2; }
s4: return make_pair(make_pair(h0, t0), make_pair(h1, t1));
}

// Exercise 8.1: Explain the postcondition of split_linked


template<typename I, typename S, typename R>
    requires(ForwardLinker(S) && I == EOPIteratorType(S) &&
        PseudoRelation(R) && I == EOPDomain(R))
triple<I, I, I>
combine_linked_nonempty(I f0, I l0, I f1, I l1, R r, S set_link)
{
    // Precondition: $\property{bounded\_range}(f0, l0) \wedge
    //                \property{bounded\_range}(f1, l1)$
    // Precondition: $f0 \neq l0 \wedge f1 \neq l1 \wedge
    //                \property{disjoint}(f0, l0, f1, l1)$
    linker_to_tail<S> link_to_tail = {set_link};
    I h; I t;
    if (r(f1, f0)) { h = f1; advance_tail(t, f1); goto s1; }
    else           { h = f0; advance_tail(t, f0); goto s0; }
s0: if (f0 == l0)                                 goto s2; 
    if (r(f1, f0)) {         link_to_tail(t, f1); goto s1; }
    else           {         advance_tail(t, f0); goto s0; }
s1: if (f1 == l1)                                 goto s3;
    if (r(f1, f0)) {         advance_tail(t, f1); goto s1; }
    else           {         link_to_tail(t, f0); goto s0; }
s2: set_link(t, f1); return make_triple(h, t, l1);
s3: set_link(t, f0); return make_triple(h, t, l0);
}

// Exercise 8.2: combine_linked


template<typename S>
    requires(ForwardLinker(S))
struct linker_to_head
{
    typedef EOPIteratorType(S) I;
    typedef I& input_type_0;
    typedef I& input_type_1;
    typedef void codomain_type;

    S set_link;
    void operator()(I& h, I& f)
    {
        // Precondition: $\func{successor}(f)$ is defined
        EOPIteratorType(S) tmp = successor(f);
        set_link(f, h);
        h = f;
        f = tmp;
    }
};

template<typename S>
    requires(ForwardLinker(S))
inline linker_to_head<S> make_linker_to_head(const S& s)
{
    linker_to_head<S> tmp = {s};
    return tmp ;
}

template<typename I, typename S>
    requires(ForwardLinker(S) && I == EOPIteratorType(S))
I reverse_append(I f, I l, I h, S set_link)
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge h \notin [f, l)$
    linker_to_head<S> link_to_head = {set_link};
    while (f != l) link_to_head(h, f);
    return h;
}

template<typename I, typename P>
    requires(Readable(I) && 
        Predicate(P) && EOPValueType(I) == EOPDomain(P))
struct predicate_source
{
    typedef I input_type_0;
    typedef bool codomain_type;

    P p;
    bool operator()(I i)
    {
        return p(source(i));
    }
};

template<typename I, typename P>
    requires(Readable(I) && 
        Predicate(P) && EOPValueType(I) == EOPDomain(P))
inline predicate_source<I, P> make_predicate_source(const P& p)
{
    predicate_source<I, P> tmp = {p};
    return tmp;
}

template<typename I, typename S, typename P>
    requires(ForwardLinker(S) && I == EOPIteratorType(S) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
pair< pair<I, I>, pair<I, I> >
partition_linked(I f, I l, P p, S set_link)
{
    // Precondition: $\property{bounded\_range}(f, l)$
    predicate_source<I, P> ps = {p};
    return split_linked(f, l, ps, set_link);
}

template<typename I0, typename I1, typename R>
    requires(Readable(I0) && Readable(I1) &&
        EOPValueType(I0) == EOPValueType(I1) &&
        Relation(R) && EOPValueType(I0) == EOPDomain(R))
struct relation_source
{
    typedef I0 input_type_0;
    typedef I1 input_type_1;
    typedef bool codomain_type;

    R r;
    bool operator()(I0 i0, I1 i1)
    {
        return r(source(i0), source(i1));
    }
};

template<typename I0, typename I1, typename R>
    requires(Readable(I0) && Readable(I1) &&
        EOPValueType(I0) == EOPValueType(I1) &&
        Relation(R) && EOPValueType(I0) == EOPDomain(R))
inline relation_source<I0, I1, R> make_relation_source(const R& r)
{
    relation_source<I0, I1, R> tmp = {r};
    return tmp;
}

template<typename I, typename S, typename R>
    requires(Readable(I) &&
        ForwardLinker(S) && I == EOPIteratorType(S) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
pair<I, I> merge_linked_nonempty(I f0, I l0, I f1, I l1,
                                 R r, S set_link)
{
    // Precondition: $f0 \neq l0 \wedge f1 \neq l1$
    // Precondition: $\property{increasing\_range}(f0, l0, r)$
    // Precondition: $\property{increasing\_range}(f1, l1, r)$
    relation_source<I, I, R> rs = {r};
    triple<I, I, I> t = combine_linked_nonempty(f0, l0, f1, l1,
                                                rs, set_link);
    set_link(find_last(t.m1, t.m2), l1);
    return make_pair(t.m0, l1);
}

template<typename I, typename S, typename R>
    requires(Readable(I) &&
        ForwardLinker(S) && I == EOPIteratorType(S) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
pair<I, I> sort_linked_nonempty_n(I f, EOPDistanceType(I) n,
                                  R r, S set_link)
{
    // Precondition: $\property{counted\_range}(f, n) \wedge
    //                n > 0 \wedge \func{weak\_ordering}(r)$
    typedef EOPDistanceType(I) N;
    typedef pair<I, I> P;
    if (n == N(1)) return make_pair(f, successor(f));
    N h = half_nonnegative(n);
    P p0 = sort_linked_nonempty_n(f, h, r, set_link);
    P p1 = sort_linked_nonempty_n(p0.m1, n - h, r, set_link);
    return merge_linked_nonempty(p0.m0, p0.m1,
                                 p1.m0, p1.m1, r, set_link);
}

// Exercise 8.3: Complexity of sort_linked_nonempty_n


// Exercise 8.4: unique


template<typename C>
     requires(EmptyLinkedBifurcateCoordinate(C))
void tree_rotate(C& curr, C& prev)
{
    // Precondition: $\neg \func{empty}(curr)$
    C tmp = left_successor(curr);
    set_left_successor(curr, right_successor(curr));
    set_right_successor(curr, prev);
    if (empty(tmp)) { prev = tmp; return; }
    prev = curr;
    curr = tmp;
}

template<typename C, typename Proc>
    requires(EmptyLinkedBifurcateCoordinate(C) &&
        Procedure(Proc) && Arity(Proc) == 1 &&
        C == EOPInputType(Proc, 0))
Proc traverse_rotating(C c, Proc proc)
{
    // Precondition: $\property{tree}(c)$
    if (empty(c)) return proc;
    C curr = c;
    C prev;
    do {
        proc(curr);
        tree_rotate(curr, prev);
    } while (curr != c);
    do {
        proc(curr);
        tree_rotate(curr, prev);
    } while (curr != c);
    proc(curr);
    tree_rotate(curr, prev);
    return proc;
}

// Exercise 8.5: Diagram each state of traverse_rotating
// for a complete binary tree with 7 nodes


template<typename T, typename N>
    requires(Integer(N))
struct counter
{
    typedef T input_type_0;
    typedef void codomain_type;

    N n;
    void operator()(T const&) { n = successor(n); }
};

template<typename T, typename N>
    requires(Integer(N))
inline counter<T, N> make_counter(const N& n)
{
    counter<T, N> tmp = {n};
    return tmp;
}

template<typename C>
    requires(EmptyLinkedBifurcateCoordinate(C))
EOPWeightType(C) weight_rotating(C c)
{
    // Precondition: $\property{tree}(c)$
    typedef EOPWeightType(C) N;
    return traverse_rotating(c, make_counter<C>(N(0))).n / N(3);
}

template<typename N, typename Proc>
    requires(Integer(N) &&
        Procedure(Proc) && Arity(Proc) == 1)
struct phased_applicator
{
    typedef EOPInputType0(Proc) input_type_0;
    typedef void codomain_type;

    N period;
    N phase;
    N n;
    // Invariant: $n, phase \in [0, period)$
    Proc proc;
    phased_applicator(N period, N phase, N n, Proc proc) :
        period(period), phase(phase), n(n), proc(proc) { }
    void operator()(input_type_0 x)
    {
        if (n == phase) proc(x);
        n = successor(n);
        if (n == period) n = 0;
    }
};

template<typename C, typename Proc>
    requires(EmptyLinkedBifurcateCoordinate(C) &&
        Procedure(Proc) && Arity(Proc) == 1 &&
        C == EOPInputType(Proc, 0))
Proc traverse_phased_rotating(C c, int phase, Proc proc)
{
    // Precondition: $\property{tree}(c) \wedge 0 \leq phase < 3$
    phased_applicator<int, Proc> applicator(3, phase, 0, proc);
    return traverse_rotating(c, applicator).proc;
}


// 
//  Chapter 9. Copying
// 


template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        EOPValueType(I) == EOPValueType(O))
void copy_step(I& f_i, O& f_o)
{
    // Precondition: $\func{source}(f_i)$ and $\func{sink}(f_o)$ are defined
    sink(f_o) = source(f_i);
    f_i = successor(f_i);
    f_o = successor(f_o);
}

template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        EOPValueType(I) == EOPValueType(O))
O copy(I f_i, I l_i, O f_o)
{
    // Precondition:
    // $\property{not\_overlapped\_forward}(f_i, l_i, f_o, f_o + (l_i - f_i))$
    while (f_i != l_i) copy_step(f_i, f_o);
    return f_o;
}

template<typename I>
    requires(Writable(I) && Iterator(I))
void fill_step(I& f_o, const EOPValueType(I)& x)
{
    sink(f_o) = x;
    f_o = successor(f_o);
}

template<typename I>
    requires(Writable(I) && Iterator(I))
I fill(I f, I l, const EOPValueType(I)& x)
{
    while (f != l) fill_step(f, x);
    return f;
}

template<typename O>
    requires(Writable(O) && Iterator(O) &&
        Integer(EOPValueType(O)))
O iota(EOPValueType(O) n, O o) // like APL $\iota$
{
    // Precondition: $\property{writable\_counted\_range}(o, n) \wedge n \geq 0$
    return copy(EOPValueType(O)(0), n, o);
}

// Useful for testing in conjunction with iota
template<typename I>
    requires(Readable(I) && Iterator(I) &&
        Integer(EOPValueType(I)))
bool equal_iota(I f, I l, EOPValueType(I) n = 0)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    while (f != l) {
        if (source(f) != n) return false;
        n = successor(n);
        f = successor(f);
    }
    return true;
}

template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        EOPValueType(I) == EOPValueType(O))
pair<I, O> copy_bounded(I f_i, I l_i, O f_o, O l_o)
{
    // Precondition: $\property{not\_overlapped\_forward}(f_i, l_i, f_o, l_o)$
    while (f_i != l_i && f_o != l_o) copy_step(f_i, f_o);
    return make_pair(f_i, f_o);
}

template<typename N>
    requires(Integer(N))
bool count_down(N& n)
{
    // Precondition: $n \geq 0$
    if (zero(n)) return false;
    n = predecessor(n);
    return true;
}

template<typename I, typename O, typename N>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        EOPValueType(I) == EOPValueType(O) &&
        Integer(N))
pair<I, O> copy_n(I f_i, N n, O f_o)
{
    // Precondition: $\property{not\_overlapped\_forward}(f_i, f_i+n, f_o, f_o+n)$
    while (count_down(n)) copy_step(f_i, f_o);
    return make_pair(f_i, f_o);
}

template<typename I>
    requires(Writable(I) && Iterator(I))
I fill_n(I f, EOPDistanceType(I) n, const EOPValueType(I)& x)
{
    while (count_down(n)) fill_step(f, x);
    return f;
}

template<typename I, typename O>
    requires(Readable(I) && BidirectionalIterator(I) &&
        Writable(O) && BidirectionalIterator(O) &&
        EOPValueType(I) == EOPValueType(O))
void copy_backward_step(I& l_i, O& l_o)
{
    // Precondition: $\func{source}(\property{predecessor}(l_i))$ and
    //               $\func{sink}(\property{predecessor}(l_o))$
    //               are defined
    l_i = predecessor(l_i);
    l_o = predecessor(l_o);
    sink(l_o) = source(l_i);
}

template<typename I, typename O>
    requires(Readable(I) && BidirectionalIterator(I) &&
        Writable(O) && BidirectionalIterator(O) &&
        EOPValueType(I) == EOPValueType(O))
O copy_backward(I f_i, I l_i, O l_o)
{
    // Precondition: $\property{not\_overlapped\_backward}(f_i, l_i, l_o-(l_i-f_i), l_o)$
    while (f_i != l_i) copy_backward_step(l_i, l_o);
    return l_o;
}

template<typename I, typename O>
    requires(Readable(I) && BidirectionalIterator(I) &&
        Writable(O) && BidirectionalIterator(O) &&
        EOPValueType(I) == EOPValueType(O))
pair<I, O> copy_backward_n(I l_i, EOPDistanceType(I) n, O l_o)
{
    while (count_down(n)) copy_backward_step(l_i, l_o);
    return make_pair(l_i, l_o);
}

template<typename I, typename O>
    requires(Readable(I) && BidirectionalIterator(I) &&
        Writable(O) && Iterator(O) &&
        EOPValueType(I) == EOPValueType(O))
void reverse_copy_step(I& l_i, O& f_o)
{
    // Precondition: $\func{source}(\func{predecessor}(l_i))$ and
    //               $\func{sink}(f_o)$ are defined
    l_i = predecessor(l_i);
    sink(f_o) = source(l_i);
    f_o = successor(f_o);
}

template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && BidirectionalIterator(O) &&
        EOPValueType(I) == EOPValueType(O))
void reverse_copy_backward_step(I& f_i, O& l_o)
{
    // Precondition: $\func{source}(f_i)$ and
    //               $\func{sink}(\property{predecessor}(l_o))$ are defined
    l_o = predecessor(l_o);
    sink(l_o) = source(f_i);
    f_i = successor(f_i);
}

template<typename I, typename O>
    requires(Readable(I) && BidirectionalIterator(I) &&
        Writable(O) && Iterator(O) &&
        EOPValueType(I) == EOPValueType(O))
O reverse_copy(I f_i, I l_i, O f_o)
{
    // Precondition: $\property{not\_overlapped}(f_i, l_i, f_o, f_o+(l_i-f_i))$
    while (f_i != l_i) reverse_copy_step(l_i, f_o);
    return f_o;
}

template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && BidirectionalIterator(O) &&
        EOPValueType(I) == EOPValueType(O))
O reverse_copy_backward(I f_i, I l_i, O l_o)
{
    // Precondition: $\property{not\_overlapped}(f_i, l_i, l_o-(l_i-f_i), l_o)$
    while (f_i != l_i) reverse_copy_backward_step(f_i, l_o);
    return l_o;
}

template<typename I, typename O, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        EOPValueType(I) == EOPValueType(O) &&
        UnaryPredicate(P) && I == EOPDomain(P))
O copy_select(I f_i, I l_i, O f_t, P p)
{
    // Precondition: $\property{not\_overlapped\_forward}(f_i, l_i, f_t, f_t+n_t)$
    // where $n_t$ is an upper bound for the number of iterators satisfying $p$
    while (f_i != l_i)
        if (p(f_i)) copy_step(f_i, f_t);
        else f_i = successor(f_i);
    return f_t;
}

template<typename I, typename O, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        EOPValueType(I) == EOPValueType(O) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
O copy_if(I f_i, I l_i, O f_t, P p)
{
    // Precondition: same as for $\func{copy\_select}$
    predicate_source<I, P> ps = {p};
    return copy_select(f_i, l_i, f_t, ps);
}

template<typename I, typename O_f, typename O_t, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O_f) && Iterator(O_f) &&
        Writable(O_t) && Iterator(O_t) &&
        EOPValueType(I) == EOPValueType(O_f) &&
        EOPValueType(I) == EOPValueType(O_t) &&
        UnaryPredicate(P) && I == EOPDomain(P))
pair<O_f, O_t> split_copy(I f_i, I l_i, O_f f_f, O_t f_t,
                          P p)
{
    // Precondition: see section 9.3 of Elements of Programming
    while (f_i != l_i)
        if (p(f_i)) copy_step(f_i, f_t);
        else        copy_step(f_i, f_f);
    return make_pair(f_f, f_t);
}

template<typename I, typename O_f, typename O_t, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O_f) && Iterator(O_f) &&
        Writable(O_t) && Iterator(O_t) &&
        EOPValueType(I) == EOPValueType(O_f) &&
        EOPValueType(I) == EOPValueType(O_t) &&
        UnaryPredicate(P) && I == EOPDomain(P))
pair<O_f, O_t> split_copy_n(I f_i, EOPDistanceType(I) n_i, O_f f_f, O_t f_t, P p)
{
    // Precondition: see exercise 9.2 of Elements of Programming
    while (count_down(n_i))
        if (p(f_i)) copy_step(f_i, f_t);
        else        copy_step(f_i, f_f);
    return make_pair(f_f, f_t);
}

template<typename I, typename O_f, typename O_t, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O_f) && Iterator(O_f) &&
        Writable(O_t) && Iterator(O_t) &&
        EOPValueType(I) == EOPValueType(O_f) &&
        EOPValueType(I) == EOPValueType(O_t) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
pair<O_f, O_t> partition_copy(I f_i, I l_i, O_f f_f, O_t f_t,
                              P p)
{
    // Precondition: same as $\func{split\_copy}$
    predicate_source<I, P> ps = {p};
    return split_copy(f_i, l_i, f_f, f_t, ps);
}

template<typename I, typename O_f, typename O_t, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O_f) && Iterator(O_f) &&
        Writable(O_t) && Iterator(O_t) &&
        EOPValueType(I) == EOPValueType(O_f) &&
        EOPValueType(I) == EOPValueType(O_t) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
pair<O_f, O_t> partition_copy_n(I f_i, EOPDistanceType(I) n,
                                O_f f_f, O_t f_t,
                                P p)
{
    // Precondition: see $\func{partition_copy}$
    predicate_source<I, P> ps = {p};
    return split_copy_n(f_i, n, f_f, f_t, ps);
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        Writable(O) && Iterator(O) &&
        BinaryPredicate(R) &&
        EOPValueType(I0) == EOPValueType(O) &&
        EOPValueType(I1) == EOPValueType(O) &&
        I0 == EOPInputType(R, 1) && I1 == EOPInputType(R, 0))
O combine_copy(I0 f_i0, I0 l_i0, I1 f_i1, I1 l_i1, O f_o, R r)
{
    // Precondition: see section 9.3 of Elements of Programming
    while (f_i0 != l_i0 && f_i1 != l_i1)
        if (r(f_i1, f_i0)) copy_step(f_i1, f_o);
        else               copy_step(f_i0, f_o);
    return copy(f_i1, l_i1, copy(f_i0, l_i0, f_o)); 
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        Writable(O) && Iterator(O) &&
        BinaryPredicate(R) &&
        EOPValueType(I0) == EOPValueType(O) &&
        EOPValueType(I1) == EOPValueType(O) &&
        I0 == EOPInputType(R, 1) && I1 = EOPInputType(R, 0))
triple<I0, I1, O> combine_copy_n(I0 f_i0, EOPDistanceType(I0) n_i0,
                                 I1 f_i1, EOPDistanceType(I1) n_i1,
                                 O f_o, R r) {
    // Precondition: see $\func{combine_copy}$
    while (true) {
        if (zero(n_i0)) {
            pair<I1, O> p = copy_n(f_i1, n_i1, f_o);
            return make_triple(f_i0, p.m0, p.m1);
        }
        if (zero(n_i1)) {
            pair<I0, O> p = copy_n(f_i0, n_i0, f_o);
            return make_triple(p.m0, f_i1, p.m1);
        }
        if (r(f_i1, f_i0)) {
            copy_step(f_i1, f_o);
            n_i1 = predecessor(n_i1);
        } else             {
            copy_step(f_i0, f_o);
            n_i0 = predecessor(n_i0);
        }
    }
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && BidirectionalIterator(I0) &&
        Readable(I1) && BidirectionalIterator(I1) &&
        Writable(O) && BidirectionalIterator(O) &&
        BinaryPredicate(R) &&
        EOPValueType(I0) == EOPValueType(O) &&
        EOPValueType(I1) == EOPValueType(O) &&
        I0 == EOPInputType(R, 1) && I1 == EOPInputType(R, 0))
O combine_copy_backward(I0 f_i0, I0 l_i0, I1 f_i1, I1 l_i1,
                        O l_o, R r)
{
    // Precondition: see section 9.3 of Elements of Programming
    while (f_i0 != l_i0 && f_i1 != l_i1) {
        if (r(predecessor(l_i1), predecessor(l_i0)))
            copy_backward_step(l_i0, l_o);
        else
            copy_backward_step(l_i1, l_o);
    }
    return copy_backward(f_i0, l_i0,
                         copy_backward(f_i1, l_i1, l_o));
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && BidirectionalIterator(I0) &&
        Readable(I1) && BidirectionalIterator(I1) &&
        Writable(O) && BidirectionalIterator(O) &&
        BinaryPredicate(R) && 
        EOPValueType(I0) == EOPValueType(O) && EOPValueType(I1) == EOPValueType(O) &&
        I0 == EOPInputType(R, 1) && I1 = EOPInputType(R, 0))
triple<I0, I1, O> combine_copy_backward_n(I0 l_i0, EOPDistanceType(I0) n_i0,
                           I1 l_i1, EOPDistanceType(I1) n_i1, O l_o, R r) {
    // Precondition: see $\func{combine\_copy\_backward}$
    while (true) {
        if (zero(n_i0)) {
            pair<I1, O> p = copy_backward_n(l_i1, n_i1, l_o);
            return make_triple(l_i0, p.m0, p.m1);
        }
        if (zero(n_i1)) {
            pair<I0, O> p = copy_backward_n(l_i0, n_i0, l_o);
            return make_triple(p.m0, l_i1, p.m1);
        }
        if (r(predecessor(l_i1), predecessor(l_i0))) {
            copy_backward_step(l_i0, l_o);
            n_i0 = predecessor(n_i0);
        } else {
            copy_backward_step(l_i1, l_o);
            n_i1 = predecessor(n_i1);
        }
    }
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        Writable(O) && Iterator(O) &&
        Relation(R) && 
        EOPValueType(I0) == EOPValueType(O) &&
        EOPValueType(I1) == EOPValueType(O) &&
        EOPValueType(I0) == EOPDomain(R))
O merge_copy(I0 f_i0, I0 l_i0, I1 f_i1, I1 l_i1, O f_o, R r)
{
    // Precondition: in addition to that for $\func{combine\_copy}$:
    // \hspace*{1em} $\property{weak\_ordering}(r) \wedge {}$
    // \hspace*{1em} $\func{increasing\_range}(f_{i_0}, l_{i_0}, r) \wedge
    //                \property{increasing\_range}(f_{i_1}, l_{i_1}, r)$
    relation_source<I1, I0, R> rs = {r};
    return combine_copy(f_i0, l_i0, f_i1, l_i1, f_o, rs); 
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        Writable(O) && Iterator(O) &&
        Relation(R) && 
        EOPValueType(I0) == EOPValueType(O) &&
        EOPValueType(I1) == EOPValueType(O) &&
        EOPValueType(I0) == EOPDomain(R))
triple<I0, I1, O> merge_copy_n(I0 f_i0, EOPDistanceType(I0) n_i0,
                               I1 f_i1, EOPDistanceType(I1) n_i1,
                               O o, R r)
{
    // Precondition: see $\func{merge\_copy}$
    relation_source<I1, I0, R> rs = {r};
    return combine_copy_n(f_i0, n_i0, f_i1, n_i1, o, rs);
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && BidirectionalIterator(I0) &&
        Readable(I1) && BidirectionalIterator(I1) &&
        Writable(O) && BidirectionalIterator(O) &&
        Relation(R) && 
        EOPValueType(I0) == EOPValueType(O) &&
        EOPValueType(I1) == EOPValueType(O) &&
        EOPValueType(I0) == EOPDomain(R))
O merge_copy_backward(I0 f_i0, I0 l_i0, I1 f_i1, I1 l_i1, O l_o,
                      R r)
{
    // Precondition: in addition to that for $\func{combine\_copy\_backward}$:
    //               $\property{weak\_ordering}(r) \wedge {}$
    //               $\func{increasing\_range}(f_{i_0}, l_{i_0}, r) \wedge
    //                \property{increasing\_range}(f_{i_1}, l_{i_1}, r)$
    relation_source<I1, I0, R> rs = {r};
    return combine_copy_backward(f_i0, l_i0, f_i1, l_i1, l_o,
                                 rs);
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && BidirectionalIterator(I0) &&
        Readable(I1) && BidirectionalIterator(I1) &&
        Writable(O) && BidirectionalIterator(O) &&
        Relation(R) && 
        EOPValueType(I0) == EOPValueType(O) && EOPValueType(I1) == EOPValueType(O) &&
        EOPValueType(I0) == EOPDomain(R))
triple<I0, I1, O> merge_copy_backward_n(I0 l_i0, EOPDistanceType(I0) n_i0,
                           I1 l_i1, EOPDistanceType(I1) n_i1, O l_o, R r) {
    // Precondition: see $\func{merge\_copy\_backward}$
    relation_source<I1, I0, R> rs = {r};
    return combine_copy_backward_n(l_i0, n_i0, l_i1, n_i1, l_o, rs);
}

template<typename I0, typename I1>
    requires(Mutable(I0) && Mutable(I1) &&
        EOPValueType(I0) == EOPValueType(I1))
void exchange_values(I0 x, I1 y)
{
    // Precondition: $\func{deref}(x)$ and $\func{deref}(y)$ are defined
    EOPValueType(I0) t = source(x);
            sink(x) = source(y);
            sink(y) = t;
}

template<typename I0, typename I1>
    requires(Mutable(I0) && ForwardIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        EOPValueType(I0) == EOPValueType(I1))
void swap_step(I0& f0, I1& f1)
{
    // Precondition: $\func{deref}(f_0)$ and $\func{deref}(f_1)$ are defined
    exchange_values(f0, f1);
    f0 = successor(f0);
    f1 = successor(f1);
}

template<typename I0, typename I1>
    requires(Mutable(I0) && ForwardIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        EOPValueType(I0) == EOPValueType(I1))
I1 swap_ranges(I0 f0, I0 l0, I1 f1)
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, l_0-f_0)$
    while (f0 != l0) swap_step(f0, f1);
    return f1;
}

template<typename I0, typename I1>
    requires(Mutable(I0) && ForwardIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        EOPValueType(I0) == EOPValueType(I1))
pair<I0, I1> swap_ranges_bounded(I0 f0, I0 l0, I1 f1, I1 l1)
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition: $\property{mutable\_bounded\_range}(f_1, l_1)$
    while (f0 != l0 && f1 != l1) swap_step(f0, f1);
    return make_pair(f0, f1);
}

template<typename I0, typename I1, typename N>
    requires(Mutable(I0) && ForwardIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        EOPValueType(I0) == EOPValueType(I1) &&
        Integer(N))
pair<I0, I1> swap_ranges_n(I0 f0, I1 f1, N n)
{
    // Precondition: $\property{mutable\_counted\_range}(f_0, n)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, n)$
    while (count_down(n)) swap_step(f0, f1);
    return make_pair(f0, f1);
}

template<typename I0, typename I1>
    requires(Mutable(I0) && BidirectionalIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        EOPValueType(I0) == EOPValueType(I1))
void reverse_swap_step(I0& l0, I1& f1)
{
    // Precondition: $\func{deref}(\func{predecessor}(l_0))$ and
    //               $\func{deref}(f_1)$ are defined
    l0 = predecessor(l0);
    exchange_values(l0, f1);
    f1 = successor(f1);
}

template<typename I0, typename I1>
    requires(Mutable(I0) && BidirectionalIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        EOPValueType(I0) == EOPValueType(I1))
I1 reverse_swap_ranges(I0 f0, I0 l0, I1 f1)
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, l_0-f_0)$
    while (f0 != l0) reverse_swap_step(l0, f1);
    return f1;
}

template<typename I0, typename I1>
    requires(Mutable(I0) && BidirectionalIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        EOPValueType(I0) == EOPValueType(I1))
pair<I0, I1>reverse_swap_ranges_bounded(I0 f0, I0 l0,
                                        I1 f1, I1 l1)
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition:  $\property{mutable\_bounded\_range}(f_1, l_1)$
    while (f0 != l0 && f1 != l1)
        reverse_swap_step(l0, f1);
    return make_pair(l0, f1);
}

template<typename I0, typename I1, typename N>
    requires(Mutable(I0) && BidirectionalIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        EOPValueType(I0) == EOPValueType(I1) &&
        Integer(N))
pair<I0, I1> reverse_swap_ranges_n(I0 l0, I1 f1, N n)
{
    // Precondition: $\property{mutable\_counted\_range}(l_0-n, n)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, n)$
    while (count_down(n)) reverse_swap_step(l0, f1);
    return make_pair(l0, f1);
}


// 
//  Chapter 10. Rearrangements
// 


template<typename I, typename F>
    requires(Mutable(I) && Transformation(F) && I == EOPDomain(F))
void cycle_to(I i, F f)
{
    // Precondition: The orbit of $i$ under $f$ is circular
    // Precondition: $(\forall n \in \mathbb{N})\,\func{deref}(f^n(i))$ is defined
    I k = f(i);
    while (k != i) {
        exchange_values(i, k);
        k = f(k);
    }
}

// Exercise 10.3: cycle_to variant doing 2n-1 assignments


template<typename I, typename F>
    requires(Mutable(I) && Transformation(F) && I == EOPDomain(F))
void cycle_from(I i, F f)
{
    // Precondition: The orbit of $i$ under $f$ is circular
    // Precondition: $(\forall n \in \mathbb{N})\,\func{deref}(f^n(i))$ is defined
    EOPValueType(I) tmp = source(i);
    I j = i;
    I k = f(i);
    while (k != i) {
        sink(j) = source(k);
        j = k;
        k = f(k);
    }
    sink(j) = tmp;
}


// Exercise 10.4: arbitrary rearrangement using array of n boolean values
// Exercise 10.5: arbitrary rearrangement using total ordering on iterators


template<typename I>
    requires(Mutable(I) && IndexedIterator(I))
void reverse_n_indexed(I f, EOPDistanceType(I) n)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    EOPDistanceType(I) i(0);
    n = predecessor(n);
    while (i < n) {
        // $n = (n_\text{original} - 1) - i$
        exchange_values(f + i, f + n);
        i = successor(i);
        n = predecessor(n);
    }
}

template<typename I>
    requires(Mutable(I) && BidirectionalIterator(I))
void reverse_bidirectional(I f, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    while (true) {
        if (f == l) return;
        l = predecessor(l);
        if (f == l) return;
        exchange_values(f, l);
        f = successor(f);
    }
}

template<typename I>
    requires(Mutable(I) && BidirectionalIterator(I))
void reverse_n_bidirectional(I f, I l, EOPDistanceType(I) n)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge 0 \leq n \leq l - f$
    reverse_swap_ranges_n(l, f, half_nonnegative(n));
}

template<typename I, typename B>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        EOPValueType(I) == EOPValueType(B))
I reverse_n_with_buffer(I f_i, EOPDistanceType(I) n, B f_b)
{
    // Precondition: $\property{mutable\_counted\_range}(f_i, n)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n)$
    return reverse_copy(f_b, copy_n(f_i, n, f_b).m1, f_i);
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I reverse_n_forward(I f, EOPDistanceType(I) n)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    typedef EOPDistanceType(I) N;
    if (n < N(2)) return f + n;
    N h = half_nonnegative(n);
    N n_mod_2 = n - twice(h);
    I m = reverse_n_forward(f, h) + n_mod_2;
    I l = reverse_n_forward(m, h);
    swap_ranges_n(f, m, h);
    return l;
}

template<typename I, typename B>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        EOPValueType(I) == EOPValueType(B))
I reverse_n_adaptive(I f_i, EOPDistanceType(I) n_i,
                     B f_b, EOPDistanceType(I) n_b)
{
    // Precondition: $\property{mutable\_counted\_range}(f_i, n_i)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_b)$
    typedef EOPDistanceType(I) N;
    if (n_i < N(2))
        return f_i + n_i;
    if (n_i <= n_b)
        return reverse_n_with_buffer(f_i, n_i, f_b);
    N h_i = half_nonnegative(n_i);
    N n_mod_2 = n_i - twice(h_i);
    I m_i = reverse_n_adaptive(f_i, h_i, f_b, n_b) + n_mod_2;
    I l_i = reverse_n_adaptive(m_i, h_i, f_b, n_b);
    swap_ranges_n(f_i, m_i, h_i);
    return l_i;
}

template<typename I>
    requires(RandomAccessIterator(I))
struct k_rotate_from_permutation_random_access
{
    typedef I input_type_0;
    typedef I codomain_type;

    EOPDistanceType(I) k;
    EOPDistanceType(I) n_minus_k;
    I m_prime;
    k_rotate_from_permutation_random_access(I f, I m, I l) :
        k(l - m), n_minus_k(m - f), m_prime(f + (l - m))
    {
        // Precondition: $\property{bounded\_range}(f, l) \wedge m \in [f, l)$
    }
    I operator()(I x)
    {
        // Precondition: $x \in [f, l)$
        if (x < m_prime) return x + n_minus_k;
        else             return x - k;
    }
};

template<typename I>
    requires(IndexedIterator(I))
struct k_rotate_from_permutation_indexed
{
    typedef I input_type_0;
    typedef I codomain_type;

    EOPDistanceType(I) k;
    EOPDistanceType(I) n_minus_k;
    I f;
    k_rotate_from_permutation_indexed(I f, I m, I l) :
        k(l - m), n_minus_k(m - f), f(f)
    {
        // Precondition: $\property{bounded\_range}(f, l) \wedge m \in [f, l)$
    }
    I operator()(I x)
    {
        // Precondition: $x \in [f, l)$
        EOPDistanceType(I) i = x - f;
        if (i < k) return x + n_minus_k;
        else       return f + (i - k);
    }
};

template<typename I, typename F>
    requires(Mutable(I) && IndexedIterator(I) &&
        Transformation(F) && I == EOPDomain(F))
I rotate_cycles(I f, I m, I l, F from)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge m \in [f, l]$
    // Precondition: $from$ is a from-permutation on $[f, l)$
    typedef EOPDistanceType(I) N;
    N d = gcd<N, N>(m - f, l - m);
    while (count_down(d)) cycle_from(f + d, from);
    return f + (l - m);
}

template<typename I>
    requires(Mutable(I) && IndexedIterator(I))
I rotate_indexed_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    k_rotate_from_permutation_indexed<I> p(f, m, l);
    return rotate_cycles(f, m, l, p);
}

template<typename I>
    requires(Mutable(I) && RandomAccessIterator(I))
I rotate_random_access_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    k_rotate_from_permutation_random_access<I> p(f, m, l);
    return rotate_cycles(f, m, l, p);
}


template<typename I>
    requires(Mutable(I) && BidirectionalIterator(I))
I rotate_bidirectional_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    reverse_bidirectional(f, m);
    reverse_bidirectional(m, l);
    pair<I, I> p = reverse_swap_ranges_bounded(m, l, f, m);
    reverse_bidirectional(p.m1, p.m0);
    if (m == p.m0) return p.m1;
    else           return p.m0;
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
void rotate_forward_annotated(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
                                      EOPDistanceType(I) a = m - f;
                                      EOPDistanceType(I) b = l - m;
    while (true) {
        pair<I, I> p = swap_ranges_bounded(f, m, m, l);
        if (p.m0 == m && p.m1 == l) { EOPAssert(a == b);
            return;
        }
        f = p.m0;           
        if (f == m) {                 EOPAssert(b > a);
            m = p.m1;                 b = b - a;
        } else {                      EOPAssert(a > b);
                                      a = a - b;
        }  
    }
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
void rotate_forward_step(I& f, I& m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    I c = m;
    do {
        swap_step(f, c);
        if (f == m) m = c;
    } while (c != l);
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I rotate_forward_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    rotate_forward_step(f, m, l);
    I m_prime = f;
    while (m != l) rotate_forward_step(f, m, l);
    return m_prime;
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I rotate_partial_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return swap_ranges(m, l, f);
}

// swap_ranges_backward
// rotate_partial_backward_nontrivial

template<typename I, typename B>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B))
I rotate_with_buffer_nontrivial(I f, I m, I l, B f_b)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    // Precondition: $\property{mutable\_counted\_range}(f_b, l-f)$
    B l_b = copy(f, m, f_b);
    I m_prime = copy(m, l, f);
    copy(f_b, l_b, m_prime);
    return m_prime;    
}

template<typename I, typename B>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        Mutable(B) && ForwardIterator(B))
I rotate_with_buffer_backward_nontrivial(I f, I m, I l, B f_b)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    // Precondition: $\property{mutable\_counted\_range}(f_b, l-f)$
    B l_b = copy(m, l, f_b);
    copy_backward(f, m, l);
    return copy(f_b, l_b, f);
}


// Section 10.5. Algorithm selection


template<typename I>
    requires(Mutable(I) && IndexedIterator(I))
void reverse_indexed(I f, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    reverse_n_indexed(f, l - f);
}


// temporary_buffer type

template<typename I>
    requires(Writeable(I) && ForwardIterator(I))
void construct_all(I f, I l)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{refers to raw memory, not an object}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a default-constructed state}$
    // We assume if an iterator is writeable, its value can be constructed
    construct_all(f, l, NeedsConstruction(EOPValueType(I))());
}

template<typename I>
    requires(Writeable(I) && ForwardIterator(I))
void construct_all(I f, I l, true_type)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{refers to raw memory, not an object}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // We assume if an iterator is writeable, its value can be constructed
    while (f != l) {
        construct(sink(f));
        f = successor(f);
    }
}

template<typename I>
    requires(Writeable(I) && ForwardIterator(I) &&
        NeedsConstruction(EOPValueType(I)) == false_type)
void construct_all(I /*f*/, I /*l*/, false_type)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
}

template<typename I>
    requires(Writeable(I) && ForwardIterator(I))
void destroy_all(I f, I l)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{refers to raw memory, not an object}$
    // We assume if an iterator is writeable, its value can be destroyed
    destroy_all(f, l, NeedsDestruction(EOPValueType(I))());
}

template<typename I>
    requires(Writeable(I) && ForwardIterator(I))
void destroy_all(I f, I l, true_type)
{
    // Precondition: $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // Postcondition: $(\forall i \in [f, l)) \func{sink}(i) \text{refers to raw memory, not an object}$
    // We assume if an iterator is writeable, its value can be destroyed
    while (f != l) {
        destroy(sink(f));
        f = successor(f);
    }
}

template<typename I>
    requires(Writeable(I) && ForwardIterator(I) &&
        NeedsDestruction(EOPValueType(I)) == false_type)
void destroy_all(I /*f*/, I /*l*/, false_type)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
}

// NeedsConstruction and NeedsDestruction should be overloaded for every POD type

template<typename T>
    requires(Regular(T))
struct temporary_buffer
{
    typedef EOPpointer(T) P;
    typedef EOPDistanceType(P) N;
    P p;
    N n;
    temporary_buffer(N n_) : n(n_)
    {
        while (true) {
            p = P(malloc(n * sizeof(T)));
            if (p != P(0)) {
                construct_all(p, p + n);
                return;
            }
            n = half_nonnegative(n);
        }
    }
    ~temporary_buffer()
    {
        destroy_all(p, p + n);
        free(p);
    }
private:
    // We use private only to signal lack of regularity of a type
    temporary_buffer(const temporary_buffer&) { }
    void operator=(const temporary_buffer&) { }
};

template<typename T>
    requires(Regular(T))
EOPDistanceType(EOPpointer(T)) size(const temporary_buffer<T>& b)
{
    return b.n;
}

template<typename T>
    requires(Regular(T))
EOPpointer(T) begin(temporary_buffer<T>& b)
{
    return b.p;
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
void reverse_n_with_temporary_buffer(I f, EOPDistanceType(I) n)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    temporary_buffer<EOPValueType(I)> b(n);
    reverse_n_adaptive(f, n, begin(b), size(b));
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I rotate(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge m \in [f, l]$
    if (m == f) return l;
    if (m == l) return f;
    return rotate_nontrivial(f, m, l, EOPIteratorConcept(I)());
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I rotate_nontrivial(I f, I m, I l, forward_iterator_tag)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return rotate_forward_nontrivial(f, m, l);
}

template<typename I>
    requires(Mutable(I) && BidirectionalIterator(I))
I rotate_nontrivial(I f, I m, I l, bidirectional_iterator_tag)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return rotate_bidirectional_nontrivial(f, m, l);
}

template<typename I>
    requires(Mutable(I) && IndexedIterator(I))
I rotate_nontrivial(I f, I m, I l, indexed_iterator_tag)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return rotate_indexed_nontrivial(f, m, l);
}

template<typename I>
    requires(Mutable(I) && RandomAccessIterator(I))
I rotate_nontrivial(I f, I m, I l, random_access_iterator_tag)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return rotate_random_access_nontrivial(f, m, l);
}


// 
//  Chapter 11. Partition and merging
// 


// Exercise 11.1:

template<typename I,  typename P>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
bool partitioned_at_point(I f, I m, I l, P p)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l) \wedge m \in [f, l]$
    return none(f, m, p) && all(m, l, p);
}


// Exercise 11.2:

template<typename I, typename P>
    requires(Readable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I potential_partition_point(I f, I l, P p)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    return count_if_not(f, l, p, f);
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I partition_semistable(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    I i = find_if(f, l, p);
    if (i == l) return i;
    I j = successor(i);
    while (true) {
        j = find_if_not(j, l, p);
        if (j == l) return i;
        swap_step(i, j);
    }
}

// Exercise 11.3: rewrite partition_semistable, expanding find_if_not inline and
// eliminating extra test against l


// Exercise 11.4: substitute copy_step(j, i) for swap_step(i, j) in partition_semistable

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I remove_if(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    I i = find_if(f, l, p);
    if (i == l) return i;
    I j = successor(i);
    while (true) {
        j = find_if_not(j, l, p);
        if (j == l) return i;
        copy_step(j, i);
    }
}


// Exercise 11.5:

//template<typename I, typename P>
//    requires(Mutable(I) && ForwardIterator(I) &&
//        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
//void partition_semistable_omit_last_predicate_evaluation(I f, I l, P p)
//{
//    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
//    ...
//}

template<typename I, typename P>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I partition_bidirectional(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    while (true) {
        f = find_if(f, l, p);
        l = find_backward_if_not(f, l, p);
        if (f == l) return f;
        reverse_swap_step(l, f);
    }
}

// Exercise 11.6:

template<typename I,  typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I partition_forward(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    I i = count_if_not(f, l, p, f);
    I j = i;
    while (true) {
        j = find_if_not(j, l, p);
        if (j == l) return i;
        f = find_if_unguarded(f, p);
        swap_step(f, j);
    }
}

// Exercise 11.7: partition_single_cycle

template<typename I, typename P>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I partition_single_cycle(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    f = find_if(f, l, p);
    l = find_backward_if_not(f, l, p);
    if (f == l) return f;
    l = predecessor(l);
    EOPValueType(I) tmp = source(f);
    while (true) {
        sink(f) = source(l);
        f = find_if(successor(f), l, p);
        if (f == l) {
            sink(l) = tmp;
            return f;
        }
        sink(l) = source(f);
        l = find_backward_if_not_unguarded(l, p);
    }
}


// Exercise 11.8: partition_sentinel

template<typename I, typename P>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I partition_bidirectional_unguarded(I f, I l, P p)
{
    // Precondition:
    // $(\neg \func{all}(f, l, p) \wedge \func{some}(f, l, p)) \vee
    // (\neg p(\func{source}(f-1)) \wedge p(\func{source}(l)))$
    while (true) {
        f = find_if_unguarded(f, p);
        l = find_backward_if_not_unguarded(l, p);
        if (successor(l) == f) return f;
        exchange_values(f, l);
        f = successor(f); // $\neg p(\func{source}(f-1)) \wedge p(\func{source}(l))$
    }
}

template<typename I, typename P>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I partition_sentinel(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    f = find_if(f, l, p);
    l = find_backward_if_not(f, l, p);
    if (f == l) return f;
    l = predecessor(l);
    exchange_values(f, l);
    f = successor(f);
    return partition_bidirectional_unguarded(f, l, p);
}


// Exercise 11.9: partition_single_cycle_sentinel


template<typename I, typename P>
    requires(Mutable(I) && IndexedIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I partition_indexed(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    typedef EOPDistanceType(I) N;
    N i(0);
    N j = l - f;
    while (true) {
        while (true) {
            if (i == j) return f + i;  
            if (p(source(f + i))) break;
            i = successor(i);
        } 
        while (true) {
            j = predecessor(j);
            if (i == j) return f + j + 1;  
            if (!p(source(f + j))) break;
        }   
        exchange_values(f + i, f + j);
        i = successor(i);
    }
}

template<typename I, typename B, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        EOPValueType(I) == EOPValueType(B) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
I partition_stable_with_buffer(I f, I l, B f_b, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, l-f)$
    pair<I, B> x = partition_copy(f, l, f, f_b, p);
    copy(f_b, x.m1, x.m0);
    return x.m0;
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
pair<I, I> partition_stable_singleton(I f, P p)
{
    // Precondition: $\property{readable\_bounded\_range}(f, \func{successor}(f))$
    I l = successor(f);
    if (!p(source(f))) f = l;
    return make_pair(f, l);
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
pair<I, I> combine_ranges(const pair<I, I>& x,
                          const pair<I, I>& y)
{
    // Precondition: $\property{mutable\_bounded\_range}(x.m0, y.m0)$
    // Precondition: $x.m1 \in [x.m0, y.m0]$
    return make_pair(rotate(x.m0, x.m1, y.m0), y.m1);
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
pair<I, I> partition_stable_n_nonempty(I f, EOPDistanceType(I) n,
                                       P p)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n) \wedge n > 0$
    if (one(n)) return partition_stable_singleton(f, p);
    EOPDistanceType(I) h = half_nonnegative(n);
    pair<I, I> x = partition_stable_n_nonempty(f, h, p);
    pair<I, I> y = partition_stable_n_nonempty(x.m1, n - h, p);
    return combine_ranges(x, y);
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
pair<I, I> partition_stable_n(I f, EOPDistanceType(I) n, P p)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    if (zero(n)) return make_pair(f, f);
    return partition_stable_n_nonempty(f, n, p);
}


// Exercise 11.10: partition_stable_n_adaptive


template<typename I, typename P>
   requires(Mutable(I) && ForwardIterator(I) &&
       UnaryPredicate(P) && EOPDomain(P) == EOPValueType(I)\)
I partition_stable(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    return partition_stable_n(f, l - f, p).m0;
}

template<typename I, typename P>
    requires(ForwardIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
struct partition_trivial 
{
    typedef I input_type_0;
    typedef pair<I, I> codomain_type;

    P p;
    pair<I, I> operator()(I i)
    {
        return partition_stable_singleton<I, P>(i, p);
    }
};

template<typename I, typename P>
    requires(ForwardIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
inline partition_trivial<I, P> make_partition_trivial(const P& p)
{
    partition_trivial<I, P> tmp = {p};
    return tmp ;
}

template<typename I, typename Op>
    requires(Mutable(I) && ForwardIterator(I) &&
        BinaryOperation(Op) && EOPValueType(I) == EOPDomain(Op))
EOPDomain(Op) add_to_counter(I f, I l, Op op, EOPDomain(Op) x,
                          const EOPDomain(Op)& z)
{
    if (x == z) return z;
    while (f != l) {
        if (source(f) == z) { 
            sink(f) = x;
            return z;
        }
        x = op(source(f), x); 
        sink(f) = z;
        f = successor(f);
    }
    return x;
}

template<typename Op>
    requires(BinaryOperation(Op))
struct counter_machine
{
    typedef EOPDomain(Op) T;
    typedef T input_type_0;
    typedef void codomain_type;

    Op op;
    T z;
    T f[64];
    EOPpointer(T) l;
    counter_machine(Op op, T const& z) :
        op(op), z(z), l(f) { }
    void operator()(T const& x)
    {
        // Precondition: must not be called more than $2^{64}-1$ times
         T tmp = add_to_counter(f, l, op, x, z);
         if (tmp != z) {
             sink(l) = tmp;
             l = successor(l);
         }
    }
};

template<typename Op>
    requires(BinaryOperation(Op))
struct transpose_operation
{
    Op op;
    typedef EOPDomain(Op) T;
    typedef T input_type_0;
    typedef T input_type_1;
    typedef T codomain_type;

    T operator()(T const& x, T const& y)
    {
        return op(y, x);
    }
};

template<typename Op>
    requires(BinaryOperation(Op))
inline transpose_operation<Op> make_transpose_operation(const Op& op)
{
    transpose_operation<Op> tmp = {op};
    return tmp;
}

template<typename I>
    requires(Iterator(I))
struct apply_source
{
    typedef I input_type_0;
    typedef EOPValueType(I) codomain_type;

    codomain_type operator()(I f) const
    {
        return source(f);
    }
};

template<typename I>
    requires(Iterator(I))
inline apply_source<I> make_apply_source()
{
    apply_source<I> tmp = {};
    return tmp ;
}

template<typename I, typename Op, typename F>
    requires(Iterator(I) && BinaryOperation(Op) && 
        UnaryFunction(F) && I == EOPDomain(F) &&
        EOPCodomain(F) == EOPDomain(Op))
EOPDomain(Op) reduce_balanced(I f, I l, Op op, F fun,
                           const EOPDomain(Op)& z)
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge l - f < 2^{64}$
    // Precondition: $\property{partially\_associative}(op)$
    // Precondition: $(\forall x \in [f, l))\,fun(x)$ is defined
    counter_machine<Op> c(op, z);
    while (f != l) {
        c(fun(f));
        f = successor(f);
    }
    return reduce_nonzeroes(c.f, c.l, make_transpose_operation(op), z);
}  

template<typename I, typename Op>
    requires(ReadableIterator(I) && BinaryOperation(Op) && 
        EOPValueType(I) == EOPDomain(Op))
inline EOPDomain(Op) reduce_balanced(I f, I l, Op op, const EOPDomain(Op)& z)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l) \wedge l-f < 2^{64}$
    // Precondition: $\property{partially\_associative}(op)$
    return reduce_balanced(f, l, op, make_apply_source<I>(), z);
}


template<typename I, typename P>
    requires(ForwardIterator(I) && UnaryPredicate(P) &&
        EOPValueType(I) == EOPDomain(P))
I partition_stable_iterative(I f, I l, P p)
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge l - f < 2^{64}$
    return reduce_balanced(
        f, l,
        combine_ranges<I>,
        make_partition_trivial<I>(p),
        make_pair(f, f)
      ).m0;
} 

template<typename I, typename B, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        EOPValueType(I) == EOPValueType(B) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
I merge_n_with_buffer(I f0, EOPDistanceType(I) n0,
                      I f1, EOPDistanceType(I) n1, B f_b, R r)
{
    // Precondition: $\func{mergeable}(f_0, n_0, f_1, n_1, r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_0)$
    copy_n(f0, n0, f_b);
    return merge_copy_n(f_b, n0, f1, n1, f0, r).m2;
}

template<typename I, typename B, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        EOPValueType(I) == EOPValueType(B) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
I sort_n_with_buffer(I f, EOPDistanceType(I) n, B f_b, R r)
{
    // Property:
    // $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, \lceil n/2 \rceil)$
    EOPDistanceType(I) h = half_nonnegative(n);
    if (zero(h)) return f + n;
    I m = sort_n_with_buffer(f, h,     f_b, r);
          sort_n_with_buffer(m, n - h, f_b, r);
    return merge_n_with_buffer(f, h, m, n - h, f_b, r);
}

template<typename I, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
void merge_n_step_0(I f0, EOPDistanceType(I) n0,
                    I f1, EOPDistanceType(I) n1, R r,
                    I& f0_0, EOPDistanceType(I)& n0_0,
                    I& f0_1, EOPDistanceType(I)& n0_1,
                    I& f1_0, EOPDistanceType(I)& n1_0,
                    I& f1_1, EOPDistanceType(I)& n1_1)
{
    // Precondition: $\property{mergeable}(f_0, n_0, f_1, n_1, r)$
    f0_0 = f0;
    n0_0 = half_nonnegative(n0);
    f0_1 = f0_0 + n0_0;
    f1_1 = lower_bound_n(f1, n1, source(f0_1), r);
    f1_0 = rotate(f0_1, f1, f1_1);
    n0_1 = f1_0 - f0_1;
    f1_0 = successor(f1_0);
    n1_0 = predecessor(n0 - n0_0);
    n1_1 = n1 - n0_1;
}

template<typename I, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
void merge_n_step_1(I f0, EOPDistanceType(I) n0,
                    I f1, EOPDistanceType(I) n1, R r,
                    I& f0_0, EOPDistanceType(I)& n0_0,
                    I& f0_1, EOPDistanceType(I)& n0_1,
                    I& f1_0, EOPDistanceType(I)& n1_0,
                    I& f1_1, EOPDistanceType(I)& n1_1)
{
    // Precondition: $\property{mergeable}(f_0, n_0, f_1, n_1, r)$
    f0_0 = f0;
    n0_1 = half_nonnegative(n1);
    f1_1 = f1 + n0_1;
    f0_1 = upper_bound_n(f0, n0, source(f1_1), r);
    f1_1 = successor(f1_1); 
    f1_0 = rotate(f0_1, f1, f1_1);
    n0_0 = f0_1 - f0_0;
    n1_0 = n0 - n0_0;
    n1_1 = predecessor(n1 - n0_1);
}

template<typename I, typename B, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        EOPValueType(I) == EOPValueType(B) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
I merge_n_adaptive(I f0, EOPDistanceType(I) n0,
                   I f1, EOPDistanceType(I) n1,
                   B f_b, EOPDistanceType(B) n_b, R r)
{
    // Precondition: $\property{mergeable}(f_0, n_0, f_1, n_1, r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_b)$
    typedef EOPDistanceType(I) N;
    if (zero(n0) || zero(n1)) return f0 + n0 + n1;
    if (n0 <= N(n_b))
        return merge_n_with_buffer(f0, n0, f1, n1, f_b, r);
    I f0_0; I f0_1; I f1_0; I f1_1;
    N n0_0; N n0_1; N n1_0; N n1_1;
    if (n0 < n1) merge_n_step_0(
                            f0, n0, f1, n1, r,
                            f0_0, n0_0, f0_1, n0_1,
                            f1_0, n1_0, f1_1, n1_1);
    else         merge_n_step_1(
                            f0, n0, f1, n1, r,
                            f0_0, n0_0, f0_1, n0_1,
                            f1_0, n1_0, f1_1, n1_1);
           merge_n_adaptive(f0_0, n0_0, f0_1, n0_1,
                            f_b, n_b, r);
    return merge_n_adaptive(f1_0, n1_0, f1_1, n1_1,
                            f_b, n_b, r);
}

template<typename I, typename B, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        EOPValueType(I) == EOPValueType(B) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
I sort_n_adaptive(I f, EOPDistanceType(I) n,
                  B f_b, EOPDistanceType(B) n_b, R r)
{
    // Precondition:
    // $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_b)$
    EOPDistanceType(I) h = half_nonnegative(n);
    if (zero(h)) return f + n;
    I m = sort_n_adaptive(f, h,     f_b, n_b, r);
          sort_n_adaptive(m, n - h, f_b, n_b, r);
    return merge_n_adaptive(f, h, m, n - h, f_b, n_b, r);
}

template<typename I, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
I sort_n(I f, EOPDistanceType(I) n, R r)
{
    // Precondition:
    // $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    temporary_buffer<EOPValueType(I)> b(half_nonnegative(n));
    return sort_n_adaptive(f, n, begin(b), size(b), r);
}


// 
//  Chapter 12. Composite objects
// 


// pair type: see Chapter 1 of this file


// Exercise 12.1: less< pair<T0, T1> > using less<T0> and less<T1>


// triple type: see Chapter 1 of this file


// Exercise 12.2: triple type


// array_k type

template<int k, typename T>
    requires(0 < k && k <= MaximumValue(int) / sizeof(T) &&
        Regular(T))
struct array_k
{
    T a[k];
    T& operator[](int i)
    {
        // Precondition: $0 \leq i < \func{size}(x)$
        return a[i];
    }
};

template<int k, typename T>
    requires(Regular(T))
struct size_value< array_k<k, T> >
{
    static const int value = k;
};

template<int k, typename T>
    requires(Regular(T))
struct iterator_type< array_k<k, T> >
{
    typedef EOPpointer(T) type;
};

template<int k, typename T>
    requires(Regular(T))
struct value_type< array_k<k, T> >
{
    typedef T type;
};

template<int k, typename T>
    requires(Regular(T))
struct size_type< array_k<k, T> >
{
    typedef EOPDistanceType(EOPpointer(T)) type;
};

template<int k, typename T>
    requires(0 < k && k <= MaximumValue(int) / sizeof(T) &&
        Regular(T))
struct underlying_type< array_k<k, T> >
{
    typedef array_k<k, UnderlyingType(T)> type;
};

template<int k, typename T>
    requires(Regular(T))
EOPpointer(T) begin(array_k<k, T>& x)
{
    return addressof(x.a[0]);
}

template<int k, typename T>
    requires(Regular(T))
const EOPpointer(T) begin(const array_k<k, T>& x)
{
    return addressof(x.a[0]);
}

template<int k, typename T>
    requires(Regular(T))
EOPpointer(T) end(array_k<k, T>& x)
{
    return begin(x) + k;
}

template<int k, typename T>
    requires(Regular(T))
const EOPpointer(T) end(const array_k<k, T>& x)
{
    return begin(x) + k;
}

template<int k, typename T>
    requires(Regular(T))
bool operator==(const array_k<k, T>& x, const array_k<k, T>& y)
{
    return lexicographical_equal(begin(x), end(x),
                                 begin(y), end(y));
}

template<int k, typename T>
    requires(Regular(T))
bool operator<(const array_k<k, T>& x, const array_k<k, T>& y)
{
    return lexicographical_less(begin(x), end(x),
                                begin(y), end(y));
}

template<int k, typename T>
    requires(Regular(T))
int size(const array_k<k, T>&) // unused parameter name dropped to avoid warning
{
    return k;
}

template<int k, typename T>
    requires(Regular(T))
bool empty(const array_k<k, T>&) // unused parameter name dropped to avoid warning
{
    return false;
}


// concept Linearizeable

//  Since we already defined ValueType for any (regular) T,
//  C++ will not let us define it for any linearizable T like this:

// template<typename W>
//     requires(Linearizable(W))
// struct value_type
// {
//     typedef EOPValueType(EOPIteratorType(W)) type;
// };

// Instead, each type W that models Linearizable must provide
//      the corresponding specialization of value_type

template<typename W>
    requires(Linearizable(W))
bool linearizable_equal(const W& x, const W& y)
{
    return lexicographical_equal(begin(x), end(x), begin(y), end(y));
}

template<typename W>
    requires(Linearizable(W))
bool linearizable_ordering(const W& x, const W& y)
{
    return lexicographical_less(begin(x), end(x), begin(y), end(y));
}

template<typename W>
    requires(Linearizeable(W))
EOPDistanceType(EOPIteratorType(W)) size(const W& x)
{
    return end(x) - begin(x);
}

template<typename W>
    requires(Linearizeable(W))
bool empty(const W& x)
{
    return begin(x) == end(x);
}


// type bounded_range
// model Linearizable(bounded_range)

template<typename I>
    requires(Readable(I) && Iterator(I))
struct bounded_range {
    I f;
    I l;
    bounded_range() { }
    bounded_range(const I& f, const I& l) : f(f), l(l) { }
    const EOPValueType(I)& operator[](EOPDistanceType(I) i)
    {
        // Precondition: $0 \leq i < l - f$
        return source(f + i);
    }
};

template<typename I>
    requires(Readable(I) && Iterator(I))
struct iterator_type< bounded_range<I> >
{
    typedef I type;
};

template<typename I>
    requires(Readable(I) && Iterator(I))
struct value_type< bounded_range<I> >
{
    typedef EOPValueType(I) type;
};

template<typename I>
    requires(Readable(I) && Iterator(I))
struct size_type< bounded_range<I> >
{
    typedef EOPDistanceType(I) type;
};

template<typename I>
    requires(Readable(I) && Iterator(I))
I begin(const bounded_range<I>& x) { return x.f; }

template<typename I>
    requires(Readable(I) && Iterator(I))
I end(const bounded_range<I>& x) { return x.l; }

template<typename I>
    requires(Readable(I) && Iterator(I))
bool operator==(const bounded_range<I>& x,
                const bounded_range<I>& y)
{
    return begin(x) == begin(y) && end(x) == end(y);
}

template<typename I>
    requires(Readable(I) && Iterator(I))
struct less< bounded_range<I> >
{
    typedef bounded_range<I> input_type_0;
    typedef bounded_range<I> input_type_1;
    typedef bool codomain_type;

    bool operator()(bounded_range<I> const& x,
                    bounded_range<I> const& y)
    {
        less<I> less_I;
        return less_I(begin(x), begin(y)) ||
               (!less_I(begin(y), begin(x)) &&
                 less_I(end(x), end(y)));
    }
};


// type counted_range
// model Linearizable(counted_range)

template<typename I>
    requires(Readable(I) && Iterator(I)) // should it be ForwardIterator?
struct counted_range {
    typedef EOPDistanceType(I) N;
    I f;
    N n;
    counted_range() { }
    counted_range(I f, N n) : f(f), n(n) { }
    const EOPValueType(I)& operator[](int i)
    {
        // Precondition: $0 \leq i < l - f$
        return source(f + i);
    }
};

template<typename I>
    requires(Readable(I) && Iterator(I))
struct iterator_type< counted_range<I> >
{
    typedef I type;
};

template<typename I>
    requires(Readable(I) && Iterator(I))
struct value_type< counted_range<I> >
{
    typedef EOPValueType(I) type;
};

template<typename I>
    requires(Readable(I) && Iterator(I))
struct size_type< counted_range<I> >
{
    typedef EOPDistanceType(I) type;
};


template<typename I>
    requires(Readable(I) && Iterator(I))
I begin(const counted_range<I>& x) { return x.f; }

template<typename I>
    requires(Readable(I) && Iterator(I))
I end(const counted_range<I>& x) { return x.f + x.n; }

template<typename I>
    requires(Readable(I) && Iterator(I))
EOPDistanceType(I) size(const counted_range<I>& x) { return x.n; }

template<typename I>
    requires(Readable(I) && Iterator(I))
bool empty(counted_range<I>& x) { return size(x) == 0; }

template<typename I>
    requires(Readable(I) && Iterator(I))
bool operator==(const counted_range<I>& x,
                const counted_range<I>& y)
{
    return begin(x) == begin(y) && size(x) == size(y);
}

template<typename I>
    requires(Readable(I) && Iterator(I))
struct less< counted_range<I> >
{
    typedef counted_range<I> input_type_0;
    typedef counted_range<I> input_type_1;
    typedef bool codomain_type;

    bool operator()(counted_range<I> const& x,
                    counted_range<I> const& y)
    {
        less<I> less_I;
        return less_I(begin(x), begin(y)) ||
               (!less_I(begin(y), begin(x)) &&
                 size(x) < size(y));
    }
};


// concept Position(T) means
//     BaseType : Position -> Linearizable
//  /\ EOPIteratorType : Position -> Iterator
//  /\ ValueType : Position -> Regular
//         T |- EOPValueType(EOPIteratorType(T))
//  /\ EOPSizeType : Position -> Integer
//         T |- EOPSizeType(EOPIteratorType(T))
//  /\ base : T -> BaseType(T)
//  /\ current : T -> EOPIteratorType(T)
//  /\ begin : T -> EOPIteratorType(T)
//         x |- begin(base(x))
//  /\ end : T -> EOPIteratorType(T)
//         x |- end(base(x))


// concept DynamicSequence(T) means
//     Sequence(T)
//  /\ T supports insert and erase


// concept InsertPosition(T) means
//     Position(T)
//  /\ BaseType : Position -> DynamicSequence

// model InsertPosition(before) /\ InsertPosition(after) /\
//       InsertPosition(front) /\ InsertPosition(back)


// concept ErasePosition(T) means
//     Position(T)
//  /\ BaseType : Position -> DynamicSequence

// model ErasePosition(before) /\ ErasePosition(after) /\
//       ErasePosition(front) /\ ErasePosition(back) /\
//       ErasePosition(at)

template<typename S>
    requires(DynamicSequence(S))
struct before
{
    typedef EOPIteratorType(S) I;
    EOPpointer(S) s;
    I i;
    before(S& s, I i) : s(&s), i(i) { }
};

template<typename S>
    requires(DynamicSequence(S))
struct base_type< before<S> >
{
    typedef S type;
};

template<typename S>
    requires(DynamicSequence(S))
struct iterator_type< before<S> >
{
    typedef EOPIteratorType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct value_type< before<S> >
{
    typedef EOPValueType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct size_type< before<S> >
{
    typedef EOPDistanceType(EOPIteratorType(S)) type;
};

template<typename S>
    requires(DynamicSequence(S))
S& base(before<S>& p)
{
    return deref(p.s);
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) current(before<S>& p)
{
    return p.i;
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) begin(before<S>& p)
{
    return begin(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) end(before<S>& p)
{
    return end(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
struct after
{
    typedef EOPIteratorType(S) I;
    EOPpointer(S) s;
    I i;
    after(S& s, I i) : s(&s), i(i) { }
};

template<typename S>
    requires(DynamicSequence(S))
struct base_type< after<S> >
{
    typedef S type;
};

template<typename S>
    requires(DynamicSequence(S))
struct iterator_type< after<S> >
{
    typedef EOPIteratorType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct value_type< after<S> >
{
    typedef EOPValueType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct size_type< after<S> >
{
    typedef EOPDistanceType(EOPIteratorType(S)) type;
};

template<typename S>
    requires(DynamicSequence(S))
S& base(after<S>& p)
{
    return deref(p.s);
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) current(after<S>& p)
{
    return p.i;
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) begin(after<S>& p)
{
    return begin(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) end(after<S>& p)
{
    return end(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
struct front
{
    EOPpointer(S) s;
    front(S& s) : s(&s) { }
};

template<typename S>
    requires(DynamicSequence(S))
struct base_type< front<S> >
{
    typedef S type;
};

template<typename S>
    requires(DynamicSequence(S))
struct iterator_type< front<S> >
{
    typedef EOPIteratorType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct value_type< front<S> >
{
    typedef EOPValueType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct size_type< front<S> >
{
    typedef EOPDistanceType(EOPIteratorType(S)) type;
};

template<typename S>
    requires(DynamicSequence(S))
S& base(front<S>& p)
{
    return deref(p.s);
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) current(front<S>& p)
{
    return begin(p);
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) begin(front<S>& p)
{
    return begin(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) end(front<S>& p)
{
    return end(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
struct back
{
    EOPpointer(S) s;
    back(S& s) : s(&s) { }
};

template<typename S>
    requires(DynamicSequence(S))
struct base_type< back<S> >
{
    typedef S type;
};

template<typename S>
    requires(DynamicSequence(S))
struct iterator_type< back<S> >
{
    typedef EOPIteratorType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct value_type< back<S> >
{
    typedef EOPValueType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct size_type< back<S> >
{
    typedef EOPDistanceType(EOPIteratorType(S)) type;
};

template<typename S>
    requires(DynamicSequence(S))
S& base(back<S>& p)
{
    return deref(p.s);
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) current(back<S>& p)
{
    return end(p);
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) begin(back<S>& p)
{
    return begin(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) end(back<S>& p)
{
    return end(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
struct at
{
    typedef EOPIteratorType(S) I;
    EOPpointer(S) s;
    I i;
    at(S& s, I i) : s(&s), i(i) { }
};

template<typename S>
    requires(DynamicSequence(S))
struct base_type< at<S> >
{
    typedef S type;
};

template<typename S>
    requires(DynamicSequence(S))
struct iterator_type< at<S> >
{
    typedef EOPIteratorType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct value_type< at<S> >
{
    typedef EOPValueType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct size_type< at<S> >
{
    typedef EOPDistanceType(EOPIteratorType(S)) type;
};

template<typename S>
    requires(DynamicSequence(S))
S& base(at<S>& p)
{
    return deref(p.s);
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) current(at<S>& p)
{
    return p.i;
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) begin(at<S>& p)
{
    return begin(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
EOPIteratorType(S) end(at<S>& p)
{
    return end(base(p));
}


// type insert_iterator
// model Iterator(insert_iterator)

template<typename P>
    requires(InsertPosition(P))
struct insert_iterator
{
    typedef insert_iterator I;
    P p;
    insert_iterator(const P& p) : p(p) { }
    void operator=(const EOPValueType(P)& x) { p = insert(p, x); }
};

template<typename P>
    requires(InsertPosition(P))
struct iterator_type< insert_iterator<P> >
{
    typedef EOPIteratorType(P) type;
};

template<typename P>
    requires(InsertPosition(P))
struct value_type< insert_iterator<P> >
{
    typedef EOPValueType(P) type;
};

template<typename P>
    requires(InsertPosition(P))
insert_iterator<P>& sink(insert_iterator<P>& i)
{
    return i;
}

template<typename P>
    requires(InsertPosition(P))
insert_iterator<P> successor(const insert_iterator<P>& x)
{
    return x;
}

template<typename P, typename W>
    requires(InsertPosition(P) && Linearizable(W))
P insert_range(P p, const W& w)
{
    return copy(begin(w), end(w), insert_iterator<P>(p)).p;
}

template<typename P, typename I>
    requires(InsertPosition(P) && Readable(I) && Iterator(I))
pair<P, I> insert_range(P p, counted_range<I> w)
{
    pair< I, insert_iterator<P> > io =
        copy_n(begin(w), size(w), insert_iterator<P>(p));
    return make_pair(io.m1.p, io.m0);
}

template<typename S, typename W>
    requires(DynamicSequence(S) && Linearizable(W))
void dynamic_sequence_construction(S& s, const W& w)
{
    construct(s);
    S tmp;
    insert_range(after<S>(tmp, end(tmp)), w);
    swap(s, tmp);
}


// type slist
// model DynamicSequence(slist)

template<typename T>
    requires(Regular(T))
struct slist_node
{
    T value;
    EOPpointer(slist_node) forward_link;
    slist_node(const T& v, EOPpointer(slist_node) f) : value(v), forward_link(f) { }
};

static int slist_node_count = 0; /* ***** TESTING ***** */

template<typename T>
    requires(Regular(T))
struct slist_iterator
{
    EOPpointer(slist_node<T>) p;
    slist_iterator() : p(0) { }
    slist_iterator(EOPpointer(slist_node<T>) p) : p(p) { }
};

template<typename T>
    requires(Regular(T))
struct value_type< slist_iterator<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct distance_type< slist_iterator<T> >
{
    typedef EOPDistanceType(slist_node<T>*) type;
};

template<typename T>
    requires(Regular(T))
struct iterator_concept< slist_iterator<T> >
{
    typedef forward_iterator_tag concept;
};

template<typename T>
    requires(Regular(T))
slist_iterator<T> successor(const slist_iterator<T>& i)
{
    return slist_iterator<T>(source(i.p).forward_link);
}

template<typename I>
    requires(LinkedForwardIterator<I>)
void set_link_forward(I i, I j)
{
    forward_linker<I>()(i, j);
}

template<typename T>
    requires(Regular(T))
bool operator==(slist_iterator<T> i, slist_iterator<T> j)
{
    return i.p == j.p;
}

template<typename T>
    requires(Regular(T))
struct less< slist_iterator<T> >
{
    typedef slist_iterator<T> input_type_0;
    typedef slist_iterator<T> input_type_1;
    typedef bool codomain_type;

    bool operator()(slist_iterator<T> i,
                    slist_iterator<T> j)
    {
        return i.p < j.p;
    }
};

template<typename T>
    requires(Regular(T))
const T& source(slist_iterator<T> i)
{
    return source(i.p).value;
}

template<typename T>
    requires(Regular(T))
T& sink(slist_iterator<T> i)
{
    return sink(i.p).value;
}

template<typename T>
    requires(Regular(T))
T& deref(slist_iterator<T> i)
{
    return sink(i.p).value;
}

template<typename T>
    requires(Regular(T))
slist_iterator<T> erase_first(slist_iterator<T> i)
{
    slist_iterator<T> j = successor(i);
    destroy(sink(i));
    free(i.p);
    slist_node_count = predecessor(slist_node_count);
    return j;
}

template<typename T,  typename U>
    requires(Regular(T) && Destroyable(T, U))
slist_iterator<T> erase_first(slist_iterator<T> i, U& u)
{
    slist_iterator<T> j = successor(i);
    destroy(sink(i), u);
    free(i.p);
    slist_node_count = predecessor(slist_node_count);
    return j;
}

template<typename T>
    requires(Regular(T))
void erase_after(slist_iterator<T> i)
{
    set_successor(i, erase_first(successor(i)));
}

template<typename T,  typename U>
    requires(Regular(T) && Destroyable(T, U))
void erase_after(slist_iterator<T> i, U& u)
{
    set_successor(i, erase_first(successor(i), u));
}

template<typename T>
    requires(Regular(T))
struct slist
{
    slist_iterator<T> first;
    slist() : first(0) { }
    slist(const slist& x)
    {
        dynamic_sequence_construction(sink(this), x);
    }
    template<typename W>
        requires(Linearizable(W) && T == EOPValueType(W))
    slist(const W& w)
    {
        dynamic_sequence_construction(sink(this), w);
    }
    void operator=(slist x)
    {
        swap(deref(this), x);
    }
    T& operator[](EOPDistanceType(slist_iterator<T>) i)
    {
        return deref(first + i);
    }
    ~slist()
    {
        erase_all(sink(this));
    }
};

template<typename T>
    requires(Regular(T))
struct iterator_type< slist<T> >
{
    typedef slist_iterator<T> type;
};

template<typename T>
    requires(Regular(T))    
struct value_type< slist<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct size_type< slist<T> >
{
    typedef EOPDistanceType(EOPIteratorType(slist<T>)) type;
};

template<typename T>
    requires(Regular(T))
struct underlying_type< slist<T> >
{
    typedef slist_iterator<T> type; // or EOPIteratorType(slist<T>)
};

template<typename T>
    requires(Regular(T))
EOPIteratorType(slist<T>) begin(const slist<T>& x)
{
    return x.first;
}

template<typename T>
    requires(Regular(T))
EOPIteratorType(slist<T>) end(const slist<T>&)
{
    return slist_iterator<T>();
}

// size, empty subsumed by definitions for Linearizeable

template<typename T>
    requires(Regular(T))
void erase_all(slist<T>& x)
{
    while (!empty(x)) x.first = erase_first(begin(x));
}

template<typename T>
    requires(Regular(T))
bool operator==(const slist<T>& x, const slist<T>& y)
{
    return linearizable_equal(x, y);
}

template<typename T>
    requires(Regular(T))
bool operator<(const slist<T>& x, const slist<T>& y)
{
    return linearizable_ordering(x, y);
}

template<typename T,  typename U>
    requires(Regular(T) && Constructible(T, U))
after< slist<T> > insert(after< slist<T> > p, const U& u)
{
    slist_node_count = successor(slist_node_count);
    slist_iterator<T> i((slist_node<T>*)malloc(sizeof(slist_node<T>)));
    construct(sink(i), u);
    if (current(p) == end(p)) {
        set_link_forward(i, begin(p));
        base(p).first = i;
    } else {
        set_link_forward(i, successor(current(p)));
        set_link_forward(current(p), i);
    }
    return after< slist<T> >(base(p), i);
}

template<typename T>
    requires(Regular(T))
void reverse(slist<T>& x)
{
    typedef EOPIteratorType(slist<T>) I;
    x.first = reverse_append(begin(x), end(x), end(x), forward_linker<I>());
}

template<typename T, typename P>
    requires(Regular(T) && UnaryPredicate(P) && EOPDomain(P) == T)
void partition(slist<T>& x, slist<T>& y, P p)
{
    typedef EOPIteratorType(slist<T>) I;
    pair< pair<I, I>, pair<I, I> > pp =
        partition_linked(begin(x), end(x), p, forward_linker<I>());
    x.first = pp.m0.m0;
    if (pp.m0.m0 != end(x))
        forward_linker<I>()(pp.m0.m1, end(x));
    if (pp.m1.m0 != end(x)) {
        forward_linker<I>()(pp.m1.m1, begin(y));
        y.first = pp.m1.m0;
    }
}

template<typename T, typename R>
    requires(Regular(T) && Regular(R) && EOPDomain(R) == T)
void merge(slist<T>& x, slist<T>& y, R r)
{
    // Precondition: $\func{weak\_ordering}(r)$
    typedef EOPIteratorType(slist<T>) I;
    if (empty(y)) return;
    if (empty(x)) { swap(x, y); return; }
    x.first = merge_linked_nonempty(
                  begin(x), end(x), begin(y), end(y),
                  r, forward_linker<I>()).m0;
    y.first = end(y); // former nodes of y now belong to x
}

template<typename T, typename R>
    requires(Regular(T) && Relation(R) && EOPDomain(R) == T)
void sort(slist<T>& x, R r)
{
    // Precondition: $\func{weak\_ordering}(r)$
    typedef EOPIteratorType(slist<T>) I;
    pair<I, I> p = sort_linked_nonempty_n(begin(x), size(x), r, forward_linker<I>());
    x.first = p.m0;
}


// type list
// model DynamicSequence(list)

template<typename T>
    requires(Regular(T))
struct list_node
{
    T value;
    EOPpointer(list_node) forward_link;
    EOPpointer(list_node) backward_link;
    list_node(
        const T& v,
        EOPpointer(list_node) f, EOPpointer(list_node) b) :
        value(v), forward_link(f), backward_link(b) { }
};

static int list_node_count = 0; /* ***** TESTING ***** */

template<typename T>
    requires(Regular(T))
struct list_iterator
{
    EOPpointer(list_node<T>) p;
    list_iterator() : p(0) { }
    list_iterator(EOPpointer(list_node<T>) p) : p(p) { }
};

template<typename T>
    requires(Regular(T))
struct value_type< list_iterator<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct distance_type< list_iterator<T> >
{
    typedef EOPDistanceType(list_node<T>*) type;
};

template<typename T>
    requires(Regular(T))
struct iterator_concept< list_iterator<T> >
{
    typedef bidirectional_iterator_tag concept;
};

template<typename T>
    requires(Regular(T))
list_iterator<T> successor(const list_iterator<T>& i)
{
    return list_iterator<T>(source(i.p).forward_link);
}

template<typename T>
    requires(Regular(T))
list_iterator<T> predecessor(const list_iterator<T>& i)
{
    return list_iterator<T>(source(i.p).backward_link);
}

template<typename I>
    requires(LinkedBidirectionalIterator<I>)
void set_link_backward(I i, I j)
{
    backward_linker<I>()(i, j);
}

template<typename I>
    requires(LinkedForwardIterator<I>)
void set_link_bidirectional(I i, I j)
{
    bidirectional_linker<I>()(i, j);
}

template<typename T>
    requires(Regular(T))
bool operator==(list_iterator<T> i, list_iterator<T> j)
{
    return i.p == j.p;
}

template<typename T>
    requires(Regular(T))
struct less< list_iterator<T> >
{
    typedef list_iterator<T> input_type_0;
    typedef list_iterator<T> input_type_1;
    typedef bool codomain_type;

    bool operator()(list_iterator<T> i,
                    list_iterator<T> j)
    {
        return i.p < j.p;
    }
};

template<typename T>
    requires(Regular(T))
const T& source(list_iterator<T> i)
{
    return source(i.p).value;
}

template<typename T>
    requires(Regular(T))
T& sink(list_iterator<T> i)
{
    return sink(i.p).value;
}

template<typename T>
    requires(Regular(T))
T& deref(list_iterator<T> i)
{
    return sink(i.p).value;
}

template<typename T>
    requires(Regular(T))
void erase(list_iterator<T> i)
{
    set_link_bidirectional(predecessor(i), successor(i));
    destroy(sink(i));
    free(i.p);
    list_node_count = predecessor(list_node_count);
}

template<typename T,  typename U>
    requires(Regular(T) && Destroyable(T, U))
void erase(list_iterator<T> i, U& u)
{
    set_link_bidirectional(predecessor(i), successor(i));
    destroy(sink(i), u);
    free(i.p);
    list_node_count = predecessor(list_node_count);
}

template<typename T>
    requires(Regular(T))
struct list
{
    list_iterator<T> dummy;
    list() : dummy((list_node<T>*)malloc(sizeof(list_node<T>)))
    {
        // The dummy node's value is never constructed
        set_link_bidirectional(dummy, dummy);
    }
    list(const list& x)
    {
        dynamic_sequence_construction(sink(this), x);
    }
    template<typename W>
        requires(Linearizable(W))
    list(const W& w)
    {
        dynamic_sequence_construction(sink(this), w);
    }
    void operator=(list x)
    {
        swap(deref(this), x);
    }
    T& operator[](EOPDistanceType(list_iterator<T>) i)
    {
        return deref(begin(deref(this)) + i);
    }
    ~list()
    {
        erase_all(sink(this));
        // We do not destroy the dummy node's value since it was not constructed
        free(dummy.p);
    }
};

template<typename T>
    requires(Regular(T))
struct iterator_type< list<T> >
{
    typedef list_iterator<T> type;
};

template<typename T>
    requires(Regular(T))    
struct value_type< list<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct size_type< list<T> >
{
    typedef EOPDistanceType(EOPIteratorType(list<T>)) type;
};

template<typename T>
    requires(Regular(T))
struct underlying_type< list<T> >
{
    typedef list_iterator<T> type; // or EOPIteratorType(list<T>)
};

template<typename T>
    requires(Regular(T))
EOPIteratorType(list<T>) begin(const list<T>& x)
{
    return successor(x.dummy);
}

template<typename T>
    requires(Regular(T))
EOPIteratorType(list<T>) end(const list<T>& x)
{
    return x.dummy;
}

// size, empty subsumed by definitions for Linearizeable

template<typename T>
    requires(Regular(T))
void erase_all(list<T>& x)
{
    while (!empty(x)) erase(predecessor(end(x)));
}

template<typename T>
    requires(Regular(T))
bool operator==(const list<T>& x, const list<T>& y)
{
    return linearizable_equal(x, y);
}

template<typename T>
    requires(Regular(T))
bool operator<(const list<T>& x, const list<T>& y)
{
    return linearizable_ordering(x, y);
}

template<typename T,  typename U>
    requires(Regular(T) && Constructible(T, U))
list_iterator<T> insert(list_iterator<T> j, const U& u)
{
    list_node_count = successor(list_node_count);
    list_iterator<T> i((list_node<T>*)malloc(sizeof(list_node<T>)));
    construct(sink(i), u);
    set_link_bidirectional(predecessor(j), i);
    set_link_bidirectional(i, j);
    return i;
}

template<typename T,  typename U>
    requires(Regular(T) && Constructible(T, U))
after< list<T> > insert(after< list<T> > p, const U& u)
{
    return after< list<T> >(base(p), insert(successor(current(p)), u));
}

template<typename T>
    requires(Regular(T))
void reverse(list<T>& x)
{
    typedef EOPIteratorType(list<T>) I;
    I i = reverse_append(begin(x), end(x), end(x), bidirectional_linker<I>());
    set_link_bidirectional(x.dummy, i);
}

template<typename T, typename P>
    requires(Regular(T) && UnaryPredicate(P) && EOPDomain(P) == T)
void partition(list<T>& x, list<T>& y, P p)
{
    typedef EOPIteratorType(list<T>) I;
    bidirectional_linker<I> set_link;
    pair< pair<I, I>, pair<I, I> > pp =
        partition_linked(begin(x), end(x), p, set_link);
    set_link(pp.m0.m1, x.dummy);
    set_link(x.dummy, pp.m0.m0);
    if (pp.m1.m0 != end(x)) {
        set_link(pp.m1.m1, begin(y));
        set_link(y.dummy, pp.m1.m0);
    }
}

template<typename T, typename R>
    requires(Regular(T) && Regular(R) && EOPDomain(R) == T)
void merge(list<T>& x, list<T>& y, R r)
{
    // Precondition: $\func{weak\_ordering}(r)$
    typedef EOPIteratorType(list<T>) I;
    bidirectional_linker<I> set_link;
    if (empty(y)) return;
    if (empty(x)) { swap(x, y); return; }
    pair<I, I> p = merge_linked_nonempty(
                  begin(x), end(x), begin(y), end(y),
                  r, set_link);
    set_link(x.dummy, p.m0);
    set_link(find_last(p.m0, p.m1), x.dummy);
    set_link(y.dummy, y.dummy); // former nodes of y now belong to x
}

template<typename T, typename R>
    requires(Regular(T) && Relation(R) && EOPDomain(R) == T)
void sort(list<T>& x, R r)
{
    // Precondition: $\func{weak\_ordering}(r)$
    typedef EOPIteratorType(list<T>) I;
    pair<I, I> p = sort_linked_nonempty_n(begin(x), size(x), r, forward_linker<I>());
    // See the end of section 8.3 of Elements of Programming
    // for the explanation of this relinking code:
    bidirectional_linker<I>()(x.dummy, p.m0);
    I f = p.m0;
    while (f != p.m1) {
        backward_linker<I>()(f, successor(f));
        f = successor(f);
    }
}


// concept BinaryTree means ...


// type stree
// model BinaryTree(stree)

template<typename T>
    requires(Regular(T))
struct stree_node
{
    typedef EOPpointer(stree_node) Link;
    T value;
    Link left_successor_link;
    Link right_successor_link;
    stree_node() : left_successor_link(0), right_successor_link(0) { }
    stree_node(T v, Link l = 0, Link r = 0) :
        value(v),
        left_successor_link(l), right_successor_link(r) { }
};

template<typename T>
    requires(Regular(T))
struct stree_coordinate
{
    EOPpointer(stree_node<T>) ptr;
    stree_coordinate() : ptr(0) { }
    stree_coordinate(EOPpointer(stree_node<T>) ptr) : ptr(ptr) { }
};

template<typename T>
    requires(Regular(T))
struct value_type< stree_coordinate<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct weight_type< stree_coordinate<T> >
{
    typedef EOPDistanceType(EOPpointer(stree_node<T>)) type;
};

template<typename T>
    requires(Regular(T))
bool empty(stree_coordinate<T> c)
{
    typedef EOPpointer(stree_node<T>) I;
    return c.ptr == I(0);
}

template<typename T>
    requires(Regular(T))
stree_coordinate<T> left_successor(stree_coordinate<T> c)
{
    return source(c.ptr).left_successor_link;
}

template<typename T>
    requires(Regular(T))
stree_coordinate<T> right_successor(stree_coordinate<T> c)
{
    return source(c.ptr).right_successor_link;
}

template<typename T>
    requires(Regular(T))
bool has_left_successor(stree_coordinate<T> c)
{
    return !empty(left_successor(c));
}

template<typename T>
    requires(Regular(T))
bool has_right_successor(stree_coordinate<T> c)
{
    return !empty(right_successor(c));
}

template<typename T>
    requires(Regular(T))
void set_left_successor(stree_coordinate<T> c, stree_coordinate<T> l)
{
    sink(c.ptr).left_successor_link = l.ptr;
}

template<typename T>
    requires(Regular(T))
void set_right_successor(stree_coordinate<T> c, stree_coordinate<T> r)
{
    sink(c.ptr).right_successor_link = r.ptr;
}

template<typename T>
    requires(Regular(T))
bool operator==(stree_coordinate<T> c0, stree_coordinate<T> c1)
{
    return c0.ptr == c1.ptr;
}

template<typename T>
    requires(Regular(T))
const T& source(stree_coordinate<T> c)
{
    return source(c.ptr).value;
}

template<typename T>
    requires(Regular(T))
T& sink(stree_coordinate<T> c)
{
    return sink(c.ptr).value;
}

static int stree_node_count = 0; /* ***** TESTING ***** */

template<typename T>
    requires(Regular(T))
struct stree_node_construct
{
    typedef stree_coordinate<T> C;
    stree_node_construct() { }
    C operator()(T x, C l = C(0), C r = C(0))
    {
        ++stree_node_count;
        return C(new stree_node<T>(x, l.ptr, r.ptr));
    }
    C operator()(C c)           { return (*this)(source(c), left_successor(c),
                                                            right_successor(c)); }
    C operator()(C c, C l, C r) { return (*this)(source(c), l, r); }
};

template<typename T>
    requires(Regular(T))
struct stree_node_destroy
{
    stree_node_destroy() { }
    void operator()(stree_coordinate<T> i)
    {
        --stree_node_count;
        delete i.ptr;
    }
};

template<typename C, typename ND>
    requires(BifurcateCoordinate(C) && TreeNodeDeleter(ND))
void bifurcate_erase(C c, ND node_delete)
{
    if (empty(c)) return;
    C stack = C(0); // chained through left_successor
    while (true) {
        C left = left_successor(c);
        C right = right_successor(c);
        if (!empty(left)) {
            if (!empty(right)) {
                set_left_successor(c, stack);
                stack = c;
            } else
                node_delete(c);
            c = left;
        } else if (!empty(right)) {
            node_delete(c);
            c = right;
        } else {
            node_delete(c);
            if (!empty(stack)) {
                c = stack;
                stack = left_successor(stack);
                set_left_successor(c, C(0));
           } else return;
        }
    }
}

/*
   The next function is based on MAKECOPY in this paper:

   K. P. Lee.
   A linear algorithm for copying binary trees using bounded workspace.
   Commun. ACM 23, 3 (March 1980), 159-162. DOI=10.1145/358826.358835
   http://doi.acm.org/10.1145/358826.358835
*/

template<typename C, typename Cons>
    requires(EmptyLinkedBifurcateCoordinate(C) &&
        TreeNodeConstructor(Cons) && NodeType(C) == NodeType(Cons))
C bifurcate_copy(C c)
{
    Cons construct_node;
    if (empty(c)) return c;              // Us      / Lee
    C stack = construct_node(c, c, C()); // stack   / V'
    C c_new = stack;                     // c\_new  / COPY
    while (!empty(stack)) {              // empty() / null
        c = left_successor(stack);       // c       / V
        C l = left_successor(c);
        C r = right_successor(c);
        C top = stack;
        if (!empty(l)) {
            if (!empty(r)) {
                r = construct_node(r, r, right_successor(stack));
                stack = construct_node(l, l, r);
            }
            else  {
                r = C();
                stack = construct_node(l, l, right_successor(stack));
            }
            l = stack;
        } else if (!empty(r)) {
            stack = construct_node(r, r, right_successor(stack));
            r = stack;
        } else
            stack = right_successor(stack);
        set_right_successor(top, r);
        set_left_successor(top, l);
    }
    return c_new;
}

template<typename T>
    requires(Regular(T))
struct stree
{
    typedef stree_coordinate<T> C;
    typedef stree_node_construct<T> Cons;
    C root;
    stree() : root(0) { }
    stree(T x) : root(Cons()(x)) { }
    stree(T x, const stree& left, const stree& right) : root(Cons()(x))
    {
        set_left_successor(root, bifurcate_copy<C, Cons>(left.root));
        set_right_successor(root, bifurcate_copy<C, Cons>(right.root));
    }
    stree(const stree& x) : root(bifurcate_copy<C, Cons>(x.root)) { }
    ~stree() { bifurcate_erase(root, stree_node_destroy<T>()); }
    void operator=(stree x) { swap(root, x.root); }
};

template<typename T>
    requires(Regular(T))
struct coordinate_type< stree<T> >
{
    typedef stree_coordinate<T> type;
};

template<typename T>
    requires(Regular(T))
struct value_type< stree<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct weight_type< stree<T> >
{
    typedef EOPWeightType(CoordinateType(stree<T>)) type;
};

template<typename T>
    requires(Regular(T))
stree_coordinate<T> begin(const stree<T>& x) { return x.root; }

template<typename T>
    requires(Regular(T))
bool empty(const stree<T>& x) { return empty(x.root); }

template<typename T>
    requires(Regular(T))
bool operator==(const stree<T>& x, const stree<T>& y)
{
    if (empty(x)) return empty(y);
    if (empty(y)) return false;
    return bifurcate_equivalent_nonempty(begin(x), begin(y), equal<T>());
}

template<typename T>
    requires(Regular(T))
bool operator<(const stree<T>& x, const stree<T>& y)
{
    if (empty(x)) return !empty(y);
    if (empty(y)) return false;
    less<T> lt;
    return 1 == bifurcate_compare_nonempty(
        begin(x), begin(y),
        make_comparator_3_way(lt));
}

template<typename T, typename Proc>
    requires(Regular(T) &&
        Procedure(Proc) && Arity(Proc) == 2 &&
        visit == EOPInputType(Proc, 0) &&
        CoordinateType(stree<T>) == EOPInputType(Proc, 1))
void traverse(stree<T>& x, Proc proc)
{
    traverse_nonempty(begin(x), proc);
}


// type tree
// model BinaryTree(tree)

template<typename T>
    requires(Regular(T))
struct tree_node
{
    typedef EOPpointer(tree_node) Link;
    T value;
    Link left_successor_link;
    Link right_successor_link;
    Link predecessor_link;
    tree_node() :
        left_successor_link(0), right_successor_link(0),
        predecessor_link(0) { }
    tree_node(T v, Link l = 0, Link r = 0, Link p = 0) :
        value(v),
        left_successor_link(l), right_successor_link(r),
        predecessor_link(p) { }
};

template<typename T>
    requires(Regular(T))
struct tree_coordinate
{
    EOPpointer(tree_node<T>) ptr;
    tree_coordinate() : ptr(0) { }
    tree_coordinate(EOPpointer(tree_node<T>) ptr) : ptr(ptr) { }
};

template<typename T>
    requires(Regular(T))
struct value_type< tree_coordinate<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct weight_type< tree_coordinate<T> >
{
    typedef EOPDistanceType(EOPpointer(tree_node<T>)) type;
};

template<typename T>
    requires(Regular(T))
bool empty(tree_coordinate<T> c)
{
    return c.ptr == 0;
}

template<typename T>
    requires(Regular(T))
tree_coordinate<T> left_successor(tree_coordinate<T> c)
{
    return source(c.ptr).left_successor_link;
}

template<typename T>
    requires(Regular(T))
tree_coordinate<T> right_successor(tree_coordinate<T> c)
{
    return source(c.ptr).right_successor_link;
}

template<typename T>
    requires(Regular(T))
bool has_left_successor(tree_coordinate<T> c)
{
    return !empty(left_successor(c));
}

template<typename T>
    requires(Regular(T))
bool has_right_successor(tree_coordinate<T> c)
{
    return !empty(right_successor(c));
}

template<typename T>
    requires(Regular(T))
tree_coordinate<T> predecessor(tree_coordinate<T> c)
{
    return source(c.ptr).predecessor_link;
}

template<typename T>
    requires(Regular(T))
bool has_predecessor(tree_coordinate<T> c)
{
    return !empty(predecessor(c));
}

template<typename T>
    requires(Regular(T))
void set_predecessor(tree_coordinate<T> c, tree_coordinate<T> p)
{
    sink(c.ptr).predecessor_link = p.ptr;
}

template<typename T>
    requires(Regular(T))
void set_left_successor(tree_coordinate<T> c, tree_coordinate<T> l)
{
    sink(c.ptr).left_successor_link = l.ptr;
    if (!empty(l)) set_predecessor(l, c);
}

template<typename T>
    requires(Regular(T))
void set_right_successor(tree_coordinate<T> c, tree_coordinate<T> r)
{
    sink(c.ptr).right_successor_link = r.ptr;
    if (!empty(r)) set_predecessor(r, c);
}

template<typename T>
    requires(Regular(T))
bool operator==(tree_coordinate<T> c0, tree_coordinate<T> c1)
{
    return c0.ptr == c1.ptr;
}

template<typename T>
    requires(Regular(T))
const T& source(tree_coordinate<T> c)
{
    return source(c.ptr).value;
}

template<typename T>
    requires(Regular(T))
T& sink(tree_coordinate<T> c)
{
    return sink(c.ptr).value;
}

static int tree_node_count = 0; /* ***** TESTING ***** */

template<typename T>
    requires(Regular(T))
struct tree_node_construct
{
    typedef tree_coordinate<T> C;
    tree_node_construct() { }
    C operator()(T x, C l = C(0), C r = C(0))
    {
        ++tree_node_count;
        return C(new tree_node<T>(x, l.ptr, r.ptr));
    }
    C operator()(C c)           { return (*this)(source(c), left_successor(c),
                                                            right_successor(c)); }
    C operator()(C c, C l, C r) { return (*this)(source(c), l, r); }
};

template<typename T>
    requires(Regular(T))
struct tree_node_destroy
{
    tree_node_destroy() { }
    void operator()(tree_coordinate<T> i)
    {
        --tree_node_count;
        delete i.ptr;
    }
};

template<typename T>
    requires(Regular(T))
struct tree
{
    typedef tree_coordinate<T> C;
    typedef tree_node_construct<T> Cons;
    C root;
    tree() : root(0) { }
    tree(T x) : root(Cons()(x)) { }
    tree(T x, const tree& left, const tree& right) : root(Cons()(x))
    {
        set_left_successor(root, bifurcate_copy<C, Cons>(left.root));
        set_right_successor(root, bifurcate_copy<C, Cons>(right.root));
    }
    tree(const tree& x) : root(bifurcate_copy<C, Cons>(x.root)) { }
    ~tree()
    {
        bifurcate_erase(root, tree_node_destroy<T>());
    }
    void operator=(tree x)
    {
        swap(root, x.root);
    }
};

template<typename T>
    requires(Regular(T))
struct coordinate_type< tree<T> >
{
    typedef tree_coordinate<T> type;
};

template<typename T>
    requires(Regular(T))
struct value_type< tree<T> >
{
    typedef EOPValueType(CoordinateType(tree<T>)) type;
};

template<typename T>
    requires(Regular(T))
struct weight_type< tree<T> >
{
    typedef EOPWeightType(CoordinateType(tree<T>)) type;
};

template<typename T>
    requires(Regular(T))
tree_coordinate<T> begin(const tree<T>& x)
{
    return x.root;
}

template<typename T>
    requires(Regular(T))
bool empty(const tree<T>& x)
{
    return empty(x.root);
}

template<typename T>
    requires(Regular(T))
bool operator==(const tree<T>& x, const tree<T>& y)
{
    return bifurcate_equal(begin(x), begin(y));
}

template<typename T>
    requires(Regular(T))
bool operator<(const tree<T>& x, const tree<T>& y)
{
    return bifurcate_less(begin(x), begin(y));
}

template<typename T, typename Proc>
    requires(Regular(T) &&
        Procedure(Proc) && Arity(Proc) == 2 &&
        visit == EOPInputType(Proc, 0) &&
        CoordinateType(tree<T>) == EOPInputType(Proc, 1))
void traverse(tree<T>& x, Proc proc)
{
    traverse(begin(x), proc);
}


// type array
// model DynamicSequence(array)

template<typename T>
    requires(Regular(T))
struct array_prefix
{
    EOPpointer(T) m;
    EOPpointer(T) l;
    T  a;
    // Invariant: $[addressof(a), m)$ are constructed elements
    // Invariant: $[m, l)$ are unconstructed (reserve) elements
};

template<typename T>
    requires(Regular(T))
EOPpointer(array_prefix<T>) allocate_array(EOPDistanceType(T*) n)
{
    typedef EOPpointer(array_prefix<T>) P;
    if (zero(n)) return P(0);
    int bsize = int(predecessor(n)) * sizeof(T);
    P p = P(malloc(sizeof(array_prefix<T>) + bsize));
    EOPpointer(T) f = &sink(p).a;
    sink(p).m = f;
    sink(p).l = f + n;
    return p;
}

template<typename T>
    requires(Regular(T))
void deallocate_array(EOPpointer(array_prefix<T>) p)
{
    free(p);
}

template<typename T>
    requires(Regular(T))
struct array
{
    typedef EOPDistanceType(EOPIteratorType(array<T>)) N;
    EOPpointer(array_prefix<T>) p;
    array() : p(0) { }
    array(N c) : p(allocate_array<T>(c)) { } // size is 0 and capacity is c
    array(N s, N c, const T& x)
        : p(allocate_array<T>(c)) // size is s, capacity is c, all elements equal to x
    {
        while (!zero(s)) { push(sink(this), x); s = predecessor(s); }
    }
    array(const array& x) : p(allocate_array<T>(size(x)))
    {
        insert_range(back< array<T> >(sink(this)), x);
    }
    template<typename W>
        requires(Linearizable(W) && T == EOPValueType(W))
    array(const W& w) : p(allocate_array<T>(0))
    {
        insert_range(back< array<T> >(sink(this)), w);
    }
    template<typename I>
        requires(Readable(I) && Iterator(I) && T == EOPValueType(I))
    array(const counted_range<I>& w) : p(allocate_array<T>(size(w)))
    {
        insert_range(back< array<T> >(sink(this)), w);
    }
    void operator=(array x)
    {
        swap(deref(this), x);
    }
    T& operator[](N i)
    {
        return deref(begin(deref(this)) + i);
    }
    const T& operator[](N i) const
    {
        return deref(begin(deref(this)) + i);
    }
    ~array()
    {
        erase_all(sink(this));
    }
};

template<typename T>
    requires(Regular(T))
struct iterator_type< array<T> >
{
    typedef EOPpointer(T) type;
};

template<typename T>
    requires(Regular(T))
struct value_type< array<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct size_type< array<T> >
{
    typedef EOPDistanceType(EOPIteratorType(array<T>)) type;
};

template<typename T>
    requires(Regular(T))
struct underlying_type< array<T> >
{
    typedef struct { EOPpointer(array_prefix<T>) p; } type;
};

template<typename T>
    requires(Regular(T))
EOPIteratorType(array<T>) begin(const array<T>& x)
{
    typedef EOPpointer(array_prefix<T>) P;
    typedef EOPIteratorType(array<T>) I;
    if (x.p == P(0)) return I(0);
    return I(addressof(source(x.p).a));
}

template<typename T>
    requires(Regular(T))
EOPIteratorType(array<T>) end(const array<T>& x)
{
    typedef EOPpointer(array_prefix<T>) P;
    typedef EOPIteratorType(array<T>) I;
    if (x.p == P(0)) return I(0);
    return I(source(x.p).m);
}

template<typename T>
    requires(Regular(T))
EOPIteratorType(array<T>) end_of_storage(const array<T>& x)
{
    typedef EOPpointer(array_prefix<T>) P;
    typedef EOPIteratorType(array<T>) I;
    if (x.p == P(0)) return I(0);
    return I(source(x.p).l);
}

template<typename T>
    requires(Regular(T))
EOPDistanceType(EOPIteratorType(array<T>)) capacity(const array<T>& x)
{
    return end_of_storage(x) - begin(x);
}

template<typename T>
    requires(Regular(T))
bool full(const array<T>& x)
{
    return end(x) == end_of_storage(x);
}

template<typename T>
    requires(Regular(T))
bool operator==(const array<T>& x, const array<T>& y)
{
    return linearizable_equal(x, y);
}

template<typename T>
    requires(Regular(T))
bool operator<(const array<T>& x, const array<T>& y)
{
    return linearizable_ordering(x, y);
}

template<typename T, typename U>
    requires(Regular(T) && Regular(U) && Constructible(T, U))
back< array<T> > insert(back< array<T> > p, const U& y)
{
    typedef EOPDistanceType(EOPIteratorType(array<T>)) N;
    N n = size(base(p));
    if (n == capacity(base(p)))
        reserve(base(p), max(N(1), n + n));
    construct(sink(source(base(p).p).m), y);
    sink(base(p).p).m = successor(sink(base(p).p).m);
    return p;
}

template<typename T, typename W>
    requires(Regular(T) &&
        Linearizable(W) && Constructible(T, EOPValueType(W)))
before< array<T> > insert_range(before< array<T> > p, const W& w)
{
    typedef EOPIteratorType(array<T>) I;
    EOPDistanceType(I) o_f = current(p) - begin(p);
    EOPDistanceType(I) o_m = size(p);
    insert_range(back< array<T> >(base(p)), w);
    return before< array<T> >(base(p), rotate(begin(p) + o_f, begin(p) + o_m, end(p)));
}
// Note that for iterators supporting fast subtraction,
// we could write a somewhat faster but also much more complex
// version (complexity mostly dealing with exception safety)

template<typename T>
    requires(Regular(T))
back< array<T> > erase(back< array<T> > x)
{
    --sink(deref(x.s).p).m;
    destroy(sink(source(deref(x.s).p).m));
    if (empty(deref(x.s))) {
        deallocate_array(deref(x.s).p);
        deref(x.s).p = 0;
    }
    return x;
}

template<typename T>
    requires(Regular(T))
void erase_all(array<T>& x)
{
    while (!empty(x)) erase(back< array<T> >(x));
}

template<typename T>
    requires(Regular(T))
inline void swap_basic(T& x, T& y)
{
    T tmp = x;
    x = y;
    y = tmp;
}

template<typename T>
    requires(Regular(T))
inline UnderlyingType(T)& underlying_ref(T& x)
{
    return reinterpret_cast<UnderlyingType(T)&>(x);
}

template<typename T>
    requires(Regular(T))
inline const UnderlyingType(T)& underlying_ref(const T& x)
{
    return reinterpret_cast<const UnderlyingType(T)&>(x);
}

template<typename T>
    requires(Regular(T))
inline void swap(T& x, T& y)
{
    swap_basic(underlying_ref(x), underlying_ref(y));
}

template<typename T>
    requires(Regular(T))
inline void rotate_right(T& x, T& y, T& z)
{
    UnderlyingType(T) tmp = underlying_ref(z);
    underlying_ref(z)     = underlying_ref(y);
    underlying_ref(y)     = underlying_ref(x);
    underlying_ref(x)     = tmp;
}

template<typename T>
    requires(Regular(T))
inline void rotate_left(T& x, T& y, T& z)
{
    UnderlyingType(T) tmp = underlying_ref(x);
    underlying_ref(x)     = underlying_ref(y);
    underlying_ref(y)     = underlying_ref(z);
    underlying_ref(z)     = tmp;
}

// Exercise 12.9:

template<typename I>
  requires(Iterator(I))   
struct underlying_iterator
{
    I i;
};

template<typename I>
  requires(Iterator(I))   
inline underlying_iterator<I> make_underlying_iterator(const I& i)
{
    underlying_iterator<I> tmp = {i};
    return tmp ;
}

template<typename I>
    requires(Iterator(I))
struct value_type< underlying_iterator<I> >
{
    typedef UnderlyingType(EOPValueType(I)) type;
};

template<typename I>
    requires(Iterator(I))
struct distance_type< underlying_iterator<I> >
{
    typedef EOPDistanceType(I) type;
};

template<typename I>
    requires(Iterator(I))
struct iterator_concept< underlying_iterator<I> >
{
    typedef EOPIteratorConcept(I) concept;
};

template<typename I>
    requires(Iterator(I))
underlying_iterator<I> successor(const underlying_iterator<I>& x)
{
  return make_underlying_iterator(successor(x.i));
}

template<typename I>
    requires(Iterator(I))
underlying_iterator<I> predecessor(const underlying_iterator<I>& x)
{
  return make_underlying_iterator(predecessor(x.i));
}

template<typename I>
    requires(Iterator(I))
underlying_iterator<I> operator+(underlying_iterator<I> x, EOPDistanceType(I) n)
{
    return make_underlying_iterator(x.i + n);
}

template<typename I>
    requires(Iterator(I))
EOPDistanceType(I) operator-(underlying_iterator<I> x, underlying_iterator<I> y)
{
    return x.i - y.i;
}

template<typename I>
    requires(Iterator(I))
underlying_iterator<I> operator-(underlying_iterator<I> x, EOPDistanceType(I) n)
{
    return make_underlying_iterator(x.i - n);
}

template<typename I>
    requires(Iterator(I))
bool operator==(const underlying_iterator<I>& x, const underlying_iterator<I>& y)
{
    return x.i == y.i;
}

template<typename I>
    requires(Iterator(I))
bool operator<(const underlying_iterator<I>& x, const underlying_iterator<I>& y)
{
    return x.i < y.i;
}

template<typename I>
    requires(Iterator(I))
const UnderlyingType(EOPValueType(I))& source(const underlying_iterator<I>& x)
{
  return underlying_ref(source(x.i));
}

template<typename I>
    requires(Iterator(I))
UnderlyingType(EOPValueType(I))& sink(underlying_iterator<I>& x)
{
  return underlying_ref(sink(x.i));
}

template<typename i>
    requires(Iterator(i))
UnderlyingType(EOPValueType(i))& deref(underlying_iterator<i>& x)
{
  return underlying_ref(deref(x.i));
}

template<typename I>
    requires(Iterator(I))
I original(const underlying_iterator<I>& x)
{
    return x.i;
}


// Project 12.5: here are some more techniques and examples:

template<typename T>
    requires(Regular(T))
void reserve_basic(array<T>& x,
                   EOPDistanceType(EOPIteratorType(array<T>)) n)
{
    if (n < size(x) || n == capacity(x)) return;
    array<T> tmp(n);
    insert_range(back< array<T> >(tmp), x);
    swap(tmp, x);
}

template<typename T>
    requires(Regular(T))
void reserve(array<T>& x, EOPDistanceType(EOPIteratorType(array<T>)) n)
{
    reserve_basic(reinterpret_cast<array<UnderlyingType(T)>&>(x), n);
}


// In order to adapt algorithms with predicates and relations as
// arguments, we use adapters that cast from the underlying type to the
// original type before calling the predicate or relation:

template<typename T>
    requires(Regular(T))
T& original_ref(UnderlyingType(T)& x)
{
    return reinterpret_cast<T&>(x);
}

template<typename T>
    requires(Regular(T))
const T& original_ref(const UnderlyingType(T)& x)
{
    return reinterpret_cast<const T&>(x);
}

template<typename P>
    requires(Predicate(P))
struct underlying_predicate
{
    typedef EOPDomain(P) T;
    typedef UnderlyingType(T) U;
    typedef U input_type_0;
    typedef bool codomain_type;

    P p;
    bool operator()(U const& x)
    {
        return p(original_ref<T>(x));
    }
};

template<typename P>
    requires(Predicate(P))
inline underlying_predicate<P> make_underlying_predicate(const P& p)
{
    underlying_predicate<P> tmp = {p};
    return tmp;
}

template<typename R>
    requires(Relation(R))
struct underlying_relation
{
    typedef EOPDomain(R) T;
    typedef UnderlyingType(T) U;
    typedef U input_type_0;
    typedef U input_type_1;
    typedef bool codomain_type;

    R r;
    bool operator()(U const& x, U const& y)
    {
        return r(original_ref<T>(x), original_ref<T>(y));
    }
};

template<typename R>
    requires(Relation(R))
inline underlying_relation<R> make_underlying_relation(const R& r)
{
    underlying_relation<R> tmp = {r};
    return tmp;
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && EOPValueType(I) == EOPDomain(P))
pair<I, I> advanced_partition_stable_n(I f, EOPDistanceType(I) n, P p)
{
    typedef underlying_iterator<I> U;
    pair<U, U> tmp = partition_stable_n(make_underlying_iterator(f), n,
                                        make_underlying_predicate(p));
    return make_pair(original(tmp.m0), original(tmp.m1));
}

template<typename I, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Relation(R) && EOPValueType(I) == EOPDomain(R))
I advanced_sort_n(I f, EOPDistanceType(I) n, R r)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    temporary_buffer<UnderlyingType(EOPValueType(I))> b(half_nonnegative(n));
    return original(sort_n_adaptive(make_underlying_iterator(f), n,
                                    begin(b), size(b),
                                    make_underlying_relation(r)));
}

template<typename T, typename R>
    requires(Regular(T) && Relation(R) && EOPDomain(R) == T)
void sort(array<T>& x, R r)
{
    // Precondition: $\func{weak\_ordering}(r)$
    advanced_sort_n(begin(x), size(x), r);
}

#endif // EOP_EOP
