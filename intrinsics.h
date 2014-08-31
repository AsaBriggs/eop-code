// intrinsics.h

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


// Implementations from Appendix B.2 of
// Elements of Programming
// by Alexander Stepanov and Paul McJones
// Addison-Wesley Professional, 2009


#ifndef EOP_INTRINSICS
#define EOP_INTRINSICS


#include <new> // placement operator new

#include "type_functions.h"

// In-place construction and destruction (not in Appendix B.2)

namespace impl {

template<typename T>
    requires(Regular(T))
inline void construct(T& p, true_type)
{
    // Precondition: $p$ refers to raw memory, not an object
    // Postcondition: $p$ is in a default-constructed state
    new (&p) T();
}

template<typename T>
    requires(Regular(T))
inline void construct(T& p, false_type)
{}

template<typename T, typename U>
    requires(Regular(T) && Constructible(T, U))
inline void construct(T& p, const U& initializer)
{
    // Precondition: $p$ refers to raw memory, not an object
    // Postcondition: Default makes $p = initializer$
    // Override $\func{construct}$ to specialize construction of a part of a 
    new (&p) T(initializer);
}    

template<typename T, typename U, ptrdiff_t N>
    requires(Regular(T) && Constructible(T, U))
inline void construct(T (&p)[N], const U& initializer)
{
    // Precondition: $p$ refers to raw memory, not an object
    // Postcondition: Default makes $p = initializer$
    // Override $\func{construct}$ to specialize construction of a part of a 
    ptrdiff_t x = N;
    T* ptr = &p[0];
    while (x > 0) {
        new (ptr) T(initializer);
        ++ptr;
        --x;
    }
}    

template<typename T, typename U>
    requires(Regular(T) && Constructible(T, U))
inline void construct(T& p, const U& initializer, false_type)
{}

template<typename T>
    requires(Regular(T))
inline void destroy(T& p, true_type)
{
    // Precondition: $p$ is in a partially-formed state
    // Postcondition: $p$ refers to raw memory, not an object
    p.~T();
}

template<typename T, ptrdiff_t N>
    requires(Regular(T))
inline void destroy(T (&p)[N], true_type)
{
    // Precondition: $p$ is in a partially-formed state
    // Postcondition: $p$ refers to raw memory, not an object
    ptrdiff_t x = N;
    T* ptr = &p[0];
    while (x > 0) {
        ptr->~T();
        ++ptr;
        --x;
    }
}

template<typename T>
    requires(Regular(T))
inline void destroy(T& p, false_type)
{}

template<typename T, typename U>
    requires(Regular(T))
inline void destroy(T& p, U& finalizer, true_type)
{
    // Precondition: $p$ is in a partially-formed state
    // Postcondition: $p$ refers to raw memory, not an object
    // Override $\func{destroy}$ to specialize destruction of a part of a container
    destroy(p);
}

template<typename T, typename U>
    requires(Regular(T))
inline void destroy(T& p, U& finalizer, false_type)
{}

} // namespace impl

template<typename T>
    requires(Regular(T))
inline void construct(T& p)
{
    impl::construct(p, EOPNeedsConstruction(T)());
}

template<typename T, typename U>
    requires(Regular(T) && Constructible(T, U))
inline void construct(T& p, const U& initializer)
{
    impl::construct(p, initializer);
}    

template<typename T>
    requires(Regular(T))
inline void destroy(T& p)
{
    impl::destroy(p, EOPNeedsDestruction(T)());
}

template<typename T, typename U>
    requires(Regular(T))
inline void destroy(T& p, U& finalizer)
{
    impl::destroy(p, finalizer, EOPNeedsDestruction(T)());
}

#endif // EOP_INTRINSICS

