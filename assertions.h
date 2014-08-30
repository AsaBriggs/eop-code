// assertions.h

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


// Run-time assertion for regression tests that works in release or debug build
// Elements of Programming
// by Alexander Stepanov and Paul McJones
// Addison-Wesley Professional, 2009


#ifndef EOP_ASSERTIONS
#define EOP_ASSERTIONS


#include <cassert> // assert
#include <cstdio> // fprintf, stderr
#include <cstdlib> // abort

#define EOPAssert( test ) do { \
  assert ( (test) ) ; \
  if ( !(test) ) { \
      fprintf(stderr, "Assert failed\n"); \
      fprintf(stderr, "%s", #test); \
      abort(); \
  } \
} while (0)

#endif // EOP_ASSERTIONS
