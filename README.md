---
author: Chun Tian
---

# cl-lockfree

A portable library of lock-free data structures in Common Lisp

## Lock-free data structures

- `constant-queue`: double-ended queue with thread-safe `O(1)`
  operations (can also be used as stack)
- `skip-list`: hashtable-like lookup data structure with
  thread-safe `O(1)` operations.

## Supported platforms

- Clozure CL
- LispWorks
- SBCL
