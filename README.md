# dependent-type-search

A semi-algorithm for unification modulo βηδ-conversion and the following type isomorphisms:

```math
\begin{align*}
A \times B &\cong B \times A &&& (\Sigma\text{-swap}) \\
\Sigma x : (\Sigma y : A. B). C &\cong \Sigma x: A. (\Sigma y: B[y\mapsto x]. C[x\mapsto (x, y)]) &&& (\Sigma\text{-assoc}) \\
\Pi x : (\Sigma y : A. B). C &\cong \Pi x: A. (\Pi y: B[y\mapsto x]. C[x\mapsto (x, y)]) &&& (\text{curry}) \\
\Pi x : A. (\Pi y : B. C) &\cong \Pi y : B. (\Pi x : A. C) & \text{if } x \notin \mathrm{FV}(B) \land y \notin \mathrm{FV}(A) && (\Pi\text{-swap}) \\
A \times \mathrm{Unit} &\cong A &&& (\Sigma\text{-unit-right}) \\
\Sigma x : \mathrm{Unit}. A &\cong A[x\mapsto \mathrm{tt}] &&& (\Sigma\text{-unit-left}) \\
\Pi x : \mathrm{Unit}. A &\cong A[x\mapsto \mathrm{tt}] &&& (\Pi\text{-unit-left}) \\
(x =_A y) &\cong (y =_A x) &&& (\text{Eq-swap}) \\
\end{align*}
```

## Usage

This repository contains a prototypical implementation of a type-based library search tool using the semi-algorithm.

To search within modules in the [`lib`](/lib) directory, run:

```shell
stack run -- lib/
```

You search with a query type, then the tool will show you components of the library that match the query type.

```haskell
> (m : Nat) -> Eq Nat (add 42 m) (add m 42)
Natural.add-comm : Equality.Commutativity Nat add
  instantiation: {x ↦ 42, y ↦ m}
```

You can turn on and off whether to search up to generalisation or search modulo the type isomorphisms.

```haskell
> :set no-generalise
> (m : Nat) -> Eq Nat (add 42 m) (add m 42)
> :set generalise
> (A : Type) -> (A * A -> A) -> List A -> A -> A
List.foldr : (A : Type) (B : Type) → (A → B → B) → B → List A → B
  instantiation: {A ↦ A, B ↦ A}

> :set no-modulo-iso
> (A : Type) -> (A * A -> A) -> List A -> A -> A
```

You can include (parametrised) metavariables in the query type.

```haskell
> :set modulo-iso
> (m : Nat) -> Eq Nat (?F m ?E) m
Natural.add-id-l : Equality.LeftIdentity Nat add 0
  instantiation: {x ↦ m}
  substitution: {?F ↦ λ x x'. x}

Natural.add-id-r : Equality.RightIdentity Nat add 0
  instantiation: {x ↦ m}
  substitution: {?E ↦ 0, ?F ↦ add}

Natural.mul-id-l : Equality.LeftIdentity Nat mul 1
  instantiation: {x ↦ m}
  substitution: {?E ↦ 0, ?F ↦ λ x. add x}

Natural.mul-id-r : Equality.RightIdentity Nat mul 1
  instantiation: {x ↦ m}
  substitution: {?E ↦ 1, ?F ↦ mul}
```

The syntax for the query type is the following:

```text
t, u, A, B ::= x                            variable or constant
             | ?M[t1, ..., tn]              metavariable application
             | Type                         type
             | (x : A) -> B                 dependent function type
             | A -> B                       non-dependent function type
             | \x. t                        lambda abstraction
             | (x, y)                       pair
             | (x : A) * B                  dependent pair
             | A * B                        non-dependent pair
             | t.1                          first projection
             | t.2                          second projection
             | Unit                         unit type
             | tt                           unit value
             | Nat                          natural numbers
             | zero                         zero
             | suc t                        successor
             | natElim tp ts tz tn          natural number eliminator
             | Eq A t u                     equality type
             | refl A t                     reflexivity for the equality type
             | eqElim ta tx tb tr ty teq    eliminator for the equality type
```
