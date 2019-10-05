# CSL with Program Abstractions
This repository hosts soundness proofs for CSL, extended with program abstractions.
The program logic has proof rules for verifying whether a program adheres to an abstract model.
Process algebra terms are used as the abstract models.
The program logic can be used to reason about concurrent and distributed, possibly non-terminating, software.
The soundness proof is mechanised in the Coq proof assistant (version 8.6).

## Structure
- **Statics.v** defines the syntax of the programming language we use to formalise the approach on, together with related operations, e.g. substitution, free variables, etc.
- **Dynamics.v** defines the denotational semantics of expressions and the operational semantics of language commands.
- **Assertions.v** defines the syntax and semantics of the assertion language of our program logic. Also contains substitution, logical entailment and soundness of the laws of bunched implications.
- **Process.v** defines a theory on process algebras with data. This file contains a syntax and operational semantics for process algebras, a definition of bisimulation, a proof that bisimulation is a congruence, and a soundness proof for our axiomatisation.
- **Permissions.v** contains lemmas and theories on fractional permissions, process permissions, and other related variants.
- **Heap.v** contains definitions and theories on heaps, heap masks, and permission heaps.
- **ProcessMap.v** contains definitions and theories regarding process maps, process masks, and permission process maps.
- **Soundness.v** defines the meaning of Hoare triples and contains the actual soundness proof.

