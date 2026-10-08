# Algebraic Automata in Lean 4

[![CI](https://github.com/ReemMelamed/algebraic-automata/actions/workflows/ci.yml/badge.svg)](https://github.com/ReemMelamed/algebraic-automata/actions/workflows/ci.yml)
[![Docs](https://img.shields.io/badge/docs-GitHub_Pages-blue.svg)](https://reemmelamed.github.io/algebraic-automata/)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.35.0--rc3-blue.svg)](https://lean-lang.org/)
[![Mathlib 4](https://img.shields.io/badge/powered_by-Mathlib4-purple.svg)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-Apache_2.0-green.svg)](LICENSE)

A formalization of finite semigroup theory, Green's relations, and Simon's Factorization Forest Theorem in Lean 4.

## Overview

In theoretical computer science and formal language theory, algebraic techniques analyze computations and regular behaviors via the structure of finite semigroups. A central combinatorial foundation is **Simon's Factorization Forest Theorem** (1990), an algebraic analogue of Ramsey's Theorem: every word evaluated in a finite semigroup $S$ admits an unranked factorization tree of bounded height ($3N(S) - 1 \le 3\vert{}S\vert{} - 1$) whose wide nodes evaluate to idempotents.

This repository provides a machine-checked, self-contained formalization in Lean 4 of the algebraic structure of finite semigroups, Simon's Factorization Forest Theorem (via Ramsey splits), infinitary extensions, and algebraic applications.

## Verification Status

All proofs in this repository are machine-checked in Lean 4 without custom axioms or `sorry` (`#print axioms` depends strictly on standard foundational axioms: `propext`, `Classical.choice`, and `Quot.sound`).

## Project Structure & Formalized Content

### 1. Green's Relations & Finite Semigroup Structure (`AlgebraicAutomata/GreensRelations/`)
- **Green's Relations** (`Basic.lean`): Definitions of Green's preorders and equivalence relations ($\mathcal{L}, \mathcal{R}, \mathcal{H}, \mathcal{D}, \mathcal{J}$), quotient spaces, and semigroup duality with opposite semigroups.
- **Multiplication Sequences** (`MulSeq.lean`): Tools for analyzing finite semigroups via iterated multiplication sequences, pigeonhole arguments, and idempotent existence.
- **Green's Lemma** (`Green.lean`): Invertible maps between $\mathcal{H}$-classes within the same $\mathcal{D}$-class, and characterizations of regular $\mathcal{D}$-classes.
- **Finite Semigroup Properties** (`Finite.lean`): Proof that $\mathcal{D} = \mathcal{J}$ in finite semigroups, group structure on $\mathcal{H}$-classes containing idempotents, and Lemma 5.3 on right-multiplication.
- **Partial Orders** (`Order.lean`): Partial order structures induced by Green's relations on quotient classes.

### 2. Factorization Forests & Ramsey Theory (`AlgebraicAutomata/FactorizationForest/`)
- **Multiplicative Labelings & Splits** (`Basic.lean`): Definitions of multiplicative labelings, split functions, normalized splits, and Ramsey splits.
- **Split Combination** (`Combine.lean`): Inductive machinery combining Ramsey splits across subintervals and the Simon complexity bound $nS(S)$.
- **Induction on $\mathcal{J}$-Classes** (`Regular.lean`, `Irregular.lean`): Split constructions for regular and irregular $\mathcal{D}$-classes.
- **Simon's Split Theorem** (`Split.lean`): Proof of Simon's Split Theorem (`simon_split`) and its specialization to words (`simon_word`).
- **Factorization Trees & Height Bound** (`Tree.lean`): Full proof of Simon's Factorization Forest Theorem (`factorization_forest_theorem`) bounding tree height by $3N(S) - 1$ and $3\vert{}S\vert{} - 1$, and tree-to-split extraction.
- **Infinitary Factorization Forests** (`Infinitary.lean`): Extension of Simon's Theorem over the infinite linear order $\langle \mathbb{N}, < \rangle$ formalized via topological compactness in Cantor space.

### 3. Applications & Optimality (`AlgebraicAutomata/Applications/`)
- **Locally Finite Semigroups** (`LocallyFinite.lean`): Colcombet's set-family fixed-point theorems and Brown's Lemma proving the local finiteness of semigroups via idempotent fibers.
- **Sub-linear Heights via Truncated Addition** (`TruncatedAddition.lean`): Formalization of the truncated addition semigroup $\{1, \dots, n\}$ demonstrating sub-linear height trees ($\le \lceil \log_2 n \rceil + 2$), proving that Simon's bound is not tight in general.
- **Aperiodicity & Tightness** (`Aperiodic.lean`): Characterization of aperiodic semigroups via trivial $\mathcal{H}$-classes, and proof of tightness ($2n - 1$ lower bound for $\langle \text{Fin } n, \max \rangle$).

### 4. Mathlib Extensions (`AlgebraicAutomata/ForMathlib/`)
- Upstream-ready utilities for semigroup products of non-empty lists (`SemigroupProd.lean`), list slice operations (`Slice.lean`), and finiteness of opposite structures (`Opposite.lean`).

## References

* Colcombet, T. - *The Factorisation Forest Theorem* (Handbook of Automata Theory, 2021)
* Simon, I. - *Factorization forests of finite height* (Theoretical Computer Science, 1990)
* Brown, T. C. - *An interesting combinatorial method in the theory of locally finite semigroups* (Pacific J. Math., 1971)
