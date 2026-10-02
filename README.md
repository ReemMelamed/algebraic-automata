# Algebraic Automata in Lean 4

[![CI](https://github.com/ReemMelamed/algebraic-automata/actions/workflows/ci.yml/badge.svg)](https://github.com/ReemMelamed/algebraic-automata/actions/workflows/ci.yml)
[![Docs](https://img.shields.io/badge/docs-GitHub_Pages-blue.svg)](https://reemmelamed.github.io/algebraic-automata/)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.35.0--rc3-blue.svg)](https://lean-lang.org/)
[![Mathlib 4](https://img.shields.io/badge/powered_by-Mathlib4-purple.svg)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-Apache_2.0-green.svg)](LICENSE)

A formalization of finite semigroup theory, Simon's Factorization Forest Theorem, and Colcombet's deterministic forward Ramsey transducers in Lean 4.

## Overview

In theoretical computer science and formal language theory, algebraic techniques analyze computations via the structure of finite semigroups. A central combinatorial foundation is **Simon's Factorization Forest Theorem** (1990), a non-commutative structural analogue of Ramsey's Theorem: every word evaluated in a finite semigroup $S$ admits an unranked factorization tree of bounded height ($3N(S) - 1$) whose wide nodes evaluate to idempotents.

This repository provides a machine-checked formalization in Lean 4 of the algebraic structure of finite semigroups, Simon's Factorization Forest Theorem, and Colcombet's deterministic transducer construction for forward Ramsey splits.

## Project Structure & Formalized Content

The codebase is organized into three main components:

### 1. Green's Relations & Finite Semigroup Structure
- **Green's Relations** (`AlgebraicAutomata/Semigroup/GreensRelations/Basic.lean`): Definitions of Green's preorders and equivalence relations ($\mathcal{L}, \mathcal{R}, \mathcal{H}, \mathcal{D}, \mathcal{J}$) and semigroup duality with opposite semigroups.
- **Multiplication Sequences** (`AlgebraicAutomata/Semigroup/GreensRelations/MulSeq.lean`): Tools for analyzing finite semigroups via iterated multiplication sequences and pigeonhole arguments.
- **Green's Lemma** (`AlgebraicAutomata/Semigroup/GreensRelations/Green.lean`): Invertible maps between $\mathcal{H}$-classes within the same $\mathcal{D}$-class.
- **Finite Semigroup Properties** (`AlgebraicAutomata/Semigroup/GreensRelations/Finite.lean`): Proof that $\mathcal{D} = \mathcal{J}$ in finite semigroups, stability lemmas under multiplication, and Lemma 5.3 on right-multiplication.
- **Preorders & Partial Orders** (`AlgebraicAutomata/Semigroup/GreensRelations/Order.lean`): Order structures induced by Green's $\mathcal{J}$-classes.
- **Locally Finite Semigroups** (`AlgebraicAutomata/Semigroup/LocallyFinite.lean`): Brown's Lemma bounding the size of finitely generated subsemigroups.
- **Aperiodicity** (`AlgebraicAutomata/Semigroup/Aperiodic.lean`): Aperiodic semigroups, null elements, and idempotent power bounds.

### 2. Factorization Forests & Ramsey Theory
- **Multiplicative Labelings & Splits** (`AlgebraicAutomata/FactorizationForest/Basic.lean`): Formal definition of multiplicative labelings, split functions, and Ramsey splits.
- **Split Combination** (`AlgebraicAutomata/FactorizationForest/Combine.lean`): Inductive machinery combining Ramsey splits across subintervals.
- **Induction on $\mathcal{J}$-Classes** (`AlgebraicAutomata/FactorizationForest/Regular.lean`, `Irregular.lean`): Split construction for regular and irregular $\mathcal{D}$-classes.
- **Simon's Split Theorem** (`AlgebraicAutomata/FactorizationForest/Split.lean`): Proof of Simon's Split Theorem (`simon_split`) and its specialization to words (`simon_word`).
- **Factorization Trees & Height Bound** (`AlgebraicAutomata/FactorizationForest/Tree.lean`): Full proof of Simon's Factorization Forest Theorem (`factorization_forest_theorem`) bounding tree height by $3N(S) - 1$.
- **Optimality via Truncated Addition** (`AlgebraicAutomata/FactorizationForest/TruncatedAddition.lean`): Sub-linear height factorization trees over the truncated addition semigroup.
- **Infinitary Factorization Forests** (`AlgebraicAutomata/FactorizationForest/Infinitary.lean`): Factorization forests over $\mathbb{N}$ formalized via topological compactness.

### 3. Deterministic Accelerating Transducers
- **Forward Ramsey Splits** (`AlgebraicAutomata/FactorizationForest/Deterministic.lean`): Weakened forward Ramsey condition and 3-point evaluation identity.
- **Valid Configurations & State Space** (`AlgebraicAutomata/FactorizationForest/Deterministic.lean`): Strict ascending $\mathcal{J}$-chains and proof that the configuration state space is finite (bounded by $|S|^{|S|}$).
- **Transducer Construction & Ramsey Proof** (`AlgebraicAutomata/FactorizationForest/Deterministic.lean`): The deterministic transition function (`stepConfig`), Lemma 5.3, transition invariants, and proof that the deterministic transducer generates forward Ramsey splits (Theorem 5.2 / Lemma 5.5).

## References

* Colcombet, T. - *The Factorization Forest Theorem* (Handbook of Automata Theory, 2021)
* Simon, I. - *Factorization forests of finite height* (Theoretical Computer Science, 1990)