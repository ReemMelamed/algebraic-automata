# Algebraic Automata in Lean 4

[![CI](https://github.com/ReemMelamed/algebraic-automata/actions/workflows/ci.yml/badge.svg)](https://github.com/ReemMelamed/algebraic-automata/actions/workflows/ci.yml)
[![Docs](https://img.shields.io/badge/docs-GitHub_Pages-blue.svg)](https://reemmelamed.github.io/algebraic-automata/)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.35.0--rc2-blue.svg)](https://lean-lang.org/)
[![Mathlib 4](https://img.shields.io/badge/powered_by-Mathlib4-purple.svg)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-Apache_2.0-green.svg)](LICENSE)

A formalization of algebraic automata theory, finite semigroups, and Simon's Factorization Forest Theorem in Lean 4.

## What is it?

In theoretical computer science, **algebraic automata theory** analyzes languages and state machines through the algebraic structure of finite semigroups and monoids. Instead of viewing an automaton merely as a state transition graph, its computational power is captured by its *transition monoid*, while the language itself canonically defines a *syntactic monoid*. Fundamental theorems, such as Schützenberger's (1965), establish exact correspondences between language expressivity (e.g. star-free languages) and algebraic properties (such as aperiodicity).

A central combinatorial tool in modern algebraic automata is **Simon's Factorization Forest Theorem**. It is a non-commutative, structural variant of Ramsey's Theorem on words: every word evaluated in a finite semigroup $S$ admits an unranked factorization tree of bounded height ($3N(S) - 1$) whose wide nodes evaluate to idempotents.

## What's in scope?

There are broadly four pillars this repository aims to formalize:

- **Green's relations & finite semigroup structure** ($\mathcal{L}, \mathcal{R}, \mathcal{H}, \mathcal{D}, \mathcal{J}$, $\mathcal{D} = \mathcal{J}$ in finite semigroups, Green's lemma, idempotent groups)
- **Factorization forests & Ramsey theory** (Simon's split theorem, factorization trees of height $\le 3N(S)-1$, infinitary variants on $\mathbb{N}$, and optimality bounds)
- **Deterministic accelerating structures** (Colcombet's deterministic forward Ramsey transducer over valid $\mathcal{J}$-chain configurations)
- **Algebraic automata & applications** (syntactic monoids, Schützenberger's theorem, tropical matrix semirings, and decidability of distance automata boundedness)

## References

* Colcombet, T. - *The Factorization Forest Theorem* (Handbook of Automata Theory, 2021)
* Simon, I. - *Factorization forests of finite height* (Theoretical Computer Science, 1990)
* Schützenberger, M. P. - *On finite monoids having only trivial subgroups* (Information and Control, 1965)
* Pin, J.-E. - *Varieties of Formal Languages* (1986)
* Leung, H. - *Limitedness of finite partial-communication automata* (1991)