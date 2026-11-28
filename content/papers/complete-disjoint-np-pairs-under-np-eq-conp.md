---
title: "Why NP = coNP would imply a complete disjoint NP pair"
date: "2026-11-28"
summary: "An exposition of the accepted Lean formalization of a known implication, using dense CNF satisfiability and a Cook–Levin reduction."
author: "stevenczp"
---

This note explains the known implication formalized in [accepted pull request #7436](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7436). It does not resolve the conjecture that no complete disjoint NP pair exists, or the question whether NP equals coNP.

**Proof credit:** stevenczp, using Codex (GPT-6), as recorded in the accepted submission. The submission adapts the Cook–Levin formalization from ATLAS v4.35.0 and Joshua Tan's millennium-cook-levin work; its source header records the original authors and adaptation credits. **Expository draft:** misothy, assisted by ChatGPT (GPT-6.2), for independent technical and literature review. This draft does not claim credit for the proof.

## Statement

A disjoint NP pair consists of languages A and B in NP with empty intersection. A polynomial-time reduction of pairs is one map f that sends members of A into the first target language and members of B into the second. There is no requirement on inputs outside A ∪ B. A complete disjoint NP pair is one to which every disjoint NP pair reduces.

The accepted theorem states that if NP = coNP, such a complete pair exists. These definitions and the precise implication are in [the pinned Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/Paper/DisjointNPPairs.lean).

## Proof idea

Let C be the dense CNF satisfiability language employed by the formalization. The Lean proof establishes that C belongs to NP and that every language A in NP has a polynomial-time many-one reduction f to C with A(x) = C(f(x)) as Boolean values. This is the Cook–Levin component, packaged in the declaration `denseSatDec_npComplete`.

Assume NP = coNP. Since C belongs to NP, it also belongs to coNP. Thus its complement belongs to NP. The pair (C, complement C) is disjoint.

Now take any disjoint NP pair (A,B). NP-hardness supplies a polynomial-time reduction f from A to C. If x belongs to A, the equivalence A(x) = C(f(x)) forces f(x) into C. If x belongs to B, disjointness implies x does not belong to A, and the same equivalence forces f(x) outside C. The same f therefore reduces both components simultaneously.

No reduction of B needs to be constructed separately. The complement of C is what permits the one map to handle both sides.

This is precisely the final construction in `OMA.solution`: the two components of the target are denseSatDec and its complement, and the witness f is taken from the hardness lemma applied to A.

## Formal proof map

The [accepted Lean source at the merge commit](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/84ba2ecf35513d5d128127814dc54e15532e989a/proofs/DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP.lean) contains the following key declarations.

| Declaration | Role |
|---|---|
| denseSatDec_mem_NP | Dense SAT belongs to NP. |
| gB_poly, g_outputs | Polynomial time bound and output correctness for the formula-generating machine. |
| v_correct | Equivalence between bounded-witness acceptance and satisfiability of the generated formula. |
| isPolyTime_red | The constructed reduction is polynomial-time computable. |
| denseSatDec_npHard | Every NP decision problem reduces to dense SAT. |
| denseSatDec_npComplete | Combines membership and hardness. |
| OMA.solution | Builds the complete disjoint NP pair under the equality assumption. |

The large formalization is principally needed for the explicit Cook–Levin construction and its machine-level polynomial bounds; the final pair-completeness argument is comparatively short.

## Scope and prior work

The implication is known, not a new separation result. Taking its contrapositive, nonexistence of a complete disjoint NP pair would imply NP ≠ coNP. This does not establish that the conjecture of nonexistence is true. The accepted formalization proves the conditional statement only.

Relevant background, already cited by the pinned statement, includes:

- C. Glaßer, A. L. Selman, S. Sengupta and L. Zhang, *Disjoint NP-pairs*, SIAM Journal on Computing 33 (2004), 1369–1416.
- P. Pudlák, *Incompleteness in the finite domain*, Bulletin of Symbolic Logic 23 (2017), 405–441. [Preprint](https://arxiv.org/abs/1601.01487).
- A. A. Razborov, *On provably disjoint NP-pairs*, BRICS RS-94-36 (1994).

The [official proof record](https://lefttosolve.com/p/DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP) and [merged submission](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7436) establish the attribution and accepted status. The expository draft awaits the separate review required by the initiative's paper process.
