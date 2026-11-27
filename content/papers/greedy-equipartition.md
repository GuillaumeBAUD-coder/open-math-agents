---
title: A counterexample to greedy convex equipartition
date: 2026-11-27
summary: A quadrilateral of area 36 admits three equal-area triangles whose total perimeter beats every partition obtained by making a longest admissible first cut.
author: Robert Leshner (@rleshner), with Codex (GPT-6.2 Astra)
---

R. Nandakumar asked how to divide a convex planar region into equal-area convex pieces of maximum total perimeter. Conjecture 2 proposes repeatedly removing one piece by the longest admissible straight cut. The rule already fails for three pieces. Each interior cut counts twice in the sum of the perimeters, so it suffices to compare total cut length. [Original problem](https://www.openproblemgarden.org/op/convex_equipartitions_with_extreme_perimeter) · [Catalog entry](https://lefttosolve.com/p/opg-convex-equipartitions-with-extreme-perimeter)

## The two partitions

Take the quadrilateral with consecutive vertices $A=(0,0)$, $B=(8,0)$, $C=(8,4)$, and $D=(2,6)$. Its area is 36. Write $E=(8,3)$. The unique longest cut removing area 12 is $AE$, of squared length 73. The remainder is $AECD$, and its longest bisector has squared length $272/5$. The greedy total is therefore $\sqrt{73}+\sqrt{272/5}<16$. The bounds $8.6$ and $7.4$ follow by squaring. The Lean results are `first_cut`, `witnessIsLongest`, `second_cut`, and `secondWitness`.

Instead, join $B$ to $D$ and to the midpoint $M=(1,3)$ of $AD$. The diagonal cuts off triangle $BCD$ of area 12. The median $BM$ bisects the remaining triangle of area 24. These cuts have squared lengths 72 and 58, so their total exceeds $8.4+7.6=16$. The result `competingTriangles` checks the three areas and the two squared lengths. The theorem `greedy_fails` compares the partitions.

## How the upper bounds are proved

Every positive-area cut has endpoints on two distinct edges. Parameterize each endpoint along its edge by a real number in $[0,1]$. For each of the six unordered pairs of edges, the shoelace formula gives twice the area on one side as a bilinear expression in the two parameters. For the first cut this quantity can be 24 or 48, since either side can be the piece removed. For the second cut it must be 24.

On each feasible interval the area equation eliminates one parameter. Clearing the squared denominator reduces the claimed bound on squared length to a polynomial inequality in the other parameter. The proof certifies positivity in the interval interior by writing the polynomial as a sum of nonnegative multiples of products of distances to the interval endpoints. It checks endpoints separately, including all possible ties. This covers all real cut positions. The relevant proofs are the edge-pair lemmas used by `first_cut` and `second_cut`. [Lean source](https://github.com/rleshner/open-math-agents/blob/paper/greedy-equipartition-counterexample/content/papers/greedy-equipartition/GreedyCounterexample.lean)

Both partitions have their cuts meet only on the outer boundary. The counterexample settles the greedy proposal and leaves Conjectures 1 and 1a about interior junctions open. Rellon and coauthors previously studied the two-piece bisection problem. [Rellon et al. (2024)](https://doi.org/10.21776/ub.ijma.2024.002.01.4)
