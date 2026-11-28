Complete proof of subtraction-game Conjecture 13
================================================

Source: Bhagat, Kulkarni, Larsson and Murali, Tie-breaking in self interest
cumulative subtraction games, arXiv:2510.24280v2, Definition 2 and Conjecture 13.
https://arxiv.org/abs/2510.24280

Claim: for positive integer actions a < b < c with c >= 2b, if friendly/friendly
and antagonistic/antagonistic outcomes agree at every heap for {a,b}, they also
agree at every heap for {a,b,c}. This is the source's original Conjecture 13.

The complete proof establishes a stronger formula for every ordered convention
pair sigma. Let dual(sigma) swap the players, and G_sigma be the ACTUAL two-move
outcome. For h=2cq+r with 0 <= r < 2c, the three-move outcome equals
  (qc + G_sigma(r).first, qc + G_sigma(r).second)                 if r < c;
  ((q+1)c + G_dual(sigma)(r-c).second,
   qc + G_dual(sigma)(r-c).first)                               otherwise.
There is no agreement assumption in this formula. The original inheritance
claim follows for the two symmetric convention pairs. Also, adding 2c to the
heap adds c to each player's utility, starting at heap zero.

These are actual outcomes in the exact finite-set recurrence used by the
approved Conjecture 4 translation. The specialized two-/three-move recurrences
are formally proved equal to that generic recurrence, for all heaps and all
four profiles. No auxiliary budget, boundary, eventual-periodicity or strategy
hypothesis remains in the final statements. This is an outcome-pair claim;
smaller moves can sometimes tie the c-move with the identical outcome.

Proof outline
-------------
Every outcome obeys the elementary total-budget bound. Below b the two-action
game has only the move a, giving explicit alternating totals independent of the
conventions. These facts prove the boundary lemma: for r < b and u >= b+r,
  G_sigma(u).first <= u-r+G_sigma(r).first;
equality forces G_sigma(u).second = G_sigma(r).second.
A simultaneous strong induction over heaps verifies the displayed formula for
all profiles. In the upper half of each 2c-block, the c-move strictly beats both
smaller moves. In the lower half, smaller moves staying in the same block are
exactly the translated original two-move candidates. A smaller move crossing
the boundary is controlled by the boundary lemma and its equality clause.
The c-move supplies the stated outcome, resolving secondary preferences too.

Verification and scope
----------------------
standalone.lean is the complete, self-contained source. Reproduce in the pinned
formal-conjectures Lake workspace:
  lake env lean -j1 /absolute/path/to/standalone.lean

Lean v4.33.1
formal-conjectures 9097e2f90e66d2f6244209cb1c07f7120d17ec53
Mathlib 0df444a360eaa60ab8c11dca51a86af692955474

All six named final declarations passed kernel/axiom auditing, including
Conj13Complete.conjecture_13_generic,
Conj13Complete.exact_outcome_formula_generic and
Conj13Complete.periodic_affine_outcome_generic.
Only propext, Classical.choice and Quot.sound occur. There is no admitted
proof, extra axiom or native evaluation. verification.json records source
hashes and the actual audit reports. An independent model review and separately
audited equivalence bridge found no mismatch with the source recurrence.

This is a complete candidate proof for a NEW target proposal, awaiting maintainer
registration and human statement review. The existing arxiv-2510.24280 ID is
Conjecture 4, already refuted in merged PR24493. It is unchanged. Named helper
audits are not original-target acceptance. This research package does not follow
the normal one-file registered statement/proof pipeline.

The source's authors conjectured the inheritance statement; this package offers
its proof and the stronger exact formula. A bounded primary-source and linked
prior-work review found no earlier complete Conjecture 13 resolution. This is
not a priority guarantee. Already public proofs of Conjectures 15 and 17 were
screened and are not claimed as new or used as unproved inputs here.

This directory contains complete results only; unrelated partial research is
excluded. Agent: Codex. Model: GPT-6 family (exact runtime identifier unavailable).
Lease: none; this specific claim is not registered.
