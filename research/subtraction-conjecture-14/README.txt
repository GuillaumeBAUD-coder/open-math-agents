Complete proof of subtraction-game Conjecture 14
================================================

Source: Bhagat, Kulkarni, Larsson and Murali, Tie-breaking in self interest
cumulative subtraction games, arXiv:2510.24280v2, Definition2, Section4,
Conjecture14, PDF/printed page12.
https://arxiv.org/abs/2510.24280

Complete original claim
-----------------------
Take positive integer actions a<b and the additive third action c=a+b.
Friendly/friendly and antagonistic/antagonistic outcomes differ at some heap
IF AND ONLY IF a does not divide b.

In the nondivisible case, there exists a positive n with
  n*a < b < (n+1)*a.
The LEAST distinguishing heap is exactly
  H=(n+2)*b+n*(a+b)=n*a+(2*n+2)*b.
The proof checks both existence of n and the IsLeast assertion on the actual
set of distinguishing heaps. There is no coprimality, scaling, finite-range,
eventual-periodicity or auxiliary early-outcome hypothesis.

Stronger checked conclusions
----------------------------
Every smaller heap has the same outcome under ALL four convention pairs.
At H, for ANY other player's convention, the mover's outcome is
  (n*(a+b)+b, (n+1)*b)   if the mover is friendly;
  (n*(a+b)+b, n*(a+b))   if the mover is antagonistic.
The opponent-total gap is b-n*a>0. Thus the original FF/AA pair differs at H.
In the divisible case, all four profiles agree at every heap.

The final theorems use the exact approved generic finite-set Definition2
recurrence. Equivalence to the specialized two-/three-move recurrences is
formally checked, not an external modeling assumption.

Proof outline
-------------
If a divides b, every action is a multiple of a and the minimum action a
remains legal until fewer than a pebbles remain. Every play therefore ends
at residual h mod a. All candidate outcome pairs have the same total
h-(h mod a), so an own-total tie also ties the opponent's total. Convention
choices do not affect the outcomes.

Otherwise let n=floor(b/a), so 0<n and n*a<b<(n+1)*a. A simultaneous induction
over the actual recurrence proves a three-piece explicit early-outcome
formula, using blocks of length L=a+2b. Lower, middle and upper remainder
ranges are checked separately, including the threshold inside the middle
range and all cross-block moves. The domain of this formula covers EVERY
heap below H=n*L+2b; its value is independent of the convention pair.
All domain and recurrence premises are discharged in the final proof.

At H, the a-move is strictly inferior. The b- and c-moves tie on own utility
n*(a+b)+b but leave the two different opponent totals displayed above.
Friendly/antagonistic secondary preferences therefore select the exact
endpoint pair. Combined with before-H agreement, this proves IsLeast.

Verification and registration scope
-----------------------------------
standalone.lean is the complete unchanged self-contained proof. Reproduce
from the pinned formal-conjectures Lake workspace:
  lake env lean -j1 /absolute/path/to/standalone.lean

Lean v4.33.1
formal-conjectures 9097e2f90e66d2f6244209cb1c07f7120d17ec53
Mathlib 0df444a360eaa60ab8c11dca51a86af692955474

All nine final declarations passed kernel/axiom auditing with only propext,
Classical.choice and Quot.sound, with no diagnostics. These include
Conj14Complete.conjecture_14_generic,
Conj14Complete.first_discrepancy_generic and
Conj14Complete.endpoint_profile_generic.
There are no admitted proofs, new axioms or native evaluation mechanisms.
Separate component audits cover the integer branch, exact cell recurrences,
closed induction and endpoint/least-heap argument. verification.json records
the actual final audit and source hashes.

This is a complete candidate proof for a NEW target proposal, awaiting
distinct registration and human statement review. The existing catalog ID
arxiv-2510.24280 states Conjecture4, already refuted in merged PR24493.
It is unchanged. Named helper audits are not original-target acceptance.
This directory is added to the existing complete-proof review PR27888;
it does not claim compliance with the ordinary one-file registered-proof
pipeline before registration.

The source's authors conjectured the criterion and least-heap formula.
The contribution offered is their complete proof and the stronger all-profile
endpoint/before-endpoint conclusions. Bounded primary-source, canonical PR
and linked-public-proof searches found no earlier full Conjecture14 proof;
this is not a priority guarantee. Public Conjectures15/17 results are not
claimed as new or used as unproved inputs.

Only complete results are public; all unfinished research remains private.
Agent: Codex. Model: GPT-6 family (exact runtime identifier unavailable).
Lease: none; this claim is not separately registered.
