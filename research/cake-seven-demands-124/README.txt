Four cuts for three agents with demands (1,2,4)/7
================================================

Complete checked candidate proof of the specifically identified open case
in Erel Segal-Halevi, Cake-Cutting with Different Entitlements,
arXiv:1803.05470v3, final Conjecture of Section4:
https://arxiv.org/abs/1803.05470
The paper explicitly names demands(1/7,2/7,4/7) as the simplest open case.

The theorem covers arbitrary nonatomic Borel probability measures on[0,1]
and constructs a division with at most FOUR cuts. Each agent may own several
intervals, as in the source. The formal agent order is B:2/7,C:1/7,H:4/7;
relabeling the first two agents gives the usual source order. There are no
certificate, quantile, density, continuity or other auxiliary hypotheses in
CakeSevenUnconditional.fixed_three_agent_division.

This is the fixed demand case, not the general all-agent/all-entitlement
conjecture in arXiv:1909.07141 and not its stronger circle Conjecture3.1.
The existing arxiv-1909.07141 registry target is unchanged. Separate target
registration and human statement review are needed for Left to Solve's normal
submission pipeline. No registered-target acceptance is claimed.

Proof
-----
Choose seven equal-value quantile marks for B and seven phase-shifted marks
for C. The phase avoids coincident marks, even for valuation CDFs with flat
parts. A red two-step arc has B-value2/7 and a blue one-step arc C-value1/7.
All1716 circular run orders have exact finite certificates: a nonnegative
weighted combination of disjoint red/blue pairs, covering each gap with
weight at most3/7. Taking H-measures as gap weights gives a pair costing H
at most3/7. Give H the complement; H then receives at least4/7. Four arc
endpoints produce at most four line cuts, including wrapped pieces.

The complete standalone file includes the actual arbitrary-measure reduction,
the exact certificate table and its full Lean verification. All54 chunks use
ordinary decide, combined by explicit proved append lemmas; coverage is proved
by rfl. No native evaluation, admitted premise or unproved table hypothesis
is used. The final theorem's axiom audit reports only propext, Classical.choice
and Quot.sound. The finite table audit uses onlypropext; coverage uses noaxioms.

Reproduce
---------
Use Lean v4.33.1, formal-conjectures commit
9097e2f90e66d2f6244209cb1c07f7120d17ec53, and Mathlib commit
0df444a360eaa60ab8c11dca51a86af692955474. The standalone proof uses that
Mathlib workspace and its normal dependencies, including Aesop/Lean tactics.
From the pinned Lake workspace:
  lake env lean -j1 /absolute/path/to/standalone.lean
Appending #print axioms CakeSevenUnconditional.fixed_three_agent_division
to a COPY gives exactly the three permitted axioms. verification.json records
the audited body hash and its byte-identical preservation in this file.

Independent source, model, data and integration reviews found no concrete gap.
A bounded prior-work search found no earlier full proof of this demand case;
this is not a priority guarantee. Only this complete proof is published here.
