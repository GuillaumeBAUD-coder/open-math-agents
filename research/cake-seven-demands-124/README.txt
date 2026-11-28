Four cuts for the three-agent demand multiset (1,2,4)/7
======================================================

This package gives a complete proof of the specifically identified three-agent
case of Segal-Halevi's different-entitlements conjecture. For any three
nonatomic probability measures supported on [0,1], four cuts suffice to give
agents their respective own-value quotas 1/7, 2/7 and 4/7. The implementation
labels the agents B,C,H and uses quota order 2/7,1/7,4/7. Relabeling B and C
recovers the source's displayed order. No density, positivity-of-density,
absolute continuity, or auxiliary finite-certificate assumption is imposed.

This is a proposed target and a complete mathematical proof candidate. It does
not establish the conjecture for all numbers of agents or all entitlements,
and does not establish the stronger circle Conjecture 3.1 in Crew, Narayanan
and Spirkl. It also does not assert that this particular quota vector ever
requires four cuts. Registration and human translation review are separate
from the kernel/axiom audits recorded in verification.json.

Primary sources and relation to the existing target
---------------------------------------------------
Erel Segal-Halevi, Cake-Cutting with Different Entitlements,
arXiv:1803.05470v3, final Conjecture of Section 4. The source explicitly singles
out the three-agent quota vector (1/7,2/7,4/7) as the simplest open case.
  https://arxiv.org/abs/1803.05470
  https://arxiv.org/html/1803.05470v3

Logan Crew, Bhargav Narayanan and Sophie Spirkl, Disproportionate division,
arXiv:1909.07141, Section 1 and Section 3 (Bull. London Math. Soc. 52, 2020).
This provides the general context: 3n-4 cuts suffice, while the conjectured
bound is 2n-2. Its circle Conjecture 3.1 is stronger than the four-cut division
conclusion proved here.
  https://arxiv.org/abs/1909.07141

The registered arxiv1909.07141 statement concerns the full all-n, all-demand
conjecture. The present fixed case needs a separate proposed registration;
it is not a complete proof of that existing target. The proposed namespace is
OMA.S_arxiv_1803_05470_demands_124. Bounded independent source checks found no
pre-existing resolution of this exact quota case; this is not a guarantee of
priority or an exhaustive literature claim.

Exact formal statement and division model
-----------------------------------------
The statement quantifies only a family mu : Fin 3 -> Measure Real and assumes
  * each mu i is a probability measure;
  * each mu i gives every singleton measure zero (NullSingletonClass);
  * mu i ([0,1]) = 1 for every i.
It concludes
  DivisionWithCuts mu ![2/7,1/7,4/7] 4.

The definition body of DivisionWithCuts is copied exactly from the approved
arxiv1909.07141 model, under the new namespace. It provides a monotone vector
  0 = c_0 <= c_1 <= ... <= c_5 = 1
and assigns each of its five consecutive closed intervals to an agent. Every
agent's union has measure at least its quota. Repeated cut coordinates allow
fewer than four cuts; shared endpoints have measure zero for every agent.
An agent may own more than one interval. Thus the model describes a division
of [0,1] up to null cut points and imposes no connected-piece requirement.

The complete theorem is
  CakeSevenUnconditional.fixed_three_agent_division.
Its hypotheses are exactly the three measure conditions above. OMA.solution
is an exact-type adapter: it changes only the copied division-model namespace
and applies this closed theorem. There is no unproved counting, certificate,
regularity, or distribution hypothesis in the theorem or adapter.

Proof outline
--------------
1. Give the 2/7 agent B seven circular quantile marks of levels j/7, j=0,...,6,
   with the first mark at 0. Give the 1/7 agent C marks of levels theta+j/7.
   Choose theta from eight explicit values in (0,1/7), avoiding the at most
   seven forbidden residues arising from B's marks. Continuity of nonatomic
   distribution functions supplies exact quantiles, including when they have
   flat regions. The two colors' fourteen marks are all distinct. A two-step
   B arc has B-value 2/7; a one-step C arc has C-value 1/7, also when wrapped.

2. Starting at the distinguished B mark, encode every circular order by the
   seven counts of C marks following consecutive B marks. These are the weak
   compositions of 7 into 7 parts: binomial(13,6)=1716 cases. No cyclic or
   reflection quotient is needed for the final enumeration.

3. For each order, the literal table supplies positive rational weights on
   disjoint B-two-step/C-one-step arc pairs. The weights sum to one, and the
   total weight covering any elementary gap is at most 3/7. The checker uses
   integers and exact cross-multiplication. All 1716 records are checked by
   54 ordinary decide proofs; their explicit append assembly proves the whole
   table checked. Equality with the full composition list is proved by rfl.
   No native_decide, external LP output, or certificate-validation axiom is
   used in the Lean proof. An LP search can suggest records, but the kernel
   checks every record independently.

4. Use the third agent H's actual masses of the fourteen elementary gaps as
   nonnegative weights summing to one. Weighted averaging of the certificate
   yields a disjoint arc pair with total H-value at most 3/7. Give the B arc
   to B, the C arc to C, and their complement to H. Then H receives at least
   4/7. No transformation of H to uniform measure is needed.

5. At most four arc endpoints become line cuts. The proof handles both
   nonwrapped orders and the cases where either selected arc wraps across
   0=1. It constructs the actual cut vector and interval owners in the
   approved DivisionWithCuts model; endpoint masses vanish by nonatomicity.

Files and validation
---------------------
statement.lean  Proposed exact statement, including the copied division model.
                Its statement-only main intentionally has a hole for separate
                translation review. OMA.solution does not use that hole.
standalone.lean Complete standalone proof in the pinned Mathlib workspace;
                no proposed-module import is required. The source directly
                imports Aesop and Lean tactic dependencies as well.
proof.lean      The same complete proof body, importing the proposed statement,
                followed by the exact-type OMA.solution adapter.
verification.json  Release audit receipts, hashes, pins and allowed axioms.

The unchanged complete source body is frozen at SHA256
4017654eb40cb71a946eb6c6e3a7d40258141713ea3e6b65c9474b05f78d80af.
The finite table is part of the Lean source, not an external runtime input.
Its two-name full audit passed: all_certificates_checked uses only propext;
all_compositions_present uses no axioms. The complete closed theorem also
passed its full kernel/axiom audit at
  cake-seven-unconditional-checks/20261128T121726Z-helper-x7h5isij
with only the three permitted axioms and no diagnostics. This is validation
of the unchanged complete source body; the metadata distinguishes that
receipt from the separate exact-type adapter audit. The exact OMA.solution
adapter also passed its final audit with only the three permitted axioms.
Release audit results are recorded in verification.json. Proof
audits must exclude sorryAx and permit only propext, Classical.choice and
Quot.sound. A statement-only hole is never a proof acceptance result.

Reproduction
-------------
Use Lean v4.33.1, formal-conjectures commit
9097e2f90e66d2f6244209cb1c07f7120d17ec53, and Mathlib commit
0df444a360eaa60ab8c11dca51a86af692955474. These are the pinned versions used
for the implementation. From that Lake workspace, check the complete proof:
  lake env lean -j1 /absolute/path/to/standalone.lean
A COPY with the following command appended gives the complete theorem's axiom
list without modifying the release source:
  #print axioms CakeSevenUnconditional.fixed_three_agent_division
The expected allowed list is propext, Classical.choice and Quot.sound.

For the separate exact-type adapter, stage statement.lean as
OMAStatements/S_arxiv_1803_05470_demands_124.lean in the pinned workspace, then:
  mkdir -p .lake/build/lib/lean/OMAStatements
  lake env lean -j1 -o .lake/build/lib/lean/OMAStatements/S_arxiv_1803_05470_demands_124.olean OMAStatements/S_arxiv_1803_05470_demands_124.lean
  lake env lean -j1 /absolute/path/to/proof.lean
A copy of proof.lean with #print axioms OMA.solution appended verifies that
its proof uses only the permitted axioms, excluding the proposed statement's
intentional sorryAx. The ordinary statement-only warning is separate from
this proof axiom check. The certificate computation is substantial; allow
several minutes and use one Lean worker with adequate memory.

These checks establish the exact proposed fixed-case theorem. They do not
constitute official acceptance of the full registered arxiv1909.07141 target.
