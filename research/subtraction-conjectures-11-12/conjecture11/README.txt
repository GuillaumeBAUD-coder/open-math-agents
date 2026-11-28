Proposed formal proof of Conjecture 11 (arXiv:2510.24280v2)
========================================================

Status and scope
----------------
This package contains a complete kernel-checked candidate proof and an exact
proposed statement of Conjecture 11 in Bhagat, Kulkarni, Larsson and Murali,
Tie-breaking in self interest cumulative subtraction games, version 2,
20 January 2026, Definition 2 and page 10.
Source: https://arxiv.org/abs/2510.24280

This conjecture is NOT a registered Left to Solve target. The existing entry
arxiv-2510.24280 states the DIFFERENT Conjecture 4. This package does not claim
to prove, replace, close, or receive acceptance for that existing entry.
Registration of a separate target and human review of the statement are still
required before the normal registry statement/proof PR process can be used.
The included audits are named-theorem kernel/axiom checks, not registry verdicts.

Claim
-----
With positive integer moves a<b satisfying b/a=(k+1)/k for a positive integer k,
the two-player pocket outcomes are identical under friendly/friendly and
antagonistic/antagonistic tie-breaking, for EVERY natural heap h. In fact the
proof covers all four fixed convention pairs. The exact integer ratio is
b*k=a*(k+1), with a>0 and k>0; these imply b>a.

Files
-----
standalone.lean : complete proof, importing only Mathlib; no statement hole.
statement.lean  : proposed registry statement; its main has the intentional
                 statement-only sorry pending translation review.
proof.lean      : proof of that proposed statement through its exact type;
                 its OMA.solution has only the three permitted axioms.
verification.json : exact hashes, pins and named-theorem audit scope.

Model
-----
A move s from child outcome (u,v) produces (s+v,u). The current player first
maximizes their own pocket, then maximizes the opponent's pocket when friendly
or minimizes it when antagonistic. The two conventions swap at the next move.
This is Definition 2 specialized to two positive ordered actions. Zero actions
are guarded only to make the total recursive definition well-founded and
cannot occur under the theorem's assumptions.

Proof outline
-------------
Normalize the actions to k,k+1. Put L=2k+1. For h=tL+r, r<L, t<=k, set A=t(k+1).
The exact outcome for every convention pair is
  (A, A-(t-r))                  when r<k,
  (A+min(k+1,r-t), A)           when r>=k,
where natural subtraction is truncated. Strong induction checks this formula
in four remainder regimes, including the terminal and one-legal-move cases.

At T=(k-1)L the formula shows that every heap in T,...,T+k is fully consumed
and has convention-independent outcome. For a later heap, both children are
in the previously established region. Both move candidates then have the same
total utility h. If their mover utilities tie, their opponent utilities also
tie. Thus the tie convention cannot change the selected pair, and total h is
preserved. Strong induction gives independence for every later heap; the early
formula covers the remaining heaps. The k=1 case is included.

For arbitrary positive d, write h=d*m+r0, r0<d. Legal moves da,db correspond
exactly to a,b at heap m, and the residue r0 is unchanged. Induction proves
that both utilities are multiplied by d. Positive multiplication preserves
all comparisons. Finally the ratio condition forces a=k*d,b=(k+1)*d with
d=b-a>0, completing the original ratio formulation.

Related work and novelty scope
------------------------------
A bounded source review found no prior complete resolution of Conjecture 11.
This does not establish priority. Previously public derivations cover related
Conjecture 15 (AvA versus zero-sum, including AvA formulas) and Conjecture 17
(discrepancy bounds); the claim here is the convention equality of Conjecture 11,
not novelty of every underlying closed formula.
https://github.com/10m-u/open-problems-catalog/blob/main/solutions/b9-2026-10-08/PROOF-Q3188.md
https://github.com/PrincipiaMathOrg/math-solutions/blob/main/mathdb/371185/solution.md

Reproduce the complete standalone theorem
-----------------------------------------
Use Lean v4.33.1 and formal-conjectures commit
9097e2f90e66d2f6244209cb1c07f7120d17ec53, whose Mathlib pin is
0df444a360eaa60ab8c11dca51a86af692955474. From that Lake workspace run
  lake env lean /absolute/path/to/standalone.lean
A copy with #print axioms Conj11Complete.conjecture_11 appended prints exactly
propext, Classical.choice and Quot.sound. No sorry, added axiom, native_decide,
unsafe code or custom elaboration is used in the proof.

The separate proposed-import proof was also compiled after building
OMAStatements.S_arxiv_2510_24280_conjecture11 from statement.lean in the pinned
workspace. It is a proposed module only, not an upstream-approved declaration.
