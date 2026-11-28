Complete candidate proofs: subtraction-game Conjectures 11 and 12
================================================================

Source: Bhagat, Kulkarni, Larsson and Murali, Tie-breaking in self interest
cumulative subtraction games, arXiv:2510.24280v2,20 January 2026, Definition 2
and Conjectures 11--12 on page 10.
https://arxiv.org/abs/2510.24280

This is a COMPLETE proof package for two NEWLY PROPOSED formalizations.
It is not a Left to Solve registered target or accepted submission. The
existing arxiv-2510.24280 entry states a different claim, Conjecture 4.
Registration of distinct entries and human statement review are required
before these can use the normal registry statement/proof-PR pipeline.
No existing target is modified or replaced here.

Conjecture 11: for positive integer moves a<b with b/a=(k+1)/k,k>=1,
friendly/friendly and antagonistic/antagonistic outcomes agree for every
heap. The proof covers all four fixed convention pairs.

Conjecture 12: for 0<a<b<2a excluding those ratios, the proof constructs a
positive n in the source's strict ratio interval and proves that the LEAST
heap distinguishing the conventions is H=(n+2)a+n*b. At H the mover pockets
agree, while the opponent pockets differ by a-n*(b-a)>0.

The authors already conjectured these formulas. The contribution claimed
by this package is the complete proof, not discovery of the formulas.
A bounded public-source review found no earlier full proof of either claim;
this does not establish priority. Related public derivations for Conjectures 15
and 17 are linked in the individual notes and do not establish11 or 12.

Run the complete self-contained proof
------------------------------------
standalone.lean imports only Mathlib and contains BOTH complete proofs.
From the pinned formal-conjectures Lake workspace in verification.json:
  lake env lean /absolute/path/to/standalone.lean
Appending #print axioms Conj11Complete.conjecture_11 and
#print axioms Conj12Complete.original_conjecture_12 to an audit COPY reports
only propext, Classical.choice and Quot.sound.

The per-conjecture folders additionally contain the proposed exact statement
and its exact-type OMA.solution proof. A proposed statement intentionally has
a main-statement sorry pending review; its proof does NOT depend on that hole.
The self-contained proof has no sorry, native_decide, added axioms or unsafe
mechanism. verification.json records hashes and actual named-theorem audits.
These kernel audits are NOT registry original-target-checker acceptance.

See conjecture11/README.txt and conjecture12/README.txt for mathematical proofs,
model conventions, domains and first-heap details. Only complete results are
published in this package; other ongoing research remains private.
