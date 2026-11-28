Proposed formal proof of Conjecture 12 (arXiv:2510.24280v2)
========================================================

This is a complete kernel-checked candidate proof, not a registered or accepted
Left to Solve target. The existing arxiv-2510.24280 registry entry is about
Conjecture 4. A distinct entry and human statement review are still required.

Source: Bhagat, Kulkarni, Larsson and Murali, Tie-breaking in self interest
cumulative subtraction games, arXiv:2510.24280v2, Definition 2 and page 10.
https://arxiv.org/abs/2510.24280
The first-heap formula below is the authors' conjectured formula. The work in
this package is its all-heaps proof, not discovery of that formula.

Exact claim
-----------
Let 0<a<b<2a be integers, excluding every ratio b/a=(k+1)/k with k>=1.
There is a positive integer n with
  (n+2)/(n+1) < b/a < (n+1)/n.
The first heap that distinguishes friendly/friendly from antagonistic/
antagonistic play is exactly H=(n+2)a+n*b. These are not merely a finite
verification or a conclusion conditional on being supplied an n: the proof
constructs the interval index from floor(a/(b-a)).

At that heap, the outcomes are
  friendly:     (a+n*b, (n+1)*a),
  antagonistic: (a+n*b, n*b),
with strictly positive opponent difference a-n*(b-a). Every smaller natural
heap has the same outcome under all four fixed convention pairs.

Proof outline
-------------
Write d=b-a, L=2a+d, with n*d<a<(n+1)*d. For h=t*L+r, r<L, before H,
all convention pairs have the explicit early outcome
  (t*b, t*a+d*min(t,floor(r/d)))                         if r<a,
  ((t+1)*a+d*min(t+1,floor((r-a)/d)), t*b)              if r>=a.
The exact generic domain is t*d<a and, if r>=2a, (t+1)*d<=a.
Strong induction checks four remainder regimes against Definition 2.
For every h<H its quotient/remainder satisfy that domain.

At H, the a-child is ((n+1)*a,n*b), and the b-child is (n*b,n*b-d).
Both moves give the mover a+n*b. Their opponent utilities differ by a-n*d>0,
so the two tie-breaking conventions choose the displayed different outcomes.
The early formula proves minimality for ALL h<H. The final theorem also
proves existence of the positive interval index for every nonresonant pair.

Verification
------------
standalone.lean imports only Mathlib and contains the full proof with no sorry.
statement.lean is a new proposed registry statement with only the intentional
main-statement hole. proof.lean proves that exact proposed type; its axiom audit
must contain only propext, Classical.choice and Quot.sound. See verification.json.
Use the same pinned workspace/reproduction instructions as the sibling
Conjecture 11 package. Named-theorem audits are not registry acceptance.

A bounded public-source search found no complete earlier Conjecture 12 proof.
This does not establish priority. Public derivations of the same paper's
Conjectures 15 and 17 do not settle the first-heap classification proved here.
