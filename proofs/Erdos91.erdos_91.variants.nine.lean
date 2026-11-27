import FormalConjectures.ErdosProblems.«91»

/-!
# Two dissimilar distance minimizers on nine points

The lower bound uses an isosceles triangle of unit legs after rescaling,
with squared base length t different from 0 and 4. Each remaining point
has a profile of three squared distances to the triangle. There are three
possible values for each component, hence 27 profiles. The two tables below
color the profiles with five colors, according as the base is a unit or a
second distance. Profiles of the same color cannot coexist.

For each forbidden pair, the displayed polynomial identity is a
Nullstellensatz certificate over the rationals, generated with Singular and
verified here by ring normalization. The auxiliary z is the inverse of the
product of the required nonzero factors. The geometric identities below
show that any planar realization satisfies every premise of the certificate.

For the upper bound we give two triangular-lattice configurations. Their
squared distances are 1, 3, 4 and 7, with 15 and 16 shortest unordered pairs.
The lattice lemmas are adapted from the eight-point witness proof in this repository.
-/

namespace OMA.NineDistances

open EuclideanGeometry Erdos91

private def palette (b c : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then b else c

private def profile (b c : ℝ) (i : Fin 27) : ℝ × ℝ × ℝ :=
  (palette b c (i.val / 9), palette b c (i.val / 3 % 3), palette b c (i.val % 3))

private def delta (t : ℝ) := t * (4 - t)
private def quad (t x y : ℝ) := x^2 + y^2 - (2-t)*x*y
private def u (p : ℝ × ℝ × ℝ) := 1 + p.1 - p.2.1
private def v (p : ℝ × ℝ × ℝ) := 1 + p.1 - p.2.2
private def locus (t : ℝ) (p : ℝ × ℝ × ℝ) := quad t (u p) (v p) - delta t * p.1
private def sep (t : ℝ) (p q : ℝ × ℝ × ℝ) := quad t (u p - u q) (v p - v q)
private def edge (t b c : ℝ) (p q : ℝ × ℝ × ℝ) :=
  let s := sep t p q
  (s - delta t) * (s - b * delta t) * (s - c * delta t)
private def invCondition (t b c z : ℝ) :=
  z*b*c*(b-1)*(c-1)*(b-c)*delta t-1

private def colorsE : Fin 27 → Fin 5 := ![1, 4, 2, 3, 2, 0, 3, 1, 4, 0, 0, 1, 3, 3, 1, 2, 4, 1, 0, 3, 2, 4, 2, 2, 0, 0, 4]

private lemma rejectE_0_7 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, 1) = 0) (h2 : locus 1 (1, c, b) = 0)
    (h3 : edge 1 b c (1, 1, 1) (1, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1/2) * h1

private lemma rejectE_0_11 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, 1) = 0) (h2 : locus 1 (b, 1, c) = 0)
    (h3 : edge 1 b c (1, 1, 1) (b, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1/2) * h1

private lemma rejectE_0_14 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, 1) = 0) (h2 : locus 1 (b, b, c) = 0)
    (h3 : edge 1 b c (1, 1, 1) (b, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1/2) * h1

private lemma rejectE_0_17 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, 1) = 0) (h2 : locus 1 (b, c, c) = 0)
    (h3 : edge 1 b c (1, 1, 1) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1/2) * h1

private lemma rejectE_1_8 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, b) = 0) (h2 : locus 1 (1, c, c) = 0)
    (h3 : edge 1 b c (1, 1, b) (1, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(8*b^4*c - 4*b^4 - 24*b^3*c^2 - 12*b^3*c + 12*b^3 + 48*b^2*c^3 - 48*b^2*c^2 + 12*b^2*c - 56*b*c^4 + 124*b*c^3 + 51*b*c^2 - 71*b*c + 4*b + 48*c^5 - 240*c^4 + 297*c^3 + 21*c^2 - 150*c + 36)/9) * h1 + (-2*z*(12*b*c^4 - 54*b*c^3 + 72*b*c^2 + 3*b*c - 36*b - 4*c^5 + 10*c^4 - 4*c^3 - 4*c^2 + 10*c - 4)/9) * h2 + (-4*z*(2*c - 1)/9) * h3

private lemma rejectE_1_16 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, b) = 0) (h2 : locus 1 (b, c, b) = 0)
    (h3 : edge 1 b c (1, 1, b) (b, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(5*b^4*c - 7*b^4 - 15*b^3*c^2 + 6*b^3*c + 21*b^3 + 30*b^2*c^3 - 57*b^2*c^2 + 21*b^2*c - 30*b*c^4 + 72*b*c^3 + 60*b*c^2 - 108*b*c - 21*b + 15*c^5 - 66*c^4 + 66*c^3 + 6*c^2 - 39*c + 21)/9) * h1 + (-z*(5*b*c^4 - 37*b*c^3 + 72*b*c^2 - 13*b*c - 28*b - 5*c^5 + 32*c^4 - 50*c^3 - 14*c^2 + 59*c - 14)/9) * h2 + (-z*(5*c - 7)/9) * h3

private lemma rejectE_1_21 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, b) = 0) (h2 : locus 1 (c, b, 1) = 0)
    (h3 : edge 1 b c (1, 1, b) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(27*b^4*c - 27*b^4 - 108*b^3*c + 108*b^3 + 27*b^2*c^3 - 108*b^2*c^2 + 270*b^2*c - 189*b^2 - b*c^4 - 47*b*c^3 + 270*b*c^2 - 251*b*c + 164*b + 9*c^5 - 54*c^4 + 81*c^3 - 117*c^2 + 135*c - 54)/27) * h1 + (z*(b*c^4 + 2*b*c^3 - 100*b*c - 38*b + c^5 - 8*c^4 + 25*c^3 - 46*c^2 + 44*c - 16)/27) * h2 + (-z*(c - 1)/27) * h3

private lemma rejectE_1_26 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, b) = 0) (h2 : locus 1 (c, c, c) = 0)
    (h3 : edge 1 b c (1, 1, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(32*b^4 - 192*b^3 - 96*b^2*c + 192*b^2 - 135*b*c^2 + 519*b*c + 32*b + 135*c^3 - 405*c^2 + 558*c - 192)/45) * h1 + (2*z*(45*b*c^2 - 165*b*c + 96*b + 32)/45) * h2 + (32*z/45) * h3

private lemma rejectE_2_4 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, c) = 0) (h2 : locus 1 (1, b, b) = 0)
    (h3 : edge 1 b c (1, 1, c) (1, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(64*b*c^4 - 612*b*c^3 + 2124*b*c^2 - 3393*b*c + 2043*b - 24*c^5 + 148*c^4 - 108*c^3 - 648*c^2 + 1215*c - 603)/9) * h1 + (-z*(8*b^5 - 92*b^4 - 24*b^3*c^2 + 132*b^3*c + 152*b^3 + 88*b^2*c^3 - 456*b^2*c^2 + 432*b^2*c + 8*b^2 - 120*b*c^4 + 692*b*c^3 - 1011*b*c^2 + 63*b*c - 92*b + 120*c^5 - 1032*c^4 + 3091*c^3 - 3576*c^2 + 1077*c + 152)/9) * h2 + (4*z*(2*b + 6*c - 19)/9) * h3

private lemma rejectE_2_15 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, c) = 0) (h2 : locus 1 (b, c, 1) = 0)
    (h3 : edge 1 b c (1, 1, c) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(b*c^4 + 57*b*c^3 - 54*b - 19*c^5 + 80*c^4 - 180*c^3 + 252*c^2 - 189*c + 54)/27) * h1 + (-z*(b^5 - 5*b^4 + 8*b^3*c^2 - 15*b^3*c + 4*b^3 - b^2*c^3 - 9*b^2*c^2 + 18*b^2*c + 8*b^2 + 18*b*c^4 - 52*b*c^3 - 90*b*c^2 + 180*b*c - 40*b - 8*c^5 + 90*c^4 - 283*c^3 + 271*c^2 - 102*c + 32)/27) * h2 + (z*(b - c + 2)/27) * h3

private lemma rejectE_2_20 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, c) = 0) (h2 : locus 1 (c, 1, c) = 0)
    (h3 : edge 1 b c (1, 1, c) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((c - 3)/2) * h1 + (-(c - 2)/2) * h2

private lemma rejectE_2_22 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, c) = 0) (h2 : locus 1 (c, b, b) = 0)
    (h3 : edge 1 b c (1, 1, c) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(1288*b*c^4 - 6552*b*c^3 + 11007*b*c^2 - 9720*b*c + 10557*b - 1736*c^5 + 4256*c^4 + 12345*c^3 - 45198*c^2 + 39798*c - 10557)/27) * h1 + (z*(56*b^5 - 1120*b^4 - 1568*b^3*c^2 + 8232*b^3*c - 2464*b^3 + 6440*b^2*c^3 - 30576*b^2*c^2 + 24696*b^2*c - 56*b^2 - 11256*b*c^4 + 59864*b*c^3 - 81903*b*c^2 + 24615*b*c + 1120*b + 8848*c^5 - 57288*c^4 + 119417*c^3 - 89488*c^2 + 14871*c + 2464)/27) * h2 + (-56*z*(b + 7*c - 22)/27) * h3

private lemma rejectE_2_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, c) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (1, 1, c) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(35*b*c^4 + 54*b*c^3 - 174*b*c^2 + 99*b*c - 27*b - 25*c^5 + 59*c^4 + 21*c^3 - 210*c^2 + 270*c - 81)/9) * h1 + (-z*(5*b^5 - 47*b^4 + 10*b^3*c^2 - 18*b^3*c + 125*b^3 + 15*b^2*c^3 - 111*b^2*c^2 + 141*b^2*c - 31*b^2 + 15*b*c^4 - 75*b*c^3 + 150*b*c^2 - 132*b*c - 164*b + 30*c^5 - 126*c^4 + 51*c^3 + 298*c^2 - 363*c + 44)/9) * h2 + (z*(5*b + 5*c - 22)/9) * h3

private lemma rejectE_3_6 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, 1) = 0) (h2 : locus 1 (1, c, 1) = 0)
    (h3 : edge 1 b c (1, b, 1) (1, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*c*z*(c - 1)*(b - c + 2)) * h1 + (-6*b*z*(c - 1)) * h2

private lemma rejectE_3_12 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, 1) = 0) (h2 : locus 1 (b, b, 1) = 0)
    (h3 : edge 1 b c (1, b, 1) (b, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((b - 3)/2) * h1 + (-(b - 2)/2) * h2

private lemma rejectE_3_13 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, 1) = 0) (h2 : locus 1 (b, b, b) = 0)
    (h3 : edge 1 b c (1, b, 1) (b, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-9/8) * h1 + (-(3*b - 8)/8) * h2

private lemma rejectE_3_19 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, 1) = 0) (h2 : locus 1 (c, 1, b) = 0)
    (h3 : edge 1 b c (1, b, 1) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(27*b^4*c - 27*b^4 - 108*b^3*c + 108*b^3 + 27*b^2*c^3 - 108*b^2*c^2 + 270*b^2*c - 189*b^2 - b*c^4 - 47*b*c^3 + 270*b*c^2 - 251*b*c + 164*b + 9*c^5 - 54*c^4 + 81*c^3 - 117*c^2 + 135*c - 54)/27) * h1 + (z*(b*c^4 + 2*b*c^3 - 100*b*c - 38*b + c^5 - 8*c^4 + 25*c^3 - 46*c^2 + 44*c - 16)/27) * h2 + (-z*(c - 1)/27) * h3

private lemma rejectE_4_15 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, b) = 0) (h2 : locus 1 (b, c, 1) = 0)
    (h3 : edge 1 b c (1, b, b) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((2946944*b^5*c - 6504256*b^5 - 4389504*b^4*c^2 - 5105216*b^4*c + 32637520*b^4 + 4374048*b^3*c^3 + 2551440*b^3*c^2 + 229232*b^3*c - 59903152*b^3 - 2532208*b^2*c^4 - 2833744*b^2*c^3 + 12718932*b^2*c^2 - 10169108*b^2*c + 50931064*b^2 + 1034425*b*c^5 - 506334*b*c^4 - 608284*b*c^3 - 10293437*b*c^2 + 15469858*b*c - 20119056*b - 221536*c^6 + 257686*c^5 + 2047228*c^4 - 6380492*c^3 + 8392912*c^2 - 5234712*c + 2254834)/280908) * h1 + ((43631*b*c^5 - 169238*b*c^4 - 89848*b*c^3 + 1354751*b*c^2 - 3567062*b*c + 4512590*b + 483*c^6 - 175138*c^5 + 780565*c^4 - 722470*c^3 - 398941*c^2 + 1286860*c - 1973926)/280908) * h2 + (-(46046*b*c - 101629*b + 483*c^2 - 174655*c + 382925)/280908) * h3

private lemma rejectE_4_20 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, b) = 0) (h2 : locus 1 (c, 1, c) = 0)
    (h3 : edge 1 b c (1, b, b) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((22*b^5*c - 83*b^5 - 244*b^4*c + 911*b^4 - 66*b^3*c^3 + 45*b^3*c^2 + 1681*b^3*c - 3470*b^3 - 242*b^2*c^4 + 1297*b^2*c^3 + 192*b^2*c^2 - 7819*b^2*c + 6023*b^2 - 330*b*c^5 + 2441*b*c^4 - 4639*b*c^3 - 2646*b*c^2 + 12793*b*c - 4361*b - 330*c^6 + 2685*c^5 - 6614*c^4 + 2122*c^3 + 10833*c^2 - 8419*c + 1004)/243) * h1 + (-(176*b*c^5 - 548*b*c^4 + 515*b*c^3 + 158*b*c^2 + 46*b*c - 1708*b + 66*c^6 - 709*c^5 + 2059*c^4 - 1171*c^3 - 2095*c^2 + 1294*c + 761)/243) * h2 + (-(22*b*c - 83*b - 66*c^2 + 181*c + 247)/243) * h3

private lemma rejectE_4_22 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, b) = 0) (h2 : locus 1 (c, b, b) = 0)
    (h3 : edge 1 b c (1, b, b) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(2*b*c^4 - 5*b*c^3 - 60*b*c^2 - 35*b*c - b - 3*c^5 + 5*c^4 + 49*c^3 - 57*c^2 + 43*c - 1)/27) * h1 + (z*(2*b*c^4 - 5*b*c^3 + 21*b*c^2 - 116*b*c - b + c^5 - 9*c^4 + 20*c^3 - 7*c^2 + 30*c + 1)/27) * h2 + (-z*(c - 1)/27) * h3

private lemma rejectE_4_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, b) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (1, b, b) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((2852*b^5*c - 4953*b^5 - 8587*b^4*c^2 - 1223*b^4*c + 28266*b^4 + 17205*b^3*c^3 - 15634*b^3*c^2 - 4606*b^3*c - 36720*b^3 - 20150*b^2*c^4 + 23925*b^2*c^3 + 74718*b^2*c^2 - 92449*b^2*c - 4953*b^2 + 14446*b*c^5 - 36928*b*c^4 - 6336*b*c^3 - 11323*b*c^2 + 82963*b*c + 30696*b - 2945*c^6 + 5470*c^5 + 30418*c^4 - 92076*c^3 + 13445*c^2 + 123932*c - 39150)/7290) * h1 + ((2883*b*c^5 - 17670*b*c^4 + 22071*b*c^3 + 13581*b*c^2 - 20394*b*c - 2430*b - 31*c^6 - 10254*c^5 + 62817*c^4 - 73113*c^3 - 63657*c^2 + 81504*c + 9720)/7290) * h2 + (-(2852*b*c - 4953*b - 31*c^2 - 10378*c + 18360)/7290) * h3

private lemma rejectE_5_9 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, c) = 0) (h2 : locus 1 (b, 1, 1) = 0)
    (h3 : edge 1 b c (1, b, c) (b, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(27*b^4*c - 27*b^4 + 27*b^3*c^2 - 162*b^3*c + 135*b^3 + 27*b^2*c^3 - 135*b^2*c^2 + 324*b^2*c - 216*b^2 + b*c^4 - 79*b*c^3 + 162*b*c^2 - 343*b*c + 124*b + c^5 - 8*c^4 + 25*c^3 - 46*c^2 + 44*c - 16)/27) * h1 + (-z*(b*c^4 - 88*b*c^3 - 46*b*c - 2*b + 18*c^5 - 54*c^4 + 135*c^3 - 153*c^2 + 54*c)/27) * h2 + (-z*(c - 1)/27) * h3

private lemma rejectE_5_10 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, c) = 0) (h2 : locus 1 (b, 1, b) = 0)
    (h3 : edge 1 b c (1, b, c) (b, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((2946944*b^5*c - 6504256*b^5 - 1442560*b^4*c^2 - 17503360*b^4*c + 45646032*b^4 - 15456*b^3*c^3 + 12119120*b^3*c^2 + 18280896*b^3*c - 99161168*b^3 - 1105104*b^2*c^4 + 6376512*b^2*c^3 - 38567388*b^2*c^2 + 30004796*b^2*c + 79212824*b^2 + 43631*b*c^5 + 4251178*b*c^4 - 25364056*b*c^3 + 54620863*b*c^2 - 33522822*b*c - 21709474*b + 483*c^6 - 175138*c^5 - 324539*c^4 + 5592218*c^3 - 12128249*c^2 + 6893704*c + 1046370)/280908) * h1 + (-(55223*b*c^5 + 2781646*b*c^4 - 20533384*b*c^3 + 35409977*b*c^2 - 8950466*b*c - 62416*b - 883568*c^6 + 8267210*c^5 - 27511016*c^4 + 41760640*c^3 - 28315612*c^2 + 4800964*c + 765462)/280908) * h2 + (-(46046*b*c - 101629*b + 483*c^2 - 174655*c + 382925)/280908) * h3

private lemma rejectE_5_18 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, c) = 0) (h2 : locus 1 (c, 1, 1) = 0)
    (h3 : edge 1 b c (1, b, c) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(b^5 - 5*b^4 + 8*b^3*c^2 - 15*b^3*c + 4*b^3 - b^2*c^3 - 9*b^2*c^2 + 18*b^2*c + 8*b^2 + 18*b*c^4 - 52*b*c^3 - 90*b*c^2 + 180*b*c - 40*b - 8*c^5 + 90*c^4 - 283*c^3 + 271*c^2 - 102*c + 32)/27) * h1 + (-z*(b*c^4 + 57*b*c^3 - 54*b - 19*c^5 + 80*c^4 - 180*c^3 + 252*c^2 - 189*c + 54)/27) * h2 + (z*(b - c + 2)/27) * h3

private lemma rejectE_5_24 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, c) = 0) (h2 : locus 1 (c, c, 1) = 0)
    (h3 : edge 1 b c (1, b, c) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((161*b^5*c - 601*b^5 - 731*b^4*c + 2731*b^4 - 1127*b^3*c^3 + 3354*b^3*c^2 + 4226*b^3*c - 3933*b^3 + 9177*b^2*c^4 - 49830*b^2*c^3 + 69399*b^2*c^2 - 43978*b^2*c + 7592*b^2 - 19320*b*c^5 + 111216*b*c^4 - 157737*b*c^3 + 37902*b*c^2 + 23761*b*c - 5462*b + 33327*c^6 - 262596*c^5 + 715737*c^4 - 863843*c^3 + 462900*c^2 - 86779*c + 654)/972) * h1 + (-(14329*b*c^5 - 79366*b*c^4 + 166345*b*c^3 - 163853*b*c^2 + 71375*b*c - 6770*b - 18193*c^6 + 97258*c^5 - 196999*c^4 + 196553*c^3 - 104756*c^2 + 25661*c - 318)/972) * h2 + (-(161*b*c - 601*b + 805*c^2 - 3575*c + 2130)/972) * h3

private lemma rejectE_5_25 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, c) = 0) (h2 : locus 1 (c, c, b) = 0)
    (h3 : edge 1 b c (1, b, c) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*c*z*(b*c - c^2 + 3*c - 1)) * h1 + (-3*c*z*(b - c^2 + 3*c - 1)) * h2

private lemma rejectE_6_12 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, 1) = 0) (h2 : locus 1 (b, b, 1) = 0)
    (h3 : edge 1 b c (1, c, 1) (b, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(64*b*c^4 - 612*b*c^3 + 2124*b*c^2 - 3393*b*c + 2043*b - 24*c^5 + 148*c^4 - 108*c^3 - 648*c^2 + 1215*c - 603)/9) * h1 + (-z*(8*b^5 - 92*b^4 - 24*b^3*c^2 + 132*b^3*c + 152*b^3 + 88*b^2*c^3 - 456*b^2*c^2 + 432*b^2*c + 8*b^2 - 120*b*c^4 + 692*b*c^3 - 1011*b*c^2 + 63*b*c - 92*b + 120*c^5 - 1032*c^4 + 3091*c^3 - 3576*c^2 + 1077*c + 152)/9) * h2 + (4*z*(2*b + 6*c - 19)/9) * h3

private lemma rejectE_6_13 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, 1) = 0) (h2 : locus 1 (b, b, b) = 0)
    (h3 : edge 1 b c (1, c, 1) (b, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(135*b^3 - 135*b^2*c - 405*b^2 - 96*b*c^2 + 519*b*c + 558*b + 32*c^4 - 192*c^3 + 192*c^2 + 32*c - 192)/45) * h1 + (-2*z*(45*b^2*c - 165*b*c + 96*c + 32)/45) * h2 + (-32*z/45) * h3

private lemma rejectE_6_19 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, 1) = 0) (h2 : locus 1 (c, 1, b) = 0)
    (h3 : edge 1 b c (1, c, 1) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(b*c^4 + 57*b*c^3 - 54*b - 19*c^5 + 80*c^4 - 180*c^3 + 252*c^2 - 189*c + 54)/27) * h1 + (-z*(b^5 - 5*b^4 + 8*b^3*c^2 - 15*b^3*c + 4*b^3 - b^2*c^3 - 9*b^2*c^2 + 18*b^2*c + 8*b^2 + 18*b*c^4 - 52*b*c^3 - 90*b*c^2 + 180*b*c - 40*b - 8*c^5 + 90*c^4 - 283*c^3 + 271*c^2 - 102*c + 32)/27) * h2 + (z*(b - c + 2)/27) * h3

private lemma rejectE_7_11 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, b) = 0) (h2 : locus 1 (b, 1, c) = 0)
    (h3 : edge 1 b c (1, c, b) (b, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(b^5*c - 2*b^5 - 4*b^4*c^2 + 8*b^4*c + 3*b^4 + 7*b^3*c^3 - 14*b^3*c^2 - 8*b^3*c - 2*b^3 - 8*b^2*c^4 + 22*b^2*c^3 - 5*b^2*c^2 + 7*b^2*c + 5*b*c^5 - 16*b*c^4 + 4*b*c^3 + 7*b*c^2 - 5*b*c + b - 2*c^6 + 10*c^5 - 17*c^4 + 16*c^3 - 8*c^2 + c)) * h1 + (z*(b*c - 2*b - 2*c^2 + 6*c - 1)/27) * h3

private lemma rejectE_7_14 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, b) = 0) (h2 : locus 1 (b, b, c) = 0)
    (h3 : edge 1 b c (1, c, b) (b, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*z*(c - 1)*(b*c + 2*b - c^2 + c - 1)) * h1 + (-3*z*(c - 1)*(2*b - c^2 + 2*c - 1)) * h2

private lemma rejectE_7_17 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, b) = 0) (h2 : locus 1 (b, c, c) = 0)
    (h3 : edge 1 b c (1, c, b) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*c*z*(b*c - c^2 + 3*c - 1)) * h1 + (-3*c*z*(b - c^2 + 3*c - 1)) * h2

private lemma rejectE_8_16 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, c) = 0) (h2 : locus 1 (b, c, b) = 0)
    (h3 : edge 1 b c (1, c, c) (b, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((217*b*c^5 + 428*b*c^4 - 911*b*c^3 - 917*b*c^2 - 1543*b*c + 250*b - 155*c^6 + 177*c^5 + 324*c^4 - 505*c^3 + 861*c^2 - 333*c + 307)/81) * h1 + ((31*b^5*c - 116*b^5 - 186*b^4*c + 699*b^4 + 62*b^3*c^3 - 387*b^3*c^2 + 825*b^3*c - 940*b^3 + 93*b^2*c^4 - 720*b^2*c^3 + 1866*b^2*c^2 - 1656*b^2*c - 348*b^2 + 93*b*c^5 - 627*b*c^4 + 1416*b*c^3 - 1680*b*c^2 + 885*b*c + 705*b + 186*c^6 - 975*c^5 + 960*c^4 + 516*c^3 - 1542*c^2 + 3336*c - 696)/81) * h2 + (-(31*b*c - 116*b + 31*c^2 - 178*c + 235)/81) * h3

private lemma rejectE_8_21 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, c) = 0) (h2 : locus 1 (c, b, 1) = 0)
    (h3 : edge 1 b c (1, c, c) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(14329*b*c^5 - 79366*b*c^4 + 166345*b*c^3 - 163853*b*c^2 + 71375*b*c - 6770*b - 18193*c^6 + 97258*c^5 - 196999*c^4 + 196553*c^3 - 104756*c^2 + 25661*c - 318)/972) * h1 + ((161*b^5*c - 601*b^5 - 731*b^4*c + 2731*b^4 - 1127*b^3*c^3 + 3354*b^3*c^2 + 4226*b^3*c - 3933*b^3 + 9177*b^2*c^4 - 49830*b^2*c^3 + 69399*b^2*c^2 - 43978*b^2*c + 7592*b^2 - 19320*b*c^5 + 111216*b*c^4 - 157737*b*c^3 + 37902*b*c^2 + 23761*b*c - 5462*b + 33327*c^6 - 262596*c^5 + 715737*c^4 - 863843*c^3 + 462900*c^2 - 86779*c + 654)/972) * h2 + (-(161*b*c - 601*b + 805*c^2 - 3575*c + 2130)/972) * h3

private lemma rejectE_8_26 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, c) = 0) (h2 : locus 1 (c, c, c) = 0)
    (h3 : edge 1 b c (1, c, c) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-9/2) * h1 + (-(3*c - 11)/2) * h2

private lemma rejectE_9_10 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, 1) = 0) (h2 : locus 1 (b, 1, b) = 0)
    (h3 : edge 1 b c (b, 1, 1) (b, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((b - 3)/2) * h1 + (-(b - 2)/2) * h2

private lemma rejectE_9_18 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, 1) = 0) (h2 : locus 1 (c, 1, 1) = 0)
    (h3 : edge 1 b c (b, 1, 1) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*c*z*(c - 1)*(b - c + 2)) * h1 + (-6*b*z*(c - 1)) * h2

private lemma rejectE_9_24 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, 1) = 0) (h2 : locus 1 (c, c, 1) = 0)
    (h3 : edge 1 b c (b, 1, 1) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(8*b^4*c - 4*b^4 - 24*b^3*c^2 - 12*b^3*c + 12*b^3 + 48*b^2*c^3 - 48*b^2*c^2 + 12*b^2*c - 56*b*c^4 + 124*b*c^3 + 51*b*c^2 - 71*b*c + 4*b + 48*c^5 - 240*c^4 + 297*c^3 + 21*c^2 - 150*c + 36)/9) * h1 + (-2*z*(12*b*c^4 - 54*b*c^3 + 72*b*c^2 + 3*b*c - 36*b - 4*c^5 + 10*c^4 - 4*c^3 - 4*c^2 + 10*c - 4)/9) * h2 + (-4*z*(2*c - 1)/9) * h3

private lemma rejectE_9_25 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, 1) = 0) (h2 : locus 1 (c, c, b) = 0)
    (h3 : edge 1 b c (b, 1, 1) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(1512*b^4*c - 1512*b^4 - 4536*b^3*c^2 + 3024*b^3*c + 1512*b^3 + 6048*b^2*c^3 - 7560*b^2*c^2 + 4536*b^2*c - 3024*b^2 - 4144*b*c^4 + 9856*b*c^3 - 10665*b*c^2 + 4063*b*c + 1592*b + 1176*c^5 - 5376*c^4 + 11841*c^3 - 14703*c^2 + 9534*c - 2472)/27) * h1 + (2*z*(196*b*c^4 - 1372*b*c^3 + 4536*b*c^2 - 7081*b*c + 4072*b - 28*c^5 - 28*c^4 + 56*c^3 + 28*c^2 + 28*c - 56)/27) * h2 + (56*z*(c - 1)/27) * h3

private lemma rejectE_10_18 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, b) = 0) (h2 : locus 1 (c, 1, 1) = 0)
    (h3 : edge 1 b c (b, 1, b) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(8*b^5 - 92*b^4 - 24*b^3*c^2 + 132*b^3*c + 152*b^3 + 88*b^2*c^3 - 456*b^2*c^2 + 432*b^2*c + 8*b^2 - 120*b*c^4 + 692*b*c^3 - 1011*b*c^2 + 63*b*c - 92*b + 120*c^5 - 1032*c^4 + 3091*c^3 - 3576*c^2 + 1077*c + 152)/9) * h1 + (z*(64*b*c^4 - 612*b*c^3 + 2124*b*c^2 - 3393*b*c + 2043*b - 24*c^5 + 148*c^4 - 108*c^3 - 648*c^2 + 1215*c - 603)/9) * h2 + (4*z*(2*b + 6*c - 19)/9) * h3

private lemma rejectE_10_24 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, b) = 0) (h2 : locus 1 (c, c, 1) = 0)
    (h3 : edge 1 b c (b, 1, b) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((22*b^5*c - 83*b^5 - 244*b^4*c + 911*b^4 - 66*b^3*c^3 + 45*b^3*c^2 + 1681*b^3*c - 3470*b^3 - 242*b^2*c^4 + 1297*b^2*c^3 + 192*b^2*c^2 - 7819*b^2*c + 6023*b^2 - 330*b*c^5 + 2441*b*c^4 - 4639*b*c^3 - 2646*b*c^2 + 12793*b*c - 4361*b - 330*c^6 + 2685*c^5 - 6614*c^4 + 2122*c^3 + 10833*c^2 - 8419*c + 1004)/243) * h1 + (-(176*b*c^5 - 548*b*c^4 + 515*b*c^3 + 158*b*c^2 + 46*b*c - 1708*b + 66*c^6 - 709*c^5 + 2059*c^4 - 1171*c^3 - 2095*c^2 + 1294*c + 761)/243) * h2 + (-(22*b*c - 83*b - 66*c^2 + 181*c + 247)/243) * h3

private lemma rejectE_10_25 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, b) = 0) (h2 : locus 1 (c, c, b) = 0)
    (h3 : edge 1 b c (b, 1, b) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((2852*b^5*c - 4953*b^5 - 8587*b^4*c^2 - 1223*b^4*c + 28266*b^4 + 17205*b^3*c^3 - 15634*b^3*c^2 - 4606*b^3*c - 36720*b^3 - 20150*b^2*c^4 + 23925*b^2*c^3 + 74718*b^2*c^2 - 92449*b^2*c - 4953*b^2 + 14446*b*c^5 - 36928*b*c^4 - 6336*b*c^3 - 11323*b*c^2 + 82963*b*c + 30696*b - 2945*c^6 + 5470*c^5 + 30418*c^4 - 92076*c^3 + 13445*c^2 + 123932*c - 39150)/7290) * h1 + ((2883*b*c^5 - 17670*b*c^4 + 22071*b*c^3 + 13581*b*c^2 - 20394*b*c - 2430*b - 31*c^6 - 10254*c^5 + 62817*c^4 - 73113*c^3 - 63657*c^2 + 81504*c + 9720)/7290) * h2 + (-(2852*b*c - 4953*b - 31*c^2 - 10378*c + 18360)/7290) * h3

private lemma rejectE_11_14 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, c) = 0) (h2 : locus 1 (b, b, c) = 0)
    (h3 : edge 1 b c (b, 1, c) (b, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*z*(c - 1)*(b*c + 2*b - c^2 + c - 1)) * h1 + (-3*z*(c - 1)*(2*b - c^2 + 2*c - 1)) * h2

private lemma rejectE_11_17 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, c) = 0) (h2 : locus 1 (b, c, c) = 0)
    (h3 : edge 1 b c (b, 1, c) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*c*z*(b*c - c^2 + 3*c - 1)) * h1 + (-3*c*z*(b - c^2 + 3*c - 1)) * h2

private lemma rejectE_12_13 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, b, 1) = 0) (h2 : locus 1 (b, b, b) = 0)
    (h3 : edge 1 b c (b, b, 1) (b, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-9/2) * h1 + (-(3*b - 11)/2) * h2

private lemma rejectE_12_19 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, b, 1) = 0) (h2 : locus 1 (c, 1, b) = 0)
    (h3 : edge 1 b c (b, b, 1) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((2946944*b^5*c - 6504256*b^5 - 4389504*b^4*c^2 - 5105216*b^4*c + 32637520*b^4 + 4374048*b^3*c^3 + 2551440*b^3*c^2 + 229232*b^3*c - 59903152*b^3 - 2532208*b^2*c^4 - 2833744*b^2*c^3 + 12718932*b^2*c^2 - 10169108*b^2*c + 50931064*b^2 + 1034425*b*c^5 - 506334*b*c^4 - 608284*b*c^3 - 10293437*b*c^2 + 15469858*b*c - 20119056*b - 221536*c^6 + 257686*c^5 + 2047228*c^4 - 6380492*c^3 + 8392912*c^2 - 5234712*c + 2254834)/280908) * h1 + ((43631*b*c^5 - 169238*b*c^4 - 89848*b*c^3 + 1354751*b*c^2 - 3567062*b*c + 4512590*b + 483*c^6 - 175138*c^5 + 780565*c^4 - 722470*c^3 - 398941*c^2 + 1286860*c - 1973926)/280908) * h2 + (-(46046*b*c - 101629*b + 483*c^2 - 174655*c + 382925)/280908) * h3

private lemma rejectE_13_19 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, b, b) = 0) (h2 : locus 1 (c, 1, b) = 0)
    (h3 : edge 1 b c (b, b, b) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((45*b*c^2 - 108*b*c + 6*b + 45*c^3 - 378*c^2 + 729*c - 196)/8) * h1 + (-3*(15*b^4*c - 31*b^4 - 30*b^3*c^2 + 2*b^3*c + 124*b^3 + 45*b^2*c^3 - 93*b^2*c^2 - 30*b*c^4 + 62*b*c^3 + 180*b*c^2 - 327*b*c - 93*b + 15*c^5 - 91*c^4 + 124*c^3 + 45*c^2 - 78*c - 6)/8) * h2 + (3*(15*c - 31)/8) * h3

private lemma rejectE_14_17 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, b, c) = 0) (h2 : locus 1 (b, c, c) = 0)
    (h3 : edge 1 b c (b, b, c) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-3*c*z*(c - 1)*(2*b*c - c^2 + 2*c - 1)) * h1 + (3*c*z*(c - 1)*(2*b*c + b - c^2 + c - 1)) * h2

private lemma rejectE_15_20 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, c, 1) = 0) (h2 : locus 1 (c, 1, c) = 0)
    (h3 : edge 1 b c (b, c, 1) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((161*b^5*c - 601*b^5 - 731*b^4*c + 2731*b^4 - 1127*b^3*c^3 + 3354*b^3*c^2 + 4226*b^3*c - 3933*b^3 + 9177*b^2*c^4 - 49830*b^2*c^3 + 69399*b^2*c^2 - 43978*b^2*c + 7592*b^2 - 19320*b*c^5 + 111216*b*c^4 - 157737*b*c^3 + 37902*b*c^2 + 23761*b*c - 5462*b + 33327*c^6 - 262596*c^5 + 715737*c^4 - 863843*c^3 + 462900*c^2 - 86779*c + 654)/972) * h1 + (-(14329*b*c^5 - 79366*b*c^4 + 166345*b*c^3 - 163853*b*c^2 + 71375*b*c - 6770*b - 18193*c^6 + 97258*c^5 - 196999*c^4 + 196553*c^3 - 104756*c^2 + 25661*c - 318)/972) * h2 + (-(161*b*c - 601*b + 805*c^2 - 3575*c + 2130)/972) * h3

private lemma rejectE_15_22 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, c, 1) = 0) (h2 : locus 1 (c, b, b) = 0)
    (h3 : edge 1 b c (b, c, 1) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*z*(c - 1)*(b*c + 2*b - c^2 + c - 1)) * h1 + (-3*z*(c - 1)*(2*b - c^2 + 2*c - 1)) * h2

private lemma rejectE_15_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, c, 1) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (b, c, 1) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*c*z*(b*c - c^2 + 3*c - 1)) * h1 + (-3*c*z*(b - c^2 + 3*c - 1)) * h2

private lemma rejectE_16_21 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, c, b) = 0) (h2 : locus 1 (c, b, 1) = 0)
    (h3 : edge 1 b c (b, c, b) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-3*z*(c - 1)*(2*b - c^2 + 2*c - 1)) * h1 + (3*z*(c - 1)*(b*c + 2*b - c^2 + c - 1)) * h2

private lemma rejectE_16_26 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, c, b) = 0) (h2 : locus 1 (c, c, c) = 0)
    (h3 : edge 1 b c (b, c, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(3*b^5 - 17*b^4 - 30*b^3*c^2 + 44*b^3*c - 4*b^3 + 60*b^2*c^3 - 75*b^2*c^2 - 36*b^2*c + 78*b^2 - 45*b*c^4 + 86*b*c^3 + 84*b*c^2 - 177*b*c + 34*b + 12*c^5 - 38*c^4 - 44*c^3 + 144*c^2 - 127*c - 10)/27) * h1 + (-(153*b*c - 54*b - 63*c^2 + 66*c - 17)/27) * h2 + ((3*b + 12*c - 14)/27) * h3

private lemma rejectE_18_24 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, 1, 1) = 0) (h2 : locus 1 (c, c, 1) = 0)
    (h3 : edge 1 b c (c, 1, 1) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((c - 3)/2) * h1 + (-(c - 2)/2) * h2

private lemma rejectE_18_25 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, 1, 1) = 0) (h2 : locus 1 (c, c, b) = 0)
    (h3 : edge 1 b c (c, 1, 1) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(35*b*c^4 + 54*b*c^3 - 174*b*c^2 + 99*b*c - 27*b - 25*c^5 + 59*c^4 + 21*c^3 - 210*c^2 + 270*c - 81)/9) * h1 + (-z*(5*b^5 - 47*b^4 + 10*b^3*c^2 - 18*b^3*c + 125*b^3 + 15*b^2*c^3 - 111*b^2*c^2 + 141*b^2*c - 31*b^2 + 15*b*c^4 - 75*b*c^3 + 150*b*c^2 - 132*b*c - 164*b + 30*c^5 - 126*c^4 + 51*c^3 + 298*c^2 - 363*c + 44)/9) * h2 + (z*(5*b + 5*c - 22)/9) * h3

private lemma rejectE_20_22 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, 1, c) = 0) (h2 : locus 1 (c, b, b) = 0)
    (h3 : edge 1 b c (c, 1, c) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((217*b*c^5 + 428*b*c^4 - 911*b*c^3 - 917*b*c^2 - 1543*b*c + 250*b - 155*c^6 + 177*c^5 + 324*c^4 - 505*c^3 + 861*c^2 - 333*c + 307)/81) * h1 + ((31*b^5*c - 116*b^5 - 186*b^4*c + 699*b^4 + 62*b^3*c^3 - 387*b^3*c^2 + 825*b^3*c - 940*b^3 + 93*b^2*c^4 - 720*b^2*c^3 + 1866*b^2*c^2 - 1656*b^2*c - 348*b^2 + 93*b*c^5 - 627*b*c^4 + 1416*b*c^3 - 1680*b*c^2 + 885*b*c + 705*b + 186*c^6 - 975*c^5 + 960*c^4 + 516*c^3 - 1542*c^2 + 3336*c - 696)/81) * h2 + (-(31*b*c - 116*b + 31*c^2 - 178*c + 235)/81) * h3

private lemma rejectE_20_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, 1, c) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (c, 1, c) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(905*b*c^5 - 2828*b*c^4 - 3970*b*c^3 + 22991*b*c^2 - 26066*b*c + 8216*b - 724*c^6 + 5713*c^5 - 17833*c^4 + 25715*c^3 - 18641*c^2 + 9104*c - 192)/972) * h1 + ((181*b^5*c - 677*b^5 - 1571*b^4*c + 5875*b^4 - 181*b^3*c^3 + 612*b^3*c^2 + 3940*b^3*c - 13827*b^3 - 362*b^2*c^4 + 3700*b^2*c^3 - 9105*b^2*c^2 + 480*b^2*c + 2823*b^2 - 543*b*c^5 + 6064*b*c^4 - 24647*b*c^3 + 40068*b*c^2 - 20106*b*c + 14940*b - 724*c^6 + 7161*c^5 - 26363*c^4 + 42873*c^3 - 27225*c^2 + 9888*c - 138)/972) * h2 + (-(181*b*c - 677*b - 362*c^2 + 1231*c + 459)/972) * h3

private lemma rejectE_21_26 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, b, 1) = 0) (h2 : locus 1 (c, c, c) = 0)
    (h3 : edge 1 b c (c, b, 1) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-3*(15*b^5 - 101*b^4 - 15*b^3*c^2 - 38*b^3*c + 164*b^3 + 60*b^2*c^3 - 123*b^2*c^2 + 180*b^2*c + 45*b^2 - 45*b*c^4 + 22*b*c^3 + 360*b*c^2 - 312*b*c - 123*b + 30*c^5 - 161*c^4 + 164*c^3 + 270*c^2 - 471*c + 90)/8) * h1 + ((225*b*c^2 - 576*b*c + 288*b - 180*c^3 + 648*c^2 - 570*c + 32)/8) * h2 + (3*(15*b + 30*c - 41)/8) * h3

private lemma rejectE_22_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, b, b) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (c, b, b) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-3*c*z*(c - 1)*(2*b*c - c^2 + 2*c - 1)) * h1 + (3*c*z*(c - 1)*(2*b*c + b - c^2 + c - 1)) * h2

private lemma rejectE_24_25 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, c, 1) = 0) (h2 : locus 1 (c, c, b) = 0)
    (h3 : edge 1 b c (c, c, 1) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(905*b*c^5 - 2828*b*c^4 - 3970*b*c^3 + 22991*b*c^2 - 26066*b*c + 8216*b - 724*c^6 + 5713*c^5 - 17833*c^4 + 25715*c^3 - 18641*c^2 + 9104*c - 192)/972) * h1 + ((181*b^5*c - 677*b^5 - 1571*b^4*c + 5875*b^4 - 181*b^3*c^3 + 612*b^3*c^2 + 3940*b^3*c - 13827*b^3 - 362*b^2*c^4 + 3700*b^2*c^3 - 9105*b^2*c^2 + 480*b^2*c + 2823*b^2 - 543*b*c^5 + 6064*b*c^4 - 24647*b*c^3 + 40068*b*c^2 - 20106*b*c + 14940*b - 724*c^6 + 7161*c^5 - 26363*c^4 + 42873*c^3 - 27225*c^2 + 9888*c - 138)/972) * h2 + (-(181*b*c - 677*b - 362*c^2 + 1231*c + 459)/972) * h3

private lemma conflictE (b c z : ℝ) (i j : Fin 27)
    (h0 : invCondition 1 b c z = 0)
    (hi : locus 1 (profile b c i) = 0) (hj : locus 1 (profile b c j) = 0)
    (he : edge 1 b c (profile b c i) (profile b c j) = 0)
    (hlt : i < j) (hcol : colorsE i = colorsE j) : False := by
  fin_cases i
  · have possible : ∀ k : Fin 27, 0 < k → colorsE 0 = colorsE k → k = 7 ∨ k = 11 ∨ k = 14 ∨ k = 17 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectE_0_7 b c z h0 hi hj he
    · exact rejectE_0_11 b c z h0 hi hj he
    · exact rejectE_0_14 b c z h0 hi hj he
    · exact rejectE_0_17 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 1 < k → colorsE 1 = colorsE k → k = 8 ∨ k = 16 ∨ k = 21 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectE_1_8 b c z h0 hi hj he
    · exact rejectE_1_16 b c z h0 hi hj he
    · exact rejectE_1_21 b c z h0 hi hj he
    · exact rejectE_1_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 2 < k → colorsE 2 = colorsE k → k = 4 ∨ k = 15 ∨ k = 20 ∨ k = 22 ∨ k = 23 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl
    · exact rejectE_2_4 b c z h0 hi hj he
    · exact rejectE_2_15 b c z h0 hi hj he
    · exact rejectE_2_20 b c z h0 hi hj he
    · exact rejectE_2_22 b c z h0 hi hj he
    · exact rejectE_2_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 3 < k → colorsE 3 = colorsE k → k = 6 ∨ k = 12 ∨ k = 13 ∨ k = 19 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectE_3_6 b c z h0 hi hj he
    · exact rejectE_3_12 b c z h0 hi hj he
    · exact rejectE_3_13 b c z h0 hi hj he
    · exact rejectE_3_19 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 4 < k → colorsE 4 = colorsE k → k = 15 ∨ k = 20 ∨ k = 22 ∨ k = 23 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectE_4_15 b c z h0 hi hj he
    · exact rejectE_4_20 b c z h0 hi hj he
    · exact rejectE_4_22 b c z h0 hi hj he
    · exact rejectE_4_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 5 < k → colorsE 5 = colorsE k → k = 9 ∨ k = 10 ∨ k = 18 ∨ k = 24 ∨ k = 25 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl
    · exact rejectE_5_9 b c z h0 hi hj he
    · exact rejectE_5_10 b c z h0 hi hj he
    · exact rejectE_5_18 b c z h0 hi hj he
    · exact rejectE_5_24 b c z h0 hi hj he
    · exact rejectE_5_25 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 6 < k → colorsE 6 = colorsE k → k = 12 ∨ k = 13 ∨ k = 19 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectE_6_12 b c z h0 hi hj he
    · exact rejectE_6_13 b c z h0 hi hj he
    · exact rejectE_6_19 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 7 < k → colorsE 7 = colorsE k → k = 11 ∨ k = 14 ∨ k = 17 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectE_7_11 b c z h0 hi hj he
    · exact rejectE_7_14 b c z h0 hi hj he
    · exact rejectE_7_17 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 8 < k → colorsE 8 = colorsE k → k = 16 ∨ k = 21 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectE_8_16 b c z h0 hi hj he
    · exact rejectE_8_21 b c z h0 hi hj he
    · exact rejectE_8_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 9 < k → colorsE 9 = colorsE k → k = 10 ∨ k = 18 ∨ k = 24 ∨ k = 25 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectE_9_10 b c z h0 hi hj he
    · exact rejectE_9_18 b c z h0 hi hj he
    · exact rejectE_9_24 b c z h0 hi hj he
    · exact rejectE_9_25 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 10 < k → colorsE 10 = colorsE k → k = 18 ∨ k = 24 ∨ k = 25 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectE_10_18 b c z h0 hi hj he
    · exact rejectE_10_24 b c z h0 hi hj he
    · exact rejectE_10_25 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 11 < k → colorsE 11 = colorsE k → k = 14 ∨ k = 17 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectE_11_14 b c z h0 hi hj he
    · exact rejectE_11_17 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 12 < k → colorsE 12 = colorsE k → k = 13 ∨ k = 19 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectE_12_13 b c z h0 hi hj he
    · exact rejectE_12_19 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 13 < k → colorsE 13 = colorsE k → k = 19 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectE_13_19 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 14 < k → colorsE 14 = colorsE k → k = 17 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectE_14_17 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 15 < k → colorsE 15 = colorsE k → k = 20 ∨ k = 22 ∨ k = 23 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectE_15_20 b c z h0 hi hj he
    · exact rejectE_15_22 b c z h0 hi hj he
    · exact rejectE_15_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 16 < k → colorsE 16 = colorsE k → k = 21 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectE_16_21 b c z h0 hi hj he
    · exact rejectE_16_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 17 < k → colorsE 17 = colorsE k → False := by decide
    exact possible j hlt hcol
  · have possible : ∀ k : Fin 27, 18 < k → colorsE 18 = colorsE k → k = 24 ∨ k = 25 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectE_18_24 b c z h0 hi hj he
    · exact rejectE_18_25 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 19 < k → colorsE 19 = colorsE k → False := by decide
    exact possible j hlt hcol
  · have possible : ∀ k : Fin 27, 20 < k → colorsE 20 = colorsE k → k = 22 ∨ k = 23 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectE_20_22 b c z h0 hi hj he
    · exact rejectE_20_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 21 < k → colorsE 21 = colorsE k → k = 26 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectE_21_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 22 < k → colorsE 22 = colorsE k → k = 23 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectE_22_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 23 < k → colorsE 23 = colorsE k → False := by decide
    exact possible j hlt hcol
  · have possible : ∀ k : Fin 27, 24 < k → colorsE 24 = colorsE k → k = 25 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectE_24_25 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 25 < k → colorsE 25 = colorsE k → False := by decide
    exact possible j hlt hcol
  · have possible : ∀ k : Fin 27, 26 < k → colorsE 26 = colorsE k → False := by decide
    exact possible j hlt hcol

private def colorsI : Fin 27 → Fin 5 := ![2, 2, 0, 1, 3, 4, 1, 1, 2, 2, 1, 4, 0, 3, 0, 0, 4, 0, 1, 4, 4, 2, 3, 1, 0, 3, 3]

private lemma rejectI_0_1 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, 1) = 0) (h2 : locus b (1, 1, b) = 0)
    (h3 : edge b b c (1, 1, 1) (1, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((b - 3)/2) * h1 + (-(b - 2)/2) * h2

private lemma rejectI_0_8 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, 1) = 0) (h2 : locus b (1, c, c) = 0)
    (h3 : edge b b c (1, 1, 1) (1, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (b*z*(b - 4)*(b - 1)*(b - 4*c)) * h1 + (-b*z*(b - 4)*(b - 1)*(b - c - 3)) * h2

private lemma rejectI_0_9 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, 1) = 0) (h2 : locus b (b, 1, 1) = 0)
    (h3 : edge b b c (1, 1, 1) (b, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (2*b*c*z*(c - 2)*(c - 1)) * h1 + (-c*z*(c - 1)*(b^2 - b*c - 3*b + 5*c - 6)/2) * h2

private lemma rejectI_0_21 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, 1) = 0) (h2 : locus b (c, b, 1) = 0)
    (h3 : edge b b c (1, 1, 1) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((15*c - 28)/88) * h0 + ((16*b^5*c*z - 5*b^5*c + 16*b^5*z - 5*b^5 - 157*b^4*c*z + 35*b^4*c - 195*b^4*z + 45*b^4 + 695*b^3*c*z - 85*b^3*c + 716*b^3*z - 100*b^3 - 1449*b^2*c*z + 75*b^2*c - 1158*b^2*z + 60*b^2 + 1059*b*c*z + 964*b*z + 40*b + 15*c^3 - 60*c^2*z + 15*c^2 - 8*c*z - 215*c - 311*z - 140)/264) * h1 + ((16*b^5*c*z - 5*b^5*c - 112*b^5*z + 35*b^5 - 32*b^4*c^2*z + 10*b^4*c^2 + 173*b^4*c*z - 40*b^4*c + 499*b^4*z - 140*b^4 + 32*b^3*c^3*z - 10*b^3*c^3 - 173*b^3*c^2*z + 40*b^3*c^2 - 487*b^3*c*z + 80*b^3*c - 847*b^3*z + 125*b^3 - 16*b^2*c^4*z + 5*b^2*c^4 + 64*b^2*c^3*z - 20*b^2*c^3 + 369*b^2*c^2*z - 45*b^2*c^2 + 50*b^2*c*z + 50*b^2*c + 1113*b^2*z + 30*b^2 - 212*b*c^2*z + 10*b*c^2 + 40*b*c*z - 35*b*c - 805*b*z - 100*b + 45*c - 16*z + 185)/264) * h2 + ((16*z - 5)/264) * h3

private lemma rejectI_1_8 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, b) = 0) (h2 : locus b (1, c, c) = 0)
    (h3 : edge b b c (1, 1, b) (1, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-b*(4*c^2 - 17*c + 19)/4) * h0 + (-(30*b^6*c*z + b^6*c + 2*b^6*z - 3*b^6 - 285*b^5*c*z - 9*b^5*c - 13*b^5*z + 27*b^5 + 870*b^4*c*z + 25*b^4*c + 18*b^4*z - 75*b^4 - 780*b^3*c*z - 17*b^3*c - 86*b^3*z + 48*b^3 - 156*b^2*c*z - 18*b^2*c + 214*b^2*z + 69*b^2 + 12*b*c*z + 17*b*c - 78*b*z - 70*b - 2*c*z - 3*c + 8*z + 8)/4) * h1 + (-(30*b^6*c*z + b^6*c - 182*b^6*z - 3*b^6 - 54*b^5*c^2*z + b^5*c^2 + 159*b^5*c*z - 24*b^5*c + 969*b^5*z + 63*b^5 + 52*b^4*c^3*z - 4*b^4*c^3 - 167*b^4*c^2*z + 36*b^4*c^2 - 569*b^4*c*z - b^4*c - 1542*b^4*z - 215*b^4 - 26*b^3*c^4*z + 5*b^3*c^4 + 82*b^3*c^3*z - 39*b^3*c^3 + 331*b^3*c^2*z + 26*b^3*c^2 + 176*b^3*c*z + 106*b^3*c + 499*b^3*z + 117*b^3 - 2*b^2*c^5*z - 3*b^2*c^5 + 14*b^2*c^4*z + 21*b^2*c^4 - 18*b^2*c^3*z - 3*b^2*c^3 - 156*b^2*c^2*z - 132*b^2*c^2 - 6*b^2*c*z - b^2*c + 474*b^2*z + 233*b^2 - 6*b*c^3*z - 9*b*c^3 + 28*b*c^2*z + 42*b*c^2 + 18*b*c*z + 27*b*c - 190*b*z - 153*b - 6*c*z - 9*c + 14*z + 25)/4) * h2 + (-(30*b*z + b + 2*c*z + 3*c - 8*z - 12)/4) * h3

private lemma rejectI_1_9 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, b) = 0) (h2 : locus b (b, 1, 1) = 0)
    (h3 : edge b b c (1, 1, b) (b, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(7*b^2 - 12*b - 3)/3) * h1 + ((7*b - 26)/6) * h2

private lemma rejectI_1_21 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, b) = 0) (h2 : locus b (c, b, 1) = 0)
    (h3 : edge b b c (1, 1, b) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(c - 2)*(55*b^2 + 55*b*c - 284*b + 55*c^2 - 339*c + 360)/12) * h0 + ((5*b^7 + 55*b^6*c*z - 79*b^6 - 559*b^5*c*z + 503*b^5 + 1826*b^4*c*z - 10*b^4*c - 52*b^4*z - 1650*b^4 - 1562*b^3*c*z + 73*b^3*c + 309*b^3*z + 2989*b^3 - 1785*b^2*c*z - 153*b^2*c - 395*b^2*z - 3057*b^2 + 2061*b*c*z + 41*b*c + 71*b*z + 2042*b - 55*c^3 + 220*c^2*z + 449*c^2 - 696*c*z - 818*c + 67*z - 862)/12) * h1 + (-(-5*b^7 + 55*b^6*c*z + 5*b^6*c + 99*b^6 + 10*b^5*c^2 - 559*b^5*c*z - 89*b^5*c - 779*b^5 - 5*b^4*c^3 - 103*b^4*c^2 + 1826*b^4*c*z + 586*b^4*c - 52*b^4*z + 3110*b^4 - 55*b^3*c^4*z - 5*b^3*c^4 + 339*b^3*c^3*z + 54*b^3*c^3 - 580*b^3*c^2*z + 342*b^3*c^2 - 1370*b^3*c*z - 1736*b^3*c + 413*b^3*z - 6649*b^3 + 275*b^2*c^4*z + 19*b^2*c^4 - 1695*b^2*c^3*z - 133*b^2*c^3 + 2955*b^2*c^2*z - 416*b^2*c^2 - 2910*b^2*c*z + 2176*b^2*c - 805*b^2*z + 7377*b^2 - 220*b*c^4*z + 1356*b*c^3*z - 2595*b*c^2*z + 209*b*c^2 + 3654*b*c*z - 815*b*c - 63*b*z - 3530*b + 220*c^2*z - 696*c*z + 220*c + 67*z - 378)/12) * h2 + (-(5*b - 19)/12) * h3

private lemma rejectI_2_12 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (b, b, 1) = 0)
    (h3 : edge b b c (1, 1, c) (b, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((24244706767312457*b^2*c^6 - 496594768973895118*b^2*c^5 + 2243522543236344590*b^2*c^4 - 3085335399876391092*b^2*c^3 - 991148448739675172*b^2*c^2 + 2233647427131424570*b^2*c + 29518486573513718*b^2 - 22697111103312797*b*c^6 + 163518431552269901*b*c^5 - 444272964578650155*b*c^4 - 171650486477371549*b*c^3 + 4496627026175110561*b*c^2 - 3058702239229548982*b*c - 66040333051871900*b + 24244706767312457*c^7 - 367702669721250691*c^6 + 2550929689591423977*c^5 - 9651114594943107330*c^4 + 20170667843559669478*c^3 - 23029520420599342093*c^2 + 12585966317819963174*c - 2808143978518331902)/216446596502295000) * h1 + ((17676326062464030*b^6*c^2 - 31817386912435254*b^6*c - 49493712974899284*b^6 - 173186136748036306*b^5*c^3 + 272023738510858148*b^5*c^2 + 479984377509982954*b^5*c + 169114580325815128*b^5 - 133534886244643407*b^4*c^4 + 1510329511391270949*b^4*c^3 - 1586701322859335282*b^4*c^2 - 3061881195706016462*b^4*c + 929372044864245006*b^4 - 46941817870625254*b^3*c^5 + 98255759403429827*b^3*c^4 - 181405543597015587*b^3*c^3 - 4355323536549709934*b^3*c^2 + 8212724924350075218*b^3*c - 3708423262776439006*b^3 + 24244706767312457*b^2*c^6 - 630955064220154257*b^2*c^5 + 5248224626870970407*b^2*c^4 - 14709182175828741969*b^2*c^3 + 17313269229893474299*b^2*c^2 - 113328271786616224*b^2*c - 197251053508134060*b^2 - 371339166925768997*b*c^6 + 3245987408886649334*b*c^5 - 8206597530161278600*b*c^4 - 4212683168777758920*b*c^3 + 35520473836775008905*b*c^2 - 38023584465889134168*b*c + 8984471292375837772*b + 50037009198624574*c^7 - 1243593407325012352*c^6 + 9632331766771228777*c^5 - 34275624164275099145*c^4 + 65133244941664616922*c^3 - 66847360956719498297*c^2 + 33573331844690298526*c - 5639439691311515882)/216446596502295000) * h2 + (-(8838163031232015*b^2*c - 24746856487449642*b^2 - 95431231405250168*b*c^2 + 309218935335520974*b*c - 138164418224139214*b + 24244706767312457*c^3 - 125255602048126121*c^2 + 402867114383601518*c - 135375472911439731)/216446596502295000) * h3

private lemma rejectI_2_14 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (b, b, c) = 0)
    (h3 : edge b b c (1, 1, c) (b, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(c - 1)*(3*b^2*c - 5*b^2 - b*c^2 - 6*b*c + 2*b + 2*c^2)) * h1 + (-z*(c - 1)*(b^2*c - b*c^2 - 5*b + 2*c^2 - 4*c + 2)) * h2

private lemma rejectI_2_15 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (b, c, 1) = 0)
    (h3 : edge b b c (1, 1, c) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((c - 4)*(5*b*c + 2*c^2 + 4*c + 18)/72) * h0 + (-(324*b^2*c^6*z - 1188*b^2*c^5*z - b^2*c^5 - 5508*b^2*c^4*z + 61*b^2*c^4 + 10692*b^2*c^3*z - 20*b^2*c^3 - 9504*b^2*c^2*z - 404*b^2*c^2 + 36288*b^2*c*z + 517*b^2*c - 31104*b^2*z + 39*b^2 - 648*b*c^6*z + 3672*b*c^5*z - 14*b*c^5 - 10584*b*c^4*z - 410*b*c^4 + 28296*b*c^3*z + 1784*b*c^3 + 20736*b*c^2*z - 2600*b*c^2 - 57024*b*c*z + 1894*b*c + 15552*b*z - 3102*b - 324*c^7*z + 2376*c^6*z + c^6 - 3024*c^5*z + 98*c^5 + 648*c^4*z - 223*c^4 - 18252*c^3*z - 16*c^3 + 52272*c^2*z + 487*c^2 - 49248*c*z - 1250*c + 15552*z - 1257)/31104) * h1 + ((-16*b^6 - 24*b^5*c + 72*b^5 + 28*b^4*c^2 + 48*b^4*c - 4*b^4 + 1080*b^3*c^4*z - 5400*b^3*c^3*z + 38*b^3*c^3 + 4320*b^3*c^2*z - 302*b^3*c^2 + 470*b^3*c - 382*b^3 - 108*b^2*c^5*z - 2376*b^2*c^4*z - 13*b^2*c^4 + 18036*b^2*c^3*z - 202*b^2*c^3 - 31104*b^2*c^2*z + 826*b^2*c^2 + 15552*b^2*c*z - 1226*b^2*c + 447*b^2 - 324*b*c^6*z + 2592*b*c^5*z - 15*b*c^5 - 14796*b*c^4*z + 256*b*c^4 + 26352*b*c^3*z - 440*b*c^3 + 38016*b*c^2*z + 428*b*c^2 - 36288*b*c*z - 521*b*c - 15552*b*z + 436*b - 324*c^7*z + 2376*c^6*z + c^6 - 3024*c^5*z + 98*c^5 + 648*c^4*z - 1247*c^4 - 18252*c^3*z + 4080*c^3 + 52272*c^2*z - 5657*c^2 - 49248*c*z + 3710*c + 15552*z - 2281)/31104) * h2 + (1/1944) * h3

private lemma rejectI_2_17 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (b, c, c) = 0)
    (h3 : edge b b c (1, 1, c) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (b*c*z*(c - 1)*(2*b*c - 8*b - c^2 + 2*c + 7)/2) * h1 + (-c*z*(c - 1)*(b^2 + b*c - 8*b - c^2 + 2*c + 7)/2) * h2

private lemma rejectI_2_24 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (c, c, 1) = 0)
    (h3 : edge b b c (1, 1, c) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(9*b^4 - 81*b^3 + 242*b^2 + 164*b*c^4 - 517*b*c^3 + 523*b*c^2 - 119*b*c - 218*b + 48*c^5 - 708*c^4 + 1891*c^3 - 1860*c^2 + 639*c - 10)/16) * h1 + (-z*(3*b^6 + b^5*c - 37*b^5 + 12*b^4*c^2 - 24*b^4*c + 147*b^4 + 4*b^3*c^3 - 93*b^3*c^2 + 139*b^3*c - 161*b^3 + 20*b^2*c^3 - 39*b^2*c^2 + 157*b^2*c - 380*b^2 + 60*b*c^4 - 531*b*c^3 + 1623*b*c^2 - 2015*b*c + 1030*b + 16*c^5 - 188*c^4 + 1053*c^3 - 2236*c^2 + 1985*c - 630)/16) * h2 + (z*(3*b + c - 10)/16) * h3

private lemma rejectI_3_6 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (1, c, 1) = 0)
    (h3 : edge b b c (1, b, 1) (1, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(72*b^6*c^2 - 74*b^6*c - 146*b^6 - 162*b^5*c^3 - 270*b^5*c^2 + 1208*b^5*c + 8*b^5 + 126*b^4*c^4 + 721*b^4*c^3 - 2141*b^4*c^2 + 342*b^4*c - 8*b^4 - 45*b^3*c^5 - 316*b^3*c^4 + 1741*b^3*c^3 - 2258*b^3*c^2 + 1226*b^3*c - 868*b^3 - 63*b^2*c^5 - 2165*b^2*c^4 + 8405*b^2*c^3 - 11212*b^2*c^2 + 8978*b^2*c - 3464*b^2 + 171*b*c^6 + 1172*b*c^5 - 7407*b*c^4 + 12493*b*c^3 - 4555*b*c^2 - 11590*b*c + 11254*b - 45*c^7 - 505*c^6 + 4948*c^5 - 17682*c^4 + 35242*c^3 - 40831*c^2 + 25370*c - 6490)/4) * h1 + (-(261*b*c^5 - 2822*b*c^4 + 13706*b*c^3 - 35275*b*c^2 + 46276*b*c - 24242*b - 45*c^6 + 80*c^5 + 641*c^4 - 3746*c^3 + 9549*c^2 - 12398*c + 6486)/4) * h2 + ((36*b*c - 73*b - 45*c^2 + 125*c - 69)/4) * h3

private lemma rejectI_3_7 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (1, c, b) = 0)
    (h3 : edge b b c (1, b, 1) (1, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (c^2*z*(4*b - c)*(c - 3)) * h1 + (-z*(b^3*c - b^3 - b^2*c^2 + b^2 + 4*b*c^2 - 12*b*c - c^2 + 3*c)) * h2

private lemma rejectI_3_10 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (b, 1, b) = 0)
    (h3 : edge b b c (1, b, 1) (b, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((5*b^2 - 9*b - 13)/6) * h1 + (-(5*b - 19)/6) * h2

private lemma rejectI_3_18 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (c, 1, 1) = 0)
    (h3 : edge b b c (1, b, 1) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-c^2 + 4*c - 1) * h0 + (-(-b^3 + 4*b^2 + 6*b*c^6*z - 60*b*c^5*z + 210*b*c^4*z - 300*b*c^3*z - b*c^3 + 144*b*c^2*z + 5*b*c^2 - 3*b*c + 3*c^2 - 12*c - 1)/3) * h1 + (-(-2*b^5*c - 2*b^5 - 3*b^4*c^2 + 12*b^4*c + 15*b^4 + 3*b^3*c^3*z - 3*b^3*c^3 - 15*b^3*c^2*z + 14*b^3*c^2 + 15*b^3*c*z - 11*b^3*c - 3*b^3*z - 31*b^3 - 6*b^2*c^4*z - b^2*c^4 + 27*b^2*c^3*z + 9*b^2*c^3 - 15*b^2*c^2*z - 11*b^2*c^2 - 9*b^2*c*z - 25*b^2*c + 3*b^2*z + 7*b^2 + 24*b*c^4*z - 150*b*c^3*z + 264*b*c^2*z - 3*b*c^2 - 138*b*c*z + 10*b*c + 13*b - 6*c^4*z + 36*c^3*z - 66*c^2*z + 36*c*z + c + 8)/3) * h2 + (-1/3) * h3

private lemma rejectI_3_23 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (c, b, c) = 0)
    (h3 : edge b b c (1, b, 1) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(b^2 - 5*b*c^3 + 22*b*c^2 - 29*b*c + 5*b + c^4 - 4*c^3 + 5*c^2)) * h1 + (-z*(b^3*c - b^3 - b^2*c^2 + b^2*c - b^2 + 4*b*c^2 - 16*b*c + 19*b - c^2 + 4*c - 5)) * h2

private lemma rejectI_4_13 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, b) = 0) (h2 : locus b (b, b, b) = 0)
    (h3 : edge b b c (1, b, b) (b, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-c*z*(c - 1)*(b^2 - 5*b + c + 1)) * h1 + (b*c*z*(c - 3)*(c - 1)) * h2

private lemma rejectI_4_22 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, b) = 0) (h2 : locus b (c, b, b) = 0)
    (h3 : edge b b c (1, b, b) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(b^2*c*z - 4*b^2*z + 10)/10) * h0 + (-z*(3*b^4*c^3*z - 15*b^4*c^2*z + 12*b^4*c*z - b^4*c - 3*b^3*c^4*z + 9*b^3*c^3*z - b^3*c^3 + 18*b^3*c^2*z + b^3*c^2 - 24*b^3*c*z + 10*b^3*c - b^3 + 6*b^2*c^4*z - b^2*c^4 - 36*b^2*c^3*z + 8*b^2*c^3 + 54*b^2*c^2*z + 21*b^2*c^2 - 24*b^2*c*z - 53*b^2*c + 4*b^2 - b*c^5 + 6*b*c^4*z + 7*b*c^4 - 48*b*c^3*z - 38*b*c^3 + 60*b*c^2*z - 32*b*c^2 + 90*b*c*z + 27*b*c + 2*b - c^6 + 4*c^5 + 18*c^4*z - 6*c^4 - 90*c^3*z + 57*c^3 + 126*c^2*z - 68*c^2 - 54*c*z + 14*c + 3)/30) * h1 + (-b*z*(-c^4 + 2*c^3 + 18*c^2*z - c^2 - 54*c*z + 13*c - 1)/10) * h2 + (-z/30) * h3

private lemma rejectI_4_25 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, b) = 0) (h2 : locus b (c, c, b) = 0)
    (h3 : edge b b c (1, b, b) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(b - 3)*(4205*b*c - 842*b - 841*c^2 - 3)/9) * h0 + (-(189225*b^4*c^3*z + 58*b^4*c^3 - 227115*b^4*c^2*z - 258*b^4*c^2 + 37890*b^4*c*z - 316*b^4*c - 227070*b^3*c^4*z + 58*b^3*c^4 - 681165*b^3*c^3*z - 693*b^3*c^3 + 1097550*b^3*c^2*z + 1648*b^3*c^2 - 189315*b^3*c*z + 2241*b^3*c - 158*b^3 + 37845*b^2*c^5*z + 1097505*b^2*c^4*z - 290*b^2*c^4 - 567765*b^2*c^3*z + 2131*b^2*c^3 - 718470*b^2*c^2*z - 2219*b^2*c^2 + 150885*b^2*c*z - 4382*b^2*c + 632*b^2 - 189225*b*c^5*z + 58*b*c^5 - 719055*b*c^4*z - 55*b*c^4 + 1059165*b*c^3*z - 1451*b*c^3 - 151425*b*c^2*z - 1495*b*c^2 + 540*b*c*z + 1466*b*c - 158*b + 151380*c^5*z - 58*c^5 - 151380*c^4*z + 287*c^4 + 540*c^3*z + 651*c^3 - 540*c^2*z - 163*c^2 + 37845*c + 15)/405) * h1 + (-(87*b^2*c^4 - 416*b^2*c^3 - 55*b^2*c^2 - 30*b^2*c - 15*b^2 - 232*b*c^4 + 1206*b*c^3 + 316*b*c^2 - 37845*b + 29*c^5 - 158*c^4 + 113535)/405) * h2 + ((29*c - 158)/405) * h3

private lemma rejectI_4_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, b) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (1, b, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-c*z*(b^2*c - b^2 - b*c^2 - b*c + 2*b + 4*c^2 - 10*c + 2)) * h1 + (2*b*c*z*(c - 3)) * h2

private lemma rejectI_5_11 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, c) = 0) (h2 : locus b (b, 1, c) = 0)
    (h3 : edge b b c (1, b, c) (b, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((455434361792*b*c^2 + 839439427704*b*c - 2553534455744*c^3 + 9560132023132*c^2 - 5605748613564*c - 9075641774337)/9075641774337) * h0 + ((69560122368*b^2*c^6 + 14392648955565*b^2*c^5*z - 4567294085504*b^2*c^5 - 33532551776817*b^2*c^4*z + 33560571118248*b^2*c^4 + 35130026624400*b^2*c^3*z - 91514762552336*b^2*c^3 - 91588945404699*b^2*c^2*z + 12717017348048*b^2*c^2 + 87653839058145*b^2*c*z + 89525046908432*b^2*c + 22823417306430*b^2*z - 89955828882072*b^2 - 139120244736*b*c^6 - 55866017268954*b*c^5*z + 9134588171008*b*c^5 + 126230626873926*b*c^4*z - 66100927108432*b*c^4 - 4257537899652*b*c^3*z + 121591897168416*b*c^3 + 75637285867620*b*c^2*z + 125008108102912*b*c^2 - 329215944424194*b*c*z - 269552380680880*b*c + 117714717325206*b*z + 155809784454480*b - 69560122368*c^7 + 8589161146131*c^6*z + 4636854207872*c^6 - 137435223677310*c^5*z - 37849624714280*c^5 + 463633142073957*c^4*z + 108150986361016*c^4 - 441884691461637*c^3*z - 52826180356672*c^3 - 201910349786940*c^2*z - 139484627119184*c^2 + 466985313718947*c*z + 192017759125568*c - 140538134631636*z - 37256100457248)/163361551938066) * h1 + (-(-556480978944*b^6*c^2 + 52317652144536*b^6*c*z + 33941441448960*b^6*c - 156952956433608*b^6*z - 106010315005248*b^6 - 556480978944*b^5*c^3 + 52317652144536*b^5*c^2*z + 35796378045440*b^5*c^2 - 331345130248728*b^5*c*z - 219148453168448*b^5*c + 523176521445360*b^5*z + 353367716684160*b^5 - 278240489472*b^4*c^4 + 26158826072268*b^4*c^3*z + 19103897810432*b^4*c^3 - 279027478104192*b^4*c^2*z - 183299510049952*b^4*c^2 + 619092217043676*b^4*c*z + 417686688003104*b^4*c - 52317652144536*b^4*z - 35336771668416*b^4 - 139120244736*b^3*c^5 + 8980503780006*b^3*c^4*z + 9412828660480*b^3*c^4 - 129890371609170*b^3*c^3*z - 84323730035536*b^3*c^3 + 386857932897222*b^3*c^2*z + 249991456218048*b^3*c^2 - 65397065180670*b^3*c*z - 51845280792528*b^3*c - 863241260384844*b^3*z - 583056732528864*b^3 - 69560122368*b^2*c^6 + 31570971247827*b^2*c^5*z + 4775974452608*b^2*c^5 - 162705662642880*b^2*c^4*z - 46497292028712*b^2*c^4 + 362801825150724*b^2*c^3*z + 142999642802056*b^2*c^3 + 30945522546549*b^2*c^2*z + 12398537592504*b^2*c^2 - 846826438582872*b^2*c*z - 514707290321400*b^2*c + 235429434650412*b^2*z + 159015472507872*b^2 + 139120244736*b*c^6 - 90222661853478*b*c^5*z - 9134588171008*b*c^5 + 495526197876210*b*c^4*z + 66889275161936*b*c^4 - 777515048589582*b*c^3*z - 168098909780768*b*c^3 - 207380243341206*b*c^2*z - 66774265193872*b*c^2 + 841180016630736*b*c*z + 323307494508176*b*c + 104635304289072*b*z + 70673543336832*b - 69560122368*c^7 + 8589161146131*c^6*z + 4497733963136*c^6 - 120256901385048*c^5*z - 28784596665640*c^5 + 214530178157730*c^4*z + 46084059066600*c^4 + 107432566238871*c^3*z + 68126534442168*c^3 - 201575395466928*c^2*z - 49315617301448*c^2 - 43598043453780*c*z + 71223610283896*c - 26158826072268*z - 17668385834208)/163361551938066) * h2 + (2*(-23186707456*c^2 + 2179902172689*c*z + 1414226727040*c - 6539706518067*z - 4417096458552)/81680775969033) * h3

private lemma rejectI_5_16 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, c) = 0) (h2 : locus b (b, c, b) = 0)
    (h3 : edge b b c (1, b, c) (b, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((-2268973*b*c^3 + 596241*b*c^2*z + 6613075*b*c^2 + 1254834*b*c + 2268973*c^4 - 596241*c^3*z - 4344102*c^3 - 596241*c^2*z - 7867909*c^2 - 93528)/93528) * h0 + ((-183786813*b^2*c^6*z + 3203256*b^2*c^6 + 48295521*b^2*c^5*z^2 + 351030510*b^2*c^5*z + 49248934*b^2*c^5 + 48295521*b^2*c^4*z^2 + 1024164405*b^2*c^4*z - 126315448*b^2*c^4 - 96591042*b^2*c^3*z^2 - 446106852*b^2*c^3*z - 68684049*b^2*c^3 + 480956049*b^2*c^2*z + 108736824*b^2*c^2 - 409407129*b^2*c*z - 8649081*b^2*c + 11363652*b^2*z - 608423508*b^2 - 533876*b*c^7 + 1286647983*b*c^6*z - 46469269*b*c^6 - 338068647*b*c^5*z^2 - 5213068794*b*c^5*z - 68884655*b*c^5 + 386364168*b*c^4*z^2 + 3292009533*b*c^4*z + 538628720*b*c^4 - 48295521*b*c^3*z^2 - 1590584769*b*c^3*z - 186536049*b*c^3 - 974643597*b*c^2*z - 78985956*b*c^2 + 536301243*b*c*z - 219025044*b*c + 36931869*b*z + 1211843619*b - 183786813*c^7*z + 10677520*c^7 + 48295521*c^6*z^2 + 716640048*c^6*z + 19660676*c^6 - 48295521*c^5*z^2 - 331744653*c^5*z - 96018468*c^5 + 442971990*c^4*z - 84941346*c^4 + 357323724*c^3*z + 183055068*c^3 - 11363652*c^2*z - 180100557*c^2 + 144886563*c*z + 2095688700*c - 48295521*z - 637300629)/7575768) * h1 + ((3203256*b^4*c^4 - 841752*b^4*c^3*z - 2537038*b^4*c^3 + 32898474*b^4*c^2*z - 13137761*b^4*c^2 + 74389833*b^4*c*z - 391713*b^4*c + 34722270*b^4*z + 4193406*b^4 - 183786813*b^3*c^5*z + 3737132*b^3*c^5 + 48295521*b^3*c^4*z^2 + 718463844*b^3*c^4*z - 25471649*b^3*c^4 - 48295521*b^3*c^3*z^2 - 389720322*b^3*c^3*z + 22448552*b^3*c^3 - 251298045*b^3*c^2*z + 53767882*b^3*c^2 - 271570239*b^3*c*z - 28109634*b^3*c - 17361135*b^3*z - 2096703*b^3 + 367573626*b^2*c^6*z - 8008140*b^2*c^6 - 96591042*b^2*c^5*z^2 - 701640144*b^2*c^5*z - 21685895*b^2*c^5 - 96591042*b^2*c^4*z^2 - 2084629365*b^2*c^4*z + 113636376*b^2*c^4 + 193182084*b^2*c^3*z^2 + 1551761469*b^2*c^3*z - 20852720*b^2*c^3 + 185150367*b^2*c^2*z - 40153883*b^2*c^2 + 100589364*b^2*c*z + 15921129*b^2*c - 17361135*b^2*z - 2096703*b^2 + 533876*b*c^7 - 1470434796*b*c^6*z + 31520741*b*c^6 + 386364168*b*c^5*z^2 + 5752656045*b*c^5*z + 38370003*b*c^5 - 386364168*b*c^4*z^2 - 3148977546*b*c^4*z - 286873664*b*c^4 + 231551946*b*c^3*z - 46976741*b*c^3 + 1311975711*b*c^2*z + 121187598*b*c^2 - 190341171*b*c*z + 589553181*b*c + 183786813*c^7*z - 10677520*c^7 - 48295521*c^6*z^2 - 716640048*c^6*z + 14507388*c^6 + 48295521*c^5*z^2 + 322765965*c^5*z - 5074076*c^5 - 72601110*c^4*z + 129671010*c^4 - 357323724*c^3*z - 183055068*c^3 + 11363652*c^2*z + 363887370*c^2 - 193182084*c*z - 2447560962*c)/7575768) * h2 + ((-533876*c^2 + 140292*c*z + 1579571*c - 5787045*z - 698901)/7575768) * h3

private lemma rejectI_5_19 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, c) = 0) (h2 : locus b (c, 1, b) = 0)
    (h3 : edge b b c (1, b, c) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((-100555*b^2*c^2 + 803439*b^2*c*z + 431145*b^2*c - 803439*b^2*z - 507170*b^2 + 200005*b*c^3 - 1598049*b*c^2*z - 656260*b*c^2 - 88290*b*c*z + 145010*b*c + 1606878*b*z + 1014340*b - 99450*c^4 + 794610*c^3*z + 226220*c^3 + 882900*c^2*z + 256685*c^2 - 715149*c*z - 46415*c - 803439*z - 2732078)/2224908) * h0 + ((-1105*b^6*c^2 + 8829*b^6*c*z + 3815*b^6*c - 79461*b^6*z - 2120*b^6 - 100555*b^5*c^3*z + 1105*b^5*c^3 + 803439*b^5*c^2*z^2 + 522871*b^5*c^2*z + 16075*b^5*c^2 - 1606878*b^5*c*z^2 - 929486*b^5*c*z - 69455*b^5*c + 803439*b^5*z^2 + 1840349*b^5*z + 68360*b^5 + 300560*b^4*c^4*z + 8840*b^4*c^4 - 2401488*b^4*c^3*z^2 - 1358042*b^4*c^3*z - 81350*b^4*c^3 + 2313198*b^4*c^2*z^2 + 2249707*b^4*c^2*z + 125045*b^4*c^2 + 2498607*b^4*c*z^2 - 1727872*b^4*c*z + 182015*b^4*c - 2410317*b^4*z^2 - 8982015*b^4*z - 489480*b^4 - 299455*b^3*c^5*z - 2210*b^3*c^5 + 2392659*b^3*c^4*z^2 + 999588*b^3*c^4*z - 53145*b^3*c^4 + 176580*b^3*c^3*z^2 + 412133*b^3*c^3*z + 563605*b^3*c^3 - 4802976*b^3*c^2*z^2 - 9469521*b^3*c^2*z - 1518535*b^3*c^2 - 176580*b^3*c*z^2 + 20653130*b^3*c*z + 1069975*b^3*c + 2410317*b^3*z^2 + 18305439*b^3*z + 1030200*b^3 + 99450*b^2*c^6*z - 17680*b^2*c^6 - 794610*b^2*c^5*z^2 - 185511*b^2*c^5*z + 188115*b^2*c^5 - 79461*b^2*c^4*z^2 - 1809481*b^2*c^4*z - 717955*b^2*c^4 - 2507436*b^2*c^3*z^2 + 7424633*b^2*c^3*z + 811235*b^2*c^3 + 7310412*b^2*c^2*z^2 + 421935*b^2*c^2*z + 948300*b^2*c^2 - 3125466*b^2*c*z^2 - 34323515*b^2*c*z - 2049225*b^2*c - 803439*b^2*z^2 - 14253923*b^2*z - 813320*b^2 - 8840*b*c^7 + 270637*b*c^6*z + 90190*b*c^6 - 1598049*b*c^5*z^2 - 2871504*b*c^5*z - 400875*b*c^5 + 8723052*b*c^4*z^2 + 10483323*b*c^4*z + 1038130*b*c^4 - 11795544*b*c^3*z^2 - 17391540*b*c^3*z - 1417995*b*c^3 + 88290*b*c^2*z^2 + 13538939*b*c^2*z + 524085*b*c^2 + 4820634*b*c*z^2 + 18326019*b*c*z + 778265*b*c + 1986525*b*z + 52530*b - 1105*c^6 + 8829*c^5*z - 10550*c^5 + 235321*c^4*z + 76205*c^4 - 1598049*c^3*z^2 - 2509872*c^3*z - 231030*c^3 + 3928905*c^2*z^2 + 3995903*c^2*z + 313685*c^2 - 2410317*c*z^2 - 6245025*c*z - 293595*c + 1986525*z + 484420)/2224908) * h1 + ((-88290*b^6*z - 7040*b^6 + 971190*b^5*z + 77440*b^5 - 3355020*b^4*z - 267520*b^4 + 3884760*b^3*z + 309760*b^3 - 2030670*b^2*z - 161920*b^2 - 99450*b*c^6*z - 30940*b*c^6 + 794610*b*c^5*z^2 + 1473457*b*c^5*z + 237210*b*c^5 - 7107345*b*c^4*z^2 - 8403000*b*c^4*z - 785780*b*c^4 + 15715620*b*c^3*z^2 + 18844208*b*c^3*z + 1362600*b*c^3 - 9641268*b*c^2*z^2 - 21042366*b*c^2*z - 1315155*b*c^2 + 8890803*b*c*z + 823230*b*c + 706320*b*z + 56320*b + 8840*c^7 - 270637*c^6*z - 70300*c^6 + 1598049*c^5*z^2 + 2112567*c^5*z + 240490*c^5 - 3928905*c^4*z^2 - 5143673*c^4*z - 436910*c^4 + 2410317*c^3*z^2 + 5406270*c^3*z + 446185*c^3 - 2375001*c^2*z - 304920*c^2 - 1236060*c*z - 83735*c - 891729*z - 514210)/2224908) * h2 + (-(-1105*c^2 + 8829*c*z + 4920*c - 88290*z - 7040)/2224908) * h3

private lemma rejectI_5_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, c) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (1, b, c) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (3*(2706162*b*c - 1437901*b + 1454886*c^2 - 11227353*c + 5548209)/125732) * h0 + ((-318372*b^5*c^2 + 20640*b^5*c*z + 934390*b^5*c + 10320*b^5*z + 626381*b^5 - 795930*b^4*c^3 + 8170086*b^4*c^2*z + 4723765*b^4*c^2 - 12535389*b^4*c*z - 3876020*b^4*c + 4231143*b^4*z - 5011048*b^4 - 955116*b^3*c^4 - 3691908*b^3*c^3*z + 6942006*b^3*c^3 - 33939414*b^3*c^2*z - 12845992*b^3*c^2 + 58465812*b^3*c*z - 3682004*b^3*c - 20751930*b^3*z + 12368434*b^3 - 636744*b^2*c^5 - 4323378*b^2*c^4*z + 5052500*b^2*c^4 + 33516939*b^2*c^3*z - 11295584*b^2*c^3 - 12197409*b^2*c^2*z - 560462*b^2*c^2 - 33310539*b^2*c*z + 23664018*b^2*c + 16510467*b^2*z - 7506209*b^2 + 159186*b*c^6 - 4374978*b*c^5*z + 647107*b*c^5 + 27924333*b*c^4*z - 4851862*b*c^4 - 59659416*b*c^3*z - 3014171*b*c^3 + 49066650*b*c^2*z + 10181282*b*c^2 - 13116549*b*c*z - 8872964*b*c - 51600*b*z + 1022612*b - 159186*c^7 + 10320*c^6*z + 785567*c^6 - 621150*c^5*z - 308009*c^5 + 3668205*c^4*z - 1730320*c^4 - 7334475*c^3*z + 2834259*c^3 + 6117975*c^2*z - 574566*c^2 - 1882155*c*z - 3443655*c + 51600*z - 9483937)/125732) * h1 + ((10320*b^5*z + 626381*b^5 - 82560*b^4*z - 5011048*b^4 + 175440*b^3*z + 10648477*b^3 - 30960*b^2*z - 1879143*b^2 - 318372*b*c^6 + 4385298*b*c^5*z + 456832*b*c^5 - 19836807*b*c^4*z + 2495161*b*c^4 + 22902729*b*c^3*z + 2505524*b*c^3 - 7301580*b*c^2*z + 1283851*b*c^2 + 20640*b*c*z + 1228295*b*c - 41280*b*z - 6819227*b + 159186*c^7 - 10320*c^6*z - 467195*c^6 + 600510*c^5*z - 785567*c^5 - 2456865*c^4*z + 626381*c^4 + 1820235*c^3*z - 795930*c^3 - 20640*c^2*z - 1643675*c^2 + 20640*c*z + 952235*c + 10320*z + 17396740)/125732) * h2 + (-(-3702*c + 240*z + 14567)/2924) * h3

private lemma rejectI_6_7 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, 1) = 0) (h2 : locus b (1, c, b) = 0)
    (h3 : edge b b c (1, c, 1) (1, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(6*b^6 - 36*b^5 + 45*b^4 + 33*b^3 - 24*b^2 + 2*b*c^3 - 54*b*c^2 + 142*b*c + 3*b + 11*c^3 - 34*c^2 - c)/3) * h1 + (-z*(6*b^6 - 2*b^5*c - 32*b^5 + 53*b^4 + 2*b^3*c^2 + 8*b^3*c - 6*b^3 + 5*b^2*c^2 - 29*b^2*c - 11*b^2 - 2*b*c^3 + 25*b*c^2 - 40*b*c - 42*b - 11*c^3 + 56*c^2 - 78*c + 32)/3) * h2 + (z*(3*b - c)/3) * h3

private lemma rejectI_6_10 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, 1) = 0) (h2 : locus b (b, 1, b) = 0)
    (h3 : edge b b c (1, c, 1) (b, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((24244706767312457*b^2*c^6 - 496594768973895118*b^2*c^5 + 2243522543236344590*b^2*c^4 - 3085335399876391092*b^2*c^3 - 991148448739675172*b^2*c^2 + 2233647427131424570*b^2*c + 29518486573513718*b^2 - 22697111103312797*b*c^6 + 163518431552269901*b*c^5 - 444272964578650155*b*c^4 - 171650486477371549*b*c^3 + 4496627026175110561*b*c^2 - 3058702239229548982*b*c - 66040333051871900*b + 24244706767312457*c^7 - 367702669721250691*c^6 + 2550929689591423977*c^5 - 9651114594943107330*c^4 + 20170667843559669478*c^3 - 23029520420599342093*c^2 + 12585966317819963174*c - 2808143978518331902)/216446596502295000) * h1 + ((17676326062464030*b^6*c^2 - 31817386912435254*b^6*c - 49493712974899284*b^6 - 173186136748036306*b^5*c^3 + 272023738510858148*b^5*c^2 + 479984377509982954*b^5*c + 169114580325815128*b^5 - 133534886244643407*b^4*c^4 + 1510329511391270949*b^4*c^3 - 1586701322859335282*b^4*c^2 - 3061881195706016462*b^4*c + 929372044864245006*b^4 - 46941817870625254*b^3*c^5 + 98255759403429827*b^3*c^4 - 181405543597015587*b^3*c^3 - 4355323536549709934*b^3*c^2 + 8212724924350075218*b^3*c - 3708423262776439006*b^3 + 24244706767312457*b^2*c^6 - 630955064220154257*b^2*c^5 + 5248224626870970407*b^2*c^4 - 14709182175828741969*b^2*c^3 + 17313269229893474299*b^2*c^2 - 113328271786616224*b^2*c - 197251053508134060*b^2 - 371339166925768997*b*c^6 + 3245987408886649334*b*c^5 - 8206597530161278600*b*c^4 - 4212683168777758920*b*c^3 + 35520473836775008905*b*c^2 - 38023584465889134168*b*c + 8984471292375837772*b + 50037009198624574*c^7 - 1243593407325012352*c^6 + 9632331766771228777*c^5 - 34275624164275099145*c^4 + 65133244941664616922*c^3 - 66847360956719498297*c^2 + 33573331844690298526*c - 5639439691311515882)/216446596502295000) * h2 + (-(8838163031232015*b^2*c - 24746856487449642*b^2 - 95431231405250168*b*c^2 + 309218935335520974*b*c - 138164418224139214*b + 24244706767312457*c^3 - 125255602048126121*c^2 + 402867114383601518*c - 135375472911439731)/216446596502295000) * h3

private lemma rejectI_6_18 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, 1) = 0) (h2 : locus b (c, 1, 1) = 0)
    (h3 : edge b b c (1, c, 1) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-2*b*c^2*z*(c - 4)*(c - 2)/3) * h1 + (-z*(3*b^3*c - 3*b^3 - 6*b^2*c^2 + 3*b^2*c + 3*b^2 + 4*b*c^3 - 10*b*c - 2*c^4 + 8*c^3 - 10*c^2 + 4*c)/3) * h2

private lemma rejectI_6_23 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, 1) = 0) (h2 : locus b (c, b, c) = 0)
    (h3 : edge b b c (1, c, 1) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((31774682*b^6 + 100787276*b^5 + 638155407*b^4 + 4068418949*b^3 + 24838551842*b^2 + 2889063444*b*c^6 - 33603557662*b*c^5 + 170421953221*b*c^4 - 488313017096*b*c^3 + 854527172885*b*c^2 - 898862466723*b*c + 150050375553*b - 1093904016*c^7 + 9956589064*c^6 - 40783028878*c^5 + 100110095133*c^4 - 157658745776*c^3 + 153197179543*c^2 - 544804285*c + 37055552)/27354) * h1 + ((17824142*b^6*c^2 - 40681420*b^6*c - 26730880*b^6 - 81227618*b^5*c^3 + 152828346*b^5*c^2 + 391308786*b^5*c - 664130352*b^5 + 126806952*b^4*c^4 + 5640776*b^4*c^3 - 2407636999*b^4*c^2 + 5001480398*b^4*c - 2860993936*b^4 - 91158668*b^3*c^5 - 124689858*b^3*c^4 + 4149971209*b^3*c^3 - 14116136088*b^3*c^2 + 20936585267*b^3*c - 16990728228*b^3 + 95234584*b^2*c^5 - 5603005202*b^2*c^4 + 35516866953*b^2*c^3 - 93729400679*b^2*c^2 + 134198199601*b^2*c - 104468211984*b^2 + 598386476*b*c^6 + 428363318*b*c^5 - 22242504357*b*c^4 + 69846902366*b*c^3 - 61834807271*b*c^2 - 71853865426*b*c + 275108805602*b - 364634672*c^7 - 30738344*c^6 + 21933534046*c^5 - 123080143985*c^4 + 328941581044*c^3 - 524277785604*c^2 + 446725104016*c - 149886320712)/27354) * h2 + (-(8912071*b*c^2 - 29252781*b*c + 15887341*b - 22789667*c^3 + 120906917*c^2 - 174577013*c + 37028198)/27354) * h3

private lemma rejectI_7_10 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, b) = 0) (h2 : locus b (b, 1, b) = 0)
    (h3 : edge b b c (1, c, b) (b, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(1391093*b*c - 583253*c^2 - 996107*c + 2387200)/2387200) * h0 + ((323866587*b^2*c^4 + 61950000*b^2*c^3*z - 462980819*b^2*c^3 - 591390125*b^2*c^2*z - 1528103065*b^2*c^2 + 220715125*b^2*c*z + 1807092478*b^2*c + 319050000*b^2*z - 709094970*b^2 - 581044116*b*c^4 + 448396375*b*c^3*z + 1094870109*b*c^3 - 422245250*b*c^2*z + 4092954130*b*c^2 - 612626125*b*c*z - 3968087434*b*c + 638100000*b*z - 256815670*b + 107955529*c^5 + 20650000*c^4*z - 364956703*c^4 - 342619875*c^3*z - 61482007*c^3 + 520726125*c^2*z + 220635420*c^2 + 89318750*c*z - 372994587*c - 277750000*z + 511959300)/298400000) * h1 + ((-514355058*b^7 - 1584331645*b^6*c + 41300000*b^6*z + 3908860819*b^6 - 1044554000*b^5*c^2 + 144550000*b^5*c*z + 10605937051*b^5*c - 268450000*b^5*z - 10619887406*b^5 + 241333645*b^4*c^3 + 144550000*b^4*c^2*z + 4198607891*b^4*c^2 - 805350000*b^4*c*z - 22515424710*b^4*c + 557550000*b^4*z + 12006982710*b^4 + 215911058*b^3*c^4 - 132586625*b^3*c^3*z - 3676400457*b^3*c^3 - 342363375*b^3*c^2*z - 1023902151*b^3*c^2 + 1156400000*b^3*c*z + 12714350738*b^3*c - 351050000*b^3*z - 3264134833*b^3 + 246793250*b^2*c^4*z - 638154471*b^2*c^4 + 523280000*b^2*c^3*z + 10697872341*b^2*c^3 - 944573250*b^2*c^2*z - 11547566218*b^2*c^2 + 401650000*b^2*c*z + 6424054819*b^2*c - 123900000*b^2*z - 2725368942*b^2 - 72906625*b*c^5*z + 215911058*b*c^5 - 750686500*b*c^4*z - 1387225283*b*c^4 + 658393125*b*c^3*z - 7152826492*b*c^3 + 1720175000*b*c^2*z + 10908622724*b*c^2 - 1668550000*b*c*z - 3537100102*b*c + 82600000*b*z + 873928355*b + 218719875*c^5*z - 15843884*c^5 - 210976125*c^4*z + 1861901065*c^4 - 502318750*c^3*z - 3663201898*c^3 + 587500000*c^2*z + 3154861216*c^2 - 123900000*c*z - 1464189922*c + 20650000*z + 282776471)/298400000) * h2 + (-(-257177529*b + 107955529*c + 20650000*z + 282776471)/298400000) * h3

private lemma rejectI_7_18 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, b) = 0) (h2 : locus b (c, 1, 1) = 0)
    (h3 : edge b b c (1, c, b) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-b*z*(c - 1)*(b^2 - b*c - b - c + 4)) * h1 + (-z*(c - 1)*(b*c - 4*b + c)) * h2

private lemma rejectI_7_23 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, b) = 0) (h2 : locus b (c, b, c) = 0)
    (h3 : edge b b c (1, c, b) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-b*z*(b^2*c - b^2 - b*c^2 + b + c^3 - 3*c^2)) * h1 + (b*c^2*z*(c - 3)) * h2

private lemma rejectI_8_9 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, c) = 0) (h2 : locus b (b, 1, 1) = 0)
    (h3 : edge b b c (1, c, c) (b, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (b*c*z*(c - 2)*(2*c^3 + 3*c^2 - 4*c + 8)/28) * h1 + (z*(4*b^6*c - 10*b^6 + 24*b^5*c^2 - 96*b^5*c + 90*b^5 + 54*b^4*c^3 - 319*b^4*c^2 + 572*b^4*c - 280*b^4 + 62*b^3*c^4 - 485*b^3*c^3 + 1273*b^3*c^2 - 1256*b^3*c + 340*b^3 + 40*b^2*c^5 - 366*b^2*c^4 + 1229*b^2*c^3 - 1810*b^2*c^2 + 964*b^2*c - 120*b^2 + 14*b*c^6 - 129*b*c^5 + 455*b*c^4 - 694*b*c^3 + 660*b*c^2 - 288*b*c + 2*c^7 - 9*c^6 - 6*c^5 + 56*c^4 - 192*c^3 + 176*c^2)/112) * h2 + (-z*(2*c - 5)/56) * h3

private lemma rejectI_8_21 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, c) = 0) (h2 : locus b (c, b, 1) = 0)
    (h3 : edge b b c (1, c, c) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(230*b^7*c + 1126*b^7 - 6238*b^6*c - 19508*b^6 - 5328*b^5*c^2 + 75032*b^5*c + 109381*b^5 + 8624*b^4*c^3 - 2800*b^4*c^2 - 283153*b^4*c - 276061*b^4 - 6400*b^3*c^4 + 11248*b^3*c^3 - 15472*b^3*c^2 + 397617*b^3*c + 283463*b^3 - 768*b^2*c^5 + 832*b^2*c^4 - 1632*b^2*c^3 - 13120*b^2*c^2 + 13642*b^2*c - 87922*b^2 - 576*b*c^3 - 432*b*c^2 - 1049*b*c - 10632*b - 132*c - 341)/14) * h1 + ((230*b^7*c + 1126*b^7 - 8054*b^6*c - 15876*b^6 + 81372*b^5*c + 73803*b^5 - 324153*b^4*c - 110514*b^4 + 440509*b^3*c - 11158*b^3 + 43194*b^2*c - 524*b^2 + 1287*b*c + 133*b + 12*c + 19)/14) * h2 + (-(115*b + 12*c + 5)/14) * h3

private lemma rejectI_9_21 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, 1) = 0) (h2 : locus b (c, b, 1) = 0)
    (h3 : edge b b c (b, 1, 1) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((24*b^6*c - 36*b^6 - 84*b^5*c^2 + 154*b^5*c - 42*b^5 + 128*b^4*c^3 - 320*b^4*c^2 + 120*b^4*c + 108*b^4 - 110*b^3*c^4 + 409*b^3*c^3 - 344*b^3*c^2 - 37*b^3*c + 6*b^3 + 56*b^2*c^5 - 316*b^2*c^4 + 532*b^2*c^3 - 326*b^2*c^2 + 197*b^2*c - 183*b^2 - 16*b*c^6 + 144*b*c^5 - 468*b*c^4 + 726*b*c^3 - 883*b*c^2 + 1063*b*c + 1044*b - 352*c^4 + 2112*c^3 - 1724*c^2 - 4310*c - 1557)/1344) * h1 + ((2*b^2*c^5 - 31*b^2*c^4 + 172*b^2*c^3 - 99*b^2*c^2 - 492*b^2*c - 1122*b^2 + 4*b*c^3 - 674*b*c^2 + 1994*b*c + 1368*b + 2*c + 669)/672) * h2 + (-(2*c - 3)/672) * h3

private lemma rejectI_10_18 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, b) = 0) (h2 : locus b (c, 1, 1) = 0)
    (h3 : edge b b c (b, 1, b) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(16046*c + 4915)*(3*c^2 - 55*c + 175)/860125) * h0 + (-(-5964*b^4*c^3 + 2567360*b^4*c^2*z + 135026*b^4*c^2 - 6915680*b^4*c*z - 803912*b^4*c - 2359200*b^4*z + 1357530*b^4 - 2982*b^3*c^5 + 1283680*b^3*c^4*z + 94351*b^3*c^4 - 15010960*b^3*c^3*z - 991681*b^3*c^3 + 22238880*b^3*c^2*z + 3891291*b^3*c^2 + 31363440*b^3*c*z - 3697149*b^3*c + 7077600*b^3*z - 4072590*b^3 + 5964*b^2*c^6 - 2326670*b^2*c^5*z - 170810*b^2*c^5 + 17740225*b^2*c^4*z + 1578284*b^2*c^4 - 6703170*b^2*c^3*z - 5385756*b^2*c^3 - 57618880*b^2*c^2*z + 3665237*b^2*c^2 - 38312385*b^2*c*z + 6018266*b^2*c - 6684400*b^2*z + 3846335*b^2 - 8946*b*c^7 + 3610350*b*c^6*z + 259197*b*c^6 - 31627965*b*c^5*z - 2548255*b*c^5 + 95395620*b*c^4*z + 11077395*b*c^4 - 123595340*b*c^3*z - 22046519*b*c^3 + 53340575*b*c^2*z + 19201147*b*c^2 + 41233940*b*c*z - 10495659*b*c + 3145600*b*z - 1810040*b + 240690*c^3 - 4335943*c^2 - 1283680*c*z + 12630058*c - 393200*z + 226255)/4300625) * h1 + ((-2982*b^2*c^6 + 1283680*b^2*c^5*z + 85405*b^2*c^5 - 11881990*b^2*c^4*z - 845800*b^2*c^4 + 47105845*b^2*c^3*z + 4006936*b^2*c^3 - 65612210*b^2*c^2*z - 10065353*b^2*c^2 + 12276590*b^2*c*z + 12346734*b^2*c + 11378225*b^2*z - 7117860*b^2 + 17892*b*c^5 - 6257940*b*c^4*z - 440862*b*c^4 + 17819730*b*c^3*z + 3156288*b*c^3 - 33267250*b*c^2*z - 7768616*b*c^2 + 30159230*b*c*z + 5192768*b*c + 12926450*b*z + 4109280*b - 8946*c^5 + 3610350*c^4*z + 223413*c^4 - 17186565*c^3*z - 1654603*c^3 + 26649360*c^2*z + 4450037*c^2 - 13146860*c*z - 4531176*c - 7053025*z + 8689415)/4300625) * h2 + (-(-2982*c^2 + 1283680*c*z + 58567*c + 393200*z - 226255)/4300625) * h3

private lemma rejectI_10_23 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, b) = 0) (h2 : locus b (c, b, c) = 0)
    (h3 : edge b b c (b, 1, b) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(901145*b^6*c + 3604580*b^6 - 2752656*b^5*c^2 - 18716641*b^5*c - 5592008*b^5 + 2406366*b^4*c^3 + 29307814*b^4*c^2 + 224422*b^4*c - 11524131*b^4 - 886944*b^3*c^4 - 12030414*b^3*c^3 + 73022201*b^3*c^2 + 77221661*b^3*c + 32314355*b^3 + 120149*b^2*c^5 - 3614645*b^2*c^4 - 166213004*b^2*c^3 - 180702155*b^2*c^2 - 137545824*b^2*c - 10211768*b^2 - 5109713*b*c^5 + 147549762*b*c^4 + 87256689*b*c^3 + 364646814*b*c^2 - 41861855*b*c + 6720895*b + 480596*c^6 - 23826728*c^5 - 17144748*c^4 - 70501034*c^3 - 4749246*c^2 - 2516375*c - 488696)/16875) * h1 + (-(9456017*b^2*c^4 - 4651897*b^2*c^3 + 103203905*b^2*c^2 - 35246235*b^2*c + 44490239*b^2 - 1727987*b*c^5 - 11236019*b*c^4 - 73856350*b*c^3 - 86496372*b*c^2 - 159545564*b*c - 16392266*b + 120149*c^6 + 1035445*c^5 + 2737124*c^4 + 28117047*c^3 + 18160688*c^2 + 66503773*c - 320614)/16875) * h2 + ((180229*b^2 - 406348*b*c - 171463*b + 120149*c^2 + 314551*c - 471821)/16875) * h3

private lemma rejectI_11_16 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, c) = 0) (h2 : locus b (b, c, b) = 0)
    (h3 : edge b b c (b, 1, c) (b, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(238554989477014368188757168*b^3 + 2102332681268148116347232013*b^2*c - 5964531295889520074650914796*b^2 + 3331334762089913379835418215*b*c^2 - 37509124215618209610710488511*b*c + 11213397623347997044735558088*b - 2110738962616842748725939808*c^3 + 17997381659694843691409431868*c^2 + 5743776441512090809953534014*c - 5323602586376442874409137534)/163818730559048463864262926) * h0 + (-(-9745979142979231383756096*b^5*c^3 + 468642279785728705371725400*b^5*c^2*z + 77081835039926648216980032*b^5*c^2 - 485577678122328767383303272*b^5*c*z + 86827814182905879600736128*b^5*c - 21603716011210823926717644*b^4*c^4 + 3935880942410609371423756674*b^4*c^3*z + 453252186346548774129336768*b^4*c^3 - 17428389737365377325912835834*b^4*c^2*z - 2040196613702066078276733696*b^4*c^2 + 13757377403410558453915291808*b^4*c*z - 2428224701876919796732051980*b^4*c - 8467699168300031005788936*b^4*z + 86827814182905879600736128*b^4 + 19491958285958462767512192*b^3*c^5 + 4457994746509771521240803705*b^3*c^4*z - 20317858562083630555243296*b^3*c^4 - 86793430258159255696842102710*b^3*c^3*z - 2981793631697338072880256684*b^3*c^3 + 145463441947923079762794912053*b^3*c^2*z + 12716510781016134731861861088*b^3*c^2 - 64429229850619344205982993000*b^3*c*z + 14369663455613173783733704800*b^3*c + 133026787787517634274795232*b^3*z - 2157995280185222926546087500*b^3 + 55065168890653240396396836*b^2*c^6 - 8360735257689653546663697616*b^2*c^5*z - 860346382918482427020433488*b^2*c^5 + 67694651922252277922527089252*b^2*c^4*z - 2307549179427474128094286224*b^2*c^4 + 149225164620887340836647769992*b^2*c^3*z + 60887882758626171034956845184*b^2*c^3 - 203193618922546213375675065568*b^2*c^2*z - 105341411875448196223387026672*b^2*c^2 - 4709964379713577031268479912*b^2*c*z + 30147741397438143573975497580*b^2*c + 594240287919357919054269168*b^2*z + 1267049045377908608605502664*b^2 - 21603716011210823926717644*b*c^7 - 30229430648672493081950184*b*c^6*z - 81318250241247314973259140*b*c^6 + 38458342471620265676293928855*b*c^5*z + 8395139421997219671245022096*b*c^5 - 441976227505201160931654055539*b*c^4*z - 49608344813440512500334448320*b*c^4 + 665601238499885722044813889327*b*c^3*z - 37786449736613302150921418400*b*c^3 - 317663318797439883478321426511*b*c^2*z + 100456573170718384622679219576*b*c^2 + 57545540560985053013004380108*b*c*z - 55771683778575902717824311912*b*c - 817955367652893032574914952*b*z - 5708588338322294530199174704*b + 206291180969129007883420344*c^7 - 8590453092868057160298734123*c^6*z - 4514569244732627205534140304*c^6 + 105104071279135072080179359382*c^5*z + 28591855008928300688442686292*c^5 - 147940265514295093344684683867*c^4*z - 51258309066833125824068208972*c^4 + 48658644100788563410870063028*c^3*z + 81018458898730167981073525404*c^3 + 3161578309231879808561036880*c^2*z - 69544117554180629797840013760*c^2 - 1021789341791847595598345064*c*z - 2420536465685647637955632100*c + 99155991114317510251639488*z - 23760369291195564761236744828)/655274922236193855457051704) * h1 + ((43207432022421647853435288*b^2*c^6 + 501782711016456051372588163*b^2*c^5*z + 130473995845022000223773376*b^2*c^5 - 8830331842582065540188487533*b^2*c^4*z - 16392345842240606398736169180*b^2*c^4 - 29405081284619222437608313275*b^2*c^3*z + 122922224960925621686519714760*b^2*c^3 + 198514855510836139816075627541*b^2*c^2*z - 177188827909261968033848566968*b^2*c^2 - 163470339569516858812604917864*b^2*c*z + 118146689392795186935743246484*b^2*c + 2015599301426456044144809984*b^2*z - 12298685353604601566337083088*b^2 - 21603716011210823926717644*b*c^7 - 30229430648672493081950184*b*c^6*z - 456215643849558191952009732*b*c^6 + 11296429383177159513628018022*b*c^5*z + 14951093473802691383504531988*b*c^5 - 135757981619456506491689444378*b*c^4*z - 79866404055921739200846664512*b*c^4 + 347971627800028694240735208042*b*c^3*z - 26130441922889449135703443176*b*c^3 - 330035512293609301019290481006*b*c^2*z + 140746857423176861133946888560*b*c^2 + 108399052235977894508813115080*b*c*z - 93314139800875438234400990196*b*c - 1007799650713228022072404992*b*z - 10497438887998303970195791256*b + 206291180969129007883420344*c^7 - 8590453092868057160298734123*c^6*z - 3544513781953392489991051776*c^6 + 124219661026386225958021639404*c^5*z + 8278534775518958106360238380*c^5 - 378888895281294733993181499314*c^4*z + 84314590303372348878398747580*c^4 + 475936260058144182488401616000*c^3*z - 234234131634902277150747001656*c^3 - 270730122177864141711369279603*c^2*z + 216523135245290535323663005260*c^2 + 58992422557744107423328973324*c*z - 87652859105672829075482148392*c - 1007799650713228022072404992*z - 47027638598989989772455857208)/655274922236193855457051704) * h2 + (-(812164928581602615313008*b*c + 705641597358335917149078*b*z - 7235651181908823300061344*b + 1800309667600901993893137*c^2 + 2519119220722707756829182*c*z - 33074005767827145582167137*c - 8262999259526459187636624*z + 150890335287799950678595249)/54606243519682821288087642) * h3

private lemma rejectI_11_19 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, c) = 0) (h2 : locus b (c, 1, b) = 0)
    (h3 : edge b b c (b, 1, c) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((54166528000*b^3 + 118337709750*b^2*c^2*z + 435634700166*b^2*c^2 - 290127122500*b^2*c*z - 1085211378980*b^2*c - 109499894750*b^2*z - 524547338606*b^2 + 92066719875*b*c^3*z + 338923729323*b*c^3 - 349076498000*b*c^2*z - 1323505043408*b*c^2 + 188619040375*b*c*z + 781682090751*b*c + 218999789500*b*z + 886595093212*b + 16448932500*c^4*z + 60553189620*c^4 - 75735478500*c^3*z - 286967890116*c^3 + 62296159625*c^2*z + 284011948289*c^2 + 101508082125*c*z + 321258568229*c - 109499894750*z - 487045002606)/70830720000) * h0 + ((24999936000*b^6*c*z + 92031860736*b^6*c - 100414464000*b^6*z - 367560105984*b^6 - 398804729856*b^5*c^2 + 376796160000*b^5*c*z + 1776824180736*b^5*c - 200828928000*b^5*z - 735120211968*b^5 + 236675419500*b^4*c^4*z^2 + 871269400332*b^4*c^4*z - 816929664500*b^4*c^3*z^2 - 2891692542292*b^4*c^3*z + 751593529344*b^4*c^3 + 361254455500*b^4*c^2*z^2 - 302888495252*b^4*c^2*z - 4029429977088*b^4*c^2 + 218999789500*b^4*c*z^2 + 2549555221212*b^4*c*z + 4104421183488*b^4*c + 65795730000*b^3*c^5*z^2 + 242212758480*b^3*c^5*z - 1302185571750*b^3*c^4*z^2 - 5090953759478*b^3*c^4*z - 774601494528*b^3*c^4 + 3754017674750*b^3*c^3*z^2 + 16026202253966*b^3*c^3*z + 5256379619328*b^3*c^3 - 1313128990750*b^3*c^2*z^2 - 7224107920302*b^3*c^2*z - 9442941272064*b^3*c^2 - 1204498842250*b^3*c*z^2 - 4430978676666*b^3*c*z + 3216150927360*b^3*c - 118337709750*b^2*c^6*z^2 - 435634700166*b^2*c^6*z + 408228321625*b^2*c^5*z^2 + 1639766776401*b^2*c^5*z + 440985999360*b^2*c^5 + 397888213500*b^2*c^4*z^2 + 695015153436*b^2*c^4*z - 3889462287360*b^2*c^4 - 1846277400750*b^2*c^3*z^2 - 5583776483262*b^2*c^3*z + 10505355082752*b^2*c^3 - 319750003750*b^2*c^2*z^2 - 2705482633590*b^2*c^2*z - 8021251292160*b^2*c^2 + 1478248579125*b^2*c*z^2 + 6138730127181*b^2*c*z + 45945013248*b^2*c - 92066719875*b*c^7*z^2 - 338923729323*b*c^7*z + 894849942125*b*c^6*z^2 + 3287339626949*b*c^6*z - 116957156352*b*c^6 - 2822208694500*b*c^5*z^2 - 10241923199172*b*c^5*z + 1373046263808*b*c^5 + 2336101178000*b*c^4*z^2 + 7694137262608*b*c^4*z - 5284809271296*b*c^4 + 2370819759875*b*c^3*z^2 + 10566380999723*b*c^3*z + 7369770381312*b*c^3 - 1811496307625*b*c^2*z^2 - 7131151419937*b*c^2*z - 3131036083200*b*c^2 - 875999158000*b*c*z^2 - 3309103188848*b*c*z + 1238837452800*b*c - 272769902000*b*z - 457775053872*b - 92066719875*c^5*z^2 - 334757073323*c^5*z + 15338643456*c^5 + 618649782500*c^4*z^2 + 2262166006980*c^4*z - 147539887104*c^4 - 1150392786750*c^3*z^2 - 4154036796878*c^3*z + 853638829056*c^3 + 240560092500*c^2*z^2 + 396049284100*c^2*z - 2271624683568*c^2 + 383249631625*c*z^2 + 1642006639121*c*z + 1181657082000*c - 96851583500*z - 805841094316)/283322880000) * h1 + (-(92066719875*b^2*c^6*z^2 + 338923729323*b^2*c^6*z - 605632542875*b^2*c^5*z^2 - 2255981532931*b^2*c^5*z - 5751991296*b^2*c^5 + 243028175250*b^2*c^4*z^2 + 1038297887874*b^2*c^4*z - 35506071552*b^2*c^4 + 2899281529750*b^2*c^3*z^2 + 10577043309926*b^2*c^3*z + 594491271168*b^2*c^3 - 2354994145125*b^2*c^2*z^2 - 9518026599677*b^2*c^2*z - 2016004921344*b^2*c^2 - 273749736875*b^2*c*z^2 + 370492389485*b^2*c*z + 2523619918848*b^2*c - 545539804000*b^2*z - 915550107744*b^2 - 118337709750*b*c^6*z^2 - 435634700166*b*c^6*z + 645140251750*b*c^5*z^2 + 2461906967478*b*c^5*z + 256922277888*b*c^5 - 1115894602000*b*c^4*z^2 - 4605293042832*b*c^4*z - 2381657911296*b*c^4 + 660219393000*b*c^3*z^2 + 4017262021288*b*c^3*z + 7729030557696*b*c^3 + 38372561750*b*c^2*z^2 - 1909524947162*b*c^2*z - 10260222382080*b*c^2 - 109499894750*b*c*z^2 + 364759395394*b*c*z + 4621317301296*b*c - 466473069000*b*z - 2286123354504*b - 92066719875*c^7*z^2 - 338923729323*c^7*z + 802783222250*c^6*z^2 + 2948415897626*c^6*z - 116957156352*c^6 - 2479759071625*c^5*z^2 - 9013125884161*c^5*z + 1164057246720*c^5 + 3159995448500*c^4*z^2 + 10900493154836*c^4*z - 4368654987264*c^4 - 1248263340125*c^3*z^2 - 3001186811957*c^3*z + 7726416838656*c^3 - 525939170750*c^2*z^2 - 3234000216142*c^2*z - 6576827735040*c^2 + 383249631625*c*z^2 + 1429677477621*c*z + 1508304997716*c + 341147995500*z + 859016036108)/283322880000) * h2 + (-(1017250*c*z + 3744786*c - 4085875*z - 14956059)/69170625) * h3

private lemma rejectI_11_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, c) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (b, 1, c) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(2*b - 3)*(100625211190*b*c^2 + 2463016007219*b*c - 720171229953*b - 407354373609*c^3 + 401259674151*c^2 + 419543772525*c - 715952999442)/907511779125) * h0 + (-(-45785477120*b^6*c^2 + 37247822848*b^6*c + 552982365184*b^6 + 160249169920*b^5*c^3 - 153260118528*b^5*c^2 - 1916814366720*b^5*c + 276491182592*b^5 + 402500844760*b^4*c^4*z - 263266493440*b^4*c^4 + 9449563184116*b^4*c^3*z + 443102366976*b^4*c^3 - 12732748948688*b^4*c^2*z + 3233783240448*b^4*c^2 + 2880684919812*b^4*c*z - 2960462895872*b^4*c - 2903157417216*b^4 - 1830667916816*b^3*c^5*z + 257543308800*b^3*c^5 - 3502829624818*b^3*c^4*z - 764667913600*b^3*c^4 - 40808305052740*b^3*c^3*z - 2882100153088*b^3*c^3 + 57681415195666*b^3*c^2*z + 6903663868160*b^3*c^2 - 11539612601292*b^3*c*z + 2681821096704*b^3*c - 207368386944*b^3 + 714083536028*b^2*c^6*z - 145941208320*b^2*c^6 + 5475596326101*b^2*c^5*z + 582305391168*b^2*c^5 + 19295421812641*b^2*c^4*z + 1711718607168*b^2*c^4 - 2398041000271*b^2*c^3*z - 7026143667200*b^2*c^3 - 20290740364907*b^2*c^2*z - 2957635147008*b^2*c^2 - 2796320309592*b^2*c*z + 14001663660480*b^2*c - 449298171712*b^2 + 22892738560*b*c^7 - 2343501030464*b*c^6*z - 61547796224*b*c^6 - 1014223485385*b*c^5*z - 466206345792*b*c^5 - 30497551837641*b*c^4*z + 1370423002048*b*c^4 + 43589137612001*b*c^3*z + 1809392057728*b*c^3 - 19748766789677*b*c^2*z - 7774737455360*b*c^2 + 10014905531166*b*c*z + 2410323528604*b*c + 777631451040*b + 714083536028*c^7*z - 20031146240*c^7 - 4703409485275*c^6*z + 122174838336*c^6 + 26947922975093*c^5*z - 22339927488*c^5 - 63373439984696*c^4*z - 1233473591360*c^4 + 64755623915860*c^3*z + 2894367490240*c^3 - 27950073567797*c^2*z - 476850854208*c^2 + 3609292610787*c*z - 864893910024*c + 1270131370032)/3630047116500) * h1 + (-(714083536028*b^2*c^6*z + 37200700160*b^2*c^6 - 9280079277315*b^2*c^5*z - 250606464704*b^2*c^5 + 24419904949130*b^2*c^4*z + 41870538624*b^2*c^4 + 886004722674*b^2*c^3*z + 2099140266816*b^2*c^3 - 30364112072470*b^2*c^2*z - 3064041119744*b^2*c^2 + 13624198141953*b^2*c*z + 3195103009984*b^2*c - 1501677557816*b^2 - 22892738560*b*c^7 + 201250422380*b*c^6*z + 121641234944*b*c^6 + 10839950725042*b*c^5*z + 219868708224*b*c^5 - 28552512000240*b*c^4*z - 1856171933440*b*c^4 + 18605327426668*b*c^3*z + 1165868491136*b*c^3 + 8920888957316*b*c^2*z + 5527905013760*b*c^2 - 10014905531166*b*c*z - 11707531386916*b*c + 2136799312860*b - 714083536028*c^7*z + 20031146240*c^7 + 4703409485275*c^6*z - 122174838336*c^6 - 26947922975093*c^5*z + 22339927488*c^5 + 63373439984696*c^4*z + 1233473591360*c^4 - 64755623915860*c^3*z - 2894367490240*c^3 + 27950073567797*c^2*z + 476850854208*c^2 - 3609292610787*c*z + 5753146393332*c + 3691257506772)/3630047116500) * h2 + (-256*(44712380*c^2 - 36374827*c - 540021841)/907511779125) * h3

private lemma rejectI_12_14 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, 1) = 0) (h2 : locus b (b, b, c) = 0)
    (h3 : edge b b c (b, b, 1) (b, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(42984*b^6*c - 499392*b^5*c - 76205*b^4*c^4 + 336724*b^4*c^3 + 1828676*b^4*c^2 - 260755*b^4*c + 42984*b^4 + 762050*b^3*c^4 - 3221872*b^3*c^3 - 18475112*b^3*c^2 + 19237390*b^3*c - 327456*b^3 - 76205*b^2*c^5 - 2068615*b^2*c^4 + 15195399*b^2*c^3 + 43099867*b^2*c^2 - 54896121*b^2*c + 2445325*b^2 + 304820*b*c^6 - 1513001*b*c^5 - 3032250*b*c^4 + 2014350*b*c^3 - 37607505*b*c^2 - 892830*b*c + 4703216*b - 228615*c^7 + 1414655*c^6 + 3532232*c^5 - 33426564*c^4 + 74637091*c^3 - 43341239*c^2 + 15088526*c - 2337811)/135000) * h1 + ((76205*b^2*c^6 - 446150*b^2*c^5 - 1479574*b^2*c^4 + 10651791*b^2*c^3 - 13912424*b^2*c^2 + 5689866*b^2*c + 3929936*b^2 - 76205*b*c^6 + 217535*b*c^5 + 4063872*b*c^4 - 12579223*b*c^3 + 8393347*b*c^2 - 27831708*b*c - 7940818*b + 76205*c^7 - 750970*c^6 + 805240*c^5 + 8917226*c^4 - 30741659*c^3 + 32185471*c^2 + 4344616*c + 637146)/135000) * h2 + ((42984*b^2 - 69552*b - 76205*c^3 + 293740*c^2 + 1871660*c - 2202811)/135000) * h3

private lemma rejectI_12_15 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, 1) = 0) (h2 : locus b (b, c, 1) = 0)
    (h3 : edge b b c (b, b, 1) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(227060*b^6*c + 227060*b^6 - 226802*b^5*c^2 - 2638924*b^5*c - 1049762*b^5 + 113186*b^4*c^3 + 1841892*b^4*c^2 + 7405704*b^4*c + 966298*b^4 + 215*b^3*c^4 - 522430*b^3*c^3 - 549085*b^3*c^2 - 4473020*b^3*c + 362360*b^3 + 129*b^2*c^5 - 565543*b^2*c^4 - 2577351*b^2*c^3 - 4391619*b^2*c^2 - 1872008*b^2*c - 22138*b^2 - 86*b*c^6 + 224265*b*c^5 + 3125532*b*c^4 + 1953686*b*c^3 - 2103989*b*c^2 - 354008*b*c + 261846*b + 731*c^6 - 1046408*c^5 + 736392*c^4 + 743795*c^3 - 806826*c^2 - 116394*c + 56926)/135000) * h1 + ((86*b^2*c^5 - 112025*b^2*c^4 + 172528*b^2*c^3 + 180441*b^2*c^2 - 104712*b^2*c - 83904*b^2 - 559*b*c^5 + 181883*b*c^4 - 286262*b*c^3 - 288795*b*c^2 + 174768*b*c + 147994*b + 43*c^6 + 43*c^5 + 297558*c^4 - 451335*c^3 - 463836*c^2 + 267458*c + 191926)/135000) * h2 + ((113530*b^2 + 129*b*c - 184291*b - 43*c^2 + 43*c - 296784)/135000) * h3

private lemma rejectI_12_17 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, 1) = 0) (h2 : locus b (b, c, c) = 0)
    (h3 : edge b b c (b, b, 1) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(71609509241975214520467979078656*b^3 + 569264033717861707280545385160954*b^2*c - 3832278837578933058596744684495574*b^2 - 603838703917999472652142197769378*b*c^2 + 2031833027191309691721592677815788*b*c + 5362313685929694452678542921261054*b + 589302182707112536183840105809805*c^3 - 3569532604149912798702965666843133*c^2 + 5452676932694040578141623523441859*c - 2547310475642130280151596056421491)/91751816414522207209393116990000) * h0 + (-(358047546209876072602339895393280*b^5*c^2*z - 1850288312427569415019716087744*b^5*c^2 - 1727121859621175436863532396203520*b^5*c*z + 14881378649524297602850878962112*b^5*c + 4107222940233898092783577502430720*b^5*z - 27991541136724768073375192096640*b^5 - 925144156213784707509858043872*b^4*c^4 + 1803735465673782781669790780006370*b^4*c^3*z + 15492214968616486535651013970224*b^4*c^3 - 12509737059287695689020346704534160*b^4*c^2*z - 78914152580104822642453219733136*b^4*c^2 - 683019135019885879340287672448850*b^4*c*z + 135039923023868762913835273601136*b^4*c - 10688480390859192982217859806557440*b^4*z - 38245523349991460113705718847600*b^4 + 1712902431392707098338142134904*b^3*c^5 - 3496626120193889485400431199004620*b^3*c^4*z - 26498157107858857061832918222288*b^3*c^4 + 3129629197660706498792648432851120*b^3*c^3*z + 149627153991850545167532560869632*b^3*c^3 + 103131356503296604795591513076181660*b^3*c^2*z - 375637197363168102878521323976320*b^3*c^2 - 50794620057571975632727799696689280*b^3*c*z + 259928776965095046307537950874248*b^3*c + 6737566374468540707821518154682880*b^3*z + 287351073726443783460264174472080*b^3 - 1850288312427569415019716087744*b^2*c^6 + 4596630119714260679918719017085675*b^2*c^5*z + 22108589007169461436987009734240*b^2*c^5 - 15788493619329449250854135196758490*b^2*c^4*z - 109143860056312451664130147479168*b^2*c^4 - 23665224722935807595688439495661820*b^2*c^3*z + 295710579521986663870742031230664*b^2*c^3 - 84995927009090958862456624571915430*b^2*c^2*z - 253225654631788630099317490126152*b^2*c^2 + 68533753490257063940579219755731665*b^2*c*z + 5669983990341402791006446111959178*b^2*c - 848930035758110451334964017825920*b^2*z - 22786746323380544592342111599401510*b^2 + 925144156213784707509858043872*b*c^7 - 2261973756829912998788604278643905*b*c^6*z - 10179564782373251414693853986664*b*c^6 + 8785673237163455502482624227177655*b*c^5*z + 57832909760388623881133268599184*b*c^5 + 25246917903347559625458026704471950*b*c^4*z - 264578686115205374227381027374504*b*c^4 - 104940306887881408346123728414397290*b*c^3*z + 641693825025627539362824246047688*b*c^3 + 112123443370711248497954151765091795*b*c^2*z - 6103199163423688580615166248592514*b*c^2 - 28044787098183205211715947892815085*b*c*z + 16030761941522128035321866325956676*b*c - 1493047416417685379379900683907840*b*z + 22145213232191567146006548461335870*b + 2946510913535562680919200529049025*c^3 - 17847525634868529131198146760262825*c^2 - 999813254574117050001814214836800*c*z + 27265548342626390381477160247377087*c + 272198071640416882688812116789120*z - 13215681484743290064193917749580375)/458759082072611036046965584950000) * h1 + ((-137385881034862316681573952840*b^2*c^6 + 999813254574117050001814214836800*b^2*c^5*z - 3327038063440748600654476491336*b^2*c^5 - 15479871398528989539716677278930435*b^2*c^4*z + 49220831991205068400349048688120*b^2*c^4 + 56909071265197053372544163362843920*b^2*c^3*z - 182896343131103048514684942980928*b^2*c^3 - 35082353579058468580317265640218405*b^2*c^2*z + 151634723752122277845529741927680*b^2*c^2 - 3474010114732512837837740662197320*b^2*c*z + 3096381994821364332554849455363865*b^2*c - 11238888981204520642080378259653695*b^2 - 1850288312427569415019716087744*b*c^5 + 16309991167802076721254010673483910*b*c^4*z + 16246395296786777049303553939320*b*c^4 - 65055937506086478427846389456137985*b*c^3*z - 78590051369144857269567118371456*b*c^3 - 43074480714731990877683406961353110*b*c^2*z + 403064941023718905335042745798120*b*c^2 + 80523208335901593788726998956384785*b*c*z - 6543158779329922652544338278702810*b*c + 22232348127888254102867212892904670*b + 925144156213784707509858043872*c^5 - 2261973756829912998788604278643905*c^4*z - 8329276469945681999674137898920*c^4 + 4261725723503629504905415669889845*c^3*z + 40249212664283475174275134757472*c^3 + 36032343107184731634057462322895545*c^2*z - 176163141959797328829201341819160*c^2 - 34137906633293223432908776793985645*c*z - 5649432834930694391398611503279650*c + 21565972784285519531790846394311590)/458759082072611036046965584950000) * h2 + ((30244992884532036*b*c + 22379022009382798560*b*z - 152517485486101720*b + 4491445972420295*c^2 - 32686089586526233400*c*z + 70735420251823746*c + 8898752356216940560*z - 665940805779581835)/14997841233506381250) * h3

private lemma rejectI_12_24 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, 1) = 0) (h2 : locus b (c, c, 1) = 0)
    (h3 : edge b b c (b, b, 1) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(2458*b^6*c + 2458*b^6 - 3758*b^5*c^2 - 29904*b^5*c - 11398*b^5 + 3475*b^4*c^3 + 34559*b^4*c^2 + 85958*b^4*c + 11492*b^4 - 1596*b^3*c^4 - 24221*b^3*c^3 - 40799*b^3*c^2 - 62802*b^3*c + 1066*b^3 + 473*b^2*c^5 + 4718*b^2*c^4 - 16322*b^2*c^3 - 12546*b^2*c^2 + 5304*b^2*c + 3538*b^2 - 10168*b*c^5 + 70329*b*c^4 - 2067*b*c^3 - 38565*b*c^2 - 19860*b*c - 2284*b + 1892*c^6 - 21032*c^5 + 31506*c^4 + 4132*c^3 - 34015*c^2 + 12856*c + 1442)/1250) * h1 + (-(11928*b^2*c^4 - 14770*b^2*c^3 + 11224*b^2*c^2 - 11560*b^2*c - 5222*b^2 - 3961*b*c^5 - 7346*b*c^4 - 24198*b*c^3 + 6311*b*c^2 + 47832*b*c + 5168*b + 473*c^6 + 1252*c^5 - 2609*c^4 + 14562*c^3 + 227*c^2 - 18240*c - 2692)/1250) * h2 + ((1229*b^2 - 650*b*c - 2012*b + 473*c^2 + 306*c - 2748)/1250) * h3

private lemma rejectI_13_22 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, b) = 0) (h2 : locus b (c, b, b) = 0)
    (h3 : edge b b c (b, b, b) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(-544*b^2*c + 1088*b^2 + 20*b*c^2*z + 544*b*c^2 - 50*b*c*z - 1088*b*c + 20*b*z + 11)/11) * h0 + (-(-34*b^7*z + 170*b^6*c*z - 42*b^6*z - 391*b^5*c^2*z + 406*b^5*c*z + 10*b^5*z + 297*b^4*c^2*z - 314*b^4*c*z - 550*b^4*z + 20*b^3*c^4*z^2 + 595*b^3*c^4*z - 70*b^3*c^3*z^2 - 510*b^3*c^3*z + 70*b^3*c^2*z^2 - 2723*b^3*c^2*z - 20*b^3*c*z^2 + 4346*b^3*c*z - 1730*b^3*z - 20*b^2*c^5*z^2 - 255*b^2*c^5*z + 50*b^2*c^4*z^2 - 1612*b^2*c^4*z + 9222*b^2*c^3*z - 50*b^2*c^2*z^2 - 16154*b^2*c^2*z + 20*b^2*c*z^2 + 15383*b^2*c*z - 6370*b^2*z - 102*b*c^6*z + 20*b*c^5*z^2 + 1771*b*c^5*z - 90*b*c^4*z^2 - 8694*b*c^4*z + 80*b*c^3*z^2 + 18710*b*c^3*z - 12124*b*c^2*z - 10*b*c*z^2 - 13555*b*c*z + 20575*b*z + 17*c^7*z - 378*c^6*z + 20*c^5*z^2 + 3837*c^5*z - 70*c^4*z^2 - 18173*c^4*z + 90*c^3*z^2 + 44730*c^3*z - 50*c^2*z^2 - 60396*c^2*z + 10*c*z^2 + 42248*c*z - 11895*z - 544)/11) * h1 + (-(68*b*c^5*z - 1291*b*c^4*z + 60*b*c^3*z^2 + 11237*b*c^3*z - 90*b*c^2*z^2 - 42677*b*c^2*z + 30*b*c*z^2 + 68876*b*c*z - 44325*b*z - 17*c^5*z + 344*c^4*z - 20*c^3*z^2 - 3132*c^3*z + 30*c^2*z^2 + 11565*c^2*z - 10*c*z^2 - 18468*c*z + 11915*z + 544)/11) * h2 + (-z*(17*b - 17*c - 30)/11) * h3

private lemma rejectI_13_25 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, b) = 0) (h2 : locus b (c, c, b) = 0)
    (h3 : edge b b c (b, b, b) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-c*z*(b - 1)*(b*c - b - c^2)) * h1 + (-b*c*z*(b - 1)) * h2

private lemma rejectI_13_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, b) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (b, b, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-c*z*(c - 1)*(b^2 - b*c - b + 4*c - 1)) * h1 + (c*z*(3*b - 1)*(c - 1)) * h2

private lemma rejectI_14_15 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, c) = 0) (h2 : locus b (b, c, 1) = 0)
    (h3 : edge b b c (b, b, c) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(238554989477014368188757168*b^3 + 2102332681268148116347232013*b^2*c - 5964531295889520074650914796*b^2 + 3331334762089913379835418215*b*c^2 - 37509124215618209610710488511*b*c + 11213397623347997044735558088*b - 2110738962616842748725939808*c^3 + 17997381659694843691409431868*c^2 + 5743776441512090809953534014*c - 5323602586376442874409137534)/163818730559048463864262926) * h0 + (-(-4872989571489615691878048*b^5*c^3 + 234321139892864352685862700*b^5*c^2*z + 38540917519963324108490016*b^5*c^2 - 242788839061164383691651636*b^5*c*z + 43413907091452939800368064*b^5*c - 8365363219860604117419798*b^4*c^4 + 1850779901258872509368946987*b^4*c^3*z + 204919139627547917164484352*b^4*c^3 - 8475639879205674294767660749*b^4*c^2*z - 1022534801636777846984305872*b^4*c^2 + 6757294282174697035111820086*b^4*c*z - 1192405397392733428465841958*b^4*c - 4233849584150015502894468*b^4*z + 43413907091452939800368064*b^4 + 15146908145781937365435507*b^3*c^5 + 1245027137652233417764462684*b^3*c^4*z - 138618884013460946175391347*b^3*c^4 - 37587005179349902468715177828*b^3*c^3*z - 790452780796588675121630694*b^3*c^3 + 64449701510645227169057120844*b^3*c^2*z + 6542090226734686675145496243*b^3*c^2 - 28773153649664957481761226314*b^3*c*z + 6556068598791630472783655373*b^3*c + 64396469101683809385950382*b^3*z - 1057290686546884993372859718*b^3 - 15674847577095027655236870*b^2*c^6 - 1239944364381556893153347967*b^2*c^5*z - 26483155458108411837529794*b^2*c^5 + 18360182854204832629929303745*b^2*c^4*z + 4660122752730054675380603340*b^2*c^4 + 37493396842671365962046322980*b^2*c^3*z - 31626827055826463417783125737*b^2*c^3 - 122592854657797028687609624176*b^2*c^2*z + 34983754279421632654376909748*b^2*c^2 + 69495573684109813318466338708*b^2*c*z - 36349153602504256344003330696*b^2*c - 590968367444802190233615516*b^2*z + 4562926077265708767092732205*b^2 + 5400929002802705981679411*b*c^7 + 7557357662168123270487546*b*c^6*z + 108652981959586842006323022*b*c^6 - 1840137110191637535551065337*b*c^5*z - 3618531453429919856072318031*b*c^5 + 27848778639210341958418136499*b*c^4*z + 19272811735041783743088381021*b*c^4 - 74566828613716086029955999009*b*c^3*z + 7020424741170839243305058823*b*c^3 + 71990873830578819808704484127*b*c^2*z - 34509231101398487990281941654*b*c^2 - 23898973697618848381913212986*b*c*z + 22721478774749629609417234554*b*c + 249832987886231997766654014*b*z + 2646066675545302462449131846*b - 46699805670792636278977038*c^7 + 3262111959844457170384884457*c^6*z + 853191659342008147974020130*c^6 - 52662848013346654959595664994*c^5*z - 2486699513129877993148685946*c^5 + 162233557343487183028778909028*c^4*z - 17883235911869623785988332399*c^4 - 203233730556663824194113090475*c^3*z + 55969713608858982597043453797*c^3 + 114536121500457002852292910533*c^2*z - 57231755846161387497597424194*c^2 - 24398953353702789042039431811*c*z + 25348808975929925809810797026*c + 280972760041036398583905588*z + 11260824736792644651277810491)/163818730559048463864262926) * h1 + ((-13766292222663310099099209*b^2*c^6 + 2090183814422413386665924404*b^2*c^5*z + 219106908809304685470451485*b^2*c^5 - 21987410490679480093477060321*b^2*c^4*z + 311818267575326240854742157*b^2*c^4 + 14682484311186100297164916209*b^2*c^3*z - 12740658125722309987555535226*b^2*c^3 - 18191966238277614786702347199*b^2*c^2*z + 22990848287449576809153226965*b^2*c^2 + 23566001420178701311009792596*b^2*c*z - 13052547225578518227112976034*b^2*c - 208722691497373273646623206*b^2*z + 697114518110954901421115988*b^2 + 5400929002802705981679411*b*c^7 + 7557357662168123270487546*b*c^6*z + 309664843040275686001230*b*c^6 - 11974111442184742717148145824*b*c^5*z - 1915899387902585494858961178*b*c^5 + 165622585418964891262840928424*b*c^4*z + 13312348428936262892074365459*b*c^4 - 265499581705312061684587034383*b*c^3*z + 1568764866986823840746075202*b*c^3 + 135831082902737437293289275486*b*c^2*z - 30140747834619783517883092236*b*c^2 - 24066255701875754832524087847*b*c*z + 17874600057110547012232491717*b*c + 233511689275952651209533078*b*z + 931062171625720840713639865*b - 46699805670792636278977038*c^7 + 3262111959844457170384884457*c^6*z + 1105451504179796058243548358*c^6 - 45654953203278980729514693136*c^5*z - 7616284175060424740641149408*c^5 + 64624030448119404567404797659*c^4*z + 15096538892028406495707437787*c^4 - 21757463044738444252793095557*c^3*z - 17811190351080529038000429045*c^3 - 761371729945240559074454880*c^2*z + 16889944475590304657623849629*c^2 + 255447335447961898899586266*c*z + 605134116421411909488908025*c - 24788997778579377562909872*z + 5940092322798891190309186207)/163818730559048463864262926) * h2 + (-(812164928581602615313008*b*c + 705641597358335917149078*b*z - 7235651181908823300061344*b + 1800309667600901993893137*c^2 + 2519119220722707756829182*c*z - 33074005767827145582167137*c - 8262999259526459187636624*z + 150890335287799950678595249)/54606243519682821288087642) * h3

private lemma rejectI_14_17 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, c) = 0) (h2 : locus b (b, c, c) = 0)
    (h3 : edge b b c (b, b, c) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(7720*b^5*c^3 - 7122*b^5*c^2 - 18188*b^5*c - 3346*b^5 - 860*b^4*c^4 - 94172*b^4*c^3 + 88642*b^4*c^2 + 81500*b^4*c + 14842*b^4 - 3000*b^3*c^5 + 35993*b^3*c^4 + 371458*b^3*c^3 - 197387*b^3*c^2 - 92902*b^3*c - 11066*b^3 + 3430*b^2*c^6 - 3487*b^2*c^5 - 224183*b^2*c^4 - 338465*b^2*c^3 - 121108*b^2*c^2 + 69161*b^2*c + 8150*b^2 - 23150*b*c^6 + 164341*b*c^5 - 6534*b*c^4 + 53707*b*c^3 - 38697*b*c^2 + 25965*b*c - 11066*b + 3430*c^7 - 19337*c^6 - 645*c^5 + 2402*c^4)/15309) * h1 + (z*(3430*b^2*c^5 - 29637*b^2*c^4 - 47859*b^2*c^3 + 62318*b^2*c^2 + 225*b^2*c - 8150*b^2 - 15000*b*c^5 + 209025*b*c^4 - 80942*b*c^3 - 15790*b*c^2 - 37031*b*c + 11066*b + 3000*c^6 - 47553*c^5 + 7955*c^4 - 3833*c^3 + 11066*c^2)/15309) * h2 + (-z*(3860*b*c^2 - 7421*b*c - 1673*b + 3430*c^3 - 19337*c^2 - 645*c + 2402)/15309) * h3

private lemma rejectI_14_24 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, c) = 0) (h2 : locus b (c, c, 1) = 0)
    (h3 : edge b b c (b, b, c) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((114933506173556896409994*b^6*c^2 + 77812566083895274362382*b^6*c - 37120940089661622047612*b^6 - 355940204024582214545534*b^5*c^3 - 1585356096218435371406856*b^5*c^2 + 328414369606608823677894*b^5*c + 37285799168276795963156*b^5 + 509428562858502558398822*b^4*c^4 + 4255190373250546279883526*b^4*c^3 + 1890103768588911123100235*b^4*c^2 - 998952005394463924328685*b^4*c + 143569201323860118879490*b^4 - 306976717667840687706576*b^3*c^5 - 5832547552471943305735196*b^3*c^4 - 2797525874791849875052267*b^3*c^3 - 532785478425782752573659*b^3*c^2 + 128704594386659025701310*b^3*c - 74654027875861178884084*b^3 + 54830334312903844255484*b^2*c^6 + 3357035005960100906561788*b^2*c^5 + 517835453236706179666309*b^2*c^4 + 5034689006946652267564118*b^2*c^3 - 3180540291949775536229462*b^2*c^2 + 1539553141897858208096378*b^2*c - 219801907512726801477952*b^2 - 3442393986552890497630648*b*c^6 + 14221443731451693411089832*b*c^5 - 24155045145836742293377619*b*c^4 + 13214160160981097946161089*b*c^3 - 3733939562555361871370348*b*c^2 + 560087500650511248307262*b*c - 43614177437453495072948*b + 712794346067749975321292*c^7 - 4237939923377837206159110*c^6 + 13216033611814827017390003*c^5 - 18601574000057909664221110*c^4 + 11531763429776755074965700*c^3 - 2587040103736344246073659*c^2 - 25576181320358137244023*c + 46264439761457629238362)/463967372565043937268) * h1 + ((3556276513308741511408030*b^2*c^5 - 5499446810620191371480822*b^2*c^4 - 894152554396408828344522*b^2*c^3 + 2880167980508475849137868*b^2*c^2 - 964047265408487263982225*b^2*c + 53334683884402610968102*b^2 - 1469233496132560505674568*b*c^6 - 12300173593186374419248236*b*c^5 + 33928743001345826565686177*b*c^4 - 23804886896997889771106562*b*c^3 + 7094876435255540729994650*b*c^2 - 861491917075496627104842*b*c + 23145310922386832503676*b + 164491002938711532766452*c^7 + 4075537409400254717712622*c^6 - 9530594730463744335028027*c^5 + 6431592454646454579455202*c^4 - 2926139343028557081812529*c^3 + 1161268178254919318059087*c^2 - 271180545937647246002363*c + 25847392922418075817498)/463967372565043937268) * h2 + (-(57466753086778448204997*b^2*c - 18560470044830811023806*b^2 - 63036595838734210862773*b*c^2 - 77161355318803718428303*b*c + 18642899584138397981578*b + 13707583578225961063871*c^3 + 33444867611943421410685*c^2 - 18274225184247015074599*c + 25383425549853031880230)/463967372565043937268) * h3

private lemma rejectI_15_17 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, 1) = 0) (h2 : locus b (b, c, c) = 0)
    (h3 : edge b b c (b, c, 1) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(688*b^5*c + 156*b^4*c^3 - 872*b^4*c^2 - 7540*b^4*c + 78*b^3*c^4 - 1386*b^3*c^3 + 8826*b^3*c^2 + 24818*b^3*c + 688*b^3 - 468*b^2*c^4 + 1260*b^2*c^3 - 31452*b^2*c^2 + 4420*b^2*c - 7936*b^2 + 195*b*c^6 - 2923*b*c^5 + 16786*b*c^4 - 19094*b*c^3 + 5111*b*c^2 - 4847*b*c + 4772*b + 312*c^6 - 3680*c^5 + 10968*c^4 - 13312*c^3 + 6248*c^2 + 96*c - 632)/1792) * h1 + (z*(195*b^2*c^5 - 1480*b^2*c^4 + 4146*b^2*c^3 + 4340*b^2*c^2 - 20205*b^2*c + 3148*b^2 + 234*b*c^5 - 3464*b*c^4 + 6548*b*c^3 - 1600*b*c^2 - 2414*b*c + 696*b - 195*c^6 + 1675*c^5 - 4434*c^4 + 7638*c^3 - 10359*c^2 + 6543*c - 868)/1792) * h2 + (-z*(172*b + 39*c^2 - 304*c - 79)/224) * h3

private lemma rejectI_15_24 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, 1) = 0) (h2 : locus b (c, c, 1) = 0)
    (h3 : edge b b c (b, c, 1) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(2*b - 3)*(100625211190*b*c^2 + 2463016007219*b*c - 720171229953*b - 407354373609*c^3 + 401259674151*c^2 + 419543772525*c - 715952999442)/907511779125) * h0 + (-(-45785477120*b^6*c^2 + 37247822848*b^6*c + 552982365184*b^6 + 160249169920*b^5*c^3 - 153260118528*b^5*c^2 - 1916814366720*b^5*c + 276491182592*b^5 + 402500844760*b^4*c^4*z - 263266493440*b^4*c^4 + 9449563184116*b^4*c^3*z + 443102366976*b^4*c^3 - 12732748948688*b^4*c^2*z + 3233783240448*b^4*c^2 + 2880684919812*b^4*c*z - 2960462895872*b^4*c - 2903157417216*b^4 - 1830667916816*b^3*c^5*z + 257543308800*b^3*c^5 - 3502829624818*b^3*c^4*z - 764667913600*b^3*c^4 - 40808305052740*b^3*c^3*z - 2882100153088*b^3*c^3 + 57681415195666*b^3*c^2*z + 6903663868160*b^3*c^2 - 11539612601292*b^3*c*z + 2681821096704*b^3*c - 207368386944*b^3 + 714083536028*b^2*c^6*z - 145941208320*b^2*c^6 + 5475596326101*b^2*c^5*z + 582305391168*b^2*c^5 + 19295421812641*b^2*c^4*z + 1711718607168*b^2*c^4 - 2398041000271*b^2*c^3*z - 7026143667200*b^2*c^3 - 20290740364907*b^2*c^2*z - 2957635147008*b^2*c^2 - 2796320309592*b^2*c*z + 14001663660480*b^2*c - 449298171712*b^2 + 22892738560*b*c^7 - 2343501030464*b*c^6*z - 61547796224*b*c^6 - 1014223485385*b*c^5*z - 466206345792*b*c^5 - 30497551837641*b*c^4*z + 1370423002048*b*c^4 + 43589137612001*b*c^3*z + 1809392057728*b*c^3 - 19748766789677*b*c^2*z - 7774737455360*b*c^2 + 10014905531166*b*c*z + 2410323528604*b*c + 777631451040*b + 714083536028*c^7*z - 20031146240*c^7 - 4703409485275*c^6*z + 122174838336*c^6 + 26947922975093*c^5*z - 22339927488*c^5 - 63373439984696*c^4*z - 1233473591360*c^4 + 64755623915860*c^3*z + 2894367490240*c^3 - 27950073567797*c^2*z - 476850854208*c^2 + 3609292610787*c*z - 864893910024*c + 1270131370032)/3630047116500) * h1 + (-(714083536028*b^2*c^6*z + 37200700160*b^2*c^6 - 9280079277315*b^2*c^5*z - 250606464704*b^2*c^5 + 24419904949130*b^2*c^4*z + 41870538624*b^2*c^4 + 886004722674*b^2*c^3*z + 2099140266816*b^2*c^3 - 30364112072470*b^2*c^2*z - 3064041119744*b^2*c^2 + 13624198141953*b^2*c*z + 3195103009984*b^2*c - 1501677557816*b^2 - 22892738560*b*c^7 + 201250422380*b*c^6*z + 121641234944*b*c^6 + 10839950725042*b*c^5*z + 219868708224*b*c^5 - 28552512000240*b*c^4*z - 1856171933440*b*c^4 + 18605327426668*b*c^3*z + 1165868491136*b*c^3 + 8920888957316*b*c^2*z + 5527905013760*b*c^2 - 10014905531166*b*c*z - 11707531386916*b*c + 2136799312860*b - 714083536028*c^7*z + 20031146240*c^7 + 4703409485275*c^6*z - 122174838336*c^6 - 26947922975093*c^5*z + 22339927488*c^5 + 63373439984696*c^4*z + 1233473591360*c^4 - 64755623915860*c^3*z - 2894367490240*c^3 + 27950073567797*c^2*z + 476850854208*c^2 - 3609292610787*c*z + 5753146393332*c + 3691257506772)/3630047116500) * h2 + (-256*(44712380*c^2 - 36374827*c - 540021841)/907511779125) * h3

private lemma rejectI_16_19 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, b) = 0) (h2 : locus b (c, 1, b) = 0)
    (h3 : edge b b c (b, c, b) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((36764931894775812879*b^3 + 35731099183964082015*b^2*c^2 + 348917005266172992*b^2*c*z - 114998753685105181552*b^2*c - 2750051959307984808*b^2*z + 9761343561812843471*b^2 - 22211223817058753685*b*c^3 - 2130258166393153248*b*c^2*z + 130536579622195766393*b*c^2 + 5445022971481181136*b*c*z - 223345329114849732205*b*c + 5500103918615969616*b*z - 129817482807953125579*b - 312885651325376334*c^4 + 105598442871370152*c^3*z + 5298514483166125343*c^3 - 991670068663730496*c^2*z + 7336892095134238767*c^2 + 2456215901176600296*c*z - 21824334938465932567*c - 2750051959307984808*z + 80889062433124193429)/2402144918240275800) * h0 + (-(5794232300102283570*b^6*c^2*z + 247917517165932624*b^6*c*z^2 - 9585099888799195572*b^6*c*z + 82653718485108*b^6*c - 743752551497797872*b^6*z^2 - 23405031244997362854*b^6*z - 1507340811559094*b^6 - 37662509950664843205*b^5*c^3*z - 1611463861578562056*b^5*c^2*z^2 - 27711833356774674924*b^5*c^2*z - 537249170153202*b^5*c^2 + 5702102894816450352*b^5*c*z^2 + 228879649166013112686*b^5*c*z + 10087003289831989*b^5*c - 2603133930242292552*b^5*z^2 - 81917609357490769989*b^5*z - 5275692840456829*b^5 + 3539723051771234568*b^4*c^3*z^2 + 266378244196653298071*b^4*c^3*z + 1529093791974498*b^4*c^3 - 9544824410888406024*b^4*c^2*z^2 - 393086346834218043153*b^4*c^2*z - 29580206242787953*b^4*c^2 + 6872812669197935640*b^4*c*z^2 + 182995334099301750795*b^4*c*z + 30859159777718873*b^4*c + 371876275748898936*b^4*z^2 + 11702515622498681427*b^4*z + 753670405779547*b^4 - 2479611554553240*b^3*c^4 + 6321790177612512984*b^3*c^3*z^2 - 442422244144459836456*b^3*c^3*z + 49518217707998436*b^3*c^3 - 61208033011358579424*b^3*c^2*z^2 + 676618243911702254823*b^3*c^2*z - 79290913104409076*b^3*c^2 + 48688304904597750840*b^3*c*z^2 - 521978284171788705777*b^3*c*z + 16332787771694710*b^3*c + 2231257654493393616*b^3*z^2 + 70215093734992088562*b^3*z + 4522022434677282*b^3 + 102337722205766091477*b^2*c^6*z + 482038170018475896*b^2*c^5*z^2 - 1015684959931702322880*b^2*c^5*z + 2396957836068132*b^2*c^5 - 35383220633161418472*b^2*c^4*z^2 + 3744072054739396013700*b^2*c^4*z - 48506799207349990*b^2*c^4 + 163653261568261079472*b^2*c^3*z^2 - 5554878219291583767279*b^2*c^3*z + 88624245988461518*b^2*c^3 - 84843084838121283744*b^2*c^2*z^2 + 2080931332674789054156*b^2*c^2*z - 20616635990330243*b^2*c^2 - 43661076749830920528*b^2*c*z^2 + 622042385009093969394*b^2*c*z - 22444804736416194*b^2*c - 1487505102995595744*b^2*z^2 - 46810062489994725708*b^2*z - 3014681623118188*b^2 - 93646373755612666122*b*c^7*z - 3649884946040811528*b*c^6*z^2 + 1019131975877368931967*b*c^6*z - 1322459495761728*b*c^6 + 53081942402136360240*b*c^5*z^2 - 4200268347131075888136*b*c^5*z + 24448067858885936*b*c^5 - 170677839744906297984*b*c^4*z^2 + 7781134081472562942219*b*c^4*z - 7351822741998104*b*c^4 + 81083037997810895256*b*c^3*z^2 - 5317743050178418412592*b*c^3*z + 12297971241575060*b*c^3 + 47063150688824568360*b*c^2*z^2 - 528639267394381294992*b*c^2*z + 163312585970362186*b*c^2 - 4297272467582421792*b*c*z^2 + 1423622764150274979864*b*c*z + 734929498415572936*b*c - 2231257654493393616*b*z^2 - 60536626286384343546*b*z + 3970335697646653596*b + 2897116150051141785*c^6*z + 123958758582966312*c^5*z^2 - 115821620600319114618*c^5*z + 41326859242554*c^5 - 4765513773287508336*c^4*z^2 + 781319684004890114955*c^4*z - 2324091056996599*c^4 + 45479174045754016080*c^3*z^2 - 2174871548075824128939*c^3*z + 25374653539461020*c^3 - 56167221012515897616*c^2*z^2 + 2590425799497445871370*c^2*z + 982905978112968235*c^2 + 14337931912802693064*c*z^2 - 1121520750672303381528*c*z - 15682643066711059823*c + 1115628827246696808*z^2 + 34742813069519553969*z - 21092973646552181889)/7206434754720827400) * h1 + (-(23176929200409134280*b^2*c^6*z + 991670068663730496*b^2*c^5*z^2 - 18222877081084299351*b^2*c^5*z + 330614873940432*b^2*c^5 - 14875157540074726368*b^2*c^4*z^2 - 596576036782987053171*b^2*c^4*z - 491564107734140*b^2*c^4 - 13538885393932568856*b^2*c^3*z^2 + 1501117421738199632178*b^2*c^3*z - 93594326570042132*b^2*c^3 + 28827203292577593288*b^2*c^2*z^2 + 632601751915679268558*b^2*c^2*z - 81636681070886807*b^2*c^2 - 5619428219054883168*b^2*c*z^2 - 1670603600726581544409*b^2*c*z - 753977892856274381*b^2*c + 4090639033237888296*b^2*z^2 + 119049204398877750681*b^2*z - 3966567345617755861*b^2 - 348511449671990388423*b*c^6*z - 9944187905145314736*b*c^5*z^2 + 2792454342396069756972*b*c^5*z - 5868414012442668*b*c^5 + 154163624614626230856*b*c^4*z^2 - 8490555838293098704089*b*c^4*z + 92722104322771990*b*c^4 - 224600006238615412632*b*c^3*z^2 + 11032753892663267040921*b*c^3*z + 200432745905594422*b*c^3 + 91371614960197099152*b*c^2*z^2 - 6233499415816936888251*b*c^2*z + 830494401584261000*b*c^2 - 11238962948228535264*b*c*z^2 + 1229012393081929957095*b*c*z + 3764770286400598004*b*c - 371876275748898936*b*z^2 - 11337781824522191115*b*z - 89200314696963697654*b + 93646373755612666122*c^7*z + 3649884946040811528*c^6*z^2 - 720810157710224082891*c^6*z + 1322459495761728*c^6 - 41388535012516127784*c^5*z^2 + 2115256069643799415011*c^5*z - 20232728216145428*c^5 + 48109901704623087336*c^4*z^2 - 2626655792696167010280*c^4*z - 56380617408383518*c^4 - 5041025019080219664*c^3*z^2 + 1265983321727362082112*c^3*z - 197207071783086956*c^3 - 7437525514977978720*c^2*z^2 - 175653121384559855385*c^2*z - 929255656092682941*c^2 + 2355216413076359928*c*z^2 + 58053896087062689888*c*z + 65477568164691717537*c - 371876275748898936*z^2 - 3452359744574727003*z - 249874375724499187234)/7206434754720827400) * h2 + ((2897116150051141785*c^2*z + 123958758582966312*c*z^2 - 4792549944399597786*c*z + 41326859242554*c - 371876275748898936*z^2 - 11702515622498681427*z - 753670405779547)/7206434754720827400) * h3

private lemma rejectI_16_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, b) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (b, c, b) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((114933506173556896409994*b^6*c^2 + 77812566083895274362382*b^6*c - 37120940089661622047612*b^6 - 355940204024582214545534*b^5*c^3 - 1585356096218435371406856*b^5*c^2 + 328414369606608823677894*b^5*c + 37285799168276795963156*b^5 + 509428562858502558398822*b^4*c^4 + 4255190373250546279883526*b^4*c^3 + 1890103768588911123100235*b^4*c^2 - 998952005394463924328685*b^4*c + 143569201323860118879490*b^4 - 306976717667840687706576*b^3*c^5 - 5832547552471943305735196*b^3*c^4 - 2797525874791849875052267*b^3*c^3 - 532785478425782752573659*b^3*c^2 + 128704594386659025701310*b^3*c - 74654027875861178884084*b^3 + 54830334312903844255484*b^2*c^6 + 3357035005960100906561788*b^2*c^5 + 517835453236706179666309*b^2*c^4 + 5034689006946652267564118*b^2*c^3 - 3180540291949775536229462*b^2*c^2 + 1539553141897858208096378*b^2*c - 219801907512726801477952*b^2 - 3442393986552890497630648*b*c^6 + 14221443731451693411089832*b*c^5 - 24155045145836742293377619*b*c^4 + 13214160160981097946161089*b*c^3 - 3733939562555361871370348*b*c^2 + 560087500650511248307262*b*c - 43614177437453495072948*b + 712794346067749975321292*c^7 - 4237939923377837206159110*c^6 + 13216033611814827017390003*c^5 - 18601574000057909664221110*c^4 + 11531763429776755074965700*c^3 - 2587040103736344246073659*c^2 - 25576181320358137244023*c + 46264439761457629238362)/463967372565043937268) * h1 + ((3556276513308741511408030*b^2*c^5 - 5499446810620191371480822*b^2*c^4 - 894152554396408828344522*b^2*c^3 + 2880167980508475849137868*b^2*c^2 - 964047265408487263982225*b^2*c + 53334683884402610968102*b^2 - 1469233496132560505674568*b*c^6 - 12300173593186374419248236*b*c^5 + 33928743001345826565686177*b*c^4 - 23804886896997889771106562*b*c^3 + 7094876435255540729994650*b*c^2 - 861491917075496627104842*b*c + 23145310922386832503676*b + 164491002938711532766452*c^7 + 4075537409400254717712622*c^6 - 9530594730463744335028027*c^5 + 6431592454646454579455202*c^4 - 2926139343028557081812529*c^3 + 1161268178254919318059087*c^2 - 271180545937647246002363*c + 25847392922418075817498)/463967372565043937268) * h2 + (-(57466753086778448204997*b^2*c - 18560470044830811023806*b^2 - 63036595838734210862773*b*c^2 - 77161355318803718428303*b*c + 18642899584138397981578*b + 13707583578225961063871*c^3 + 33444867611943421410685*c^2 - 18274225184247015074599*c + 25383425549853031880230)/463967372565043937268) * h3

private lemma rejectI_17_24 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, c) = 0) (h2 : locus b (c, c, 1) = 0)
    (h3 : edge b b c (b, c, c) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((c - 2)*(289523816*b^3 - 7345786621*b^2 - 35886371632*b*c^2 + 81503994416*b*c + 877899095*b + 12259803776*c^3 - 52272871754*c^2 + 67771379047*c - 27753264202)/5046867) * h0 + ((18735616*b^7 + 108672256*b^6*c - 429069632*b^6 + 1737142896*b^5*c^3*z - 5211428688*b^5*c^2*z - 930254592*b^5*c^2 + 3474285792*b^5*c*z + 2912597856*b^5*c - 1274081952*b^5 - 51023291310*b^4*c^3*z + 2370126464*b^4*c^3 + 153069873930*b^4*c^2*z - 8056686240*b^4*c^2 - 102046582620*b^4*c*z + 5019546272*b^4*c + 2061962656*b^4 - 216186801240*b^3*c^5*z + 1141058656008*b^3*c^4*z - 2972957696*b^3*c^4 - 1729170657318*b^3*c^3*z + 12596004016*b^3*c^3 + 442903398498*b^3*c^2*z - 13277209520*b^3*c^2 + 361395404052*b^3*c*z - 1180866384*b^3*c + 2125657744*b^3 + 72690251208*b^2*c^6*z + 357682295019*b^2*c^5*z + 1682035392*b^2*c^5 - 3230787103491*b^2*c^4*z - 9386890688*b^2*c^4 + 5935285387935*b^2*c^3*z + 14111426512*b^2*c^3 - 2808978652101*b^2*c^2*z + 262682016*b^2*c^2 - 325892178570*b^2*c*z - 6846833648*b^2*c - 2652626976*b^2 - 287139909552*b*c^6*z + 1817054980647*b*c^5*z + 2840394688*b*c^5 - 4738489227825*b*c^4*z - 8829549840*b*c^4 + 6410700776085*b*c^3*z + 19709140016*b*c^3 - 4402871747439*b*c^2*z + 8616907568*b*c^2 + 1200745128084*b*c*z - 83157004416*b*c + 918090232*b + 72690251208*c^7*z - 446975087469*c^6*z - 11709760*c^6 + 1080530229165*c^5*z - 35129280*c^5 - 1318419460050*c^4*z - 9045795520*c^4 + 850989612498*c^3*z + 3009980112*c^3 - 270350081025*c^2*z - 42766608576*c^2 + 31534535673*c*z + 181826550976*c - 4085334104)/60562404) * h1 + ((214449658344*b^2*c^6*z - 1958550474426*b^2*c^5*z - 288067200*b^2*c^5 + 6828217675308*b^2*c^4*z - 756455984*b^2*c^4 - 10567529358288*b^2*c^3*z - 1720841200*b^2*c^3 + 6621088555800*b^2*c^2*z - 11338834560*b^2*c^2 - 1137676056738*b^2*c*z - 31697999232*b^2*c + 167135178000*b^2 - 72690251208*b*c^7*z + 446975087469*b*c^6*z + 11709760*b*c^6 - 1080530229165*b*c^5*z + 1305438144*b*c^5 + 1318419460050*b*c^4*z + 2821588800*b*c^4 - 850989612498*b*c^3*z + 6646797616*b*c^3 + 270350081025*b*c^2*z + 38966808128*b*c^2 - 31534535673*b*c*z - 173935524352*b*c - 15061873872*b + 211718144*c^5 - 1322781248*c^4 + 3173943552*c^3 + 143415320704*c^2 - 625159108216*c + 665662994580)/60562404) * h2 + (-16*(292744*b + 3308096*c - 7436073)/15140601) * h3

private lemma rejectI_18_23 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, 1, 1) = 0) (h2 : locus b (c, b, c) = 0)
    (h3 : edge b b c (c, 1, 1) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((72827556*b^2*c*z - 5947581*b^2*c - 660763884*b^2*z + 53944321*b^2 - 587936328*b*c^2*z + 48014778*b*c^2 - 952074108*b*c*z + 78138818*b*c + 2643055536*b*z - 215445263*b - 660763884*c^3*z + 53962359*c^3 + 2643055536*c^2*z - 215445263*c^2 - 1505280)/1505280) * h0 + ((72827556*b^5*c^2*z^2 - 7010757*b^5*c^2*z + 86826*b^5*c^2 - 733591440*b^5*c*z^2 + 60246294*b^5*c*z + 248066*b^5*c + 660763884*b^5*z^2 - 53235537*b^5*z + 80620*b^5 - 733591440*b^4*c^3*z^2 + 59909940*b^4*c^3*z + 1030217544*b^4*c^2*z^2 - 76801539*b^4*c^2*z - 564369*b^4*c^2 + 3007193316*b^4*c*z^2 - 247713693*b^4*c*z - 1488396*b^4*c - 3303819420*b^4*z^2 + 266022860*b^4*z - 279067*b^4 + 660763884*b^3*c^4*z^2 - 53962359*b^3*c^4*z + 3007193316*b^3*c^3*z^2 - 244396750*b^3*c^3*z - 130239*b^3*c^3 - 6680466396*b^3*c^2*z^2 + 532413219*b^3*c^2*z + 458954*b^3*c^2 + 369453660*b^3*c*z^2 - 32340651*b^3*c*z + 1916320*b^3*c + 2643055536*b^3*z^2 - 208801299*b^3*z + 272861*b^3 - 3303819420*b^2*c^4*z^2 + 265559091*b^2*c^4*z + 347304*b^2*c^4 + 369453660*b^2*c^3*z^2 - 30188924*b^2*c^3*z + 1203123*b^2*c^3 + 5577421296*b^2*c^2*z^2 - 445611405*b^2*c^2*z + 1097679*b^2*c^2 - 2643055536*b^2*c*z^2 + 222201082*b^2*c*z + 99209*b^2*c - 3454436*b^2*z - 117827*b^2 + 2643055536*b*c^4*z^2 - 191927976*b*c^4*z - 1953585*b*c^4 - 2643055536*b*c^3*z^2 + 160542356*b*c^3*z - 1420014*b*c^3 + 42018266*b*c^2*z + 3919205*b*c^2 - 17100300*b*c*z - 2858617*b*c + 663067432*b*z - 53578428*b - 4252704*c^5*z + 347304*c^5 + 9657182*c^4*z + 248037*c^4 - 7087840*c^3*z - 768964*c^3 + 2303548*c^2*z + 372041*c^2 - 154947*c - 3230991864*z + 263262464)/1505280) * h1 + ((708784*b^5*z + 80620*b^5 - 4961488*b^4*z - 564340*b^4 + 9214192*b^3*z + 1048060*b^3 - 2126352*b^2*z - 241860*b^2 + 4252704*b*c^5*z - 347304*b*c^5 - 22415294*b*c^4*z + 793875*b*c^4 + 41109472*b*c^3*z + 1029326*b*c^3 - 32072476*b*c^2*z - 3609137*b*c^2 + 9214192*b*c*z + 1643111*b*c - 660763884*b*z + 53944321*b - 531588*c^5*z + 43413*c^5 + 708784*c^4*z + 80620*c^4 - 660763884*c*z + 53962359*c + 2643055536*z - 215445263)/1505280) * h2 + ((531588*c*z - 43413*c - 708784*z - 80620)/1505280) * h3

private lemma rejectI_19_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, 1, b) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (c, 1, b) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(179262722*b^7 - 118009364*b^6 - 2775554416*b^5 + 4607647108*b^4 + 5473365332*b^3 - 4263242308*b^2 - 2510329080*b*c^5 + 26559614369*b*c^4 - 106128795086*b*c^3 + 197850633397*b*c^2 - 167108277817*b*c + 13307975603*b + 451019331*c^6 - 6384217269*c^5 + 36650738232*c^4 - 105256133789*c^3 + 161343652633*c^2 - 127276862328*c + 39652031722)/256412500) * h1 + ((2711730*b^7*c - 176550992*b^7 - 273093198*b^6*c^2 + 1133416620*b^6*c + 1720052284*b^6 + 572416887*b^5*c^3 + 198977332*b^5*c^2 - 9358002519*b^5*c + 444942476*b^5 - 435870288*b^4*c^4 - 1999964841*b^4*c^3 + 12328115600*b^4*c^2 - 1607046751*b^4*c - 10602325864*b^4 + 150339777*b^3*c^5 + 653620211*b^3*c^4 - 6151050830*b^3*c^3 + 12066581813*b^3*c^2 - 7388297326*b^3*c + 27307825551*b^3 + 542118801*b^2*c^5 + 6493812115*b^2*c^4 - 48232203928*b^2*c^3 + 80959326876*b^2*c^2 - 53335264832*b^2*c + 8772838208*b^2 - 736549842*b*c^6 - 3516756031*b*c^5 + 44671709550*b*c^4 - 118186813783*b*c^3 + 132707130340*b*c^2 - 43777491343*b*c - 65996087841*b + 150339777*c^7 - 393334768*c^6 - 410177948*c^5 + 604200351*c^4 - 4765638619*c^3 + 26515260643*c^2 - 47459973884*c + 39908444222)/256412500) * h2 + (-(1355865*b^2*c - 89631361*b^2 - 135190734*b*c^2 + 534839107*b*c - 209889401*b + 150339777*c^3 - 694014322*c^2 + 526831365*c + 580202148)/256412500) * h3

private lemma rejectI_22_25 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, b, b) = 0) (h2 : locus b (c, c, b) = 0)
    (h3 : edge b b c (c, b, b) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(2*b^5*c^2 - 2*b^5 - 4*b^4*c^3 - 12*b^4*c^2 + 20*b^4*c + 4*b^4 - b^3*c^4 + 38*b^3*c^3 - 45*b^3*c^2 - 48*b^3*c + 8*b^3 + b^2*c^5 + 6*b^2*c^4 - 79*b^2*c^3 + 187*b^2*c^2 - 51*b^2*c - 6*b*c^5 - 19*b*c^4 + 65*b*c^3 - 54*b*c^2 + 47*b*c - 8*b + c^6 + 7*c^5 - 18*c^4 + 7*c^3 - 8*c^2)) * h1 + (-z*(2*b^2*c^5 - 19*b^2*c^4 + 50*b^2*c^3 - 55*b^2*c^2 + 45*b^2*c - 16*b^2 - b*c^6 + 6*b*c^5 + 15*b*c^4 - 70*b*c^3 + 45*b*c^2 - 23*b*c + 8*b - 2*c^6 + 5*c^5 - c^4)) * h2 + (z*(b*c - b - 2*c^2 + 5*c - 1)) * h3

private lemma rejectI_22_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, b, b) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (c, b, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-6*b^2*c*z + 6*b^2*z + 6*b*c^2*z - 6*b*c*z - 1) * h0 + (-c*z*(6*b^4*c^2*z - 12*b^4*c*z + 6*b^4*z - 6*b^3*c^3*z - 6*b^3*c^2*z + 30*b^3*c*z - 18*b^3*z - 6*b^2*c^4*z + 54*b^2*c^3*z - 108*b^2*c^2*z + 78*b^2*c*z + b^2*c - 18*b^2*z - b^2 + 6*b*c^4*z - 24*b*c^3*z + 12*b*c^2*z + 24*b*c*z - 3*b*c - 18*b*z + 3*b + 72*c^4*z - 426*c^3*z + 654*c^2*z - 66*c*z - 4*c - 18*z + 9)) * h1 + (-z*(6*b*c^6*z - 60*b*c^5*z + 162*b*c^4*z - 6*b*c^3*z - b*c^3 - 300*b*c^2*z + 5*b*c^2 - 18*b*c*z - 3*b*c - 6*b + 18*c^6*z - 138*c^5*z + 360*c^4*z - 360*c^3*z - c^3 + 102*c^2*z + 4*c^2 + 18*c*z - 3*c)) * h2

private lemma rejectI_25_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, c, b) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (c, c, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-b*z*(b^3 + b^2*c - 4*b^2 - b*c^2 + 4*b + 4*c^2 - 17*c + 4)) * h1 + (z*(b^4 - 4*b^3 + 4*b^2 + 5*b*c^2 - 21*b*c + 4*b - c^3 + 4*c^2)) * h2

private lemma conflictI (b c z : ℝ) (i j : Fin 27)
    (h0 : invCondition b b c z = 0)
    (hi : locus b (profile b c i) = 0) (hj : locus b (profile b c j) = 0)
    (he : edge b b c (profile b c i) (profile b c j) = 0)
    (hlt : i < j) (hcol : colorsI i = colorsI j) : False := by
  fin_cases i
  · have possible : ∀ k : Fin 27, 0 < k → colorsI 0 = colorsI k → k = 1 ∨ k = 8 ∨ k = 9 ∨ k = 21 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectI_0_1 b c z h0 hi hj he
    · exact rejectI_0_8 b c z h0 hi hj he
    · exact rejectI_0_9 b c z h0 hi hj he
    · exact rejectI_0_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 1 < k → colorsI 1 = colorsI k → k = 8 ∨ k = 9 ∨ k = 21 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectI_1_8 b c z h0 hi hj he
    · exact rejectI_1_9 b c z h0 hi hj he
    · exact rejectI_1_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 2 < k → colorsI 2 = colorsI k → k = 12 ∨ k = 14 ∨ k = 15 ∨ k = 17 ∨ k = 24 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl
    · exact rejectI_2_12 b c z h0 hi hj he
    · exact rejectI_2_14 b c z h0 hi hj he
    · exact rejectI_2_15 b c z h0 hi hj he
    · exact rejectI_2_17 b c z h0 hi hj he
    · exact rejectI_2_24 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 3 < k → colorsI 3 = colorsI k → k = 6 ∨ k = 7 ∨ k = 10 ∨ k = 18 ∨ k = 23 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl
    · exact rejectI_3_6 b c z h0 hi hj he
    · exact rejectI_3_7 b c z h0 hi hj he
    · exact rejectI_3_10 b c z h0 hi hj he
    · exact rejectI_3_18 b c z h0 hi hj he
    · exact rejectI_3_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 4 < k → colorsI 4 = colorsI k → k = 13 ∨ k = 22 ∨ k = 25 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectI_4_13 b c z h0 hi hj he
    · exact rejectI_4_22 b c z h0 hi hj he
    · exact rejectI_4_25 b c z h0 hi hj he
    · exact rejectI_4_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 5 < k → colorsI 5 = colorsI k → k = 11 ∨ k = 16 ∨ k = 19 ∨ k = 20 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectI_5_11 b c z h0 hi hj he
    · exact rejectI_5_16 b c z h0 hi hj he
    · exact rejectI_5_19 b c z h0 hi hj he
    · exact rejectI_5_20 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 6 < k → colorsI 6 = colorsI k → k = 7 ∨ k = 10 ∨ k = 18 ∨ k = 23 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectI_6_7 b c z h0 hi hj he
    · exact rejectI_6_10 b c z h0 hi hj he
    · exact rejectI_6_18 b c z h0 hi hj he
    · exact rejectI_6_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 7 < k → colorsI 7 = colorsI k → k = 10 ∨ k = 18 ∨ k = 23 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectI_7_10 b c z h0 hi hj he
    · exact rejectI_7_18 b c z h0 hi hj he
    · exact rejectI_7_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 8 < k → colorsI 8 = colorsI k → k = 9 ∨ k = 21 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectI_8_9 b c z h0 hi hj he
    · exact rejectI_8_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 9 < k → colorsI 9 = colorsI k → k = 21 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectI_9_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 10 < k → colorsI 10 = colorsI k → k = 18 ∨ k = 23 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectI_10_18 b c z h0 hi hj he
    · exact rejectI_10_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 11 < k → colorsI 11 = colorsI k → k = 16 ∨ k = 19 ∨ k = 20 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectI_11_16 b c z h0 hi hj he
    · exact rejectI_11_19 b c z h0 hi hj he
    · exact rejectI_11_20 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 12 < k → colorsI 12 = colorsI k → k = 14 ∨ k = 15 ∨ k = 17 ∨ k = 24 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectI_12_14 b c z h0 hi hj he
    · exact rejectI_12_15 b c z h0 hi hj he
    · exact rejectI_12_17 b c z h0 hi hj he
    · exact rejectI_12_24 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 13 < k → colorsI 13 = colorsI k → k = 22 ∨ k = 25 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectI_13_22 b c z h0 hi hj he
    · exact rejectI_13_25 b c z h0 hi hj he
    · exact rejectI_13_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 14 < k → colorsI 14 = colorsI k → k = 15 ∨ k = 17 ∨ k = 24 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectI_14_15 b c z h0 hi hj he
    · exact rejectI_14_17 b c z h0 hi hj he
    · exact rejectI_14_24 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 15 < k → colorsI 15 = colorsI k → k = 17 ∨ k = 24 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectI_15_17 b c z h0 hi hj he
    · exact rejectI_15_24 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 16 < k → colorsI 16 = colorsI k → k = 19 ∨ k = 20 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectI_16_19 b c z h0 hi hj he
    · exact rejectI_16_20 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 17 < k → colorsI 17 = colorsI k → k = 24 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectI_17_24 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 18 < k → colorsI 18 = colorsI k → k = 23 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectI_18_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 19 < k → colorsI 19 = colorsI k → k = 20 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectI_19_20 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 20 < k → colorsI 20 = colorsI k → False := by decide
    exact possible j hlt hcol
  · have possible : ∀ k : Fin 27, 21 < k → colorsI 21 = colorsI k → False := by decide
    exact possible j hlt hcol
  · have possible : ∀ k : Fin 27, 22 < k → colorsI 22 = colorsI k → k = 25 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectI_22_25 b c z h0 hi hj he
    · exact rejectI_22_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 23 < k → colorsI 23 = colorsI k → False := by decide
    exact possible j hlt hcol
  · have possible : ∀ k : Fin 27, 24 < k → colorsI 24 = colorsI k → False := by decide
    exact possible j hlt hcol
  · have possible : ∀ k : Fin 27, 25 < k → colorsI 25 = colorsI k → k = 26 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectI_25_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 26 < k → colorsI 26 = colorsI k → False := by decide
    exact possible j hlt hcol

private def squared (x y : ℝ × ℝ) := (x.1-y.1)^2 + (x.2-y.2)^2
private def len (x : ℝ × ℝ) := x.1^2 + x.2^2
private def dot (x y : ℝ × ℝ) := x.1*y.1 + x.2*y.2
private noncomputable def coords (o : ℝ²) (r : ℝ) (x : ℝ²) : ℝ × ℝ :=
  ((x 0-o 0)/r, (x 1-o 1)/r)

private lemma coords_sq (o x y : ℝ²) (r : ℝ) :
    squared (coords o r x) (coords o r y) = dist x y ^ 2 / r^2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs, squared, coords, div_eq_mul_inv]
  ring

private lemma coords_len (o x : ℝ²) (r : ℝ) :
    len (coords o r x) = dist x o ^ 2 / r^2 := by
  simpa [squared, coords, len] using coords_sq o x o r

private lemma squared_pos (o x y : ℝ²) {r : ℝ} (hr : 0 < r) (hne : x ≠ y) :
    0 < squared (coords o r x) (coords o r y) := by
  rw [coords_sq]
  exact div_pos (sq_pos_of_pos (dist_pos.mpr hne)) (sq_pos_of_pos hr)

private lemma squared_symm (x y : ℝ × ℝ) : squared x y = squared y x := by
  simp only [squared]
  ring

private lemma antipodal (e f : ℝ × ℝ) (he : len e = 1) (hf : len f = 1)
    (h : squared e f = 4) : f = (-e.1, -e.2) := by
  have hz : (e.1+f.1)^2 + (e.2+f.2)^2 = 0 := by
    unfold squared at h
    unfold len at he hf
    linear_combination 2*he + 2*hf - h
  exact Prod.ext (by dsimp; nlinarith [sq_nonneg (e.2+f.2), sq_nonneg (e.1+f.1)])
    (by dsimp; nlinarith [sq_nonneg (e.1+f.1), sq_nonneg (e.2+f.2)])

private def geometric (e f x : ℝ × ℝ) := (len x, squared x e, squared x f)

private lemma geom_u (e f x : ℝ × ℝ) (he : len e = 1) :
    u (geometric e f x) = 2 * dot e x := by
  simp only [u, geometric, squared, len, dot]
  unfold len at he
  linear_combination -he

private lemma geom_v (e f x : ℝ × ℝ) (hf : len f = 1) :
    v (geometric e f x) = 2 * dot f x := by
  simp only [v, geometric, squared, len, dot]
  unfold len at hf
  linear_combination -hf

private lemma basis_t (e f : ℝ × ℝ) (he : len e = 1) (hf : len f = 1) :
    squared e f = 2 - 2*dot e f := by
  simp only [squared, dot]
  unfold len at he hf
  linear_combination he + hf

private lemma gram (e f w : ℝ × ℝ) (he : len e = 1) (hf : len f = 1) :
    quad (squared e f) (2*dot e w) (2*dot f w) = delta (squared e f) * len w := by
  have h : len f * (dot e w)^2 + len e * (dot f w)^2 - 2*dot e f*dot e w*dot f w =
      (len e * len f - (dot e f)^2) * len w := by
    unfold len dot
    ring
  rw [he, hf] at h
  rw [basis_t e f he hf]
  unfold quad delta
  linear_combination 4*h

private lemma geom_locus (e f x : ℝ × ℝ) (he : len e = 1) (hf : len f = 1) :
    locus (squared e f) (geometric e f x) = 0 := by
  unfold locus
  rw [geom_u _ _ _ he, geom_v _ _ _ hf, gram _ _ _ he hf]
  exact sub_self _

private lemma geom_sep (e f x y : ℝ × ℝ) (he : len e = 1) (hf : len f = 1) :
    sep (squared e f) (geometric e f x) (geometric e f y) =
    delta (squared e f) * squared x y := by
  let w : ℝ × ℝ := (x.1-y.1,x.2-y.2)
  have hd (a : ℝ × ℝ) : 2*dot a x - 2*dot a y = 2*dot a w := by
    simp only [dot,w]
    ring
  unfold sep
  rw [geom_u _ _ _ he, geom_u _ _ _ he, geom_v _ _ _ hf, geom_v _ _ _ hf,
    hd, hd, gram _ _ _ he hf]
  rfl

private lemma pad_distances (D : Finset ℝ) (hcard : D.card ≤ 3) (h1 : 1 ∈ D)
    (h0 : 0 ∉ D) : ∃ b c : ℝ, b ≠ 0 ∧ c ≠ 0 ∧ b ≠ 1 ∧ c ≠ 1 ∧ b ≠ c ∧
      ∀ d ∈ D, d = 1 ∨ d = b ∨ d = c := by
  classical
  obtain ⟨T, hT, hfour⟩ := Infinite.exists_superset_card_eq (insert 0 D) 4
    (by rw [Finset.card_insert_of_notMem h0]; omega)
  have z : (0:ℝ) ∈ T := hT (by simp)
  have one : (1:ℝ) ∈ T.erase 0 := Finset.mem_erase.mpr ⟨one_ne_zero, hT (by simp [h1])⟩
  have two : ((T.erase 0).erase 1).card = 2 := by
    rw [Finset.card_erase_of_mem one, Finset.card_erase_of_mem z, hfour]
  obtain ⟨b,c,hbc,hs⟩ := Finset.card_eq_two.mp two
  have hb : b ∈ (T.erase 0).erase 1 := by simp [hs]
  have hc : c ∈ (T.erase 0).erase 1 := by simp [hs]
  simp only [Finset.mem_erase] at hb hc
  refine ⟨b,c,hb.2.1,hc.2.1,hb.1,hc.1,hbc,?_⟩
  intro d hd
  by_cases h : d = 1
  · exact Or.inl h
  right
  have hmem : d ∈ (T.erase 0).erase 1 :=
    Finset.mem_erase.mpr ⟨h, Finset.mem_erase.mpr ⟨fun e => h0 (e ▸ hd), hT (Finset.mem_insert_of_mem hd)⟩⟩
  simpa [hs] using hmem

private def inPalette (b c x : ℝ) : Prop := x = 1 ∨ x = b ∨ x = c

private lemma profile_exists (b c x y z : ℝ)
    (hx : inPalette b c x) (hy : inPalette b c y) (hz : inPalette b c z) :
    ∃ i : Fin 27, profile b c i = (x,y,z) := by
  have index (w : ℝ) (hw : inPalette b c w) : ∃ i : Fin 3, palette b c i.val = w := by
    rcases hw with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  obtain ⟨i, rfl⟩ := index x hx
  obtain ⟨j, rfl⟩ := index y hy
  obtain ⟨k, rfl⟩ := index z hz
  have pack : ∀ i j k : Fin 3, ∃ n : Fin 27,
      n.val / 9 = i.val ∧ n.val / 3 % 3 = j.val ∧ n.val % 3 = k.val := by decide
  obtain ⟨n,h1,h2,h3⟩ := pack i j k
  exact ⟨n, by simp only [profile,h1,h2,h3]⟩

private lemma color_bound (R : Finset ℝ²) (X : ℝ² → ℝ × ℝ) (e f : ℝ × ℝ)
    (he : len e = 1) (hf : len f = 1) (b c : ℝ) (hd : delta (squared e f) ≠ 0)
    (col : Fin 27 → Fin 5)
    (conflict : ∀ i j : Fin 27, locus (squared e f) (profile b c i) = 0 →
      locus (squared e f) (profile b c j) = 0 →
      edge (squared e f) b c (profile b c i) (profile b c j) = 0 →
      i < j → col i = col j → False)
    (mem : ∀ x ∈ R, inPalette b c (len (X x)) ∧
      inPalette b c (squared (X x) e) ∧ inPalette b c (squared (X x) f))
    (pairs : ∀ x ∈ R, ∀ y ∈ R, x ≠ y →
      squared (X x) (X y) ≠ 0 ∧ inPalette b c (squared (X x) (X y))) : R.card ≤ 5 := by
  classical
  have codes (x : R) : ∃ i : Fin 27, profile b c i = geometric e f (X x) := by
    obtain ⟨h1,h2,h3⟩ := mem x x.property
    exact profile_exists b c _ _ _ h1 h2 h3
  choose idx eqn using codes
  have loc (x : R) : locus (squared e f) (profile b c (idx x)) = 0 := by
    rw [eqn]; exact geom_locus _ _ _ he hf
  have no_lt (x y : R) (ne : x ≠ y) (lt : idx x < idx y) (co : col (idx x) = col (idx y)) : False := by
    apply conflict _ _ (loc x) (loc y) _ lt co
    obtain ⟨_,ds⟩ := pairs x x.property y y.property (fun h => ne (Subtype.ext h))
    rw [eqn,eqn]
    unfold edge
    rw [geom_sep _ _ _ _ he hf]
    rcases ds with d | d | d <;> rw [d] <;> ring
  have inj : Function.Injective (fun x : R => col (idx x)) := by
    intro x y hcol
    by_contra hne
    rcases lt_trichotomy (idx x) (idx y) with h | h | h
    · exact no_lt x y hne h hcol
    · have hp := (eqn x).symm.trans ((congrArg (profile b c) h).trans (eqn y))
      have hs := geom_sep e f (X x) (X y) he hf
      rw [hp] at hs
      simp [sep,quad] at hs
      exact hs.elim hd (pairs x x.property y y.property (fun h => hne (Subtype.ext h))).1
    · exact no_lt y x (Ne.symm hne) h hcol.symm
  simpa using Fintype.card_le_of_injective _ inj

private lemma radius_anchors (S : Finset ℝ²) (hS : S.card = 9)
    (hD : (distanceSet S).card ≤ 3) (o : ℝ²) (ho : o ∈ S) :
    ∃ (r : ℝ) (a b : ℝ²), 0 < r ∧ a ∈ S ∧ b ∈ S ∧
      a ≠ o ∧ b ≠ o ∧ a ≠ b ∧
      len (coords o r a) = 1 ∧ len (coords o r b) = 1 ∧
      squared (coords o r a) (coords o r b) ≠ 4 := by
  classical
  have maps (x : ℝ²) (hx : x ∈ S.erase o) : dist x o ∈ distanceSet S := by
    obtain ⟨hne,hx⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_image.mpr ⟨(x,o),Finset.mem_offDiag.mpr ⟨hx,ho,hne⟩,rfl⟩
  have hlt : (distanceSet S).card * 2 < (S.erase o).card := by
    rw [Finset.card_erase_of_mem ho,hS]; omega
  obtain ⟨r,_,hr⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to maps hlt
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp hr
  simp only [Finset.mem_filter,Finset.mem_erase] at ha hb hc
  have rp : 0 < r := ha.2 ▸ dist_pos.mpr ha.1.1
  have normalized (x : ℝ²) (hx : dist x o = r) : len (coords o r x) = 1 := by
    rw [coords_len,hx,div_self (pow_ne_zero _ rp.ne')]
  refine ⟨r,a,?_⟩
  by_cases h : squared (coords o r a) (coords o r b) = 4
  · refine ⟨c,rp,ha.1.2,hc.1.2,ha.1.1,hc.1.1,hac,normalized a ha.2,normalized c hc.2,?_⟩
    intro hc4
    have eq := (antipodal _ _ (normalized a ha.2) (normalized b hb.2) h).trans
      (antipodal _ _ (normalized a ha.2) (normalized c hc.2) hc4).symm
    have pos := squared_pos o b c rp hbc
    rw [eq] at pos
    simpa [squared] using pos
  · exact ⟨b,rp,ha.1.2,hb.1.2,ha.1.1,hb.1.1,hab,normalized a ha.2,normalized b hb.2,h⟩

private def validColoring (t b c : ℝ) (col : Fin 27 → Fin 5) : Prop :=
  ∀ i j : Fin 27, locus t (profile b c i) = 0 → locus t (profile b c j) = 0 →
    edge t b c (profile b c i) (profile b c j) = 0 → i < j → col i = col j → False

private lemma lower_from_colors
    (colorings : ∀ t b c z : ℝ, (t = 1 ∨ t = b) → invCondition t b c z = 0 →
      ∃ col, validColoring t b c col)
    (S : Finset ℝ²) (hS : S.card = 9) : 4 ≤ distinctDistances S := by
  classical
  by_contra! h
  have hD : (distanceSet S).card ≤ 3 := by change distinctDistances S ≤ 3; omega
  obtain ⟨o,ho⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨r,a,f,hr,ha,hf,hao,hfo,haf,unitA,unitF,notFour⟩ :=
    radius_anchors S hS hD o ho
  let X := coords o r
  let t := squared (X a) (X f)
  have ht : t ≠ 0 := (squared_pos o a f hr haf).ne'
  have hd : delta t ≠ 0 := mul_ne_zero ht (sub_ne_zero.mpr (Ne.symm notFour))
  let D := (distanceSet S).image (fun d : ℝ => d^2 / r^2)
  have inD (x : ℝ²) (hx : x ∈ S) (y : ℝ²) (hy : y ∈ S) (hne : x ≠ y) :
      squared (X x) (X y) ∈ D := by
    refine Finset.mem_image.mpr ⟨dist x y,Finset.mem_image.mpr
      ⟨(x,y),Finset.mem_offDiag.mpr ⟨hx,hy,hne⟩,rfl⟩,(coords_sq _ _ _ _).symm⟩
  have origin (x : ℝ²) : squared (X x) (X o) = len (X x) := by
    simp only [X,coords_sq,coords_len]
  have one : 1 ∈ D := by
    have hh := inD a ha o ho hao
    rwa [origin,unitA] at hh
  have zero : 0 ∉ D := by
    intro hz
    obtain ⟨d,hm,eq⟩ := Finset.mem_image.mp hz
    obtain ⟨⟨x,y⟩,hp,rfl⟩ := Finset.mem_image.mp hm
    have ne := (Finset.mem_offDiag.mp hp).2.2
    exact (div_pos (sq_pos_of_pos (dist_pos.mpr ne)) (sq_pos_of_pos hr)).ne' eq
  obtain ⟨b,c,b0,c0,b1,c1,bc,cover⟩ := pad_distances D (Finset.card_image_le.trans hD) one zero
  have tmem := cover t (inD a ha f hf haf)
  have oriented : ∃ b c : ℝ, b ≠ 0 ∧ c ≠ 0 ∧ b ≠ 1 ∧ c ≠ 1 ∧ b ≠ c ∧
      (t = 1 ∨ t = b) ∧ ∀ d ∈ D, inPalette b c d := by
    rcases tmem with e | e | e
    · exact ⟨b,c,b0,c0,b1,c1,bc,Or.inl e,cover⟩
    · exact ⟨b,c,b0,c0,b1,c1,bc,Or.inr e,cover⟩
    · refine ⟨c,b,c0,b0,c1,b1,bc.symm,Or.inr e,?_⟩
      intro d hmem
      rcases cover d hmem with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
  obtain ⟨B,C,B0,C0,B1,C1,BC,shape,pal⟩ := oriented
  let factor := B*C*(B-1)*(C-1)*(B-C)*delta t
  have nonzero : factor ≠ 0 := by
    dsimp [factor]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero B0 C0)
      (sub_ne_zero.mpr B1)) (sub_ne_zero.mpr C1)) (sub_ne_zero.mpr BC)) hd
  have inv : invCondition t B C factor⁻¹ = 0 := by
    unfold invCondition
    rw [show factor⁻¹*B*C*(B-1)*(C-1)*(B-C)*delta t = factor⁻¹*factor by dsimp [factor]; ring]
    rw [inv_mul_cancel₀ nonzero, sub_self]
  obtain ⟨col,hcol⟩ := colorings t B C factor⁻¹ shape inv
  let R := ((S.erase o).erase a).erase f
  have rem (x : ℝ²) (hx : x ∈ R) : x ≠ f ∧ x ≠ a ∧ x ≠ o ∧ x ∈ S := by
    simpa only [R,Finset.mem_erase] using hx
  have amem : a ∈ S.erase o := Finset.mem_erase.mpr ⟨hao,ha⟩
  have fmem : f ∈ (S.erase o).erase a :=
    Finset.mem_erase.mpr ⟨haf.symm, Finset.mem_erase.mpr ⟨hfo,hf⟩⟩
  have size : R.card = 6 := by
    simp only [R,Finset.card_erase_of_mem fmem,Finset.card_erase_of_mem amem,
      Finset.card_erase_of_mem ho,hS]
  have bound := color_bound R X (X a) (X f) unitA unitF B C hd col hcol (by
    intro x hx
    obtain ⟨xf,xa,xo,xS⟩ := rem x hx
    refine ⟨?_,pal _ (inD x xS a ha xa),pal _ (inD x xS f hf xf)⟩
    rw [← origin]
    exact pal _ (inD x xS o ho xo)) (by
    intro x hx y hy ne
    exact ⟨(squared_pos o x y hr ne).ne',pal _ (inD x (rem x hx).2.2.2 y (rem y hy).2.2.2 ne)⟩)
  omega

private lemma nine_lower (S : Finset ℝ²) (hs : S.card = 9) : 4 ≤ distinctDistances S := by
  apply lower_from_colors _ S hs
  intro t b c z shape inv
  rcases shape with eq | eq
  · subst t
    exact ⟨colorsE, fun i j => conflictE b c z i j inv⟩
  · subst t
    exact ⟨colorsI, fun i j => conflictI b c z i j inv⟩

end OMA.NineDistances

namespace OMA.Erdos91Nine

open EuclideanGeometry Finset Erdos91

private def firstPoints : Finset (ℤ × ℤ) :=
  {(0, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-2, -1)}

private def secondPoints : Finset (ℤ × ℤ) :=
  {(0, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-2, 2)}

private noncomputable def point (p : ℤ × ℤ) : ℝ² :=
  !₂[(p.1 : ℝ) + (p.2 : ℝ) / 2, (p.2 : ℝ) * Real.sqrt 3 / 2]

private noncomputable def lattice : (ℤ × ℤ) ↪ ℝ² where
  toFun := point
  inj' := by
    intro p q h
    have hx := congrArg (fun x : ℝ² => x 0) h
    have hy := congrArg (fun x : ℝ² => x 1) h
    simp only [point, Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
    have hp : (p.2 : ℝ) = q.2 := by
      apply mul_right_cancel₀ (by positivity : Real.sqrt (3 : ℝ) ≠ 0)
      linarith
    exact Prod.ext (by exact_mod_cast (show (p.1 : ℝ) = q.1 by linarith)) (by exact_mod_cast hp)

private def squareDistance (p q : ℤ × ℤ) : ℤ :=
  let x := p.1 - q.1
  let y := p.2 - q.2
  x ^ 2 + x * y + y ^ 2

private theorem lattice_square (p q : ℤ × ℤ) :
    dist (lattice p) (lattice q) ^ 2 = (squareDistance p q : ℝ) := by
  change dist (point p) (point q) ^ 2 = _
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [point, Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs,
    squareDistance, Int.cast_add, Int.cast_sub, Int.cast_pow, Int.cast_mul]
  calc
    _ = ((p.1 : ℝ) - q.1 + ((p.2 : ℝ) - q.2) / 2) ^ 2 +
        ((p.2 : ℝ) - q.2) ^ 2 * (Real.sqrt 3) ^ 2 / 4 := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring

private def squaredValues : Finset ℤ := {1, 3, 4, 7}

private theorem first_values :
    firstPoints.offDiag.image (fun p => squareDistance p.1 p.2) = squaredValues := by decide

private theorem second_values :
    secondPoints.offDiag.image (fun p => squareDistance p.1 p.2) = squaredValues := by decide

private theorem offDiag_map {α β : Type} (e : α ↪ β) (S : Finset α) :
    (S.map e).offDiag = S.offDiag.map (e.prodMap e) := by
  ext p
  rcases p with ⟨p, q⟩
  simp only [mem_offDiag, mem_map]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, hxy⟩
    exact ⟨(x, y), ⟨hx, hy, fun h => hxy (congrArg e h)⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, h⟩
    have h' : (e x, e y) = (p, q) := h
    cases h'
    exact ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, fun he => hxy (e.injective he)⟩

private theorem distances_le_four (S : Finset (ℤ × ℤ))
    (hc : S.offDiag.image (fun p => squareDistance p.1 p.2) = squaredValues) :
    distinctDistances (S.map lattice) ≤ 4 := by
  classical
  unfold distinctDistances distanceSet
  apply le_trans (card_le_card (t := squaredValues.image (fun z : ℤ => Real.sqrt (z : ℝ))) ?_)
    ((card_image_le).trans (by decide))
  intro d hd
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
  rw [offDiag_map] at hp
  obtain ⟨q, hq, rfl⟩ := mem_map.mp hp
  refine mem_image.mpr ⟨squareDistance q.1 q.2, ?_, ?_⟩
  · rw [← hc]
    exact mem_image.mpr ⟨q, hq, rfl⟩
  · change Real.sqrt (squareDistance q.1 q.2 : ℝ) = dist (lattice q.1) (lattice q.2)
    rw [← lattice_square, Real.sqrt_sq dist_nonneg]

private theorem unit_minimum (S : Finset (ℤ × ℤ))
    (hc : S.offDiag.image (fun p => squareDistance p.1 p.2) = squaredValues) :
    (∀ z ∈ (S.map lattice).offDiag, (1 : ℝ) ≤ dist z.1 z.2 ^ 2) ∧
      ∃ z ∈ (S.map lattice).offDiag, dist z.1 z.2 ^ 2 = (1 : ℝ) := by
  rw [offDiag_map]
  constructor
  · intro z hz
    obtain ⟨q, hq, rfl⟩ := mem_map.mp hz
    change (1 : ℝ) ≤ dist (lattice q.1) (lattice q.2) ^ 2
    rw [lattice_square]
    have h : squareDistance q.1 q.2 ∈ squaredValues := by
      rw [← hc]
      exact mem_image.mpr ⟨q, hq, rfl⟩
    simp only [squaredValues, mem_insert, mem_singleton] at h
    rcases h with h | h | h | h <;> rw [h] <;> norm_num
  · have h : (1 : ℤ) ∈ S.offDiag.image (fun p => squareDistance p.1 p.2) := by
      rw [hc]
      decide
    obtain ⟨q, hq, h1⟩ := mem_image.mp h
    refine ⟨(lattice.prodMap lattice) q, mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
    change dist (lattice q.1) (lattice q.2) ^ 2 = 1
    rw [lattice_square, h1, Int.cast_one]

private noncomputable def unitCount (S : Finset ℝ²) : ℕ :=
  S.offDiag.filter (fun z => dist z.1 z.2 ^ 2 = (1 : ℝ)) |>.card

private theorem unitCount_lattice (S : Finset (ℤ × ℤ)) :
    unitCount (S.map lattice) = (S.offDiag.filter fun z => squareDistance z.1 z.2 = 1).card := by
  classical
  rw [unitCount, offDiag_map, filter_map, card_map]
  congr 1
  ext z
  simp only [mem_filter, Function.comp_apply]
  change (z ∈ S.offDiag ∧ dist (lattice z.1) (lattice z.2) ^ 2 = 1) ↔
    z ∈ S.offDiag ∧ squareDistance z.1 z.2 = 1
  rw [lattice_square, ← Int.cast_one (R := ℝ), Int.cast_inj]

private theorem first_units : (firstPoints.offDiag.filter
    fun z => squareDistance z.1 z.2 = 1).card = 30 := by decide

private theorem second_units : (secondPoints.offDiag.filter
    fun z => squareDistance z.1 z.2 = 1).card = 32 := by decide

private theorem unitCount_invariant (A B : Finset ℝ²)
    (hA : (∀ z ∈ A.offDiag, (1 : ℝ) ≤ dist z.1 z.2 ^ 2) ∧
      ∃ z ∈ A.offDiag, dist z.1 z.2 ^ 2 = (1 : ℝ))
    (hB : (∀ z ∈ B.offDiag, (1 : ℝ) ≤ dist z.1 z.2 ^ 2) ∧
      ∃ z ∈ B.offDiag, dist z.1 z.2 ^ 2 = (1 : ℝ))
    (hs : DilationEquivSimilar A B) : unitCount A = unitCount B := by
  classical
  obtain ⟨f, hf⟩ := hs
  let e : ℝ² ↪ ℝ² := ⟨f, f.injective⟩
  have hmap : A.map e = B := by
    ext p
    rw [mem_map]
    change (∃ q ∈ (A : Set ℝ²), f q = p) ↔ p ∈ (B : Set ℝ²)
    rw [← hf]
    rfl
  have hpair : A.offDiag.map (e.prodMap e) = B.offDiag :=
    (offDiag_map e A).symm.trans (congrArg Finset.offDiag hmap)
  have hsquare (z : ℝ² × ℝ²) :
      dist ((e.prodMap e) z).1 ((e.prodMap e) z).2 ^ 2 =
        (Dilation.ratio f : ℝ) ^ 2 * dist z.1 z.2 ^ 2 := by
    change dist (f z.1) (f z.2) ^ 2 = _
    rw [Dilation.dist_eq, mul_pow]
  have hratio : (Dilation.ratio f : ℝ) ^ 2 = 1 := by
    apply le_antisymm
    · obtain ⟨z, hz, hd⟩ := hB.2
      rw [← hpair] at hz
      obtain ⟨u, hu, rfl⟩ := mem_map.mp hz
      rw [hsquare] at hd
      calc
        (Dilation.ratio f : ℝ) ^ 2 = (Dilation.ratio f : ℝ) ^ 2 * 1 := by ring
        _ ≤ (Dilation.ratio f : ℝ) ^ 2 * dist u.1 u.2 ^ 2 :=
          mul_le_mul_of_nonneg_left (hA.1 u hu) (sq_nonneg _)
        _ = 1 := hd
    · obtain ⟨z, hz, hd⟩ := hA.2
      have hzB : (e.prodMap e) z ∈ B.offDiag := by
        rw [← hpair]
        exact mem_map.mpr ⟨z, hz, rfl⟩
      have hh := hB.1 _ hzB
      rwa [hsquare, hd, mul_one] at hh
  unfold unitCount
  rw [← hpair, filter_map, card_map]
  congr 1
  ext z
  simp only [mem_filter, Function.comp_apply, hsquare, hratio, one_mul]

theorem witnesses :
    ∃ A B : Finset ℝ², A.card = 9 ∧ B.card = 9 ∧
      distinctDistances A ≤ 4 ∧ distinctDistances B ≤ 4 ∧ ¬DilationEquivSimilar A B := by
  refine ⟨firstPoints.map lattice, secondPoints.map lattice, ?_, ?_,
    distances_le_four _ first_values, distances_le_four _ second_values, ?_⟩
  · rw [card_map]
    decide
  · rw [card_map]
    decide
  · intro h
    have hc := unitCount_invariant _ _ (unit_minimum _ first_values) (unit_minimum _ second_values) h
    rw [unitCount_lattice, unitCount_lattice, first_units, second_units] at hc
    omega

end OMA.Erdos91Nine

open EuclideanGeometry Erdos91

theorem OMA.solution : type_of% @Erdos91.erdos_91.variants.nine := by
  intro unique
  obtain ⟨A, B, cardA, cardB, upperA, upperB, different⟩ := OMA.Erdos91Nine.witnesses
  have lower := OMA.NineDistances.nine_lower
  have countA := le_antisymm upperA (lower A cardA)
  have countB := le_antisymm upperB (lower B cardB)
  have minimum : minimalDistinctDistances ℝ² 9 = 4 := by
    unfold minimalDistinctDistances
    refine le_antisymm (Nat.sInf_le ⟨A, cardA, countA⟩) ?_
    apply le_csInf
    · exact ⟨4, A, cardA, countA⟩
    · rintro d ⟨S, cardS, rfl⟩
      exact lower S cardS
  exact different (unique A B ⟨cardA, countA.trans minimum.symm⟩
    ⟨cardB, countB.trans minimum.symm⟩)

