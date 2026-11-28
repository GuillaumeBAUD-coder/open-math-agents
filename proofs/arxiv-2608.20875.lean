import OMAStatements.S_arxiv_2608_20875

/-!
A counterexample to the symmetric-maximizer conjecture for Lyapunov operators
(D. Kressner and B. Vandereycken, https://arxiv.org/abs/2608.20875, Theorem 2).

With `L_A(X) = A * X + X * A.transpose` and `||X||^2 = frobSq X`, the operator norm of `L_A`
induced by the Frobenius norm is the larger of its norms on the symmetric and on the
skew-symmetric matrices, since both subspaces are invariant. The paper exhibits the
order-seven integer matrix `A` below, for which

  (norm of `L_A` on symmetric matrices)^2 < 1196 < (norm of `L_A` on skew ones)^2.

The right inequality is witnessed by the single integer skew-symmetric matrix `K` below:
`frobSq (lyap A K) = 64387950` while `1196 * frobSq K = 1196 * 53836 = 64387856`.

The left inequality is the exact rational certificate `sos` of the paper, a sum of squares
that equals `1196 * frobSq S - frobSq (lyap A S)` for symmetric `S` (`sos_identity`,
verified by `ring` from the explicit quadratic form `Qexpr`). Hence that quadratic form is
positive semidefinite on symmetric matrices and `sym_bound` records the inequality.

Consequently no nonzero symmetric matrix `S` satisfies
`frobSq (lyap A S) * frobSq X >= frobSq (lyap A X) * frobSq S` for every `X`: `X = K` fails.
The conjecture of the statement is therefore false.

Credit: the counterexample is due to D. Kressner and B. Vandereycken.
-/

open scoped BigOperators

namespace OMA.P_arxiv_2608_20875

open OMA.S_arxiv_2608_20875

/-- The order-seven integer matrix (4) of Kressner-Vandereycken. -/
def A : Matrix (Fin 7) (Fin 7) ℝ :=
  !![0,0,0,0,0,0,0;
       0,0,0,0,0,0,0;
       6,-5,-13,0,0,0,0;
       -14,-18,0,0,0,0,0;
       12,-12,11,0,0,0,0;
       0,0,0,-6,0,-14,0;
       0,0,0,6,-18,0,0]

/-- The skew-symmetric integer witness matrix of the paper. -/
def K : Matrix (Fin 7) (Fin 7) ℝ :=
  !![0,4,-9,41,71,4,6;
       -4,0,-11,-59,105,-12,3;
       9,11,0,59,-10,36,-8;
       -41,59,-59,0,9,0,2;
       -71,-105,10,-9,0,-15,0;
       -4,12,-36,0,15,0,4;
       -6,-3,8,-2,0,-4,0]

/-- The symmetric matrix whose upper triangle is that of `S`. -/
def SmatE (S : Matrix (Fin 7) (Fin 7) ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  !![     S 0 0, S 0 1, S 0 2, S 0 3, S 0 4, S 0 5, S 0 6;
     S 0 1, S 1 1, S 1 2, S 1 3, S 1 4, S 1 5, S 1 6;
     S 0 2, S 1 2, S 2 2, S 2 3, S 2 4, S 2 5, S 2 6;
     S 0 3, S 1 3, S 2 3, S 3 3, S 3 4, S 3 5, S 3 6;
     S 0 4, S 1 4, S 2 4, S 3 4, S 4 4, S 4 5, S 4 6;
     S 0 5, S 1 5, S 2 5, S 3 5, S 4 5, S 5 5, S 5 6;
     S 0 6, S 1 6, S 2 6, S 3 6, S 4 6, S 5 6, S 6 6]

/-- The quadratic form `frobSq (lyap A S)` for symmetric `S`, written in the entries of `S`. -/
noncomputable def Qexpr (S : Matrix (Fin 7) (Fin 7) ℝ) : ℝ :=
  752 * (S 0 0) ^ 2 + 986 * (S 1 1) ^ 2 + 918 * (S 2 2) ^ 2 + 144 * (S 3 3) ^ 2 + 648 * (S 4 4) ^ 2 + 784 * (S 5 5) ^ 2 + 1738 * (S 0 1) ^ 2 + 1404 * (S 0 2) ^ 2 + 1288 * (S 0 3) ^ 2 + 1688 * (S 0 4) ^ 2 + 1144 * (S 0 5) ^ 2 + 752 * (S 0 6) ^ 2 + 1616 * (S 1 2) ^ 2 + 1778 * (S 1 3) ^ 2 + 1922 * (S 1 4) ^ 2 + 1378 * (S 1 5) ^ 2 + 986 * (S 1 6) ^ 2 + 724 * (S 2 3) ^ 2 + 1470 * (S 2 4) ^ 2 + 1700 * (S 2 5) ^ 2 + 580 * (S 2 6) ^ 2 + 792 * (S 3 4) ^ 2 + 608 * (S 3 5) ^ 2 + 216 * (S 3 6) ^ 2 + 1040 * (S 4 5) ^ 2 + 1296 * (S 4 6) ^ 2 + 392 * (S 5 6) ^ 2 + 312 * (S 0 0) * (S 0 1) + 216 * (S 0 0) * (S 0 2) + 312 * (S 1 1) * (S 0 1) - 268 * (S 1 1) * (S 1 2) - 96 * (S 2 2) * (S 0 2) + 264 * (S 2 2) * (S 0 4) - 8 * (S 2 2) * (S 1 2) - 220 * (S 2 2) * (S 1 4) - 572 * (S 2 2) * (S 2 4) + 336 * (S 3 3) * (S 0 5) - 336 * (S 3 3) * (S 0 6) + 432 * (S 3 3) * (S 1 5) - 432 * (S 3 3) * (S 1 6) - 432 * (S 3 3) * (S 3 4) + 336 * (S 3 3) * (S 3 5) - 864 * (S 4 4) * (S 0 6) + 864 * (S 4 4) * (S 1 6) - 792 * (S 4 4) * (S 2 6) - 432 * (S 4 4) * (S 3 4) + 672 * (S 5 5) * (S 3 5) - 268 * (S 0 1) * (S 0 2) + 216 * (S 0 1) * (S 1 2) - 336 * (S 0 2) * (S 0 3) + 288 * (S 0 2) * (S 0 4) + 192 * (S 0 2) * (S 1 2) + 280 * (S 0 2) * (S 1 3) - 240 * (S 0 2) * (S 1 4) + 728 * (S 0 2) * (S 2 3) - 624 * (S 0 2) * (S 2 4) - 1104 * (S 0 3) * (S 0 4) + 336 * (S 0 3) * (S 0 5) - 432 * (S 0 3) * (S 1 2) + 1320 * (S 0 3) * (S 1 3) - 864 * (S 0 3) * (S 1 4) + 216 * (S 0 3) * (S 2 3) - 288 * (S 0 4) * (S 1 2) + 672 * (S 0 4) * (S 1 3) - 264 * (S 0 4) * (S 1 4) - 616 * (S 0 4) * (S 2 3) + 744 * (S 0 4) * (S 2 4) + 312 * (S 0 5) * (S 1 5) - 144 * (S 0 5) * (S 2 3) - 120 * (S 0 5) * (S 2 5) - 288 * (S 0 5) * (S 3 4) + 784 * (S 0 5) * (S 3 5) - 672 * (S 0 5) * (S 4 5) + 312 * (S 0 6) * (S 1 6) + 144 * (S 0 6) * (S 2 3) - 432 * (S 0 6) * (S 2 4) + 216 * (S 0 6) * (S 2 6) + 1296 * (S 0 6) * (S 3 4) + 360 * (S 1 2) * (S 1 3) + 240 * (S 1 2) * (S 1 4) + 936 * (S 1 2) * (S 2 3) + 624 * (S 1 2) * (S 2 4) + 432 * (S 1 3) * (S 1 4) + 336 * (S 1 3) * (S 1 5) - 268 * (S 1 3) * (S 2 3) - 792 * (S 1 4) * (S 2 3) - 796 * (S 1 4) * (S 2 4) + 120 * (S 1 5) * (S 2 3) + 12 * (S 1 5) * (S 2 5) + 288 * (S 1 5) * (S 3 4) + 1008 * (S 1 5) * (S 3 5) + 672 * (S 1 5) * (S 4 5) - 120 * (S 1 6) * (S 2 3) + 360 * (S 1 6) * (S 2 4) - 268 * (S 1 6) * (S 2 6) + 1008 * (S 1 6) * (S 3 4) - 432 * (S 2 3) * (S 2 4) + 648 * (S 2 3) * (S 2 5) - 312 * (S 2 3) * (S 2 6) + 936 * (S 2 4) * (S 2 6) - 264 * (S 2 5) * (S 3 4) - 616 * (S 2 5) * (S 4 5) + 264 * (S 2 6) * (S 3 4) + 336 * (S 3 4) * (S 4 5) - 144 * (S 3 5) * (S 3 6) - 432 * (S 3 5) * (S 4 5) - 336 * (S 3 5) * (S 5 6) + 432 * (S 3 6) * (S 4 5) - 864 * (S 3 6) * (S 4 6) + 336 * (S 3 6) * (S 5 6) + 1008 * (S 4 5) * (S 5 6)

/-- `frobSq S` for symmetric `S`, written in the entries of `S`. -/
noncomputable def Dnorm (S : Matrix (Fin 7) (Fin 7) ℝ) : ℝ :=
  (S 0 0) ^ 2 + (S 1 1) ^ 2 + (S 2 2) ^ 2 + (S 3 3) ^ 2 + (S 4 4) ^ 2 + (S 5 5) ^ 2 + (S 6 6) ^ 2 + 2 * (S 0 1) ^ 2 + 2 * (S 0 2) ^ 2 + 2 * (S 0 3) ^ 2 + 2 * (S 0 4) ^ 2 + 2 * (S 0 5) ^ 2 + 2 * (S 0 6) ^ 2 + 2 * (S 1 2) ^ 2 + 2 * (S 1 3) ^ 2 + 2 * (S 1 4) ^ 2 + 2 * (S 1 5) ^ 2 + 2 * (S 1 6) ^ 2 + 2 * (S 2 3) ^ 2 + 2 * (S 2 4) ^ 2 + 2 * (S 2 5) ^ 2 + 2 * (S 2 6) ^ 2 + 2 * (S 3 4) ^ 2 + 2 * (S 3 5) ^ 2 + 2 * (S 3 6) ^ 2 + 2 * (S 4 5) ^ 2 + 2 * (S 4 6) ^ 2 + 2 * (S 5 6) ^ 2

/-- The sum-of-squares certificate: for symmetric `S`, `sos S = 1196 * frobSq S - frobSq (lyap A S)`. -/
noncomputable def sos (S : Matrix (Fin 7) (Fin 7) ℝ) : ℝ :=
  ((1 : ℝ) / 247) * ((494 * (S 0 2)) + (60 * (S 1 4)) - (72 * (S 0 4)) - (54 * (S 0 0)) + (67 * (S 0 1)) - (48 * (S 1 2)) - (70 * (S 1 3)) + (84 * (S 0 3)) + (156 * (S 2 4)) - (182 * (S 2 3)) + (24 * (S 2 2))) ^ 2
    + ((2 : ℝ) / 205) * ((410 * (S 0 6)) + (42 * (S 3 3)) - (39 * (S 1 6)) - (162 * (S 3 4)) - (27 * (S 2 6)) + (108 * (S 4 4)) + (54 * (S 2 4)) - (18 * (S 2 3))) ^ 2
    + ((2 : ℝ) / 13892515) * ((56245 * (S 1 4)) + (18462 * (S 0 4)) + (1620 * (S 0 0)) - (2010 * (S 0 1)) - (13380 * (S 1 2)) - (24576 * (S 1 3)) + (50832 * (S 0 3)) + (44473 * (S 2 4)) + (54366 * (S 2 3)) + (12865 * (S 2 2))) ^ 2
    + ((2 : ℝ) / 250684921165) * ((8914034 * (S 0 4)) - (281880 * (S 0 0)) + (349740 * (S 0 1)) + (2328120 * (S 1 2)) - (4093032 * (S 1 3)) + (6206394 * (S 0 3)) - (6253434 * (S 2 4)) + (1553087 * (S 2 3)) - (2238510 * (S 2 2))) ^ 2
    + ((8 : ℝ) / 137) * ((137 * (S 4 6)) + (54 * (S 3 6))) ^ 2
    + ((3 : ℝ) / 713786886845272) * ((320298032 * (S 0 0)) - (104069069 * (S 0 1)) - (1588032 * (S 1 2)) - (13948074 * (S 1 3)) + (15203484 * (S 0 3)) + (7183296 * (S 2 4)) - (36381114 * (S 2 3)) - (2070684 * (S 2 2))) ^ 2
    + ((2 : ℝ) / 169) * ((338 * (S 4 5)) - (126 * (S 5 6)) + (77 * (S 2 5)) - (42 * (S 3 4)) - (54 * (S 3 6)) - (84 * (S 1 5)) + (54 * (S 3 5)) + (84 * (S 0 5))) ^ 2
    + ((2 : ℝ) / 6469489) * ((76562 * (S 5 6)) + (4851 * (S 2 5)) - (2646 * (S 3 4)) - (10500 * (S 3 6)) - (5292 * (S 1 5)) + (10500 * (S 3 5)) + (5292 * (S 0 5))) ^ 2
    + ((3 : ℝ) / 75049747376) * ((3920992 * (S 2 5)) + (1111682 * (S 3 4)) + (414414 * (S 3 6)) + (500719 * (S 1 5)) - (414414 * (S 3 5)) - (156190 * (S 0 5)) - (2067174 * (S 2 3))) ^ 2
    + ((4 : ℝ) / 10871765) * ((53033 * (S 3 3)) + (11889 * (S 1 6)) + (14472 * (S 3 4)) + (567 * (S 2 6)) - (2268 * (S 4 4)) - (11070 * (S 1 5)) - (8610 * (S 3 5)) - (8610 * (S 0 5)) - (1134 * (S 2 4)) + (378 * (S 2 3))) ^ 2
    + ((1 : ℝ) / 15100063832729084408) * ((94287584213 * (S 0 1)) - (16982545632 * (S 1 2)) - (24983246496 * (S 1 1)) + (2753969722 * (S 1 3)) - (3001843452 * (S 0 3)) - (1418301888 * (S 2 4)) + (7183248842 * (S 2 3)) + (408845052 * (S 2 2))) ^ 2
    + ((1196 : ℝ) / 1) * ((S 6 6)) ^ 2
    + ((1 : ℝ) / 1508094347081226795685850) * ((31989245660900 * (S 1 2)) + (4992629582975 * (S 1 1)) - (7633215033174 * (S 1 3)) + (9979621337700 * (S 0 3)) - (3838211442624 * (S 2 4)) - (19784312463942 * (S 2 3)) + (3557894497534 * (S 2 2))) ^ 2
    + ((1 : ℝ) / 62273243635115327879487742) * ((97334654738719 * (S 1 1)) + (19082645442114 * (S 1 3)) - (24314817858732 * (S 0 3)) + (6628179664704 * (S 2 4)) + (49507730284818 * (S 2 3)) - (7102998837610 * (S 2 2))) ^ 2
    + ((2 : ℝ) / 970352664685576220412120543358075) * ((398769653949191917 * (S 1 3)) - (236376860478912150 * (S 0 3)) - (204402774951309900 * (S 1 5)) - (28502146469833308 * (S 2 4)) + (251528378280858661 * (S 2 3)) - (962286858873672 * (S 2 2))) ^ 2
    + ((1 : ℝ) / 235398319562) * ((17754856 * (S 1 6)) - (8338689 * (S 3 4)) + (1607518 * (S 2 6)) - (5051214 * (S 4 4)) + (642006 * (S 1 5)) + (499338 * (S 3 5)) + (499338 * (S 0 5)) - (2048310 * (S 2 4)) + (682770 * (S 2 3))) ^ 2
    + ((1 : ℝ) / 4255220148677058855502354384) * ((1955955191899094 * (S 3 4)) - (262689565504728 * (S 2 6)) - (117140489920818 * (S 3 6)) + (478257722525016 * (S 4 4)) - (284221658610537 * (S 1 5)) + (255358654509546 * (S 3 5)) + (566841432371802 * (S 0 5)) + (40955597591544 * (S 2 4)) + (186192891642546 * (S 2 3))) ^ 2
    + ((299 : ℝ) / 22744405327416425602828424896544) * ((11628285464624176 * (S 2 6)) - (47305924868286 * (S 3 6)) + (3198482629097796 * (S 4 4)) - (128352860604099 * (S 1 5)) + (92567059309242 * (S 3 5)) + (218356023460554 * (S 0 5)) - (2858853873089124 * (S 2 4)) + (1033656443366946 * (S 2 3))) ^ 2
    + ((3 : ℝ) / 675405646191393845276462340860030591) * ((6774895125569898092 * (S 0 3)) - (3309276046704770100 * (S 1 5)) - (5582775155288686838 * (S 0 5)) - (1844305616268785970 * (S 2 4)) - (8118435100686446379 * (S 2 3)) - (599427165150448134 * (S 2 2))) ^ 2
    + ((299 : ℝ) / 16356321262590490268630792108204645984) * ((10267137546587534482 * (S 3 6)) + (80745411062868804 * (S 4 4)) - (463841107115061627 * (S 1 5)) + (823413052894806666 * (S 3 5)) + (475183345341388698 * (S 0 5)) - (3465520316153028 * (S 2 4)) + (213186367991049138 * (S 2 3))) ^ 2
    + ((1196 : ℝ) / 2987074906513251127333476430785568921) * ((581871021588886481 * (S 4 4)) + (182700971841194676 * (S 1 5)) - (129961612935990612 * (S 3 5)) - (300724237500489936 * (S 0 5)) + (59289156472010256 * (S 2 4)) - (132081807890757384 * (S 2 3))) ^ 2
    + ((4 : ℝ) / 103) * ((103 * (S 5 5)) - (84 * (S 3 5))) ^ 2
    + ((4 : ℝ) / 18716393568625802767636151434796217344928492841918495637372767319102834149) * ((56973658657509519348541855943334028269 * (S 1 5)) - (35115658804194106695063036606539438703 * (S 3 5)) - (9440295874585206706088059153820319554 * (S 0 5)) - (3663251098696202535203682190129142454 * (S 2 4)) - (547153688041809789564777233852221155 * (S 2 3)) - (756920876652854702758443474483172662 * (S 2 2))) ^ 2
    + ((1196 : ℝ) / 3544966956456369956700535806553672799057551244205350366099705902015609932729211) * ((1812266706827456912953611587363112963619 * (S 3 5)) - (1016827397762452483958088754234715217370 * (S 0 5)) - (36931665281512043668256046168631249266 * (S 2 4)) - (99954501140718211759759460857307557473 * (S 2 3)) - (9290691218559414036524427916164038934 * (S 2 2))) ^ 2
    + ((3 : ℝ) / 137870467790254050433930535343627278606563187514055792559417734120602240690000143) * ((152152514054191564059141700077075194577994 * (S 0 5)) - (16649351634941510217657534925355213388174 * (S 2 4)) - (67474637991043278780154058662870707813389 * (S 2 3)) - (5913611454902914560382480744005329366026 * (S 2 2))) ^ 2
    + ((4 : ℝ) / 48893081103712444234558719641970282850703587787176363686973952249688962350323364211) * ((642685155846960075047970850093508203214263 * (S 2 4)) - (295825070460540458544071314334404625894817 * (S 2 3)) + (1500374876529850619854786730835430090670650 * (S 2 2))) ^ 2
    + ((2 : ℝ) / 8762846248828409380882671911110324445841335047500794957650314863107154392700581912423) * ((13634741940290074576057190343436529141818321 * (S 2 3)) + (852470847639055217779015931722958586741534 * (S 2 2))) ^ 2
    + ((215247521466165572152452957869795833431964384 : ℝ) / 13634741940290074576057190343436529141818321) * ((S 2 2)) ^ 2

theorem eq_SmatE (S : Matrix (Fin 7) (Fin 7) ℝ) (hS : S.transpose = S) : S = SmatE S := by
  have hsym : ∀ i j, S i j = S j i := fun i j => by
    have h := congrFun (congrFun hS i) j
    simp only [Matrix.transpose_apply] at h
    exact h.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [SmatE, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val'] <;>
    first | rfl | exact hsym _ _ | exact (hsym _ _).symm

theorem frobSq_nonneg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ frobSq X :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (X i j)

set_option maxHeartbeats 1000000 in
theorem Knorm : frobSq K = 53836 := by
  simp only [K, frobSq, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.cons_val',
    Matrix.empty_val']
  norm_num

set_option maxHeartbeats 1000000 in
theorem LKnorm : frobSq (lyap A K) = 64387950 := by
  simp only [A, K, frobSq, lyap, Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    Matrix.cons_val', Matrix.empty_val', Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

set_option maxHeartbeats 4000000 in
theorem Q_identity (S : Matrix (Fin 7) (Fin 7) ℝ) :
    frobSq (lyap A (SmatE S)) = Qexpr S := by
  simp only [A, SmatE, Qexpr, Dnorm, frobSq, lyap, sos, Matrix.mul_apply, Matrix.add_apply,
    Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Matrix.cons_val', Matrix.empty_val', Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  ring

set_option maxHeartbeats 4000000 in
theorem D_identity (S : Matrix (Fin 7) (Fin 7) ℝ) : frobSq (SmatE S) = Dnorm S := by
  simp only [A, SmatE, Qexpr, Dnorm, frobSq, lyap, sos, Matrix.mul_apply, Matrix.add_apply,
    Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Matrix.cons_val', Matrix.empty_val', Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  ring

set_option maxHeartbeats 4000000 in
theorem sos_identity (S : Matrix (Fin 7) (Fin 7) ℝ) :
    Qexpr S = 1196 * Dnorm S - sos S := by
  simp only [Qexpr, Dnorm, sos]
  ring

set_option maxHeartbeats 4000000 in
theorem sos_nonneg (S : Matrix (Fin 7) (Fin 7) ℝ) : 0 ≤ sos S := by
  rw [sos]
  positivity

theorem sym_bound (S : Matrix (Fin 7) (Fin 7) ℝ) (hS : S.transpose = S) :
    frobSq (lyap A S) ≤ 1196 * frobSq S := by
  have h1 : frobSq (lyap A S) = Qexpr S := by
    conv_lhs => rw [eq_SmatE S hS]
    exact Q_identity S
  have h2 : frobSq S = Dnorm S := by
    conv_lhs => rw [eq_SmatE S hS]
    exact D_identity S
  have h3 : Qexpr S = 1196 * Dnorm S - sos S := sos_identity S
  have h4 : 0 ≤ sos S := sos_nonneg S
  linarith

end OMA.P_arxiv_2608_20875

open OMA.P_arxiv_2608_20875 OMA.S_arxiv_2608_20875 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2608_20875.main) := by
  intro h
  obtain ⟨S, hSym, hne, hAll⟩ := h 7 (by norm_num) A
  have hb : frobSq (lyap A S) ≤ 1196 * frobSq S := sym_bound S hSym
  have hK : frobSq (lyap A K) * frobSq S ≤ 1196 * frobSq S * frobSq K :=
    le_trans (hAll K) (mul_le_mul_of_nonneg_right hb (frobSq_nonneg K))
  rw [LKnorm, Knorm] at hK
  have hpos : 0 < frobSq S := lt_of_le_of_ne (frobSq_nonneg S) (Ne.symm hne)
  nlinarith [hK, hpos]
