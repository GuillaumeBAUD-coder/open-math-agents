import FormalConjectures.Wikipedia.RefactorableNumber

/-!
# Zelinsky's theorem on three consecutive refactorable numbers

The Pell sequence and Jacobi symbol proof of Ljunggren's equation below is adapted
from Sky (ChironTheCentaur), rh-lab-refactorable-numbers, licensed under Apache 2.0,
following the elementary proof by M. Luo and L. Lin. The port uses the pinned Mathlib.
https://github.com/ChironTheCentaur/rh-lab-refactorable-numbers/tree/1d1d800bc765379c544473134a2995db585d023b/RefactorableFC/Ljunggren

The divisor argument and assembly follow Joshua Zelinsky, J. Integer Sequences 5
(2002), Article 02.2.8, Theorem 59, using the project's reduction by limaries30
and Marcus Buffett's proof of its fourth-power criterion.
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1397
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1631
-/

namespace RefactorableFC.LjunggrenProof

open Zsqrtd

/-- The unit `1 + √2` of `ℤ√2`. -/
def u : (ℤ√2)ˣ := ⟨⟨1, 1⟩, ⟨-1, 1⟩, by ext <;> simp, by ext <;> simp⟩

/-- `Q n` is the rational part of `(1 + √2) ^ n`. -/
def Q (n : ℤ) : ℤ := ((u ^ n : (ℤ√2)ˣ) : ℤ√2).re

/-- `P n` is the `√2` part of `(1 + √2) ^ n`. -/
def P (n : ℤ) : ℤ := ((u ^ n : (ℤ√2)ˣ) : ℤ√2).im

/-- The sign `(-1) ^ n` for `n : ℤ`, as an integer. -/
def sgn (n : ℤ) : ℤ := (((-1 : ℤˣ) ^ n : ℤˣ) : ℤ)

lemma coe_u_zpow (n : ℤ) : ((u ^ n : (ℤ√2)ˣ) : ℤ√2) = ⟨Q n, P n⟩ := by ext <;> rfl

lemma Q_zero : Q 0 = 1 := by simp [Q]
lemma P_zero : P 0 = 0 := by simp [P]

lemma Q_add_one (n : ℤ) : Q (n + 1) = Q n + 2 * P n := by
  have h : ((u ^ (n + 1) : (ℤ√2)ˣ) : ℤ√2) = ((u ^ n : (ℤ√2)ˣ) : ℤ√2) * ⟨1, 1⟩ := by
    rw [zpow_add_one]; rfl
  have := congrArg Zsqrtd.re h
  rw [coe_u_zpow, coe_u_zpow] at this
  simpa [Q, mul_comm] using this

lemma P_add_one (n : ℤ) : P (n + 1) = Q n + P n := by
  have h : ((u ^ (n + 1) : (ℤ√2)ˣ) : ℤ√2) = ((u ^ n : (ℤ√2)ˣ) : ℤ√2) * ⟨1, 1⟩ := by
    rw [zpow_add_one]; rfl
  have := congrArg Zsqrtd.im h
  rw [coe_u_zpow, coe_u_zpow] at this
  simpa using this

lemma Q_one : Q 1 = 1 := by simpa [Q_zero, P_zero] using Q_add_one 0
lemma P_one : P 1 = 1 := by simpa [Q_zero, P_zero] using P_add_one 0

lemma P_add_two (n : ℤ) : P (n + 2) = 2 * P (n + 1) + P n := by
  rw [show n + 2 = n + 1 + 1 by ring, P_add_one, Q_add_one, P_add_one]; ring

lemma Q_add_two (n : ℤ) : Q (n + 2) = 2 * Q (n + 1) + Q n := by
  rw [show n + 2 = n + 1 + 1 by ring, Q_add_one, Q_add_one, P_add_one]; ring

lemma sgn_add (m n : ℤ) : sgn (m + n) = sgn m * sgn n := by
  simp [sgn, zpow_add]

lemma sgn_sq (n : ℤ) : sgn n * sgn n = 1 := by
  rw [← sgn_add]; simp only [sgn]
  rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ n) with h | h
  · rw [← two_mul, mul_comm, zpow_mul, h]; simp
  · rw [← two_mul, mul_comm, zpow_mul, h]; simp

lemma sgn_odd {n : ℤ} (h : Odd n) : sgn n = -1 := by simp [sgn, h.neg_one_zpow]
lemma sgn_even {n : ℤ} (h : Even n) : sgn n = 1 := by simp [sgn, h.neg_one_zpow]

/-- (2.2) -/
lemma Q_sq_sub (n : ℤ) : Q n ^ 2 - 2 * P n ^ 2 = sgn n := by
  have hu : Units.map (Zsqrtd.normMonoidHom (d := 2)) u = -1 := by
    ext; show Zsqrtd.norm (⟨1, 1⟩ : ℤ√2) = -1; simp [Zsqrtd.norm_def]
  have h := congrArg Units.val (map_zpow (Units.map (Zsqrtd.normMonoidHom (d := 2))) u n)
  rw [hu] at h
  unfold sgn; rw [← h]
  show _ = Zsqrtd.norm ((u ^ n : (ℤ√2)ˣ) : ℤ√2)
  rw [coe_u_zpow, Zsqrtd.norm_def]; ring

lemma Q_add (m n : ℤ) : Q (m + n) = Q m * Q n + 2 * (P m * P n) := by
  have h := congrArg Zsqrtd.re (congrArg Units.val (zpow_add u m n))
  rw [Units.val_mul, coe_u_zpow, coe_u_zpow, coe_u_zpow] at h
  simp at h; rw [h]; ring

lemma P_add (m n : ℤ) : P (m + n) = Q m * P n + P m * Q n := by
  have h := congrArg Zsqrtd.im (congrArg Units.val (zpow_add u m n))
  rw [Units.val_mul, coe_u_zpow, coe_u_zpow, coe_u_zpow] at h
  simpa using h

/-- (2.1) -/
lemma Q_two_mul (n : ℤ) : Q (2 * n) = Q n ^ 2 + 2 * P n ^ 2 := by
  rw [two_mul, Q_add]; ring

/-- (2.1) -/
lemma P_two_mul (n : ℤ) : P (2 * n) = 2 * P n * Q n := by
  rw [two_mul, P_add]; ring

lemma sgn_neg (n : ℤ) : sgn (-n) = sgn n := by
  have h := sgn_add n (-n)
  rw [add_neg_cancel] at h
  have h0 : sgn 0 = 1 := by simp [sgn]
  linear_combination (-(sgn (-n))) * sgn_sq n - sgn n * (h0.symm.trans h)

lemma Q_neg_P_neg (n : ℤ) : Q (-n) = sgn n * Q n ∧ P (-n) = -(sgn n * P n) := by
  have e1 := Q_add n (-n)
  have e2 := P_add n (-n)
  rw [add_neg_cancel, Q_zero] at e1
  rw [add_neg_cancel, P_zero] at e2
  have e3 := Q_sq_sub n
  have e4 := sgn_sq n
  constructor
  · linear_combination (-(Q (-n))) * e4 + sgn n * (-(Q n) * e1 + 2 * P n * e2 - Q (-n) * e3)
  · linear_combination (-(P (-n))) * e4 + sgn n * (P n * e1 - Q n * e2 - P (-n) * e3)

/-- (2.3) -/
lemma P_neg (n : ℤ) : P (-n) = -(sgn n * P n) := (Q_neg_P_neg n).2

lemma Q_neg (n : ℤ) : Q (-n) = sgn n * Q n := (Q_neg_P_neg n).1

/-- (2.5), `P` half. -/
lemma Q_dvd_P_add (n k : ℤ) : Q k ∣ P (n + 2 * k) + sgn k * P n := by
  refine ⟨2 * Q n * P k + 2 * P n * Q k, ?_⟩
  rw [P_add, Q_two_mul, P_two_mul]
  linear_combination (-P n) * Q_sq_sub k

/-- (2.5), `Q` half. -/
lemma Q_dvd_Q_add (n k : ℤ) : Q k ∣ Q (n + 2 * k) + sgn k * Q n := by
  refine ⟨2 * Q n * Q k + 4 * P n * P k, ?_⟩
  rw [Q_add, Q_two_mul, P_two_mul]
  linear_combination (-Q n) * Q_sq_sub k

lemma pos_nat (n : ℕ) : 1 ≤ Q n ∧ 0 ≤ P n ∧ (1 ≤ n → 1 ≤ P n) := by
  induction n with
  | zero => simp [Q_zero, P_zero]
  | succ n ih =>
    push_cast
    rw [Q_add_one, P_add_one]
    omega

lemma P_pos_of_odd {n : ℤ} (h : Odd n) : 1 ≤ P n := by
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn
    exact (pos_nat n).2.2 (by rcases h with ⟨k, hk⟩; omega)
  · have := (pos_nat (-n).toNat).2.2 (by omega)
    rw [Int.toNat_of_nonneg (by omega), P_neg, sgn_odd h] at this
    linarith

/-- The fundamental solution `3 + 2√2` of `x ^ 2 - 2 y ^ 2 = 1`. -/
def f : Pell.Solution₁ 2 := Pell.Solution₁.mk 3 2 (by norm_num)

lemma f_isFundamental : Pell.IsFundamental f := by
  refine ⟨by simp [f], by simp [f], fun {b} hb => ?_⟩
  have hp := b.prop
  simp only [f, Pell.Solution₁.x_mk]
  by_contra hlt
  have hx : b.x = 2 := by omega
  rw [hx] at hp
  omega

lemma coe_u_sq : ((u : ℤ√2)) ^ 2 = ⟨3, 2⟩ := by
  ext <;> simp [u, sq]

/-- Every nonnegative solution of `a ^ 2 - 2 b ^ 2 = -1` is `(Q n, P n)` with `n` odd. -/
theorem neg_pell_classify {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 - 2 * b ^ 2 = -1) :
    ∃ n : ℤ, Odd n ∧ a = Q n ∧ b = P n := by
  set s : Pell.Solution₁ 2 := Pell.Solution₁.mk (a + 2 * b) (a + b) (by linear_combination -h)
  obtain ⟨m, hm⟩ := f_isFundamental.eq_pow_of_nonneg (a := s)
    (by simp [s]; nlinarith) (by simp [s]; omega)
  have hc : ((u ^ (2 * (m : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨a + 2 * b, a + b⟩ := by
    have h1 := congrArg (fun t : Pell.Solution₁ 2 => (t : ℤ√2)) hm
    simp only [s, Pell.Solution₁.coe_mk] at h1
    rw [h1, zpow_mul, zpow_natCast, zpow_two]
    push_cast
    rw [← sq, coe_u_sq]
    rfl
  rw [coe_u_zpow] at hc
  have hQ := congrArg Zsqrtd.re hc
  have hP := congrArg Zsqrtd.im hc
  simp only at hQ hP
  have h2 : 2 * (m : ℤ) = (2 * m - 1) + 1 := by ring
  rw [h2, Q_add_one] at hQ
  rw [h2, P_add_one] at hP
  exact ⟨2 * m - 1, ⟨m - 1, by ring⟩, by omega, by omega⟩

end RefactorableFC.LjunggrenProof

namespace RefactorableFC.LjunggrenProof

/-- One step of `(Q, P) ↦ (Q + 2P, Q + P)`, reduced mod `a`. -/
def stp (a : ℕ) (s : ℕ × ℕ) : ℕ × ℕ := ((s.1 + 2 * s.2) % a, (s.1 + s.2) % a)

/-- `(Q n mod a, P n mod a)` computed by iteration. -/
def qp (a : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1 % a, 0)
  | n + 1 => stp a (qp a n)

/-- `v` is a square mod `a`. -/
def isSqMod (a v : ℕ) : Bool := (List.range a).any fun t => t * t % a == v

/-- The (prime, period) pairs of Luo–Lin §3. -/
def mods : List (ℕ × ℕ) :=
  [(13, 28), (113, 56), (3, 8), (7, 6), (83, 168), (41, 10), (19, 40), (31, 30), (281, 280),
    (71, 70), (241, 80)]

/-- Residue `r` (mod the period `T`) forces `P` to be a non-square mod `a`. -/
def bad (a T r : ℕ) : Bool := !isSqMod a (qp a (r % T)).2

/-- Every odd residue mod 1680 outside `±1, ±7 (mod 840)` is killed by one modulus. -/
def sieveOK : Bool := (List.range 1680).all fun r =>
  r % 2 == 0 || [1, 7, 833, 839].contains (r % 840) || mods.any fun m => bad m.1 m.2 r

/-- Each period is a period of `(1 + √2) ^ n` mod its prime, is even, and divides 1680. -/
def periodOK : Bool :=
  mods.all fun m => qp m.1 m.2 == (1 % m.1, 0) && 1680 % m.2 == 0 && m.2 % 2 == 0 && 0 < m.1

set_option maxRecDepth 100000 in
theorem sieveOK_eq : sieveOK = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem periodOK_eq : periodOK = true := by decide +kernel

lemma qp_spec (a n : ℕ) : (Q n : ZMod a) = (qp a n).1 ∧ (P n : ZMod a) = (qp a n).2 := by
  induction n with
  | zero => simp [qp, Q_zero, P_zero]
  | succ n ih =>
    have h1 := Q_add_one (n : ℤ)
    have h2 := P_add_one (n : ℤ)
    push_cast at h1 h2 ⊢
    simp only [qp, stp, ZMod.natCast_mod]
    rw [h1, h2]
    push_cast
    rw [ih.1, ih.2]
    exact ⟨rfl, rfl⟩

lemma qp_snd_lt {a : ℕ} (ha : 0 < a) (n : ℕ) : (qp a n).2 < a := by
  cases n with
  | zero => simpa [qp] using ha
  | succ n => exact Nat.mod_lt _ ha

lemma period_mul {a T : ℕ} (hT : qp a T = (1 % a, 0)) (hev : Even T) (j : ℤ) :
    (Q (T * j) : ZMod a) = 1 ∧ (P (T * j) : ZMod a) = 0 := by
  have hQ : (Q T : ZMod a) = 1 := by rw [(qp_spec a T).1, hT]; simp
  have hP : (P T : ZMod a) = 0 := by rw [(qp_spec a T).2, hT]; simp
  have hs : sgn (T : ℤ) = 1 := sgn_even (by exact_mod_cast hev)
  induction j using Int.induction_on with
  | zero => simp [Q_zero, P_zero]
  | succ j ih =>
    rw [mul_add, mul_one, Q_add, P_add]
    push_cast
    rw [ih.1, ih.2, hQ, hP]; simp
  | pred j ih =>
    rw [show (T : ℤ) * (-(j : ℤ) - 1) = T * -j + -T by ring, Q_add, P_add, Q_neg, P_neg, hs]
    push_cast
    rw [ih.1, ih.2, hQ, hP]; simp

/-- `(Q n, P n)` mod `a` depends only on `n` mod a period `T`. -/
lemma QP_mod {a T : ℕ} (hT : qp a T = (1 % a, 0)) (hev : Even T) (hTpos : 0 < T) (n : ℤ) :
    (Q n : ZMod a) = (qp a (n % T).toNat).1 ∧ (P n : ZMod a) = (qp a (n % T).toNat).2 := by
  set r := (n % T).toNat with hr
  have hrz : (r : ℤ) = n % T := Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hTpos.ne'))
  have hn : n = (r : ℤ) + T * (n / T) := by rw [hrz]; exact (Int.emod_add_mul_ediv n T).symm
  have h1 := (qp_spec a r).1
  have h2 := (qp_spec a r).2
  constructor
  · rw [hn, Q_add]; push_cast
    rw [(period_mul hT hev _).1, (period_mul hT hev _).2, h1]; ring
  · rw [hn, P_add]; push_cast
    rw [(period_mul hT hev _).1, (period_mul hT hev _).2, h2]; ring

lemma cast_mod {x : ℤ} {a c : ℕ} (h : (x : ZMod a) = (c : ZMod a)) : x % a = (c : ℤ) % a := by
  rw [← Int.cast_natCast, ZMod.intCast_eq_intCast_iff'] at h; exact h

lemma isSqMod_of {a T : ℕ} (ha : 0 < a) (hT : qp a T = (1 % a, 0)) (hev : Even T)
    (hdvd : T ∣ 1680) {n : ℤ} (hsq : IsSquare (P n)) :
    isSqMod a (qp a ((n % 1680).toNat % T)).2 = true := by
  have : NeZero a := ⟨ha.ne'⟩
  have hTpos : 0 < T := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  set r := (n % 1680).toNat % T with hr
  have hrz : ((r : ℕ) : ℤ) = n % T := by
    rw [hr]; push_cast
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    exact Int.emod_emod_of_dvd n (by exact_mod_cast hdvd)
  have hn : n = (r : ℤ) + T * (n / T) := by rw [hrz]; exact (Int.emod_add_mul_ediv n T).symm
  have hPn : (P n : ZMod a) = (qp a r).2 := by
    rw [hn, P_add]; push_cast
    rw [(period_mul hT hev _).1, (period_mul hT hev _).2]
    have := (qp_spec a r).2
    rw [this]; ring
  obtain ⟨y, hy⟩ := hsq
  have hv := qp_snd_lt ha r
  unfold isSqMod
  rw [List.any_eq_true]
  refine ⟨(y : ZMod a).val, List.mem_range.2 (ZMod.val_lt _), ?_⟩
  rw [beq_iff_eq]
  have h1 : (((y : ZMod a).val * (y : ZMod a).val : ℕ) : ZMod a) = ((qp a r).2 : ZMod a) := by
    push_cast; rw [ZMod.natCast_zmod_val, ← hPn, hy]; push_cast; ring
  rw [ZMod.natCast_eq_natCast_iff'] at h1
  rw [h1, Nat.mod_eq_of_lt hv]

/-- Luo–Lin Lemma 3.1. -/
theorem sieve {n : ℤ} (hodd : Odd n) (hsq : IsSquare (P n)) :
    n % 840 = 1 ∨ n % 840 = 7 ∨ n % 840 = 833 ∨ n % 840 = 839 := by
  set r := (n % 1680).toNat with hr
  have hr0 : (r : ℤ) = n % 1680 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hrlt : r < 1680 := by omega
  have h840 : n % 840 = ((r % 840 : ℕ) : ℤ) := by
    push_cast; rw [hr0]; exact (Int.emod_emod_of_dvd n (by norm_num)).symm
  have hodd' : r % 2 = 1 := by
    rcases hodd with ⟨k, hk⟩; omega
  have hs := sieveOK_eq
  unfold sieveOK at hs
  rw [List.all_eq_true] at hs
  have := hs r (List.mem_range.2 hrlt)
  simp only [Bool.or_eq_true, beq_iff_eq, hodd', List.any_eq_true] at this
  rcases this with (h | h) | ⟨m, hm, hb⟩
  · omega
  · simp only [List.contains_iff_mem, List.mem_cons, List.mem_nil_iff, or_false] at h
    rw [h840]; omega
  · exfalso
    have hp := periodOK_eq
    unfold periodOK at hp
    rw [List.all_eq_true] at hp
    have := hp m hm
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    obtain ⟨⟨⟨hT, hd⟩, he⟩, ha⟩ := this
    have := isSqMod_of ha hT (Nat.even_iff.2 he) (Nat.dvd_of_mod_eq_zero hd) hsq
    rw [← hr] at this
    simp [bad, this] at hb

end RefactorableFC.LjunggrenProof

namespace RefactorableFC.LjunggrenProof

/-- Residues of `Q k`, `P k`, `P (k + 1)` for `k ≡ 9 (mod 12)`, read off the period 24 mod 40. -/
lemma res40 {k : ℤ} (hk : k % 12 = 9) :
    Q k % 8 = 1 ∧ P k % 2 = 1 ∧ P (k + 1) % 4 = 2 ∧ P (k + 1) % 5 = 3 := by
  have hT : qp 40 24 = (1 % 40, 0) := by decide +kernel
  have h1 := QP_mod hT (by decide) (by norm_num) k
  have h2 := QP_mod hT (by decide) (by norm_num) (k + 1)
  simp only [Nat.cast_ofNat] at h1 h2
  have hk24 : k % 24 = 9 ∨ k % 24 = 21 := by omega
  rcases hk24 with h | h
  · have h' : (k + 1) % 24 = 10 := by omega
    rw [h] at h1; rw [h'] at h2
    have a1 := cast_mod h1.1; have a2 := cast_mod h1.2; have a3 := cast_mod h2.2
    have c1 : (qp 40 9).1 % 8 = 1 := by decide +kernel
    have c2 : (qp 40 9).2 % 2 = 1 := by decide +kernel
    have c3 : (qp 40 10).2 % 4 = 2 := by decide +kernel
    have c4 : (qp 40 10).2 % 5 = 3 := by decide +kernel
    simp only [show ((9 : ℤ)).toNat = 9 from rfl, show ((10 : ℤ)).toNat = 10 from rfl] at a1 a2 a3
    omega
  · have h' : (k + 1) % 24 = 22 := by omega
    rw [h] at h1; rw [h'] at h2
    have a1 := cast_mod h1.1; have a2 := cast_mod h1.2; have a3 := cast_mod h2.2
    have c1 : (qp 40 21).1 % 8 = 1 := by decide +kernel
    have c2 : (qp 40 21).2 % 2 = 1 := by decide +kernel
    have c3 : (qp 40 22).2 % 4 = 2 := by decide +kernel
    have c4 : (qp 40 22).2 % 5 = 3 := by decide +kernel
    simp only [show ((21 : ℤ)).toNat = 21 from rfl, show ((22 : ℤ)).toNat = 22 from rfl] at a1 a2 a3
    omega

lemma J_congr {a b R : ℤ} {Rn : ℕ} (hR : (Rn : ℤ) = R) (h : R ∣ a - b) :
    jacobiSym a Rn = jacobiSym b Rn :=
  jacobiSym.mod_left' (Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd (hR ▸ h)))

lemma J_sq_one {a x : ℤ} {Rn : ℕ} (_hR : 0 < (Rn : ℤ)) (h : (Rn : ℤ) ∣ a - x ^ 2)
    (hc : IsCoprime x Rn) : jacobiSym a Rn = 1 := by
  rw [J_congr rfl h]
  exact jacobiSym.sq_one' (Int.isCoprime_iff_gcd_eq_one.1 hc)

/-- `R k ∣ P (n) + P (1 + 4 k)` for `n = 1 + (24 m - 8) k`. -/
lemma R_dvd {k m : ℤ} (hk : Odd k) :
    (8 * P k ^ 2 - 4 * P k - 1) ∣ P (1 + (24 * m - 8) * k) + P (1 + 4 * k) := by
  set R := 8 * P k ^ 2 - 4 * P k - 1 with hR
  have e := Q_sq_sub k
  rw [sgn_odd hk] at e
  have h6 : R ∣ Q (6 * k) := by
    have h1 : Q (6 * k) = Q (2 * k) * (Q (2 * k) ^ 2 + 6 * P (2 * k) ^ 2) := by
      rw [show 6 * k = 2 * k + 2 * (2 * k) by ring, Q_add, Q_two_mul (2 * k),
        P_two_mul (2 * k)]; ring
    have hfac : Q (2 * k) ^ 2 + 6 * P (2 * k) ^ 2 = (8 * P k ^ 2 + 4 * P k - 1) * R := by
      rw [Q_two_mul, P_two_mul, hR]
      linear_combination (30 * P k ^ 2 + Q k ^ 2 - 1) * e
    rw [h1, hfac]; exact ⟨Q (2 * k) * (8 * P k ^ 2 + 4 * P k - 1), by ring⟩
  have hstep : ∀ x, R ∣ P (x + 12 * k) + P x := by
    intro x
    have := Q_dvd_P_add x (6 * k)
    rw [sgn_even ⟨3 * k, by ring⟩, one_mul, show x + 2 * (6 * k) = x + 12 * k by ring] at this
    exact h6.trans this
  have h24 : ∀ y, R ∣ P (y + 24 * k) - P y := by
    intro y
    have a := hstep (y + 12 * k)
    have b := hstep y
    rw [show y + 12 * k + 12 * k = y + 24 * k by ring] at a
    have := dvd_sub a b
    rwa [show P (y + 24 * k) + P (y + 12 * k) - (P (y + 12 * k) + P y)
      = P (y + 24 * k) - P y by ring] at this
  have hj : ∀ j : ℤ, ∀ x, R ∣ P (x + 24 * k * j) - P x := by
    intro j
    induction j using Int.induction_on with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      have := dvd_add (h24 (x + 24 * k * j)) (ih x)
      rwa [show x + 24 * k * j + 24 * k = x + 24 * k * (j + 1) by ring, sub_add_sub_cancel]
        at this
    | pred j ih =>
      intro x
      have h := h24 (x + 24 * k * (-j - 1))
      rw [show x + 24 * k * (-j - 1) + 24 * k = x + 24 * k * -j by ring] at h
      have hd := dvd_sub (ih x) h
      rwa [show P (x + 24 * k * -(j : ℤ)) - P x -
          (P (x + 24 * k * -(j : ℤ)) - P (x + 24 * k * (-(j : ℤ) - 1))) =
          P (x + 24 * k * (-(j : ℤ) - 1)) - P x by abel] at hd
  have a := hj (m - 1) (1 + 4 * k + 12 * k)
  have b := hstep (1 + 4 * k)
  rw [show 1 + 4 * k + 12 * k + 24 * k * (m - 1) = 1 + (24 * m - 8) * k by ring] at a
  have hd := dvd_add a b
  rwa [show P (1 + (24 * m - 8) * k) - P (1 + 4 * k + 12 * k) +
      (P (1 + 4 * k + 12 * k) + P (1 + 4 * k)) =
      P (1 + (24 * m - 8) * k) + P (1 + 4 * k) by abel] at hd

/-- The pure algebra of Theorem 1.1, after the Pell sequences are named. -/
lemma theorem_1_1_core {q p q' p' Pn P14 : ℤ} (hp1 : 1 ≤ p) (hq1 : 1 ≤ q)
    (hq8 : q % 8 = 1) (hp2 : p % 2 = 1) (hp4 : p' % 4 = 2) (hp5 : p' % 5 = 3)
    (e : q ^ 2 - 2 * p ^ 2 = -1) (e' : q' ^ 2 - 2 * p' ^ 2 = 1)
    (hp' : p' = q + p) (hq' : q' = q + 2 * p)
    (hP14 : P14 = (q ^ 2 + 2 * p ^ 2) ^ 2 + 2 * (2 * p * q) ^ 2
      + 2 * (2 * p * q) * (q ^ 2 + 2 * p ^ 2))
    (hdvd : (8 * p ^ 2 - 4 * p - 1) ∣ Pn + P14) :
    jacobiSym Pn (8 * p ^ 2 - 4 * p - 1).toNat = -1 := by
  have hR0 : 0 < 8 * p ^ 2 - 4 * p - 1 := by nlinarith
  set Rn := (8 * p ^ 2 - 4 * p - 1).toNat with hRndef
  have hRn : (Rn : ℤ) = 8 * p ^ 2 - 4 * p - 1 := Int.toNat_of_nonneg hR0.le
  have hR8 : Rn % 8 = 3 := by
    have hpj : p = 2 * (p / 2) + 1 := by omega
    have : (Rn : ℤ) = 8 * (4 * (p / 2) ^ 2 + 3 * (p / 2)) + 3 := by
      rw [hRn]; nth_rw 1 [hpj]; nth_rw 2 [hpj]; ring
    omega
  have hRodd : Odd Rn := Nat.odd_iff.2 (by omega)
  -- step 1: `P n ≡ T0 (mod R)`
  set T0 := -4 * p ^ 2 + 2 * p - q * (2 * p + 1) with hT0
  have s1 : jacobiSym Pn Rn = jacobiSym T0 Rn := by
    refine J_congr hRn ?_
    have h2 : (8 * p ^ 2 - 4 * p - 1) ∣ P14 + T0 :=
      ⟨-(-4 * p ^ 2 - 2 * p * q - 2 * p - q + 1), by
        rw [hP14, hT0]
        linear_combination (-(-14 * p ^ 2 - 4 * p * q - q ^ 2 + 1)) * e⟩
    have hd := dvd_sub hdvd h2
    rwa [show Pn + P14 - (P14 + T0) = Pn - T0 by abel] at hd
  -- step 2: `J(-2 | R) = 1`
  have hneg2 : jacobiSym (-2) Rn = 1 := by
    rw [jacobiSym.at_neg_two hRodd, ZMod.χ₈'_nat_eq_if_mod_eight]
    have : Rn % 2 = 1 := by omega
    simp [hR8, this]
  have s2 : jacobiSym T0 Rn = jacobiSym (1 + q * (4 * p + 2)) Rn := by
    rw [show jacobiSym T0 Rn = jacobiSym (-2) Rn * jacobiSym T0 Rn by rw [hneg2, one_mul],
      ← jacobiSym.mul_left]
    exact J_congr hRn ⟨1, by rw [hT0]; ring⟩
  -- Lemma 4.1, first half: `J(Q k | R k) = 1`
  have hq0 : 0 ≤ q := by omega
  set qn := q.toNat with hqndef
  have hqn : (qn : ℤ) = q := Int.toNat_of_nonneg hq0
  have L41a : jacobiSym q Rn = 1 := by
    rw [← hqn, jacobiSym.quadratic_reciprocity_one_mod_four (by omega) hRodd, hRn]
    refine J_sq_one (x := 2 * p - 1) (by omega) ⟨2 * q, by rw [hqn]; linear_combination (-2) * e⟩
      ⟨2 * p + 1, -2 * q, by rw [hqn]; linear_combination (-2) * e⟩
  -- step 4
  set N := p' - 1 with hN
  have hN0 : 0 < N := by omega
  set Nn := N.toNat with hNndef
  have hNn : (Nn : ℤ) = N := Int.toNat_of_nonneg hN0.le
  have hN4 : Nn % 4 = 1 := by omega
  have hN5 : Nn % 5 = 2 := by omega
  have s4 : jacobiSym (1 + q * (4 * p + 2)) Rn = jacobiSym N Rn := by
    rw [show jacobiSym (1 + q * (4 * p + 2)) Rn = jacobiSym q Rn * jacobiSym (1 + q * (4 * p + 2)) Rn
      by rw [L41a, one_mul], ← jacobiSym.mul_left]
    exact J_congr hRn ⟨p + 1, by rw [hN, hp']; linear_combination (4 * p + 2) * e⟩
  -- step 5: reciprocity
  have s5 : jacobiSym N Rn = jacobiSym (8 * p ^ 2 - 4 * p - 1) Nn := by
    rw [← hNn, jacobiSym.quadratic_reciprocity_one_mod_four hN4 hRodd, hRn]
  -- step 6: `R ≡ 5 (7 - 4 Q_{k+1}) (mod N)`
  have hpq : p = q' - p' := by omega
  have s6 : jacobiSym (8 * p ^ 2 - 4 * p - 1) Nn = jacobiSym 5 Nn * jacobiSym (7 - 4 * q') Nn := by
    rw [← jacobiSym.mul_left]
    exact J_congr hNn ⟨24 * p' - 16 * q' + 28, by rw [hpq, hN]; linear_combination 8 * e'⟩
  -- Lemma 4.1, second half
  have L41b : jacobiSym (7 - 4 * q') Nn = 1 :=
    J_sq_one (x := q' - 2) (by omega) ⟨-(2 * p' + 2), by rw [hNn, hN]; linear_combination (-1) * e'⟩
      ⟨-(q' + 2), 2 * p' + 2, by rw [hNn, hN]; linear_combination (-1) * e'⟩
  -- step 7
  have s7 : jacobiSym 5 Nn = -1 := by
    have h := jacobiSym.quadratic_reciprocity_one_mod_four (a := 5) (b := Nn) (by norm_num)
      (Nat.odd_iff.2 (by omega))
    push_cast at h
    rw [h, jacobiSym.mod_left, show ((Nn : ℤ) % ((5 : ℕ) : ℤ)) = 2 by omega]
    norm_num
  rw [s1, s2, s4, s5, s6, L41b, s7]; norm_num

/-- Luo–Lin Theorem 1.1. -/
theorem theorem_1_1 {k m : ℤ} (hk0 : 0 < k) (hk : k % 12 = 9) :
    jacobiSym (P (1 + (24 * m - 8) * k)) (8 * P k ^ 2 - 4 * P k - 1).toNat = -1 := by
  have hko : Odd k := Int.odd_iff.2 (by omega)
  have hk1e : Even (k + 1) := Int.even_iff.2 (by omega)
  obtain ⟨hq8, hp2, hp4, hp5⟩ := res40 hk
  have hpos : 1 ≤ Q k ∧ 1 ≤ P k := by
    have := pos_nat k.toNat
    rw [Int.toNat_of_nonneg hk0.le] at this
    exact ⟨this.1, this.2.2 (by omega)⟩
  have e := Q_sq_sub k
  rw [sgn_odd hko] at e
  have e' := Q_sq_sub (k + 1)
  rw [sgn_even hk1e] at e'
  have hP14 : P (1 + 4 * k) = (Q k ^ 2 + 2 * P k ^ 2) ^ 2 + 2 * (2 * P k * Q k) ^ 2
      + 2 * (2 * P k * Q k) * (Q k ^ 2 + 2 * P k ^ 2) := by
    rw [show 1 + 4 * k = 2 * (2 * k) + 1 by ring, P_add_one]
    simp only [Q_two_mul, P_two_mul]
  exact theorem_1_1_core hpos.2 hpos.1 hq8 hp2 hp4 hp5 e e' (P_add_one k) (Q_add_one k) hP14
    (R_dvd hko)

end RefactorableFC.LjunggrenProof

namespace RefactorableFC.LjunggrenProof

/-- Luo–Lin Lemma 5.1, even case: `x ^ 6 + 5 x ^ 4 + 6 x ^ 2 + 1 = s ^ 2` with `x = 2 z`, `z ≥ 1`,
forces `z = 1`. -/
lemma sextic {z s : ℤ} (hz : 1 ≤ z) (hs : 0 ≤ s)
    (h : (2 * z) ^ 6 + 5 * (2 * z) ^ 4 + 6 * (2 * z) ^ 2 + 1 = s ^ 2) : z = 1 := by
  set A := 8 * z ^ 3 + 5 * z with hA
  have hf : s ^ 2 = A ^ 2 - z ^ 2 + 1 := by rw [← h, hA]; ring
  have hA1 : 1 ≤ A := by nlinarith
  have hlo : (A - 1) ^ 2 < s ^ 2 := by rw [hf]; nlinarith
  have hhi : s ^ 2 ≤ A ^ 2 := by rw [hf]; nlinarith
  have h1 : A - 1 < s := by
    by_contra hc; push Not at hc; nlinarith
  have h2 : s ≤ A := by
    by_contra hc; push Not at hc; nlinarith
  have hsA : s = A := by omega
  rw [hsA] at hf
  nlinarith

lemma three_le_Q_nat (n : ℕ) (hn : 2 ≤ n) : 3 ≤ Q n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · omega
      · have h1 := Q_add_one 1
        rw [Q_one, P_one] at h1
        push_cast; rw [show (1 : ℤ) + 1 = 2 by norm_num] at h1; omega
    · have := ih h
      have h1 := Q_add_one (n : ℤ)
      have := (pos_nat n).2.1
      push_cast; omega

/-- `|Q m| = 1` with `m` odd forces `m = ±1`. -/
lemma eq_one_of_Q {m : ℤ} (h : Q m = 1 ∨ Q m = -1) : m = 1 ∨ m = -1 ∨ m = 0 := by
  rcases le_or_gt 0 m with hm | hm
  · lift m to ℕ using hm
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · interval_cases m <;> simp
    · have := three_le_Q_nat m h2; omega
  · have hm' : 0 ≤ -m := by omega
    have hq := Q_neg (-m)
    rw [neg_neg] at hq
    lift (-m) to ℕ using hm' with k hk
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · interval_cases k <;> omega
    · have := three_le_Q_nat k h2
      have hs := sgn_sq (k : ℤ)
      have : sgn (k : ℤ) = 1 ∨ sgn (k : ℤ) = -1 := by
        rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ (k : ℤ)) with h | h <;> simp [sgn, h]
      rcases this with h3 | h3 <;> rw [h3] at hq <;> omega

lemma P_seven_mul (m : ℤ) :
    P (7 * m) = P m * (7 * Q m ^ 6 + 70 * Q m ^ 4 * P m ^ 2 + 84 * Q m ^ 2 * P m ^ 4
      + 8 * P m ^ 6) := by
  rw [show 7 * m = m + (m + (m + (m + (m + (m + m))))) by ring]
  simp only [Q_add, P_add]
  ring

/-- Luo–Lin Lemma 5.2: `n = 7 m`, `m` odd, `P n` a square ⇒ `m = ±1`. -/
theorem seven {m : ℤ} (hm : Odd m) (hsq : IsSquare (P (7 * m))) : m = 1 ∨ m = -1 := by
  have e := Q_sq_sub m
  rw [sgn_odd hm] at e
  set q := Q m
  set p := P m
  set S := 7 * q ^ 6 + 70 * q ^ 4 * p ^ 2 + 84 * q ^ 2 * p ^ 4 + 8 * p ^ 6 with hS
  have hp1 : 1 ≤ p := P_pos_of_odd hm
  have hSpos : 0 < S := by positivity
  have h7 : ¬ (7 : ℤ) ∣ p := by
    rintro ⟨c, hc⟩
    have : q ^ 2 % 7 = 6 := by
      have : q ^ 2 = 7 * (14 * c ^ 2) - 1 := by rw [hc] at e; linear_combination e
      omega
    have h := Int.emod_emod_of_dvd q (by norm_num : (7 : ℤ) ∣ 7)
    have : q ^ 2 % 7 = (q % 7) ^ 2 % 7 := by rw [sq, sq, Int.mul_emod]
    have hq7 : 0 ≤ q % 7 ∧ q % 7 < 7 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
    obtain ⟨h0, h6⟩ := hq7
    interval_cases hr : q % 7 <;> omega
  have hcop : IsCoprime p S := by
    -- S ≡ -7 (mod p) and 7 ∤ p, 7 prime
    have hSmod : S = 7 * q ^ 6 + p * (70 * q ^ 4 * p + 84 * q ^ 2 * p ^ 3 + 8 * p ^ 5) := by
      rw [hS]; ring
    have hq6 : IsCoprime p q := by
      refine ⟨2 * p, -q, ?_⟩; linear_combination (-1 : ℤ) * e
    have h7p : IsCoprime p 7 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hd : Int.gcd p 7 ∣ 7 := by
        have := Int.gcd_dvd_right (a := p) (b := 7); exact_mod_cast this
      have h7' : Nat.Prime 7 := by norm_num
      rcases (Nat.dvd_prime h7').1 hd with h | h
      · exact h
      · exfalso; apply h7
        have := Int.gcd_dvd_left (a := p) (b := 7)
        rw [h] at this; exact_mod_cast this
    have : IsCoprime p (7 * q ^ 6) := h7p.mul_right (hq6.pow_right)
    rw [hSmod]
    exact this.add_mul_left_right _
  obtain ⟨y, hy⟩ := hsq
  rw [P_seven_mul] at hy
  obtain ⟨s0, hs0⟩ := Int.sq_of_isCoprime hcop.symm (by rw [mul_comm, hy, sq])
  have hSsq : S = |s0| ^ 2 := by
    rcases hs0 with h | h
    · rw [h, sq_abs]
    · exfalso; have := sq_nonneg s0; linarith
  have hqne : q ≠ 0 := by rintro hq; rw [hq] at e; nlinarith
  have hz : 1 ≤ |q| := Int.one_le_abs hqne
  have hf : (2 * |q|) ^ 6 + 5 * (2 * |q|) ^ 4 + 6 * (2 * |q|) ^ 2 + 1 = |s0| ^ 2 := by
    rw [← hSsq, hS]
    have hq2 : |q| ^ 2 = q ^ 2 := sq_abs q
    have e2 : (2 * |q|) ^ 6 + 5 * (2 * |q|) ^ 4 + 6 * (2 * |q|) ^ 2 + 1
        = 64 * (q ^ 2) ^ 3 + 80 * (q ^ 2) ^ 2 + 24 * q ^ 2 + 1 := by rw [← hq2]; ring
    rw [e2]
    linear_combination (4 * p ^ 4 + 44 * p ^ 2 * q ^ 2 + 2 * p ^ 2 + 57 * q ^ 4
      + 23 * q ^ 2 + 1) * e
  have h1 := sextic hz (abs_nonneg s0) hf
  have hq1 : q = 1 ∨ q = -1 := by
    rcases abs_eq (zero_le_one) |>.1 h1 with h | h <;> simp [h]
  rcases eq_one_of_Q hq1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso; rw [h] at hm; exact absurd hm (by decide)

end RefactorableFC.LjunggrenProof

namespace RefactorableFC.LjunggrenProof

/-- Luo–Lin Lemma 4.2. -/
lemma split {n : ℤ} (h1 : n % 840 = 1) (hne : n ≠ 1) :
    ∃ m k : ℤ, n = 1 + (24 * m - 8) * k ∧ 0 < k ∧ k % 12 = 9 := by
  obtain ⟨t, ht⟩ : ∃ t, n - 1 = 840 * t := ⟨(n - 1) / 840, by omega⟩
  have ht0 : t.natAbs ≠ 0 := by omega
  obtain ⟨e, w, hw, hsw⟩ := Nat.exists_eq_pow_mul_and_not_dvd ht0 3 (by norm_num)
  set X : ℤ := 3 ^ e with hX
  have hXodd : X % 2 = 1 := by
    rw [hX, ← Int.odd_iff]; exact Odd.pow (by decide)
  have hXpos : 0 < X := by positivity
  have hw3 : (w : ℤ) % 3 ≠ 0 := by
    intro h; exact hw (by exact_mod_cast Int.dvd_of_emod_eq_zero h)
  obtain ⟨w', hw', htw⟩ : ∃ w' : ℤ, w' % 3 ≠ 0 ∧ t = w' * X := by
    rcases Int.natAbs_eq t with h | h
    · exact ⟨w, hw3, by rw [h, hsw]; push_cast; ring⟩
    · exact ⟨-w, by omega, by rw [h, hsw]; push_cast; ring⟩
  have hn : n = 1 + 840 * (w' * X) := by rw [← htw]; omega
  have hX4 : X % 4 = 1 ∨ X % 4 = 3 := by omega
  have hl : (8 * w') % 24 = 8 ∨ (8 * w') % 24 = 16 := by omega
  rcases hX4 with hX4 | hX4 <;> rcases hl with hl | hl
  · -- l = 5 l0, k = 7 (3 X)
    refine ⟨(5 * (8 * w') + 8) / 24, 7 * (3 * X), ?_, by omega, by omega⟩
    rw [show 24 * ((5 * (8 * w') + 8) / 24) - 8 = 5 * (8 * w') by omega, hn]; ring
  · -- l = l0, k = 35 (3 X)
    refine ⟨(8 * w' + 8) / 24, 35 * (3 * X), ?_, by omega, by omega⟩
    rw [show 24 * ((8 * w' + 8) / 24) - 8 = 8 * w' by omega, hn]; ring
  · -- l = 35 l0, k = 3 X
    refine ⟨(35 * (8 * w') + 8) / 24, 3 * X, ?_, by omega, by omega⟩
    rw [show 24 * ((35 * (8 * w') + 8) / 24) - 8 = 35 * (8 * w') by omega, hn]; ring
  · -- l = 7 l0, k = 5 (3 X)
    refine ⟨(7 * (8 * w') + 8) / 24, 5 * (3 * X), ?_, by omega, by omega⟩
    rw [show 24 * ((7 * (8 * w') + 8) / 24) - 8 = 7 * (8 * w') by omega, hn]; ring

/-- Luo–Lin Corollary 4.3, the `n ≡ 1 (mod 840)` half. -/
lemma cor_4_3 {n : ℤ} (h1 : n % 840 = 1) (hsq : IsSquare (P n)) : n = 1 := by
  by_contra hne
  obtain ⟨m, k, rfl, hk0, hk⟩ := split h1 hne
  have hJ := theorem_1_1 (m := m) hk0 hk
  obtain ⟨y, hy⟩ := hsq
  rw [hy, ← sq, jacobiSym.pow_left] at hJ
  nlinarith [sq_nonneg (jacobiSym y (8 * P k ^ 2 - 4 * P k - 1).toNat)]

lemma P_neg_odd {n : ℤ} (h : Odd n) : P (-n) = P n := by
  rw [P_neg, sgn_odd h]; ring

/-- All odd `n` with `P n` a square: `n = ±1, ±7`. -/
theorem P_sq {n : ℤ} (hodd : Odd n) (hsq : IsSquare (P n)) :
    n = 1 ∨ n = -1 ∨ n = 7 ∨ n = -7 := by
  rcases sieve hodd hsq with h | h | h | h
  · exact Or.inl (cor_4_3 h hsq)
  · obtain ⟨m, rfl⟩ : ∃ m, n = 7 * m := ⟨n / 7, by omega⟩
    have hm : Odd m := by rcases hodd with ⟨j, hj⟩; exact Int.odd_iff.2 (by omega)
    rcases seven hm hsq with rfl | rfl <;> simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = 7 * m := ⟨n / 7, by omega⟩
    have hm : Odd m := by rcases hodd with ⟨j, hj⟩; exact Int.odd_iff.2 (by omega)
    rcases seven hm hsq with rfl | rfl <;> simp
  · have h' : (-n) % 840 = 1 := by omega
    have := cor_4_3 h' (by rwa [P_neg_odd hodd])
    omega

lemma Q_seven : Q 7 = 239 := by
  simp only [show (7 : ℤ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by norm_num, Q_add_one, P_add_one,
    Q_zero, P_zero]
  norm_num

/-- **Ljunggren's theorem** (1942), by the elementary method of Luo–Lin (Proc. AMS 154 (2026)). -/
theorem ljunggren : ∀ x y : ℕ, x ^ 2 + 1 = 2 * y ^ 4 → x = 1 ∨ x = 239 := by
  intro x y h
  have h' : (x : ℤ) ^ 2 - 2 * ((y : ℤ) ^ 2) ^ 2 = -1 := by
    have : ((x ^ 2 + 1 : ℕ) : ℤ) = ((2 * y ^ 4 : ℕ) : ℤ) := by rw [h]
    push_cast at this; linear_combination this
  obtain ⟨n, hodd, hx, hy⟩ := neg_pell_classify (by positivity) (by positivity) h'
  have hsq : IsSquare (P n) := ⟨(y : ℤ), by rw [← hy]; ring⟩
  have hs1 := sgn_odd (show Odd (1 : ℤ) by decide)
  have hs7 := sgn_odd (show Odd (7 : ℤ) by decide)
  rcases P_sq hodd hsq with rfl | rfl | rfl | rfl
  · left; rw [Q_one] at hx; exact_mod_cast hx
  · exfalso; rw [Q_neg, hs1, Q_one] at hx; omega
  · right; rw [Q_seven] at hx; exact_mod_cast hx
  · exfalso; rw [Q_neg, hs7, Q_seven] at hx; omega

end RefactorableFC.LjunggrenProof

namespace Zelinsky

lemma odd_refactorable_square {n : ℕ} (hn : n.IsRefactorable) (ho : Odd n) :
    ∃ x : ℕ, n = x ^ 2 := by
  have hn0 : n ≠ 0 := by have := hn.pos; omega
  have hcount : Odd n.divisors.card := ho.of_dvd_nat hn.2
  have hexp (p : ℕ) (hp : p ∈ n.primeFactors) : Even (n.factorization p) := by
    have hd : n.factorization p + 1 ∣ n.divisors.card := by
      rw [Nat.card_divisors hn0]
      exact Finset.dvd_prod_of_mem _ hp
    have := Nat.odd_iff.mp (hcount.of_dvd_nat hd)
    exact Nat.even_iff.mpr (by omega)
  have hs : IsSquare n := by
    rw [← Nat.prod_factorization_pow_eq_self hn0, Finsupp.prod]
    apply Finset.isSquare_prod
    intro p hp
    obtain ⟨k, hk⟩ := hexp p (by simpa using hp)
    refine ⟨p ^ k, ?_⟩
    rw [hk, pow_add]
  exact hs.exists_sq

/-- The refactorable successor of an odd square is twice a fourth power. -/
lemma fourth_power : ∀ x : ℕ, Odd x → (x ^ 2 + 1).IsRefactorable →
    ∃ y : ℕ, x ^ 2 + 1 = 2 * y ^ 4 := by
  intro x hx href
  obtain ⟨t, ht⟩ := hx
  let m := 2*(t*(t+1))+1
  have oddm : Odd m := ⟨t*(t+1), rfl⟩
  have m0 : m ≠ 0 := by dsimp [m]; omega
  have split : x^2+1 = 2*m := by rw [ht]; dsimp [m]; ring
  have tau : m.divisors.card ∣ m := by
    have h := href.2
    rw [split, oddm.coprime_two_left.card_divisors_mul, show (2 : ℕ).divisors.card = 2 by decide] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) h
  have allDiv (d : ℕ) (hd : d ∣ m) : d % 4 = 1 := by
    have hd0 : d ≠ 0 := fun h => m0 (by simp [h] at hd)
    have primes (p : ℕ) (hp : p ∈ d.primeFactors) : (p : ZMod 4) = 1 := by
      have prime := Nat.prime_of_mem_primeFactors hp
      have pd := Nat.dvd_of_mem_primeFactors hp
      have pm := pd.trans hd
      have pn : p ∣ x^2+1 := split ▸ pm.trans (dvd_mul_left m 2)
      have sq : (x : ZMod p)^2 + 1 = 0 := by
        exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr pn
      let : Fact p.Prime := ⟨prime⟩
      have h3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one (eq_neg_of_add_eq_zero_left sq)
      have po := Nat.odd_iff.mp (oddm.of_dvd_nat pm)
      have h1 : p ≡ 1 [MOD 4] := by change p % 4 = 1; omega
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
    have hm : (d : ZMod 4) = 1 := calc
      _ = ∏ p ∈ d.primeFactors, (p : ZMod 4) ^ d.factorization p := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 4) (Nat.prod_primeFactors_pow_factorization hd0)
      _ = 1 := Finset.prod_eq_one fun p hp => by rw [primes p hp, one_pow]
    exact (ZMod.natCast_eq_natCast_iff d 1 4).mp (by simpa using hm)
  have hexp (p : ℕ) (hp : p ∈ m.primeFactors) : m.factorization p % 4 = 0 := by
    have hd : m.factorization p + 1 ∣ m.divisors.card := by
      rw [Nat.card_divisors m0]
      exact Finset.dvd_prod_of_mem _ hp
    have := allDiv _ (hd.trans tau)
    omega
  refine ⟨∏ p ∈ m.primeFactors, p^(m.factorization p/4), ?_⟩
  rw [split, ← Finset.prod_pow]
  apply congrArg (2 * ·)
  calc
    m = _ := Nat.prod_primeFactors_pow_factorization m0
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul]
      congr 1
      have := hexp p hp
      omega

lemma odd_pair_first_eq_one {n : ℕ}
    (ho : Odd n) (hn : n.IsRefactorable) (hs : (n + 1).IsRefactorable) : n = 1 := by
  obtain ⟨x, hx⟩ := odd_refactorable_square hn ho
  have hxo : Odd x := (Nat.odd_pow_iff (by decide : 2 ≠ 0)).mp (hx ▸ ho)
  obtain ⟨y, hy⟩ := fourth_power x hxo (by simpa [hx] using hs)
  rcases RefactorableFC.LjunggrenProof.ljunggren x y hy with h | h
  · simpa [h] using hx
  · have hnval : n = 57121 := by norm_num [h] at hx; exact hx
    have bad : ¬ Nat.IsRefactorable 57122 := by decide +kernel
    exact False.elim (bad (by simpa [hnval] using hs))

end Zelinsky

theorem OMA.solution : type_of% @RefactorableNumber.no_three_consecutive_refactorable := by
  intro n h
  rcases h with ⟨hn, hn1, hn2⟩
  rcases Nat.even_or_odd n with he | ho
  · have hodd : Odd (n + 1) := he.add_odd (by decide)
    have hsmall := Zelinsky.odd_pair_first_eq_one hodd hn1 (by simpa [Nat.add_assoc] using hn2)
    have := hn.pos
    omega
  · have hsmall := Zelinsky.odd_pair_first_eq_one ho hn hn1
    have bad : ¬ Nat.IsRefactorable 3 := by decide
    exact bad (by simpa [hsmall] using hn2)
