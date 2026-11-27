import OMAStatements.S_oeis_a028886

-- Proof of Kurkov's primality criterion for OEIS A028886
-- via norm-Euclidean descent in Z[sqrt(2)].

namespace OMA.OeisA028886Proof

-- Basic integer and natural helpers

private lemma nat_exists_min (P : ℕ → Prop) (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ k, P k → n ≤ k := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hlt : ∃ k, k < n ∧ P k
    · obtain ⟨k, hkn, hk⟩ := hlt
      exact ih k hkn hk
    · refine ⟨n, hn, fun k hk => ?_⟩
      by_contra hle
      exact hlt ⟨k, Nat.lt_of_not_le hle, hk⟩

private lemma int_sq_le {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) : a * a ≤ b * b :=
  Int.le_trans (Int.mul_le_mul_of_nonneg_left hab ha)
    (Int.mul_le_mul_of_nonneg_right hab (by omega))

private lemma int_sq_lt {a b : ℤ} (ha : 0 ≤ a) (hab : a < b) : a * a < b * b :=
  Int.lt_of_le_of_lt (Int.mul_le_mul_of_nonneg_left hab.le ha)
    (Int.mul_lt_mul_of_pos_right hab (by omega))

private lemma int_le_of_sq_le {a b : ℤ} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b := by
  by_contra hba
  have hlt : b < a := by omega
  have hsq := int_sq_lt hb hlt
  omega

private lemma int_lt_of_sq_lt {a b : ℤ} (hb : 0 ≤ b) (h : a * a < b * b) : a < b := by
  by_contra hba
  have hle : b ≤ a := by omega
  have hsq := int_sq_le hb hle
  omega

private lemma int_mul_le_mul {a b c d : ℤ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hcd : c ≤ d) : a * c ≤ b * d :=
  Int.le_trans (Int.mul_le_mul_of_nonneg_left hcd ha)
    (Int.mul_le_mul_of_nonneg_right hab (by omega))

private def iabs (x : ℤ) : ℤ := if 0 ≤ x then x else -x

private lemma iabs_of_nonneg {x : ℤ} (h : 0 ≤ x) : iabs x = x := if_pos h

private lemma iabs_of_neg {x : ℤ} (h : x < 0) : iabs x = -x := if_neg (by omega)

private lemma iabs_nonneg (x : ℤ) : 0 ≤ iabs x := by
  by_cases h : 0 ≤ x
  · rw [iabs_of_nonneg h]; exact h
  · rw [iabs_of_neg (by omega)]; omega

private lemma iabs_sq (x : ℤ) : iabs x * iabs x = x * x := by
  by_cases h : 0 ≤ x
  · rw [iabs_of_nonneg h]
  · rw [iabs_of_neg (by omega), Int.neg_mul_neg]

private lemma iabs_mul (x y : ℤ) : iabs (x * y) = iabs x * iabs y := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> rcases lt_trichotomy y 0 with hy | rfl | hy
  · have hxy : 0 ≤ x * y := Int.mul_nonneg_of_nonpos_of_nonpos hx.le hy.le
    rw [iabs_of_nonneg hxy, iabs_of_neg hx, iabs_of_neg hy, Int.neg_mul_neg]
  · simp [iabs]
  · have hxy : x * y < 0 := Int.mul_neg_of_neg_of_pos hx hy
    rw [iabs_of_neg hxy, iabs_of_neg hx, iabs_of_nonneg hy.le, Int.neg_mul]
  · simp [iabs]
  · simp [iabs]
  · simp [iabs]
  · have hxy : x * y < 0 := Int.mul_neg_of_pos_of_neg hx hy
    rw [iabs_of_neg hxy, iabs_of_nonneg hx.le, iabs_of_neg hy, Int.mul_neg]
  · simp [iabs]
  · have hxy : 0 ≤ x * y := Int.mul_nonneg hx.le hy.le
    rw [iabs_of_nonneg hxy, iabs_of_nonneg hx.le, iabs_of_nonneg hy.le]

private lemma int_natAbs_eq_iabs (x : ℤ) : (x.natAbs : ℤ) = iabs x := by
  by_cases h : 0 ≤ x
  · rw [Int.natAbs_of_nonneg h, iabs_of_nonneg h]
  · rw [iabs_of_neg (by omega)]
    have := Int.ofNat_natAbs_of_nonpos (show x ≤ 0 by omega)
    omega

private lemma int_natAbs_sq (x : ℤ) : (x.natAbs : ℤ) * (x.natAbs : ℤ) = x * x := by
  rw [int_natAbs_eq_iabs, iabs_sq]

-- Combinatorial and Pell identities

private lemma choose_two_int (q : ℕ) :
    2 * (q.choose 2 : ℤ) = (q : ℤ) * ((q : ℤ) - 1) := by
  induction q with
  | zero => decide
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    have h1 : ((n : ℤ) + 1) * ((n : ℤ) + 1 - 1) = (n : ℤ) * ((n : ℤ) - 1) + 2 * (n : ℤ) := by
      rw [Int.add_sub_cancel, Int.add_mul, Int.one_mul, Int.mul_sub, Int.mul_one]
      omega
    omega

private lemma int_linear_sq (a b : ℤ) :
    (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]
  omega

private lemma int_diff_sq (a b : ℤ) :
    (a - b) * (a + b) = a * a - b * b := by
  rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm a b]
  omega

private lemma int_two_mul_sq (a : ℤ) : (2 * a) * (2 * a) = 4 * (a * a) := by
  rw [Int.mul_assoc, Int.mul_comm a (2 * a), Int.mul_assoc]
  omega

private lemma pell_expand (q m k : ℤ) :
    (2 * q + 2 * m + 1) * (2 * q + 2 * m + 1) - 8 * (k * k) - ((2 * m + 1) * (2 * m + 1) - 8) =
      4 * (q * (q - 1)) + 8 * (q * (m + 1) + 1 - k * k) := by
  have h4 : 2 * q + 2 * m + 1 = 2 * q + (2 * m + 1) := by omega
  have h1 : (2 * q + (2 * m + 1)) * (2 * q + (2 * m + 1)) =
      (2 * q) * (2 * q) + 2 * ((2 * q) * (2 * m + 1)) + (2 * m + 1) * (2 * m + 1) :=
    int_linear_sq (2 * q) (2 * m + 1)
  have h2 : (2 * q) * (2 * q) = 4 * (q * q) := int_two_mul_sq q
  have h3 : 2 * ((2 * q) * (2 * m + 1)) = 8 * (q * m) + 4 * q := by
    rw [Int.mul_add, Int.mul_one]
    have ha : (2 * q) * (2 * m) = 4 * (q * m) := by
      rw [Int.mul_assoc, Int.mul_comm q (2 * m), Int.mul_assoc, Int.mul_comm m q]
      omega
    rw [ha]
    omega
  have h5 : q * (q - 1) = q * q - q := by rw [Int.mul_sub, Int.mul_one]
  have h6 : q * (m + 1) = q * m + q := by rw [Int.mul_add, Int.mul_one]
  rw [h4, h1, h2, h3, h5, h6]
  omega

private lemma sq_iff_pell (m q k : ℕ) :
    q * (m + 1) + q.choose 2 + 1 = k * k ↔
      (2 * (q : ℤ) + 2 * (m : ℤ) + 1) * (2 * (q : ℤ) + 2 * (m : ℤ) + 1) - 8 * ((k : ℤ) * (k : ℤ)) =
        (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1) - 8 := by
  have hc := choose_two_int q
  have hexp := pell_expand (q : ℤ) (m : ℤ) (k : ℤ)
  constructor
  · intro h
    have hz : (q : ℤ) * ((m : ℤ) + 1) + (q.choose 2 : ℤ) + 1 = (k : ℤ) * (k : ℤ) := by
      exact_mod_cast h
    omega
  · intro h
    have hz : (q : ℤ) * ((m : ℤ) + 1) + (q.choose 2 : ℤ) + 1 = (k : ℤ) * (k : ℤ) := by
      omega
    exact_mod_cast hz

private lemma N_cast (m : ℕ) (hm : 2 < m) :
    (((2 * m + 1) ^ 2 - 8 : ℕ) : ℤ) = (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1) - 8 := by
  have hge : 8 ≤ (2 * m + 1) ^ 2 := by
    rw [Nat.pow_two]
    have h1 : 7 ≤ 2 * m + 1 := by omega
    exact Nat.le_trans (by decide : 8 ≤ 7 * 7) (Nat.mul_le_mul h1 h1)
  rw [Int.natCast_sub hge, Nat.pow_two]
  push_cast
  rfl

-- Forward direction: N prime -> no square in range

private lemma forward_dir (m : ℕ) (hm : 2 < m) (hN : Nat.Prime ((2 * m + 1) ^ 2 - 8)) :
    ∀ q : ℕ, 1 ≤ q → q ≤ 2 * (m - 2) → ¬ IsSquare (q * (m + 1) + q.choose 2 + 1) := by
  intro q hq1 hq2 ⟨k, hk⟩
  have hpell := (sq_iff_pell m q k).mp hk
  set N : ℕ := (2 * m + 1) ^ 2 - 8
  have hNz : (N : ℤ) = (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1) - 8 := N_cast m hm
  have hk2_ge : 5 ≤ k * k := by
    have : 1 * (m + 1) ≤ q * (m + 1) := Nat.mul_le_mul_right (m + 1) hq1
    omega
  have hk_ub : (k : ℤ) ≤ 2 * (m : ℤ) - 3 := by
    have hq_ub : (q : ℤ) ≤ 2 * (m : ℤ) - 4 := by omega
    have hc := choose_two_int q
    have hk2z : (k : ℤ) * (k : ℤ) = (q : ℤ) * ((m : ℤ) + 1) + (q.choose 2 : ℤ) + 1 := by
      exact_mod_cast hk.symm
    have h1 : (q : ℤ) * ((m : ℤ) + 1) ≤ (2 * (m : ℤ) - 4) * ((m : ℤ) + 1) :=
      Int.mul_le_mul_of_nonneg_right hq_ub (by omega)
    have h2 : (q : ℤ) * ((q : ℤ) - 1) ≤ (2 * (m : ℤ) - 4) * (2 * (m : ℤ) - 5) :=
      int_mul_le_mul (by omega) hq_ub (by omega) (by omega)
    have hm1 : (2 * (m : ℤ) - 4) * ((m : ℤ) + 1) = 2 * ((m : ℤ) * (m : ℤ)) - 2 * (m : ℤ) - 4 := by
      rw [Int.sub_mul, Int.mul_add, Int.mul_one, Int.mul_add, Int.mul_assoc]
      omega
    have hm2 : (2 * (m : ℤ) - 4) * (2 * (m : ℤ) - 5) =
        4 * ((m : ℤ) * (m : ℤ)) - 18 * (m : ℤ) + 20 := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, int_two_mul_sq]
      omega
    have hm3 : (2 * (m : ℤ) - 2) * (2 * (m : ℤ) - 2) =
        4 * ((m : ℤ) * (m : ℤ)) - 8 * (m : ℤ) + 4 := by
      rw [Int.sub_mul, Int.mul_sub, int_two_mul_sq]
      omega
    have hbound : (k : ℤ) * (k : ℤ) < (2 * (m : ℤ) - 2) * (2 * (m : ℤ) - 2) := by
      omega
    have hlt := int_lt_of_sq_lt (by omega) hbound
    omega
  set A : ℤ := 2 * (q : ℤ) + 2 * (m : ℤ) + 1
  have hA_pos : 0 < A := by omega
  have hA_ub : A ≤ 6 * (m : ℤ) - 7 := by omega
  have hprod : ((2 * (m : ℤ) + 1) * (k : ℤ) - A) * ((2 * (m : ℤ) + 1) * (k : ℤ) + A) =
      (N : ℤ) * ((k : ℤ) * (k : ℤ) - 1) := by
    have hdiff_id : ((2 * (m : ℤ) + 1) * (k : ℤ) - A) * ((2 * (m : ℤ) + 1) * (k : ℤ) + A) =
        ((2 * (m : ℤ) + 1) * (k : ℤ)) * ((2 * (m : ℤ) + 1) * (k : ℤ)) - A * A :=
      int_diff_sq ((2 * (m : ℤ) + 1) * (k : ℤ)) A
    have hsq_mul : ((2 * (m : ℤ) + 1) * (k : ℤ)) * ((2 * (m : ℤ) + 1) * (k : ℤ)) =
        ((2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1)) * ((k : ℤ) * (k : ℤ)) := by
      rw [Int.mul_assoc, Int.mul_left_comm (k : ℤ) (2 * (m : ℤ) + 1) (k : ℤ), ← Int.mul_assoc]
    have hrhs_id : ((2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1) - 8) * ((k : ℤ) * (k : ℤ) - 1) =
        ((2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1)) * ((k : ℤ) * (k : ℤ)) -
          8 * ((k : ℤ) * (k : ℤ)) - ((2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1) - 8) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_one]
      omega
    have hpell' : A * A - 8 * ((k : ℤ) * (k : ℤ)) =
        (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1) - 8 := hpell
    rw [hdiff_id, hsq_mul, hNz, hrhs_id]
    omega
  have hsum_pos : 0 < (2 * (m : ℤ) + 1) * (k : ℤ) + A := by
    have : 0 ≤ (2 * (m : ℤ) + 1) * (k : ℤ) := Int.mul_nonneg (by omega) (by omega)
    omega
  have hsum_lt : (2 * (m : ℤ) + 1) * (k : ℤ) + A < (N : ℤ) := by
    have h1 : (2 * (m : ℤ) + 1) * (k : ℤ) ≤ (2 * (m : ℤ) + 1) * (2 * (m : ℤ) - 3) :=
      Int.mul_le_mul_of_nonneg_left hk_ub (by omega)
    have h2 : (2 * (m : ℤ) + 1) * (2 * (m : ℤ) - 3) =
        4 * ((m : ℤ) * (m : ℤ)) - 4 * (m : ℤ) - 3 := by
      rw [Int.add_mul, Int.mul_sub, Int.one_mul, int_two_mul_sq]
      omega
    have h3 : (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1) =
        4 * ((m : ℤ) * (m : ℤ)) + 4 * (m : ℤ) + 1 := by
      rw [int_linear_sq, int_two_mul_sq]
      omega
    rw [hNz, h3]
    omega
  have hN_pos : (0 : ℤ) < (N : ℤ) := by
    have h1 : (7 : ℤ) * 7 ≤ (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1) :=
      int_sq_le (by omega) (by omega)
    omega
  have hk1_pos : (0 : ℤ) < (k : ℤ) * (k : ℤ) - 1 := by
    have : (5 : ℤ) ≤ (k : ℤ) * (k : ℤ) := by exact_mod_cast hk2_ge
    omega
  have hrhs_pos : 0 < (N : ℤ) * ((k : ℤ) * (k : ℤ) - 1) := Int.mul_pos hN_pos hk1_pos
  have hdiff_pos : 0 < (2 * (m : ℤ) + 1) * (k : ℤ) - A := by
    by_contra hle
    have hnp : ((2 * (m : ℤ) + 1) * (k : ℤ) - A) * ((2 * (m : ℤ) + 1) * (k : ℤ) + A) ≤ 0 :=
      Int.mul_nonpos_of_nonpos_of_nonneg (by omega) hsum_pos.le
    omega
  have hdiff_lt : (2 * (m : ℤ) + 1) * (k : ℤ) - A < (N : ℤ) := by omega
  set u : ℕ := ((2 * (m : ℤ) + 1) * (k : ℤ) - A).natAbs
  set v : ℕ := ((2 * (m : ℤ) + 1) * (k : ℤ) + A).natAbs
  have hu_eq : (u : ℤ) = (2 * (m : ℤ) + 1) * (k : ℤ) - A := Int.natAbs_of_nonneg hdiff_pos.le
  have hv_eq : (v : ℤ) = (2 * (m : ℤ) + 1) * (k : ℤ) + A := Int.natAbs_of_nonneg hsum_pos.le
  have hu_pos : 0 < u := by omega
  have hv_pos : 0 < v := by omega
  have hu_lt : u < N := by omega
  have hv_lt : v < N := by omega
  have hdvd : N ∣ u * v := by
    refine ⟨k * k - 1, ?_⟩
    have hk_ge1 : 1 ≤ k * k := by omega
    have hk_sub : ((k * k - 1 : ℕ) : ℤ) = (k : ℤ) * (k : ℤ) - 1 := by
      rw [Int.natCast_sub hk_ge1]
      push_cast
      rfl
    have hcz : ((u * v : ℕ) : ℤ) = ((N * (k * k - 1) : ℕ) : ℤ) := by
      push_cast
      rw [hk_sub, hu_eq, hv_eq]
      exact hprod
    exact_mod_cast hcz
  rcases hN.dvd_mul.mp hdvd with hdu | hdv
  · exact absurd (Nat.le_of_dvd hu_pos hdu) (Nat.not_le_of_gt hu_lt)
  · exact absurd (Nat.le_of_dvd hv_pos hdv) (Nat.not_le_of_gt hv_lt)

-- Minimal Z[sqrt(2)] arithmetic

private structure Z2 where
  re : ℤ
  im : ℤ
  deriving DecidableEq

private def z2_ofInt (n : ℤ) : Z2 := ⟨n, 0⟩
private def z2_add (a b : Z2) : Z2 := ⟨a.re + b.re, a.im + b.im⟩
private def z2_neg (a : Z2) : Z2 := ⟨-a.re, -a.im⟩
private def z2_sub (a b : Z2) : Z2 := ⟨a.re - b.re, a.im - b.im⟩
private def z2_mul (a b : Z2) : Z2 := ⟨a.re * b.re + 2 * (a.im * b.im), a.re * b.im + a.im * b.re⟩
private def z2_star (a : Z2) : Z2 := ⟨a.re, -a.im⟩
private def Z2.norm (a : Z2) : ℤ := a.re * a.re - 2 * (a.im * a.im)
private def z2_dvd (a b : Z2) : Prop := ∃ c : Z2, b = z2_mul a c
private def z2_unit (u : Z2) : Prop := u.norm.natAbs = 1
private def z2_assoc (a b : Z2) : Prop := ∃ u : Z2, z2_unit u ∧ z2_mul a u = b

private lemma z2_eq_iff (a b : Z2) : a = b ↔ a.re = b.re ∧ a.im = b.im := by
  cases a; cases b; simp

private lemma z2_mul_comm (a b : Z2) : z2_mul a b = z2_mul b a := by
  rw [z2_eq_iff]
  simp only [z2_mul]
  exact ⟨by rw [Int.mul_comm a.re b.re, Int.mul_comm a.im b.im],
         by rw [Int.mul_comm a.re b.im, Int.mul_comm a.im b.re, Int.add_comm]⟩

private lemma z2_mul_assoc (a b c : Z2) : z2_mul (z2_mul a b) c = z2_mul a (z2_mul b c) := by
  rw [z2_eq_iff]
  simp only [z2_mul, Int.add_mul, Int.mul_add]
  constructor
  · have h1 : (2 * (a.im * b.im)) * c.re = 2 * (a.im * (b.im * c.re)) := by
      rw [Int.mul_assoc, Int.mul_assoc]
    have h2 : (a.re * b.im) * c.im = a.re * (b.im * c.im) := Int.mul_assoc _ _ _
    have h3 : (a.im * b.re) * c.im = a.im * (b.re * c.im) := Int.mul_assoc _ _ _
    have h4 : a.re * (2 * (b.im * c.im)) = 2 * (a.re * (b.im * c.im)) :=
      Int.mul_left_comm a.re 2 (b.im * c.im)
    have h5 : (a.re * b.re) * c.re = a.re * (b.re * c.re) := Int.mul_assoc _ _ _
    omega
  · have h1 : (2 * (a.im * b.im)) * c.im = 2 * (a.im * (b.im * c.im)) := by
      rw [Int.mul_assoc, Int.mul_assoc]
    have h2 : a.im * (2 * (b.im * c.im)) = 2 * (a.im * (b.im * c.im)) :=
      Int.mul_left_comm a.im 2 (b.im * c.im)
    have h3 : (a.re * b.re) * c.im = a.re * (b.re * c.im) := Int.mul_assoc _ _ _
    have h4 : (a.re * b.im) * c.re = a.re * (b.im * c.re) := Int.mul_assoc _ _ _
    have h5 : (a.im * b.re) * c.re = a.im * (b.re * c.re) := Int.mul_assoc _ _ _
    omega

private lemma z2_mul_add (a b c : Z2) :
    z2_mul a (z2_add b c) = z2_add (z2_mul a b) (z2_mul a c) := by
  rw [z2_eq_iff]
  simp only [z2_mul, z2_add, Int.mul_add]
  exact ⟨by omega, by omega⟩

private lemma z2_add_mul (a b c : Z2) :
    z2_mul (z2_add a b) c = z2_add (z2_mul a c) (z2_mul b c) := by
  rw [z2_mul_comm, z2_mul_add, z2_mul_comm c a, z2_mul_comm c b]

private lemma z2_mul_one (a : Z2) : z2_mul a (z2_ofInt 1) = a := by
  rw [z2_eq_iff]
  simp [z2_mul, z2_ofInt]

private lemma z2_one_mul (a : Z2) : z2_mul (z2_ofInt 1) a = a := by
  rw [z2_mul_comm, z2_mul_one]

private lemma z2_norm_mul (a b : Z2) : Z2.norm (z2_mul a b) = Z2.norm a * Z2.norm b := by
  simp only [Z2.norm, z2_mul]
  have hL1 : (a.re * b.re + 2 * (a.im * b.im)) * (a.re * b.re + 2 * (a.im * b.im)) =
      (a.re * b.re) * (a.re * b.re) + 4 * ((a.re * b.re) * (a.im * b.im)) +
        4 * ((a.im * b.im) * (a.im * b.im)) := by
    rw [int_linear_sq, int_two_mul_sq]
    have h1 : 2 * ((a.re * b.re) * (2 * (a.im * b.im))) = 4 * ((a.re * b.re) * (a.im * b.im)) := by
      rw [Int.mul_left_comm (a.re * b.re) 2 (a.im * b.im)]
      omega
    rw [h1]
  have hL2 : (a.re * b.im + a.im * b.re) * (a.re * b.im + a.im * b.re) =
      (a.re * b.im) * (a.re * b.im) + 2 * ((a.re * b.im) * (a.im * b.re)) +
        (a.im * b.re) * (a.im * b.re) :=
    int_linear_sq (a.re * b.im) (a.im * b.re)
  have hR : (a.re * a.re - 2 * (a.im * a.im)) * (b.re * b.re - 2 * (b.im * b.im)) =
      (a.re * a.re) * (b.re * b.re) - 2 * ((a.re * a.re) * (b.im * b.im)) -
        2 * ((a.im * a.im) * (b.re * b.re)) + 4 * ((a.im * a.im) * (b.im * b.im)) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have h1 : (2 * (a.im * a.im)) * (2 * (b.im * b.im)) = 4 * ((a.im * a.im) * (b.im * b.im)) := by
      rw [Int.mul_assoc, Int.mul_comm (a.im * a.im) (2 * (b.im * b.im)), Int.mul_assoc,
        Int.mul_comm (b.im * b.im) (a.im * a.im)]
      omega
    have h2 : (2 * (a.im * a.im)) * (b.re * b.re) = 2 * ((a.im * a.im) * (b.re * b.re)) :=
      Int.mul_assoc 2 _ _
    have h3 : (a.re * a.re) * (2 * (b.im * b.im)) = 2 * ((a.re * a.re) * (b.im * b.im)) :=
      Int.mul_left_comm _ 2 _
    omega
  have hc1 : ∀ x y z w : ℤ, (x * y) * (z * w) = (x * z) * (y * w) := fun x y z w => by
    rw [Int.mul_assoc, Int.mul_assoc, Int.mul_left_comm y z w]
  have he1 : (a.re * b.re) * (a.re * b.re) = (a.re * a.re) * (b.re * b.re) := hc1 _ _ _ _
  have he2 : (a.im * b.im) * (a.im * b.im) = (a.im * a.im) * (b.im * b.im) := hc1 _ _ _ _
  have he3 : (a.re * b.im) * (a.re * b.im) = (a.re * a.re) * (b.im * b.im) := hc1 _ _ _ _
  have he4 : (a.im * b.re) * (a.im * b.re) = (a.im * a.im) * (b.re * b.re) := hc1 _ _ _ _
  have he5 : (a.re * b.im) * (a.im * b.re) = (a.re * b.re) * (a.im * b.im) := by
    rw [hc1, Int.mul_comm b.im b.re, ← hc1]
  omega

private lemma z2_norm_star (a : Z2) : Z2.norm (z2_star a) = Z2.norm a := by
  simp only [Z2.norm, z2_star, Int.neg_mul_neg]

private lemma z2_norm_neg (a : Z2) : Z2.norm (z2_neg a) = Z2.norm a := by
  simp only [Z2.norm, z2_neg, Int.neg_mul_neg]

private lemma z2_mul_star (a : Z2) : z2_mul a (z2_star a) = z2_ofInt (Z2.norm a) := by
  rw [z2_eq_iff]
  simp only [z2_mul, z2_star, z2_ofInt, Z2.norm, Int.mul_neg]
  exact ⟨by omega, by rw [Int.mul_comm a.im a.re]; omega⟩

private lemma z2_star_mul (a b : Z2) : z2_star (z2_mul a b) = z2_mul (z2_star a) (z2_star b) := by
  rw [z2_eq_iff]
  simp only [z2_star, z2_mul, Int.mul_neg, Int.neg_mul, Int.neg_neg]
  exact ⟨trivial, by omega⟩

private lemma z2_star_star (a : Z2) : z2_star (z2_star a) = a := by
  rw [z2_eq_iff]
  simp [z2_star]

private lemma z2_star_neg (a : Z2) : z2_star (z2_neg a) = z2_neg (z2_star a) := by
  rw [z2_eq_iff]
  simp [z2_star, z2_neg]

private lemma z2_dvd_trans {a b c : Z2} (h1 : z2_dvd a b) (h2 : z2_dvd b c) : z2_dvd a c := by
  obtain ⟨x, rfl⟩ := h1
  obtain ⟨y, rfl⟩ := h2
  exact ⟨z2_mul x y, z2_mul_assoc a x y⟩

private lemma z2_dvd_sub {a b c : Z2} (h1 : z2_dvd a b) (h2 : z2_dvd a c) :
    z2_dvd a (z2_sub b c) := by
  obtain ⟨x, rfl⟩ := h1
  obtain ⟨y, rfl⟩ := h2
  refine ⟨z2_sub x y, ?_⟩
  rw [z2_eq_iff]
  simp only [z2_sub, z2_mul, Int.mul_sub]
  exact ⟨by omega, by omega⟩

private lemma z2_dvd_mul_right {a b c : Z2} (h : z2_dvd a b) : z2_dvd a (z2_mul b c) := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨z2_mul x c, z2_mul_assoc a x c⟩

private lemma z2_unit_inv {u : Z2} (hu : z2_unit u) :
    ∃ v : Z2, z2_unit v ∧ z2_mul u v = z2_ofInt 1 := by
  have h1 : u.norm = 1 ∨ u.norm = -1 := by
    have := hu
    dsimp [z2_unit] at this
    omega
  rcases h1 with hp | hn
  · refine ⟨z2_star u, ?_, ?_⟩
    · dsimp [z2_unit]
      rw [z2_norm_star, hp]
      decide
    · rw [z2_mul_star, hp]
  · refine ⟨z2_neg (z2_star u), ?_, ?_⟩
    · dsimp [z2_unit]
      rw [z2_norm_neg, z2_norm_star, hn]
      decide
    · rw [z2_eq_iff]
      have hm := congr_arg Z2.re (z2_mul_star u)
      have hi := congr_arg Z2.im (z2_mul_star u)
      simp only [z2_mul, z2_star, z2_neg, z2_ofInt, Int.mul_neg, Int.neg_neg,
        hn] at hm hi ⊢
      exact ⟨by omega, by omega⟩

private lemma z2_assoc_refl (a : Z2) : z2_assoc a a :=
  ⟨z2_ofInt 1, rfl, z2_mul_one a⟩

private lemma z2_assoc_trans {a b c : Z2} (h1 : z2_assoc a b) (h2 : z2_assoc b c) :
    z2_assoc a c := by
  obtain ⟨u, hu, rfl⟩ := h1
  obtain ⟨v, hv, rfl⟩ := h2
  refine ⟨z2_mul u v, ?_, (z2_mul_assoc a u v).symm⟩
  dsimp [z2_unit] at hu hv ⊢
  rw [z2_norm_mul, Int.natAbs_mul, hu, hv]

private lemma z2_norm_eq_zero (a : Z2) : Z2.norm a = 0 ↔ a = ⟨0, 0⟩ := by
  constructor
  · intro h
    dsimp [Z2.norm] at h
    have hsq : a.re * a.re = 2 * (a.im * a.im) := by omega
    have hboth : a.re.natAbs = 0 ∧ a.im.natAbs = 0 := by
      suffices ∀ n : ℕ, ∀ x y : ℕ, y ≤ n → x * x = 2 * (y * y) → x = 0 ∧ y = 0 by
        refine this a.im.natAbs a.re.natAbs a.im.natAbs (le_refl _) ?_
        have hr := int_natAbs_sq a.re
        have hi := int_natAbs_sq a.im
        have hz : ((a.re.natAbs * a.re.natAbs : ℕ) : ℤ) =
            ((2 * (a.im.natAbs * a.im.natAbs) : ℕ) : ℤ) := by
          push_cast
          rw [hr, hi, hsq]
        exact_mod_cast hz
      intro n
      induction n using Nat.strongRecOn with
      | ind n ih =>
        intro x y hyn hxy
        by_cases hy0 : y = 0
        · rw [hy0] at hxy
          have hx0 : x = 0 := by
            by_contra hx
            have : 1 ≤ x * x := Nat.mul_pos (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hx)
            omega
          exact ⟨hx0, hy0⟩
        · have hx_even : x % 2 = 0 := by
            by_contra hx_odd
            have : x = 2 * (x / 2) + 1 := by omega
            rw [this] at hxy
            have hexp : (2 * (x / 2) + 1) * (2 * (x / 2) + 1) =
                4 * ((x / 2) * (x / 2) + (x / 2)) + 1 := by
              rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul]
              have h4 : (2 * (x / 2)) * (2 * (x / 2)) = 4 * ((x / 2) * (x / 2)) := by
                rw [Nat.mul_assoc, Nat.mul_comm (x / 2) (2 * (x / 2)), Nat.mul_assoc]
                omega
              omega
            omega
          have hx2 : x = 2 * (x / 2) := by omega
          rw [hx2] at hxy
          have hy_sq : y * y = 2 * ((x / 2) * (x / 2)) := by
            have : 2 * (x / 2) * (2 * (x / 2)) = 4 * ((x / 2) * (x / 2)) := by
              rw [Nat.mul_assoc, Nat.mul_comm (x / 2) (2 * (x / 2)), Nat.mul_assoc]
              omega
            omega
          have hy_pos : 0 < y := Nat.pos_of_ne_zero hy0
          have hx_gt : x / 2 < y := by
            by_contra hle
            have h1 : y ≤ x / 2 := by omega
            have h2 : y * y ≤ (x / 2) * (x / 2) := Nat.mul_le_mul h1 h1
            have h3 : 1 ≤ y * y := Nat.mul_pos hy_pos hy_pos
            omega
          have hsub := ih (x / 2) (Nat.lt_of_lt_of_le hx_gt hyn) y (x / 2) (le_refl _) hy_sq
          omega
    rw [z2_eq_iff]
    dsimp
    omega
  · rintro rfl
    rfl

private lemma z2_mul_left_cancel {a b c : Z2} (ha : a ≠ ⟨0, 0⟩)
    (h : z2_mul a b = z2_mul a c) : b = c := by
  have hsub : z2_mul a (z2_sub b c) = ⟨0, 0⟩ := by
    rw [z2_eq_iff]
    have hre := congr_arg Z2.re h
    have him := congr_arg Z2.im h
    simp only [z2_mul, z2_sub, Int.mul_sub] at hre him ⊢
    exact ⟨by omega, by omega⟩
  have hnm : Z2.norm a * Z2.norm (z2_sub b c) = 0 := by
    rw [← z2_norm_mul, hsub]
    rfl
  have hna : Z2.norm a ≠ 0 := fun hz => ha ((z2_norm_eq_zero a).mp hz)
  have hnbc : Z2.norm (z2_sub b c) = 0 := by
    rcases Int.mul_eq_zero.mp hnm with h1 | h2
    · exact absurd h1 hna
    · exact h2
  have hbc0 := (z2_norm_eq_zero (z2_sub b c)).mp hnbc
  rw [z2_eq_iff] at hbc0 ⊢
  simp only [z2_sub] at hbc0
  omega

private lemma z2_mul_right_cancel {a b c : Z2} (hc : c ≠ ⟨0, 0⟩)
    (h : z2_mul a c = z2_mul b c) : a = b := by
  rw [z2_mul_comm a c, z2_mul_comm b c] at h
  exact z2_mul_left_cancel hc h

private lemma z2_intCast_dvd (z : ℤ) (a : Z2) :
    z2_dvd (z2_ofInt z) a → z ∣ a.re ∧ z ∣ a.im := by
  rintro ⟨c, hc⟩
  have hre := congr_arg Z2.re hc
  have him := congr_arg Z2.im hc
  simp only [z2_mul, z2_ofInt, Int.zero_mul, Int.mul_zero, Int.add_zero] at hre him
  exact ⟨⟨c.re, hre⟩, ⟨c.im, him⟩⟩

private lemma int_round (x n : ℤ) (hn : n ≠ 0) :
    ∃ q : ℤ, 2 * iabs (x - q * n) ≤ iabs n := by
  set m := iabs n
  have hm : 0 < m := by
    by_cases h0 : 0 ≤ n
    · dsimp [m]; rw [iabs_of_nonneg h0]; omega
    · dsimp [m]; rw [iabs_of_neg (by omega)]; omega
  have hdiv : m * (x / m) + x % m = x := Int.mul_ediv_add_emod x m
  have h0 : 0 ≤ x % m := Int.emod_nonneg x (by omega)
  have h1 : x % m < m := Int.emod_lt_of_pos x hm
  have hex : ∃ q' : ℤ, 2 * iabs (x - q' * m) ≤ m := by
    by_cases hc : 2 * (x % m) ≤ m
    · refine ⟨x / m, ?_⟩
      have heq : x - (x / m) * m = x % m := by
        rw [Int.mul_comm]
        omega
      rw [heq, iabs_of_nonneg h0]
      exact hc
    · refine ⟨x / m + 1, ?_⟩
      have heq : x - (x / m + 1) * m = x % m - m := by
        rw [Int.add_mul, Int.one_mul, Int.mul_comm (x / m) m]
        omega
      rw [heq, iabs_of_neg (by omega)]
      omega
  obtain ⟨q', hq'⟩ := hex
  by_cases hn0 : 0 ≤ n
  · refine ⟨q', ?_⟩
    simpa only [m, iabs_of_nonneg hn0] using hq'
  · refine ⟨-q', ?_⟩
    have hm_eq : m = -n := iabs_of_neg (by omega)
    have hmul : (-q') * n = q' * m := by
      rw [hm_eq, Int.neg_mul, Int.mul_neg]
    rw [hmul]
    exact hq'

private lemma z2_div (a b : Z2) (hb : b ≠ ⟨0, 0⟩) :
    ∃ q r : Z2, a = z2_add (z2_mul q b) r ∧ r.norm.natAbs < b.norm.natAbs := by
  have hbn : b.norm ≠ 0 := fun h => hb ((z2_norm_eq_zero b).mp h)
  set w := z2_mul a (z2_star b)
  obtain ⟨q1, hq1⟩ := int_round w.re b.norm hbn
  obtain ⟨q2, hq2⟩ := int_round w.im b.norm hbn
  set q : Z2 := ⟨q1, q2⟩
  set r : Z2 := z2_sub a (z2_mul q b)
  refine ⟨q, r, ?_, ?_⟩
  · rw [z2_eq_iff]
    simp only [z2_add, r, z2_sub]
    exact ⟨by omega, by omega⟩
  · have hz2_sub_mul : ∀ x y z : Z2,
        z2_mul (z2_sub x y) z = z2_sub (z2_mul x z) (z2_mul y z) := by
      intro x y z
      rw [z2_eq_iff]
      simp only [z2_sub, z2_mul, Int.sub_mul]
      exact ⟨by omega, by omega⟩
    have hrw : z2_mul r (z2_star b) = z2_sub w (z2_mul q (z2_ofInt b.norm)) := by
      calc z2_mul r (z2_star b)
        _ = z2_sub (z2_mul a (z2_star b)) (z2_mul (z2_mul q b) (z2_star b)) := hz2_sub_mul _ _ _
        _ = z2_sub w (z2_mul q (z2_ofInt b.norm)) := by rw [z2_mul_assoc, z2_mul_star]
    set u := (z2_mul r (z2_star b)).re
    set v := (z2_mul r (z2_star b)).im
    have hu_eq : u = w.re - q1 * b.norm := by
      have hre := congr_arg Z2.re hrw
      simp only [z2_sub, z2_mul, z2_ofInt, Int.mul_zero, Int.add_zero] at hre
      exact hre
    have hv_eq : v = w.im - q2 * b.norm := by
      have him := congr_arg Z2.im hrw
      simp only [z2_sub, z2_mul, z2_ofInt, Int.mul_zero, Int.zero_add] at him
      exact him
    have hu2 : 2 * iabs u ≤ iabs b.norm := hu_eq ▸ hq1
    have hv2 : 2 * iabs v ≤ iabs b.norm := hv_eq ▸ hq2
    have hnorm_mul : r.norm * b.norm = u * u - 2 * (v * v) := by
      calc r.norm * b.norm = r.norm * (z2_star b).norm := by rw [z2_norm_star]
        _ = (z2_mul r (z2_star b)).norm := (z2_norm_mul r (z2_star b)).symm
        _ = u * u - 2 * (v * v) := rfl
    have hu_sq : 4 * (u * u) ≤ b.norm * b.norm := by
      have h := int_sq_le (iabs_nonneg u |> fun h => by omega) hu2
      rw [int_two_mul_sq, iabs_sq, iabs_sq] at h
      exact h
    have hv_sq : 4 * (2 * (v * v)) ≤ 2 * (b.norm * b.norm) := by
      have h := int_sq_le (iabs_nonneg v |> fun h => by omega) hv2
      rw [int_two_mul_sq, iabs_sq, iabs_sq] at h
      omega
    have hu0 : 0 ≤ u * u := by
      rw [← iabs_sq u]
      exact Int.mul_nonneg (iabs_nonneg u) (iabs_nonneg u)
    have hv0 : 0 ≤ v * v := by
      rw [← iabs_sq v]
      exact Int.mul_nonneg (iabs_nonneg v) (iabs_nonneg v)
    have habs_le : 4 * iabs (r.norm * b.norm) ≤ 2 * (b.norm * b.norm) := by
      rw [hnorm_mul]
      by_cases hsign : 0 ≤ u * u - 2 * (v * v)
      · rw [iabs_of_nonneg hsign]
        omega
      · rw [iabs_of_neg (by omega)]
        omega
    have habs_bn : 0 < iabs b.norm := by
      by_cases h0 : 0 ≤ b.norm
      · rw [iabs_of_nonneg h0]; omega
      · rw [iabs_of_neg (by omega)]; omega
    rw [iabs_mul, ← iabs_sq b.norm] at habs_le
    have hlt_abs : iabs r.norm < iabs b.norm := by
      by_contra hle
      have h1 : iabs b.norm ≤ iabs r.norm := by omega
      have h2 : 2 * (iabs b.norm * iabs b.norm) < 4 * (iabs r.norm * iabs b.norm) := by
        have hmul := Int.mul_le_mul_of_nonneg_right h1 habs_bn.le
        have hpos : 0 < iabs b.norm * iabs b.norm := Int.mul_pos habs_bn habs_bn
        omega
      omega
    have hcr := int_natAbs_eq_iabs r.norm
    have hcb := int_natAbs_eq_iabs b.norm
    omega

-- Prime factor in Z[sqrt(2)]

private lemma nat_dvd_prime_sq {d p : ℕ} (hp : Nat.Prime p) (hd : d ∣ p * p) :
    d = 1 ∨ d = p ∨ d = p * p := by
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  · obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd1
    have hqpp : q ∣ p * p := Nat.dvd_trans hqd hd
    have hqp : q ∣ p := by
      rcases hq.dvd_mul.mp hqpp with h | h <;> exact h
    have hq_eq : q = p := by
      rcases (Nat.dvd_prime hp).mp hqp with h1 | h2
      · exact absurd h1 hq.ne_one
      · exact h2
    rw [hq_eq] at hqd
    obtain ⟨c, hc⟩ := hqd
    have hcp : c ∣ p := by
      rw [hc] at hd
      obtain ⟨k, hk⟩ := hd
      refine ⟨k, ?_⟩
      have hpp : p * p = p * (c * k) := by rw [hk, Nat.mul_assoc]
      exact Nat.mul_left_cancel hp.pos hpp
    rcases (Nat.dvd_prime hp).mp hcp with hc1 | hcp'
    · right; left; rw [hc, hc1, Nat.mul_one]
    · right; right; rw [hc, hcp']

private lemma exists_prime_factor_z2 (m p : ℕ) (hm : 2 < m) (hp : Nat.Prime p) (hp2 : 2 < p)
    (hpN : p ∣ (2 * m + 1) ^ 2 - 8) :
    ∃ pi : Z2, pi.norm = (p : ℤ) ∧ z2_dvd pi ⟨2 * (m : ℤ) + 1, 2⟩ := by
  set N : ℕ := (2 * m + 1) ^ 2 - 8
  have hNz := N_cast m hm
  set α : Z2 := ⟨2 * (m : ℤ) + 1, 2⟩
  have hα_norm : α.norm = (N : ℤ) := by
    dsimp [α, Z2.norm]
    omega
  set pz : Z2 := z2_ofInt (p : ℤ)
  have hpz_ne : pz ≠ ⟨0, 0⟩ := by
    intro h
    have := congr_arg Z2.re h
    simp [pz, z2_ofInt] at this
    omega
  let S : ℕ → Prop := fun n =>
    ∃ u v : Z2, z2_add (z2_mul u pz) (z2_mul v α) ≠ ⟨0, 0⟩ ∧
      (z2_add (z2_mul u pz) (z2_mul v α)).norm.natAbs = n
  have hS_ne : ∃ n, S n := by
    refine ⟨pz.norm.natAbs, z2_ofInt 1, z2_ofInt 0, ?_, ?_⟩
    · rw [z2_one_mul]
      have h0 : z2_mul (z2_ofInt 0) α = ⟨0, 0⟩ := by
        rw [z2_eq_iff]; simp [z2_mul, z2_ofInt]
      rw [h0]
      intro h
      apply hpz_ne
      rw [z2_eq_iff] at h ⊢
      simp [z2_add] at h
      exact h
    · have h0 : z2_mul (z2_ofInt 0) α = ⟨0, 0⟩ := by
        rw [z2_eq_iff]; simp [z2_mul, z2_ofInt]
      rw [z2_one_mul, h0]
      have hadd : z2_add pz ⟨0, 0⟩ = pz := by rw [z2_eq_iff]; simp [z2_add]
      rw [hadd]
  obtain ⟨n₀, ⟨u₀, v₀, hg_ne, hg_norm⟩, hn₀_min⟩ := nat_exists_min S hS_ne
  set g := z2_add (z2_mul u₀ pz) (z2_mul v₀ α)
  have hg_dvd_p : z2_dvd g pz := by
    obtain ⟨q, r, hqr, hr_lt⟩ := z2_div pz g hg_ne
    have hr_eq : r = z2_add (z2_mul (z2_sub (z2_ofInt 1) (z2_mul q u₀)) pz)
        (z2_mul (z2_neg (z2_mul q v₀)) α) := by
      have h1 : z2_mul q g = z2_add (z2_mul (z2_mul q u₀) pz) (z2_mul (z2_mul q v₀) α) := by
        dsimp [g]
        rw [z2_mul_add, ← z2_mul_assoc q u₀ pz, ← z2_mul_assoc q v₀ α]
      have hm1 : z2_mul (z2_sub (z2_ofInt 1) (z2_mul q u₀)) pz =
          z2_sub pz (z2_mul (z2_mul q u₀) pz) := by
        rw [z2_eq_iff]
        simp only [z2_mul, z2_sub, z2_ofInt, Int.sub_mul]
        exact ⟨by omega, by omega⟩
      have hm2 : z2_mul (z2_neg (z2_mul q v₀)) α = z2_neg (z2_mul (z2_mul q v₀) α) := by
        rw [z2_eq_iff]
        simp only [z2_mul, z2_neg, Int.neg_mul]
        exact ⟨by omega, by omega⟩
      rw [hm1, hm2, z2_eq_iff]
      have hre := congr_arg Z2.re hqr
      have him := congr_arg Z2.im hqr
      have h1re := congr_arg Z2.re h1
      have h1im := congr_arg Z2.im h1
      simp only [z2_add, z2_sub, z2_neg] at hre him h1re h1im ⊢
      exact ⟨by omega, by omega⟩
    by_cases hr0 : r = ⟨0, 0⟩
    · rw [hr0] at hqr
      refine ⟨q, ?_⟩
      rw [z2_mul_comm g q]
      rw [z2_eq_iff] at hqr ⊢
      simp [z2_add] at hqr
      exact hqr
    · exfalso
      have hSn : S r.norm.natAbs := ⟨z2_sub (z2_ofInt 1) (z2_mul q u₀),
        z2_neg (z2_mul q v₀), hr_eq ▸ hr0, by rw [← hr_eq]⟩
      have hle := hn₀_min r.norm.natAbs hSn
      omega
  have hg_dvd_α : z2_dvd g α := by
    obtain ⟨q, r, hqr, hr_lt⟩ := z2_div α g hg_ne
    have hr_eq : r = z2_add (z2_mul (z2_neg (z2_mul q u₀)) pz)
        (z2_mul (z2_sub (z2_ofInt 1) (z2_mul q v₀)) α) := by
      have h1 : z2_mul q g = z2_add (z2_mul (z2_mul q u₀) pz) (z2_mul (z2_mul q v₀) α) := by
        dsimp [g]
        rw [z2_mul_add, ← z2_mul_assoc q u₀ pz, ← z2_mul_assoc q v₀ α]
      have hm1 : z2_mul (z2_neg (z2_mul q u₀)) pz = z2_neg (z2_mul (z2_mul q u₀) pz) := by
        rw [z2_eq_iff]
        simp only [z2_mul, z2_neg, Int.neg_mul]
        exact ⟨by omega, by omega⟩
      have hm2 : z2_mul (z2_sub (z2_ofInt 1) (z2_mul q v₀)) α =
          z2_sub α (z2_mul (z2_mul q v₀) α) := by
        rw [z2_eq_iff]
        simp only [z2_mul, z2_sub, z2_ofInt, Int.sub_mul]
        exact ⟨by omega, by omega⟩
      rw [hm1, hm2, z2_eq_iff]
      have hre := congr_arg Z2.re hqr
      have him := congr_arg Z2.im hqr
      have h1re := congr_arg Z2.re h1
      have h1im := congr_arg Z2.im h1
      simp only [z2_add, z2_sub, z2_neg] at hre him h1re h1im ⊢
      exact ⟨by omega, by omega⟩
    by_cases hr0 : r = ⟨0, 0⟩
    · rw [hr0] at hqr
      refine ⟨q, ?_⟩
      rw [z2_mul_comm g q]
      rw [z2_eq_iff] at hqr ⊢
      simp [z2_add] at hqr
      exact hqr
    · exfalso
      have hSn : S r.norm.natAbs := ⟨z2_neg (z2_mul q u₀),
        z2_sub (z2_ofInt 1) (z2_mul q v₀), hr_eq ▸ hr0, by rw [← hr_eq]⟩
      have hle := hn₀_min r.norm.natAbs hSn
      omega
  obtain ⟨qp, hqp⟩ := hg_dvd_p
  have hpna : pz.norm.natAbs = p * p := by
    simp only [pz, Z2.norm, z2_ofInt, Int.mul_zero, Int.sub_zero]
    have : ((p * p : ℕ) : ℤ) = (p : ℤ) * (p : ℤ) := by push_cast; rfl
    rw [← this, Int.natAbs_natCast]
  have hmul_na : p * p = g.norm.natAbs * qp.norm.natAbs := by
    have h1 := congr_arg (fun z : Z2 => z.norm.natAbs) hqp
    rw [z2_norm_mul, Int.natAbs_mul, hpna] at h1
    exact h1
  have hdvd_p2 : g.norm.natAbs ∣ p * p := ⟨qp.norm.natAbs, hmul_na⟩
  have hg_na_p : g.norm.natAbs = p := by
    rcases nat_dvd_prime_sq hp hdvd_p2 with hg1 | hgp | hgpp
    · exfalso
      obtain ⟨ginv, _, hginv⟩ := z2_unit_inv (show z2_unit g from hg1)
      have h1_comb : z2_ofInt 1 = z2_add (z2_mul (z2_mul ginv u₀) pz)
          (z2_mul (z2_mul ginv v₀) α) := by
        rw [← hginv, z2_mul_comm g ginv]
        dsimp [g]
        rw [z2_mul_add, ← z2_mul_assoc ginv u₀ pz, ← z2_mul_assoc ginv v₀ α]
      obtain ⟨k, hk⟩ := hpN
      have hα_mul_star : z2_mul α (z2_star α) = z2_mul pz (z2_ofInt (k : ℤ)) := by
        rw [z2_mul_star, hα_norm, hk]
        rw [z2_eq_iff]
        simp [pz, z2_mul, z2_ofInt]
      have hp_dvd_star : z2_dvd pz (z2_star α) := by
        refine ⟨z2_add (z2_mul (z2_mul ginv u₀) (z2_star α))
            (z2_mul (z2_mul ginv v₀) (z2_ofInt (k : ℤ))), ?_⟩
        calc z2_star α = z2_mul (z2_ofInt 1) (z2_star α) := (z2_one_mul _).symm
          _ = z2_mul (z2_add (z2_mul (z2_mul ginv u₀) pz) (z2_mul (z2_mul ginv v₀) α))
                (z2_star α) := by rw [h1_comb]
          _ = z2_add (z2_mul (z2_mul (z2_mul ginv u₀) pz) (z2_star α))
                (z2_mul (z2_mul (z2_mul ginv v₀) α) (z2_star α)) := z2_add_mul _ _ _
          _ = z2_add (z2_mul pz (z2_mul (z2_mul ginv u₀) (z2_star α)))
                (z2_mul pz (z2_mul (z2_mul ginv v₀) (z2_ofInt (k : ℤ)))) := by
                have ha : z2_mul (z2_mul (z2_mul ginv u₀) pz) (z2_star α) =
                    z2_mul pz (z2_mul (z2_mul ginv u₀) (z2_star α)) := by
                  rw [z2_mul_comm (z2_mul ginv u₀) pz, z2_mul_assoc pz (z2_mul ginv u₀) (z2_star α)]
                have hb : z2_mul (z2_mul (z2_mul ginv v₀) α) (z2_star α) =
                    z2_mul pz (z2_mul (z2_mul ginv v₀) (z2_ofInt (k : ℤ))) := by
                  rw [z2_mul_assoc, hα_mul_star, ← z2_mul_assoc,
                    z2_mul_comm (z2_mul ginv v₀) pz, z2_mul_assoc]
                rw [ha, hb]
          _ = z2_mul pz (z2_add (z2_mul (z2_mul ginv u₀) (z2_star α))
                (z2_mul (z2_mul ginv v₀) (z2_ofInt (k : ℤ)))) := (z2_mul_add _ _ _).symm
      have him := (z2_intCast_dvd (p : ℤ) (z2_star α) hp_dvd_star).2
      have him_eq : (z2_star α).im = -2 := rfl
      rw [him_eq] at him
      have hp_dvd_2 : p ∣ 2 := by
        have h2 : (p : ℤ) ∣ (2 : ℤ) := Int.dvd_neg.mp him
        exact_mod_cast h2
      exact absurd (Nat.le_of_dvd (by omega) hp_dvd_2) (Nat.not_le_of_gt hp2)
    · exact hgp
    · exfalso
      have hqp1 : qp.norm.natAbs = 1 := by
        rw [hgpp] at hmul_na
        have hpp : 0 < p * p := Nat.mul_pos hp.pos hp.pos
        exact Nat.mul_left_cancel hpp (by omega)
      obtain ⟨qinv, _, hqinv⟩ := z2_unit_inv (show z2_unit qp from hqp1)
      have hp_dvd_g : z2_dvd pz g := ⟨qinv, by
        calc g = z2_mul g (z2_ofInt 1) := (z2_mul_one g).symm
          _ = z2_mul g (z2_mul qp qinv) := by rw [hqinv]
          _ = z2_mul (z2_mul g qp) qinv := (z2_mul_assoc g qp qinv).symm
          _ = z2_mul pz qinv := by rw [← hqp]⟩
      have hp_dvd_α : z2_dvd pz α := z2_dvd_trans hp_dvd_g hg_dvd_α
      have him := (z2_intCast_dvd (p : ℤ) α hp_dvd_α).2
      have him_eq : α.im = 2 := rfl
      rw [him_eq] at him
      have hp_dvd_2 : p ∣ 2 := by exact_mod_cast him
      exact absurd (Nat.le_of_dvd (by omega) hp_dvd_2) (Nat.not_le_of_gt hp2)
  rcases Int.natAbs_eq g.norm with hpos | hneg
  · exact ⟨g, by rw [hpos, hg_na_p], hg_dvd_α⟩
  · set e : Z2 := ⟨1, 1⟩
    set e_inv : Z2 := ⟨-1, 1⟩
    have hee : z2_mul e e_inv = z2_ofInt 1 := by
      rw [z2_eq_iff]; simp [e, e_inv, z2_mul, z2_ofInt]
    have he_norm : e.norm = -1 := rfl
    refine ⟨z2_mul g e, ?_, ?_⟩
    · rw [z2_norm_mul, he_norm, show g.norm = -(p : ℤ) from by omega]
      omega
    · obtain ⟨w, hw⟩ := hg_dvd_α
      refine ⟨z2_mul e_inv w, ?_⟩
      calc α = z2_mul g w := hw
        _ = z2_mul g (z2_mul (z2_ofInt 1) w) := by rw [z2_one_mul]
        _ = z2_mul g (z2_mul (z2_mul e e_inv) w) := by rw [hee]
        _ = z2_mul (z2_mul g e) (z2_mul e_inv w) := by rw [z2_mul_assoc, z2_mul_assoc]

-- Backward direction: N composite -> exists square in range

private lemma backward_dir (m : ℕ) (hm : 2 < m) (hnot : ¬ Nat.Prime ((2 * m + 1) ^ 2 - 8)) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ 2 * (m - 2) ∧ IsSquare (q * (m + 1) + q.choose 2 + 1) := by
  set N : ℕ := (2 * m + 1) ^ 2 - 8
  have hNz := N_cast m hm
  have hN_gt1 : 1 < N := by
    have h1 : 7 ≤ 2 * m + 1 := by omega
    have h2 : 49 ≤ (2 * m + 1) ^ 2 := by
      rw [Nat.pow_two]
      exact Nat.mul_le_mul h1 h1
    omega
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd hN_gt1.ne'
  have hp_lt : p < N :=
    Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hpN) (fun h => hnot (h ▸ hp))
  have hN_odd : N % 2 = 1 := by
    have hsq : (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 := by
      rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      have h4 : (2 * m) * (2 * m) = 4 * (m * m) := by
        rw [Nat.mul_assoc, Nat.mul_comm m (2 * m), Nat.mul_assoc]
        omega
      omega
    omega
  have hp_ne2 : p ≠ 2 := by
    intro h
    rw [h] at hpN
    obtain ⟨t, ht⟩ := hpN
    omega
  have hp2 : 2 < p := Nat.lt_of_le_of_ne hp.two_le hp_ne2.symm
  set r : ℕ := N / p
  have hpr : p * r = N := Nat.mul_div_cancel' hpN
  have hr_gt1 : 1 < r := by
    by_contra hr_le
    have hr1 : r ≤ 1 := by omega
    have hle : p * r ≤ p * 1 := Nat.mul_le_mul_left p hr1
    omega
  have hr_odd : r % 2 = 1 := by
    by_contra hr_even
    have hr0 : r % 2 = 0 := by omega
    have hr2 : r = 2 * (r / 2) := by omega
    have hmod : (p * (2 * (r / 2))) % 2 = 0 := by
      have : p * (2 * (r / 2)) = 2 * (p * (r / 2)) := Nat.mul_left_comm p 2 (r / 2)
      omega
    rw [← hr2, hpr] at hmod
    omega
  obtain ⟨pi, hpi_norm, rho, hrho_eq⟩ := exists_prime_factor_z2 m p hm hp hp2 hpN
  set α : Z2 := ⟨2 * (m : ℤ) + 1, 2⟩
  have hα_norm : α.norm = (N : ℤ) := by
    dsimp [α, Z2.norm]
    omega
  have hrho_norm : rho.norm = (r : ℤ) := by
    have h := congr_arg Z2.norm hrho_eq
    rw [z2_norm_mul, hpi_norm, hα_norm, ← hpr] at h
    push_cast at h
    exact Int.eq_of_mul_eq_mul_left (by omega : (p : ℤ) ≠ 0) h.symm
  have hpi_ne : pi ≠ ⟨0, 0⟩ := fun h => by
    rw [h] at hpi_norm; simp [Z2.norm] at hpi_norm; omega
  have hstar_pi_ne : z2_star pi ≠ ⟨0, 0⟩ := fun h =>
    hpi_ne (by rw [← z2_star_star pi, h]; rfl)
  have hrho_ne : rho ≠ ⟨0, 0⟩ := fun h => by
    rw [h] at hrho_norm; simp [Z2.norm] at hrho_norm; omega
  set β : Z2 := z2_mul (z2_star pi) rho
  have hβ_norm : β.norm = (N : ℤ) := by
    rw [z2_norm_mul, z2_norm_star, hpi_norm, hrho_norm, ← hpr]
    push_cast
    rfl
  have hβ_im : (2 : ℤ) ∣ β.im := by
    have him := congr_arg Z2.im hrho_eq
    simp only [α, z2_mul] at him
    refine ⟨1 - pi.im * rho.re, ?_⟩
    simp only [β, z2_mul, z2_star, Int.neg_mul]
    omega
  have hdiff_star : z2_sub α (z2_star α) = ⟨0, 4⟩ := by
    rw [z2_eq_iff]; simp [z2_sub, z2_star, α]
  have hdiff_norm : (⟨0, 4⟩ : Z2).norm.natAbs = 32 := rfl
  have h_not_assoc1 : ¬ z2_assoc β α := by
    rintro ⟨u, hu, hbu⟩
    have h1 : z2_mul (z2_mul (z2_star pi) u) rho = z2_mul pi rho := by
      rw [z2_mul_assoc, z2_mul_comm u rho, ← z2_mul_assoc]
      exact hbu.trans hrho_eq
    have h2 : z2_mul (z2_star pi) u = pi := z2_mul_right_cancel hrho_ne h1
    obtain ⟨uinv, _, huinv⟩ := z2_unit_inv hu
    have hpi_star : z2_dvd pi (z2_star pi) := ⟨uinv, by
      calc z2_star pi = z2_mul (z2_star pi) (z2_ofInt 1) := (z2_mul_one _).symm
        _ = z2_mul (z2_star pi) (z2_mul u uinv) := by rw [huinv]
        _ = z2_mul (z2_mul (z2_star pi) u) uinv := (z2_mul_assoc _ _ _).symm
        _ = z2_mul pi uinv := by rw [h2]⟩
    have hpi_α : z2_dvd pi α := ⟨rho, hrho_eq⟩
    have hpi_sα : z2_dvd pi (z2_star α) := by
      have hs : z2_star α = z2_mul (z2_star pi) (z2_star rho) := by
        rw [hrho_eq, z2_star_mul]
      rw [hs]
      exact z2_dvd_mul_right hpi_star
    have hpi_diff : z2_dvd pi ⟨0, 4⟩ := hdiff_star ▸ z2_dvd_sub hpi_α hpi_sα
    obtain ⟨w, hw⟩ := hpi_diff
    have hdvd32 : p ∣ 32 := by
      have hnm := congr_arg (fun z : Z2 => z.norm.natAbs) hw
      rw [z2_norm_mul, Int.natAbs_mul, hdiff_norm, hpi_norm, Int.natAbs_natCast] at hnm
      exact ⟨w.norm.natAbs, hnm⟩
    have hp_dvd2 : p ∣ 2 := by
      have h5 : p ∣ 2 * (2 * (2 * (2 * 2))) := hdvd32
      rcases hp.dvd_mul.mp h5 with h | h
      · exact h
      · rcases hp.dvd_mul.mp h with h | h
        · exact h
        · rcases hp.dvd_mul.mp h with h | h
          · exact h
          · rcases hp.dvd_mul.mp h with h | h <;> exact h
    exact absurd (Nat.le_of_dvd (by omega) hp_dvd2) (Nat.not_le_of_gt hp2)
  have h_not_assoc2 : ¬ z2_assoc β (z2_star α) := by
    rintro ⟨u, hu, hbu⟩
    have hs : z2_star α = z2_mul (z2_star pi) (z2_star rho) := by
      rw [hrho_eq, z2_star_mul]
    have h1 : z2_mul (z2_star pi) (z2_mul rho u) = z2_mul (z2_star pi) (z2_star rho) := by
      rw [← z2_mul_assoc]
      exact hbu.trans hs
    have h2 : z2_mul rho u = z2_star rho := z2_mul_left_cancel hstar_pi_ne h1
    have hrho_star : z2_dvd rho (z2_star rho) := ⟨u, h2.symm⟩
    have hrho_α : z2_dvd rho α := ⟨pi, by rw [hrho_eq, z2_mul_comm]⟩
    have hrho_sα : z2_dvd rho (z2_star α) := by
      rw [hs, z2_mul_comm]
      exact z2_dvd_mul_right hrho_star
    have hrho_diff : z2_dvd rho ⟨0, 4⟩ := hdiff_star ▸ z2_dvd_sub hrho_α hrho_sα
    obtain ⟨w, hw⟩ := hrho_diff
    have hdvd32 : r ∣ 32 := by
      have hnm := congr_arg (fun z : Z2 => z.norm.natAbs) hw
      rw [z2_norm_mul, Int.natAbs_mul, hdiff_norm, hrho_norm, Int.natAbs_natCast] at hnm
      exact ⟨w.norm.natAbs, hnm⟩
    obtain ⟨p', hp', hp'r⟩ := Nat.exists_prime_and_dvd hr_gt1.ne'
    have hp'32 : p' ∣ 32 := Nat.dvd_trans hp'r hdvd32
    have hp'2 : p' ∣ 2 := by
      have h5 : p' ∣ 2 * (2 * (2 * (2 * 2))) := hp'32
      rcases hp'.dvd_mul.mp h5 with h | h
      · exact h
      · rcases hp'.dvd_mul.mp h with h | h
        · exact h
        · rcases hp'.dvd_mul.mp h with h | h
          · exact h
          · rcases hp'.dvd_mul.mp h with h | h <;> exact h
    have hp'eq : p' = 2 := ((Nat.dvd_prime Nat.prime_two).mp hp'2).resolve_left hp'.ne_one
    rw [hp'eq] at hp'r
    obtain ⟨t, ht⟩ := hp'r
    omega
  let OrbitCond : Z2 → Prop := fun z =>
    (z2_assoc β z ∨ z2_assoc β (z2_star z)) ∧ z.norm = (N : ℤ) ∧ (2 : ℤ) ∣ z.im
  have hOrbit_neg : ∀ z, OrbitCond z → OrbitCond (z2_neg z) := by
    intro z ⟨ha, hn, him⟩
    refine ⟨?_, by rw [z2_norm_neg]; exact hn, ?_⟩
    · have hu_neg : z2_unit (z2_ofInt (-1)) := rfl
      have hz_neg : ∀ w : Z2, z2_assoc w (z2_neg w) := fun w =>
        ⟨z2_ofInt (-1), hu_neg, by rw [z2_eq_iff]; simp [z2_mul, z2_ofInt, z2_neg]⟩
      rcases ha with ha1 | ha2
      · exact Or.inl (z2_assoc_trans ha1 (hz_neg z))
      · refine Or.inr (z2_assoc_trans ha2 ?_)
        rw [z2_star_neg]
        exact hz_neg (z2_star z)
    · obtain ⟨t, ht⟩ := him
      exact ⟨-t, by dsimp [z2_neg]; rw [ht, Int.mul_neg]⟩
  have hOrbit_star : ∀ z, OrbitCond z → OrbitCond (z2_star z) := by
    intro z ⟨ha, hn, him⟩
    refine ⟨?_, by rw [z2_norm_star]; exact hn, ?_⟩
    · rcases ha with ha1 | ha2
      · exact Or.inr (by rw [z2_star_star]; exact ha1)
      · exact Or.inl ha2
    · obtain ⟨t, ht⟩ := him
      exact ⟨-t, by dsimp [z2_star]; rw [ht, Int.mul_neg]⟩
  let u_inv : Z2 := ⟨3, -2⟩
  let u_fwd : Z2 := ⟨3, 2⟩
  have hu_inv : z2_unit u_inv := rfl
  have hu_fwd : z2_unit u_fwd := rfl
  have hOrbit_mul : ∀ z, OrbitCond z → OrbitCond (z2_mul z u_inv) := by
    intro z ⟨ha, hn, him⟩
    refine ⟨?_, ?_, ?_⟩
    · rcases ha with ha1 | ha2
      · exact Or.inl (z2_assoc_trans ha1 ⟨u_inv, hu_inv, rfl⟩)
      · refine Or.inr (z2_assoc_trans ha2 ⟨u_fwd, hu_fwd, ?_⟩)
        rw [z2_star_mul]
        have hs : z2_star u_inv = u_fwd := by rw [z2_eq_iff]; simp [u_inv, u_fwd, z2_star]
        rw [hs]
    · rw [z2_norm_mul, hn, show u_inv.norm = 1 from rfl, Int.mul_one]
    · obtain ⟨t, ht⟩ := him
      refine ⟨-z.re + 3 * t, ?_⟩
      simp only [z2_mul, u_inv, ht]
      omega
  let P : ℕ → Prop := fun n => ∃ z : Z2, OrbitCond z ∧ z.re = (n : ℤ)
  have hP_ne : ∃ n, P n := by
    refine ⟨β.re.natAbs, ?_⟩
    by_cases h0 : 0 ≤ β.re
    · exact ⟨β, ⟨Or.inl (z2_assoc_refl β), hβ_norm, hβ_im⟩, (Int.natAbs_of_nonneg h0).symm⟩
    · refine ⟨z2_neg β, hOrbit_neg β ⟨Or.inl (z2_assoc_refl β), hβ_norm, hβ_im⟩, ?_⟩
      dsimp [z2_neg]
      have := Int.ofNat_natAbs_of_nonpos (show β.re ≤ 0 by omega)
      omega
  obtain ⟨n₁, ⟨z₀, hz₀_orb, hz₀_re⟩, hn₁_min⟩ := nat_exists_min P hP_ne
  set z₁ : Z2 := if 0 ≤ z₀.im then z₀ else z2_star z₀
  have hz₁_orb : OrbitCond z₁ := by
    dsimp [z₁]
    by_cases him0 : 0 ≤ z₀.im
    · rw [if_pos him0]; exact hz₀_orb
    · rw [if_neg him0]; exact hOrbit_star z₀ hz₀_orb
  have hz₁_re : z₁.re = (n₁ : ℤ) := by
    dsimp [z₁]
    by_cases him0 : 0 ≤ z₀.im
    · rw [if_pos him0]; exact hz₀_re
    · rw [if_neg him0]; exact hz₀_re
  have hz₁_im0 : 0 ≤ z₁.im := by
    dsimp [z₁]
    by_cases him0 : 0 ≤ z₀.im
    · rw [if_pos him0]; exact him0
    · rw [if_neg him0]; dsimp [z2_star]; omega
  obtain ⟨k, hk⟩ := hz₁_orb.2.2
  have hk0 : 0 ≤ k := by omega
  have hnorm_z1 : (n₁ : ℤ) * (n₁ : ℤ) - 8 * (k * k) = (N : ℤ) := by
    have h := hz₁_orb.2.1
    dsimp [Z2.norm] at h
    rw [hz₁_re, hk] at h
    have h8 : 2 * (2 * k * (2 * k)) = 8 * (k * k) := by
      rw [int_two_mul_sq]
      omega
    omega
  have hn₁_pos : 0 < n₁ := by
    by_contra h0
    have hn0 : n₁ = 0 := by omega
    rw [hn0] at hnorm_z1
    have hkk : 0 ≤ k * k := Int.mul_nonneg hk0 hk0
    omega
  set z' : Z2 := z2_mul z₁ u_inv
  have hz'_orb : OrbitCond z' := hOrbit_mul z₁ hz₁_orb
  have hz'_re : z'.re = 3 * (n₁ : ℤ) - 8 * k := by
    simp only [z', z2_mul, u_inv, hz₁_re, hk]
    omega
  have hP_z' : P z'.re.natAbs := by
    by_cases h0 : 0 ≤ z'.re
    · exact ⟨z', hz'_orb, (Int.natAbs_of_nonneg h0).symm⟩
    · refine ⟨z2_neg z', hOrbit_neg z' hz'_orb, ?_⟩
      dsimp [z2_neg]
      have := Int.ofNat_natAbs_of_nonpos (show z'.re ≤ 0 by omega)
      omega
  have hmin : n₁ ≤ z'.re.natAbs := hn₁_min z'.re.natAbs hP_z'
  have habs_min : (n₁ : ℤ) ≤ iabs (3 * (n₁ : ℤ) - 8 * k) := by
    have hcz := int_natAbs_eq_iabs z'.re
    rw [← hz'_re, ← hcz]
    exact_mod_cast hmin
  have hk_lt_n1 : 2 * k < (n₁ : ℤ) := by
    by_contra hle
    have h1 : (n₁ : ℤ) ≤ 2 * k := by omega
    have hsq := int_sq_le (by omega) h1
    have h4 : (2 * k) * (2 * k) = 4 * (k * k) := int_two_mul_sq k
    have hkk : 0 ≤ k * k := Int.mul_nonneg hk0 hk0
    omega
  have hn1_ge_4k : 4 * k ≤ (n₁ : ℤ) := by
    have hneg : -(n₁ : ℤ) < 3 * (n₁ : ℤ) - 8 * k := by omega
    by_cases hpos : 0 ≤ 3 * (n₁ : ℤ) - 8 * k
    · rw [iabs_of_nonneg hpos] at habs_min
      omega
    · rw [iabs_of_neg (by omega)] at habs_min
      omega
  have hn1_sq_ub : (n₁ : ℤ) * (n₁ : ℤ) ≤ 2 * (N : ℤ) := by
    have hsq := int_sq_le (by omega) hn1_ge_4k
    have h16 : (4 * k) * (4 * k) = 16 * (k * k) := by
      rw [Int.mul_assoc, Int.mul_comm k (4 * k), Int.mul_assoc]
      omega
    omega
  have hm_z : (3 : ℤ) ≤ (m : ℤ) := by omega
  have hn1_ub : (n₁ : ℤ) < 6 * (m : ℤ) - 7 := by
    set t : ℤ := (m : ℤ) - 3
    have ht0 : 0 ≤ t := by omega
    have htt : 0 ≤ t * t := Int.mul_nonneg ht0 ht0
    have hgap : (6 * (m : ℤ) - 7) * (6 * (m : ℤ) - 7) - 2 * (N : ℤ) =
        28 * (t * t) + 76 * t + 39 := by
      have hm_eq : (m : ℤ) = t + 3 := by omega
      rw [hNz, hm_eq]
      have hL : (6 * (t + 3) - 7) * (6 * (t + 3) - 7) =
          36 * (t * t) + 132 * t + 121 := by
        have h1 : 6 * (t + 3) - 7 = 6 * t + 11 := by omega
        rw [h1, int_linear_sq]
        have h36 : (6 * t) * (6 * t) = 36 * (t * t) := by
          rw [Int.mul_assoc, Int.mul_comm t (6 * t), Int.mul_assoc]
          omega
        omega
      have hR : (2 * (t + 3) + 1) * (2 * (t + 3) + 1) =
          4 * (t * t) + 28 * t + 49 := by
        have h1 : 2 * (t + 3) + 1 = 2 * t + 7 := by omega
        rw [h1, int_linear_sq, int_two_mul_sq]
        omega
      rw [hL, hR]
      omega
    have hsq_lt : (n₁ : ℤ) * (n₁ : ℤ) < (6 * (m : ℤ) - 7) * (6 * (m : ℤ) - 7) := by omega
    exact int_lt_of_sq_lt (by omega) hsq_lt
  have hk_ne0 : k ≠ 0 := by
    intro hk0'
    rw [hk0'] at hnorm_z1
    have hlb : (2 * (m : ℤ)) * (2 * (m : ℤ)) < (N : ℤ) := by
      have h1 : (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1) =
          4 * ((m : ℤ) * (m : ℤ)) + 4 * (m : ℤ) + 1 := by
        rw [int_linear_sq, int_two_mul_sq]
        omega
      have h2 : (2 * (m : ℤ)) * (2 * (m : ℤ)) = 4 * ((m : ℤ) * (m : ℤ)) := int_two_mul_sq (m : ℤ)
      omega
    have hub : (N : ℤ) < (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1) := by omega
    have h1 : 2 * (m : ℤ) < (n₁ : ℤ) := by
      by_contra hle
      have hsq := int_sq_le (by omega : 0 ≤ (n₁ : ℤ)) (by omega : (n₁ : ℤ) ≤ 2 * (m : ℤ))
      omega
    have h2 : (n₁ : ℤ) < 2 * (m : ℤ) + 1 :=
      int_lt_of_sq_lt (by omega) (by omega)
    omega
  have hk_ne1 : k ≠ 1 := by
    intro hk1
    rw [hk1] at hnorm_z1
    have hsq : (n₁ : ℤ) * (n₁ : ℤ) = (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1) := by omega
    have hle1 : (n₁ : ℤ) ≤ 2 * (m : ℤ) + 1 := int_le_of_sq_le (by omega) hsq.le
    have hle2 : 2 * (m : ℤ) + 1 ≤ (n₁ : ℤ) := int_le_of_sq_le (by omega) hsq.symm.le
    have hn1_eq : (n₁ : ℤ) = 2 * (m : ℤ) + 1 := by omega
    have hz1_eq : z₁ = α := by
      rw [z2_eq_iff]
      exact ⟨by rw [hz₁_re, hn1_eq], by rw [hk, hk1]; rfl⟩
    rw [hz1_eq] at hz₁_orb
    rcases hz₁_orb.1 with ha1 | ha2
    · exact h_not_assoc1 ha1
    · exact h_not_assoc2 ha2
  have hk_ge2 : 2 ≤ k := by omega
  have hn1_lb : 2 * (m : ℤ) + 1 < (n₁ : ℤ) := by
    have h4 : 2 * 2 ≤ k * k := int_sq_le (by omega) hk_ge2
    have hsq : (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1) < (n₁ : ℤ) * (n₁ : ℤ) := by omega
    by_contra hle
    have hsq2 := int_sq_le (by omega : 0 ≤ (n₁ : ℤ)) (by omega : (n₁ : ℤ) ≤ 2 * (m : ℤ) + 1)
    omega
  have hn1_odd : n₁ % 2 = 1 := by
    by_contra heven
    have hdiv2 : n₁ % 2 = 0 := by omega
    have hn2 : (n₁ : ℤ) = 2 * ((n₁ / 2 : ℕ) : ℤ) := by omega
    rw [hn2] at hnorm_z1
    rw [int_two_mul_sq] at hnorm_z1
    have hNmod : (N : ℤ) % 2 = 1 := by exact_mod_cast hN_odd
    omega
  set q : ℕ := (n₁ - (2 * m + 1)) / 2
  have hq1 : 1 ≤ q := by omega
  have hq2 : q ≤ 2 * (m - 2) := by omega
  have hn1_q : 2 * q + 2 * m + 1 = n₁ := by omega
  set kn : ℕ := k.natAbs
  have hkn : (kn : ℤ) = k := Int.natAbs_of_nonneg hk0
  have hpell : (2 * (q : ℤ) + 2 * (m : ℤ) + 1) * (2 * (q : ℤ) + 2 * (m : ℤ) + 1) -
      8 * ((kn : ℤ) * (kn : ℤ)) = (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 1) - 8 := by
    have hq_cast : 2 * (q : ℤ) + 2 * (m : ℤ) + 1 = (n₁ : ℤ) := by exact_mod_cast hn1_q
    rw [hq_cast, hkn, hnorm_z1, hNz]
  exact ⟨q, hq1, hq2, kn, (sq_iff_pell m q kn).mpr hpell⟩

end OMA.OeisA028886Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a028886.main := by
  intro m hm
  constructor
  · exact OMA.OeisA028886Proof.forward_dir m hm
  · intro h
    by_contra hnot
    obtain ⟨q, hq1, hq2, hsq⟩ := OMA.OeisA028886Proof.backward_dir m hm hnot
    exact h q hq1 hq2 hsq
