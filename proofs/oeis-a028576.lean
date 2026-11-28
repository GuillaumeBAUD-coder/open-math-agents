import OMAStatements.S_oeis_a028576
import Mathlib

namespace OMA.A028576Proof

open OMA.S_oeis_a028576

/-! ### Part 1: Basic divisibility by 4 -/

private lemma two_dvd_choose_two_mul {d : ℕ} (hd : 1 ≤ d) : 2 ∣ (2 * d).choose d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hd
  have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
  rw [h1, Nat.choose_succ_succ]
  have hsym : (2 * k + 1).choose (k + 1) = (2 * k + 1).choose k := by
    have h2 : 2 * k + 1 = k + (k + 1) := by omega
    rw [h2, Nat.choose_symm_add]
  rw [hsym, ← two_mul]
  exact dvd_mul_right 2 _

private lemma four_dvd_S (n : ℕ) : (4 : ℤ) ∣ S n := by
  unfold S
  apply Finset.dvd_sum
  intro d hd
  have hd_pos : 1 ≤ d := Nat.pos_of_mem_divisors hd
  obtain ⟨c, hc⟩ := two_dvd_choose_two_mul hd_pos
  refine dvd_mul_of_dvd_right ?_ _
  refine ⟨(c : ℤ) ^ 2, ?_⟩
  rw [hc]
  push_cast
  ring

/-! ### Part 2: Exact factorial-ratio identity -/

private lemma prod_Icc_eq_factorial (n : ℕ) : ∏ j ∈ Finset.Icc 1 n, j = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
    rw [hIcc, Finset.prod_insert hnot, ih, Nat.factorial_succ]

private lemma factorial_mul_eq (p n : ℕ) (hp : 0 < p) :
    (p * n).factorial =
      p ^ n * n.factorial * ∏ j ∈ (Finset.Icc 1 (p * n)).filter (fun j => ¬ p ∣ j), j := by
  rw [← prod_Icc_eq_factorial (p * n)]
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (p * n)) (fun j => p ∣ j)]
  congr 1
  have himg : (Finset.Icc 1 (p * n)).filter (fun j => p ∣ j) =
      (Finset.Icc 1 n).image (fun t => p * t) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hx1, hxn⟩, ⟨t, rfl⟩⟩
      refine ⟨t, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos t with rfl | ht
        · simp at hx1
        · exact ht
      · exact Nat.le_of_mul_le_mul_left hxn hp
    · rintro ⟨t, ⟨ht1, htn⟩, rfl⟩
      exact ⟨⟨Nat.mul_pos hp ht1, Nat.mul_le_mul_left p htn⟩, dvd_mul_right p t⟩
  rw [himg, Finset.prod_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp h)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
  simp [prod_Icc_eq_factorial]

private lemma prod_coprime_two_mul (p k : ℕ) :
    (∏ j ∈ (Finset.Icc 1 (p * (2 * k))).filter (fun j => ¬ p ∣ j), j) =
      (∏ j ∈ (Finset.Icc 1 (p * k)).filter (fun j => ¬ p ∣ j), j) *
      (∏ j ∈ (Finset.Icc 1 (p * k)).filter (fun j => ¬ p ∣ j), (p * k + j)) := by
  set X := p * k
  have h2X : p * (2 * k) = X + X := by dsimp only [X]; ring
  rw [h2X]
  set A := (Finset.Icc 1 X).filter (fun j => ¬ p ∣ j)
  set B := (Finset.Icc (X + 1) (X + X)).filter (fun j => ¬ p ∣ j)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro j hjA hjB
    simp only [A, B, Finset.mem_filter, Finset.mem_Icc] at hjA hjB
    omega
  have hunion : (Finset.Icc 1 (X + X)).filter (fun j => ¬ p ∣ j) = A ∪ B := by
    ext j
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hnd⟩
      by_cases hle : j ≤ X
      · exact Or.inl ⟨⟨h1, hle⟩, hnd⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, hnd⟩
    · rintro (⟨⟨h1, h2⟩, hnd⟩ | ⟨⟨h1, h2⟩, hnd⟩) <;> exact ⟨⟨by omega, by omega⟩, hnd⟩
  rw [hunion, Finset.prod_union hdisj]
  congr 1
  have hB : B = A.image (fun j => X + j) := by
    ext y
    simp only [A, B, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, hnd⟩
      refine ⟨y - X, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      intro hdvd
      apply hnd
      have hX : p ∣ X := dvd_mul_right p k
      have hadd : p ∣ X + (y - X) := dvd_add hX hdvd
      rwa [Nat.add_sub_of_le (by omega)] at hadd
    · rintro ⟨j, ⟨⟨h1, h2⟩, hnd⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      intro hdvd
      apply hnd
      exact (Nat.dvd_add_right (dvd_mul_right p k)).mp hdvd
  rw [hB, Finset.prod_image (fun x _ y _ h => by omega)]

private lemma choose_mul_prod_coprime (p k : ℕ) (hp : p.Prime) :
    (2 * (p * k)).choose (p * k) *
      (∏ j ∈ (Finset.Icc 1 (p * k)).filter (fun j => ¬ p ∣ j), j) =
    (2 * k).choose k *
      (∏ j ∈ (Finset.Icc 1 (p * k)).filter (fun j => ¬ p ∣ j), (p * k + j)) := by
  set U := (Finset.Icc 1 (p * k)).filter (fun j => ¬ p ∣ j)
  set P := ∏ j ∈ U, j
  set Q := ∏ j ∈ U, (p * k + j)
  have hP_pos : 0 < P := by
    apply Finset.prod_pos
    intro j hj
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
    omega
  have h1 : (2 * (p * k)).choose (p * k) * (p * k).factorial * (p * k).factorial =
      (2 * (p * k)).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show p * k ≤ 2 * (p * k) by omega)
    simpa [show 2 * (p * k) - p * k = p * k by omega] using this
  have h2 : (2 * k).choose k * k.factorial * k.factorial = (2 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    simpa [show 2 * k - k = k by omega] using this
  have hf1 : (p * k).factorial = p ^ k * k.factorial * P :=
    factorial_mul_eq p k hp.pos
  have hf2 : (2 * (p * k)).factorial = p ^ (2 * k) * (2 * k).factorial * (P * Q) := by
    rw [show 2 * (p * k) = p * (2 * k) by ring, factorial_mul_eq p (2 * k) hp.pos,
      prod_coprime_two_mul p k]
  have heq :
      ((2 * (p * k)).choose (p * k) * P) * (p ^ (2 * k) * k.factorial ^ 2 * P) =
      ((2 * k).choose k * Q) * (p ^ (2 * k) * k.factorial ^ 2 * P) := by
    calc ((2 * (p * k)).choose (p * k) * P) * (p ^ (2 * k) * k.factorial ^ 2 * P)
        = (2 * (p * k)).choose (p * k) * (p ^ k * k.factorial * P) * (p ^ k * k.factorial * P) := by
            rw [show 2 * k = k + k by ring, pow_add]; ring
      _ = (2 * (p * k)).choose (p * k) * (p * k).factorial * (p * k).factorial := by
            rw [← hf1]
      _ = (2 * (p * k)).factorial := h1
      _ = p ^ (2 * k) * (2 * k).factorial * (P * Q) := hf2
      _ = p ^ (2 * k) * ((2 * k).choose k * k.factorial * k.factorial) * (P * Q) := by
            rw [h2]
      _ = ((2 * k).choose k * Q) * (p ^ (2 * k) * k.factorial ^ 2 * P) := by ring
  have hpos : 0 < p ^ (2 * k) * k.factorial ^ 2 * P := by
    exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hp.pos) (Nat.pow_pos (Nat.factorial_pos k))) hP_pos
  exact Nat.eq_of_mul_eq_mul_right hpos heq

/-! ### Part 3: Algebraic product expansion modulo x^3 = 0 -/

private lemma prod_one_add_sq_of_cube_eq_zero {α R : Type*} [CommRing R] (s : Finset α)
    (x : R) (hx : x ^ 3 = 0) (c : α → R) :
    ∏ u ∈ s, (1 + x * c u) ^ 2 =
      1 + 2 * x * (∑ u ∈ s, c u) +
      x ^ 2 * (2 * (∑ u ∈ s, c u) ^ 2 - ∑ u ∈ s, (c u) ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih]
    set A := ∑ u ∈ s, c u
    set B := ∑ u ∈ s, (c u) ^ 2
    linear_combination
      (4 * c a * A ^ 2 - 2 * c a * B + 2 * c a ^ 2 * A +
       2 * x * c a ^ 2 * A ^ 2 - x * c a ^ 2 * B) * hx

/-! ### Part 4: Sum of squares of coprime residues -/

private lemma six_mul_sum_sq_int (N : ℕ) :
    6 * (∑ k ∈ Finset.range N, (k : ℤ) ^ 2) = (N : ℤ) * ((N : ℤ) - 1) * (2 * (N : ℤ) - 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

private lemma pow_dvd_six_mul_sum_sq_coprime (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    p ^ r ∣ 6 * ∑ k ∈ (Finset.range (p ^ r)).filter (fun k => ¬ p ∣ k), k ^ 2 := by
  rw [← Int.natCast_dvd_natCast]
  set V := (Finset.range (p ^ r)).filter (fun k => ¬ p ∣ k)
  set W := (Finset.range (p ^ r)).filter (fun k => p ∣ k)
  have hsplit : (∑ k ∈ W, (k : ℤ) ^ 2) + (∑ k ∈ V, (k : ℤ) ^ 2) =
      ∑ k ∈ Finset.range (p ^ r), (k : ℤ) ^ 2 :=
    Finset.sum_filter_add_sum_filter_not (Finset.range (p ^ r)) (fun k => p ∣ k) (fun k => (k : ℤ) ^ 2)
  have hW : W = (Finset.range (p ^ (r - 1))).image (fun t => p * t) := by
    ext x
    simp only [W, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hxr, ⟨t, rfl⟩⟩
      refine ⟨t, ?_, rfl⟩
      have hpr : p ^ r = p * p ^ (r - 1) := by
        conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ']
      rw [hpr] at hxr
      exact Nat.lt_of_mul_lt_mul_left hxr
    · rintro ⟨t, htr, rfl⟩
      have hpr : p ^ r = p * p ^ (r - 1) := by
        conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ']
      rw [hpr]
      exact ⟨Nat.mul_lt_mul_of_pos_left htr hp.pos, dvd_mul_right p t⟩
  have hW_sum : ∑ k ∈ W, (k : ℤ) ^ 2 = (p : ℤ) ^ 2 * ∑ t ∈ Finset.range (p ^ (r - 1)), (t : ℤ) ^ 2 := by
    rw [hW, Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    push_cast
    ring
  have h6V : (6 * ∑ k ∈ V, (k : ℤ) ^ 2) =
      ((p ^ r : ℕ) : ℤ) * (((p ^ r : ℕ) : ℤ) - 1) * (2 * ((p ^ r : ℕ) : ℤ) - 1) -
      (p : ℤ) ^ 2 * (((p ^ (r - 1) : ℕ) : ℤ) * (((p ^ (r - 1) : ℕ) : ℤ) - 1) *
        (2 * ((p ^ (r - 1) : ℕ) : ℤ) - 1)) := by
    have h1 := six_mul_sum_sq_int (p ^ r)
    have h2 := six_mul_sum_sq_int (p ^ (r - 1))
    linear_combination 6 * hsplit - 6 * hW_sum + h1 - (p : ℤ) ^ 2 * h2
  have hcast : ((6 * ∑ k ∈ V, k ^ 2 : ℕ) : ℤ) = 6 * ∑ k ∈ V, (k : ℤ) ^ 2 := by
    push_cast; rfl
  rw [hcast, h6V]
  apply dvd_sub
  · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  · have hp2 : (p : ℤ) ^ 2 * ((p ^ (r - 1) : ℕ) : ℤ) = ((p ^ r : ℕ) : ℤ) * (p : ℤ) := by
      push_cast
      rw [show (p : ℤ) ^ 2 * (p : ℤ) ^ (r - 1) = (p : ℤ) ^ ((r - 1) + 1) * (p : ℤ) by ring]
      rw [show r - 1 + 1 = r by omega]
    have : (p : ℤ) ^ 2 * (((p ^ (r - 1) : ℕ) : ℤ) * (((p ^ (r - 1) : ℕ) : ℤ) - 1) *
        (2 * ((p ^ (r - 1) : ℕ) : ℤ) - 1)) =
        ((p ^ r : ℕ) : ℤ) * ((p : ℤ) * (((p ^ (r - 1) : ℕ) : ℤ) - 1) *
          (2 * ((p ^ (r - 1) : ℕ) : ℤ) - 1)) := by
      linear_combination ((((p ^ (r - 1) : ℕ) : ℤ) - 1) * (2 * ((p ^ (r - 1) : ℕ) : ℤ) - 1)) * hp2
    rw [this]
    exact dvd_mul_right _ _

private lemma sum_sq_coprime_dvd (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    p ^ (if p = 2 ∨ p = 3 then r - 1 else r) ∣
      ∑ k ∈ (Finset.range (p ^ r)).filter (fun k => ¬ p ∣ k), k ^ 2 := by
  have h6 := pow_dvd_six_mul_sum_sq_coprime p r hp hr
  set S := ∑ k ∈ (Finset.range (p ^ r)).filter (fun k => ¬ p ∣ k), k ^ 2
  by_cases h23 : p = 2 ∨ p = 3
  · rw [if_pos h23]
    rcases h23 with rfl | rfl
    · have h2r : 2 ^ r = 2 * 2 ^ (r - 1) := by
        conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ']
      rw [h2r, show 6 * S = 2 * (3 * S) by ring] at h6
      have h3S : 2 ^ (r - 1) ∣ 3 * S := (mul_dvd_mul_iff_left (by decide : 2 ≠ 0)).mp h6
      have hcop : Nat.Coprime (2 ^ (r - 1)) 3 := (by decide : Nat.Coprime 2 3).pow_left _
      exact hcop.dvd_of_dvd_mul_left h3S
    · have h3r : 3 ^ r = 3 * 3 ^ (r - 1) := by
        conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ']
      rw [h3r, show 6 * S = 3 * (2 * S) by ring] at h6
      have h2S : 3 ^ (r - 1) ∣ 2 * S := (mul_dvd_mul_iff_left (by decide : 3 ≠ 0)).mp h6
      have hcop : Nat.Coprime (3 ^ (r - 1)) 2 := (by decide : Nat.Coprime 3 2).pow_left _
      exact hcop.dvd_of_dvd_mul_left h2S
  · rw [if_neg h23]
    have hcop2 : Nat.Coprime p 2 := (hp.coprime_iff_not_dvd).mpr (by
      intro h; exact h23 (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)))
    have hcop3 : Nat.Coprime p 3 := (hp.coprime_iff_not_dvd).mpr (by
      intro h; exact h23 (Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)))
    have hcop6 : Nat.Coprime (p ^ r) 6 := (hcop2.mul_right hcop3).pow_left r
    exact hcop6.dvd_of_dvd_mul_left h6

/-! ### Part 5: Congruence for the product ∏ (1 + X / j)^2 in ZMod (p^N) -/

private lemma zmod_castHom_inv {a b j : ℕ} (hab : a ∣ b) (hcop : Nat.Coprime j b) :
    ZMod.castHom hab (ZMod a) ((j : ZMod b)⁻¹) = (j : ZMod a)⁻¹ := by
  have hcop_a : Nat.Coprime j a := hcop.coprime_dvd_right hab
  have hb : (j : ZMod b) * (j : ZMod b)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one j hcop
  have ha : (j : ZMod a) * (j : ZMod a)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one j hcop_a
  have hmap := congrArg (ZMod.castHom hab (ZMod a)) hb
  rw [map_mul, map_one, map_natCast] at hmap
  calc ZMod.castHom hab (ZMod a) ((j : ZMod b)⁻¹)
      = 1 * ZMod.castHom hab (ZMod a) ((j : ZMod b)⁻¹) := (one_mul _).symm
    _ = ((j : ZMod a)⁻¹ * (j : ZMod a)) * ZMod.castHom hab (ZMod a) ((j : ZMod b)⁻¹) := by
          rw [mul_comm (j : ZMod a)⁻¹, ha]
    _ = (j : ZMod a)⁻¹ * ((j : ZMod a) * ZMod.castHom hab (ZMod a) ((j : ZMod b)⁻¹)) := by
          rw [mul_assoc]
    _ = (j : ZMod a)⁻¹ := by rw [hmap, mul_one]

private lemma prod_one_add_inv_sq_eq_one (p r m N : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (hm : 0 < m)
    (hN_le : N ≤ 3 * r)
    (hN_cond : (p = 2 → N = 3 * r) ∧ (p = 3 → N = 3 * r - 1) ∧ (p ≠ 2 → p ≠ 3 → N = 3 * r)) :
    let X := p ^ r * m
    let U := (Finset.Icc 1 X).filter (fun j => ¬ p ∣ j)
    ∏ j ∈ U, (1 + (X : ZMod (p ^ N)) * (j : ZMod (p ^ N))⁻¹) ^ 2 = 1 := by
  intro X U
  set R := ZMod (p ^ N)
  set x : R := (X : R)
  have hX_pos : 0 < X := Nat.mul_pos (Nat.pow_pos hp.pos) hm
  have hp_dvd_X : p ∣ X := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m
  have hx3 : x ^ 3 = 0 := by
    have hpow : p ^ N ∣ X ^ 3 := by
      have h1 : p ^ (3 * r) ∣ (p ^ r * m) ^ 3 := by
        rw [mul_pow, ← pow_mul, mul_comm r 3]
        exact dvd_mul_right _ _
      exact dvd_trans (pow_dvd_pow p hN_le) h1
    change ((X : R) ^ 3) = 0
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact hpow
  have hcop_U : ∀ j ∈ U, Nat.Coprime j (p ^ N) := by
    intro j hj
    have hnd : ¬ p ∣ j := (Finset.mem_filter.mp hj).2
    exact ((hp.coprime_iff_not_dvd).mpr hnd).symm.pow_right N
  have hmul_inv : ∀ j ∈ U, (j : R) * (j : R)⁻¹ = 1 :=
    fun j hj => ZMod.coe_mul_inv_eq_one j (hcop_U j hj)
  have hU_sub : ∀ j ∈ U, X - j ∈ U := by
    intro j hj
    simp only [U, Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    have hlt : j < X := by
      rcases lt_or_eq_of_le hj.1.2 with h | rfl
      · exact h
      · exact absurd hp_dvd_X hj.2
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro hdvd
    apply hj.2
    have hadd : X - j + j = X := by omega
    have hX' : p ∣ X - j + j := by rwa [hadd]
    exact (Nat.dvd_add_right hdvd).mp hX'
  have hU_le : ∀ j ∈ U, j ≤ X := fun j hj => (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).2
  set s1 : R := ∑ j ∈ U, (j : R)⁻¹
  set s2 : R := ∑ j ∈ U, ((j : R)⁻¹) ^ 2
  have hs1_inv : s1 = ∑ j ∈ U, ((X - j : ℕ) : R)⁻¹ := by
    refine Finset.sum_nbij (fun j => X - j) ?_ ?_ ?_ ?_
    · exact hU_sub
    · intro a ha b hb hab
      dsimp only at hab
      have ha' := hU_le a ha
      have hb' := hU_le b hb
      omega
    · intro y hy
      refine ⟨X - y, hU_sub y hy, ?_⟩
      dsimp only
      have hy' := hU_le y hy
      omega
    · intro a ha
      rw [Nat.sub_sub_self (hU_le a ha)]
  have hpair : ∀ j ∈ U,
      x * ((j : R)⁻¹ + ((X - j : ℕ) : R)⁻¹) = -(x ^ 2 * ((j : R)⁻¹) ^ 2) := by
    intro j hj
    have hj_inv := hmul_inv j hj
    have hs_inv := hmul_inv (X - j) (hU_sub j hj)
    have hsub_cast : ((X - j : ℕ) : R) = x - (j : R) := Nat.cast_sub (hU_le j hj)
    have h1 : x * ((j : R)⁻¹ + ((X - j : ℕ) : R)⁻¹) =
        x ^ 2 * (j : R)⁻¹ * ((X - j : ℕ) : R)⁻¹ := by
      calc x * ((j : R)⁻¹ + ((X - j : ℕ) : R)⁻¹)
          = x * ((j : R)⁻¹ * (((X - j : ℕ) : R) * ((X - j : ℕ) : R)⁻¹) +
                 ((j : R) * (j : R)⁻¹) * ((X - j : ℕ) : R)⁻¹) := by
              rw [hs_inv, hj_inv, mul_one, one_mul]
        _ = x * (((X - j : ℕ) : R) + (j : R)) * (j : R)⁻¹ * ((X - j : ℕ) : R)⁻¹ := by ring
        _ = x ^ 2 * (j : R)⁻¹ * ((X - j : ℕ) : R)⁻¹ := by rw [hsub_cast]; ring
    have h2 : x ^ 2 * ((X - j : ℕ) : R)⁻¹ = -(x ^ 2 * (j : R)⁻¹) := by
      have hmul : ((X - j : ℕ) : R) * (x ^ 2 * ((X - j : ℕ) : R)⁻¹) =
          ((X - j : ℕ) : R) * (-(x ^ 2 * (j : R)⁻¹)) := by
        calc ((X - j : ℕ) : R) * (x ^ 2 * ((X - j : ℕ) : R)⁻¹)
            = x ^ 2 * (((X - j : ℕ) : R) * ((X - j : ℕ) : R)⁻¹) := by ring
          _ = x ^ 2 := by rw [hs_inv, mul_one]
          _ = -x ^ 3 * (j : R)⁻¹ + x ^ 2 * ((j : R) * (j : R)⁻¹) := by
                rw [hx3, hj_inv]; ring
          _ = (x - (j : R)) * (-(x ^ 2 * (j : R)⁻¹)) := by ring
          _ = ((X - j : ℕ) : R) * (-(x ^ 2 * (j : R)⁻¹)) := by rw [hsub_cast]
      have hinvL : ((X - j : ℕ) : R)⁻¹ * ((X - j : ℕ) : R) = 1 := by
        rw [mul_comm, hs_inv]
      calc x ^ 2 * ((X - j : ℕ) : R)⁻¹
          = (((X - j : ℕ) : R)⁻¹ * ((X - j : ℕ) : R)) * (x ^ 2 * ((X - j : ℕ) : R)⁻¹) := by
              rw [hinvL, one_mul]
        _ = ((X - j : ℕ) : R)⁻¹ * (((X - j : ℕ) : R) * (x ^ 2 * ((X - j : ℕ) : R)⁻¹)) := by
              rw [mul_assoc]
        _ = ((X - j : ℕ) : R)⁻¹ * (((X - j : ℕ) : R) * (-(x ^ 2 * (j : R)⁻¹))) := by
              rw [hmul]
        _ = (((X - j : ℕ) : R)⁻¹ * ((X - j : ℕ) : R)) * (-(x ^ 2 * (j : R)⁻¹)) := by
              rw [← mul_assoc]
        _ = -(x ^ 2 * (j : R)⁻¹) := by rw [hinvL, one_mul]
    rw [h1, show x ^ 2 * (j : R)⁻¹ * ((X - j : ℕ) : R)⁻¹ =
        (x ^ 2 * ((X - j : ℕ) : R)⁻¹) * (j : R)⁻¹ by ring, h2]
    ring
  have h2xs1 : 2 * x * s1 = -(x ^ 2 * s2) := by
    calc 2 * x * s1
        = x * (s1 + s1) := by ring
      _ = x * ((∑ j ∈ U, (j : R)⁻¹) + (∑ j ∈ U, ((X - j : ℕ) : R)⁻¹)) := by
            rw [← hs1_inv]
      _ = ∑ j ∈ U, x * ((j : R)⁻¹ + ((X - j : ℕ) : R)⁻¹) := by
            rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ j ∈ U, -(x ^ 2 * ((j : R)⁻¹) ^ 2) := Finset.sum_congr rfl hpair
      _ = -(x ^ 2 * s2) := by
            rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  have h2x2s1 : 2 * x ^ 2 * s1 ^ 2 = 0 := by
    calc 2 * x ^ 2 * s1 ^ 2
        = (2 * x * s1) * (x * s1) := by ring
      _ = -(x ^ 2 * s2) * (x * s1) := by rw [h2xs1]
      _ = -(x ^ 3 * s2 * s1) := by ring
      _ = 0 := by rw [hx3]; ring
  rw [prod_one_add_sq_of_cube_eq_zero U x hx3 (fun j => (j : R)⁻¹)]
  change 1 + 2 * x * s1 + x ^ 2 * (2 * s1 ^ 2 - s2) = 1
  have hsimp : 1 + 2 * x * s1 + x ^ 2 * (2 * s1 ^ 2 - s2) = 1 - 2 * x ^ 2 * s2 := by
    linear_combination h2xs1 + h2x2s1
  rw [hsimp]
  -- Now show 2 * x^2 * s2 = 0 in R = ZMod (p ^ N)
  set M := if p = 2 ∨ p = 3 then r - 1 else r
  have hMr : M ≤ r := by
    dsimp only [M]; split_ifs <;> omega
  have hMN : M ≤ N := by
    by_cases h2 : p = 2
    · have := hN_cond.1 h2; dsimp only [M]; simp [h2]; omega
    · by_cases h3 : p = 3
      · have := hN_cond.2.1 h3; dsimp only [M]; simp [h3]; omega
      · have := hN_cond.2.2 h2 h3; dsimp only [M]; simp [h2, h3]; omega
  have hdivMN : p ^ M ∣ p ^ N := pow_dvd_pow p hMN
  have hdivMr : p ^ M ∣ p ^ r := pow_dvd_pow p hMr
  -- Show castHom (p^M | p^N) s2 = 0 in ZMod (p^M)
  have hs2_modM : ZMod.castHom hdivMN (ZMod (p ^ M)) s2 = 0 := by
    have hmap : ZMod.castHom hdivMN (ZMod (p ^ M)) s2 =
        ∑ j ∈ U, ((j : ZMod (p ^ M))⁻¹) ^ 2 := by
      dsimp only [s2]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_pow, zmod_castHom_inv hdivMN (hcop_U j hj)]
    rw [hmap]
    set V := (Finset.range (p ^ r)).filter (fun k => ¬ p ∣ k)
    have hU_biUnion : U = (Finset.range m).biUnion (fun q => V.image (fun v => q * p ^ r + v)) := by
      ext j
      simp only [U, V, Finset.mem_filter, Finset.mem_Icc, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨⟨hj1, hjX⟩, hnd⟩
        have hjlt : j < p ^ r * m := by
          rcases lt_or_eq_of_le hjX with h | rfl
          · exact h
          · exact absurd hp_dvd_X hnd
        have hpr_pos : 0 < p ^ r := Nat.pow_pos hp.pos
        refine ⟨j / p ^ r, Nat.div_lt_of_lt_mul hjlt, j % p ^ r,
          ⟨Nat.mod_lt j hpr_pos, ?_⟩, ?_⟩
        · intro hdvd
          apply hnd
          have h1 : p ∣ p ^ r * (j / p ^ r) := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
          have h2 := dvd_add h1 hdvd
          rwa [Nat.div_add_mod j (p ^ r)] at h2
        · rw [mul_comm, Nat.div_add_mod]
      · rintro ⟨q, hqm, v, ⟨hvlt, hvnd⟩, rfl⟩
        have hvpos : 1 ≤ v := by
          rcases Nat.eq_zero_or_pos v with rfl | hpos
          · exact absurd (dvd_zero p) hvnd
          · exact hpos
        have hpr_pos : 0 < p ^ r := Nat.pow_pos hp.pos
        refine ⟨⟨by omega, ?_⟩, ?_⟩
        · have hle : (q + 1) * p ^ r ≤ m * p ^ r := Nat.mul_le_mul_right (p ^ r) hqm
          dsimp only [X]
          nlinarith
        · intro hdvd
          apply hvnd
          have h1 : p ∣ q * p ^ r := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) q
          exact (Nat.dvd_add_right h1).mp hdvd
    have hdisj_bi : Set.PairwiseDisjoint (↑(Finset.range m))
        (fun q => V.image (fun v => q * p ^ r + v)) := by
      intro q1 _ q2 _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      simp only [V, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hy1 hy2
      rcases hy1 with ⟨v1, ⟨hv1, _⟩, rfl⟩
      rcases hy2 with ⟨v2, ⟨hv2, _⟩, heq⟩
      have hpr_pos : 0 < p ^ r := Nat.pow_pos hp.pos
      have hq : q1 = q2 := by
        have h1 : (q1 * p ^ r + v1) / p ^ r = q1 := by
          rw [mul_comm, Nat.mul_add_div hpr_pos, Nat.div_eq_of_lt hv1, add_zero]
        have h2 : (q2 * p ^ r + v2) / p ^ r = q2 := by
          rw [mul_comm, Nat.mul_add_div hpr_pos, Nat.div_eq_of_lt hv2, add_zero]
        rw [← h1, ← h2, heq]
      exact hne hq
    have hsum_U : ∑ j ∈ U, ((j : ZMod (p ^ M))⁻¹) ^ 2 =
        (m : ZMod (p ^ M)) * ∑ v ∈ V, ((v : ZMod (p ^ M))⁻¹) ^ 2 := by
      rw [hU_biUnion, Finset.sum_biUnion hdisj_bi]
      have hblock : ∀ q ∈ Finset.range m,
          ∑ j ∈ V.image (fun v => q * p ^ r + v), ((j : ZMod (p ^ M))⁻¹) ^ 2 =
          ∑ v ∈ V, ((v : ZMod (p ^ M))⁻¹) ^ 2 := by
        intro q _
        rw [Finset.sum_image (fun x _ y _ h => by omega)]
        apply Finset.sum_congr rfl
        intro v _
        have hcast0 : ((q * p ^ r + v : ℕ) : ZMod (p ^ M)) = (v : ZMod (p ^ M)) := by
          have hdvd : p ^ M ∣ q * p ^ r := dvd_mul_of_dvd_right hdivMr q
          have h0 : ((q * p ^ r : ℕ) : ZMod (p ^ M)) = 0 :=
            (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
          rw [Nat.cast_add, h0, zero_add]
        rw [hcast0]
      rw [Finset.sum_congr rfl hblock, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum_U]
    have hV_inv_r : ∑ v ∈ V, ((v : ZMod (p ^ r))⁻¹) ^ 2 = ∑ v ∈ V, ((v : ZMod (p ^ r)) ^ 2) := by
      have : NeZero (p ^ r) := ⟨(Nat.pow_pos hp.pos).ne'⟩
      have hcop_V : ∀ v ∈ V, Nat.Coprime v (p ^ r) := by
        intro v hv
        exact ((hp.coprime_iff_not_dvd).mpr (Finset.mem_filter.mp hv).2).symm.pow_right r
      let inv_nat : ℕ → ℕ := fun v => ((v : ZMod (p ^ r))⁻¹).val
      have hpr_dvd_self : p ∣ p ^ r := dvd_pow_self p (by omega)
      have hinv_mem : ∀ v ∈ V, inv_nat v ∈ V := by
        intro v hv
        simp only [V, Finset.mem_filter, Finset.mem_range]
        refine ⟨ZMod.val_lt _, ?_⟩
        intro hdvd
        have hmul := ZMod.coe_mul_inv_eq_one v (hcop_V v hv)
        have hcast : ((inv_nat v : ℕ) : ZMod (p ^ r)) = (v : ZMod (p ^ r))⁻¹ :=
          ZMod.natCast_zmod_val _
        rw [← hcast, ← Nat.cast_mul] at hmul
        have h1 : ZMod.castHom hpr_dvd_self (ZMod p) (((v * inv_nat v : ℕ) : ZMod (p ^ r))) =
            ZMod.castHom hpr_dvd_self (ZMod p) 1 := congrArg _ hmul
        rw [map_natCast, map_one] at h1
        have h0 : ((v * inv_nat v : ℕ) : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_mul_of_dvd_right hdvd v)
        rw [h0] at h1
        have : Fact p.Prime := ⟨hp⟩
        exact zero_ne_one h1
      have hinv_invol : ∀ v ∈ V, inv_nat (inv_nat v) = v := by
        intro v hv
        have hmul := ZMod.coe_mul_inv_eq_one v (hcop_V v hv)
        have hcast : ((inv_nat v : ℕ) : ZMod (p ^ r)) = (v : ZMod (p ^ r))⁻¹ :=
          ZMod.natCast_zmod_val _
        have hcop_iv : Nat.Coprime (inv_nat v) (p ^ r) := hcop_V (inv_nat v) (hinv_mem v hv)
        have hmul2 := ZMod.coe_mul_inv_eq_one (inv_nat v) hcop_iv
        have heq : ((inv_nat v : ℕ) : ZMod (p ^ r))⁻¹ = (v : ZMod (p ^ r)) := by
          calc ((inv_nat v : ℕ) : ZMod (p ^ r))⁻¹
              = ((v : ZMod (p ^ r)) * ((inv_nat v : ℕ) : ZMod (p ^ r))) *
                  ((inv_nat v : ℕ) : ZMod (p ^ r))⁻¹ := by
                    rw [hcast, hmul, one_mul]
            _ = (v : ZMod (p ^ r)) * (((inv_nat v : ℕ) : ZMod (p ^ r)) *
                  ((inv_nat v : ℕ) : ZMod (p ^ r))⁻¹) := by rw [mul_assoc]
            _ = (v : ZMod (p ^ r)) := by rw [hmul2, mul_one]
        dsimp only [inv_nat]
        rw [heq]
        exact ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hv).1)
      refine Finset.sum_nbij inv_nat hinv_mem ?_ ?_ ?_
      · intro a ha b hb hab
        have := congrArg inv_nat hab
        rwa [hinv_invol a ha, hinv_invol b hb] at this
      · intro y hy
        exact ⟨inv_nat y, hinv_mem y hy, hinv_invol y hy⟩
      · intro v _
        rw [ZMod.natCast_zmod_val]
    have hV_sum_M : ∑ v ∈ V, ((v : ZMod (p ^ M))⁻¹) ^ 2 = 0 := by
      have hproj := congrArg (ZMod.castHom hdivMr (ZMod (p ^ M))) hV_inv_r
      rw [map_sum, map_sum] at hproj
      have hlhs : ∑ v ∈ V, ZMod.castHom hdivMr (ZMod (p ^ M)) (((v : ZMod (p ^ r))⁻¹) ^ 2) =
          ∑ v ∈ V, ((v : ZMod (p ^ M))⁻¹) ^ 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        have hcop_v : Nat.Coprime v (p ^ r) :=
          ((hp.coprime_iff_not_dvd).mpr (Finset.mem_filter.mp hv).2).symm.pow_right r
        rw [map_pow, zmod_castHom_inv hdivMr hcop_v]
      have hrhs : ∑ v ∈ V, ZMod.castHom hdivMr (ZMod (p ^ M)) ((v : ZMod (p ^ r)) ^ 2) =
          ((∑ v ∈ V, v ^ 2 : ℕ) : ZMod (p ^ M)) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro v _
        rw [map_pow, map_natCast, Nat.cast_pow]
      rw [← hlhs, hproj, hrhs, ZMod.natCast_eq_zero_iff]
      exact sum_sq_coprime_dvd p r hp hr
    rw [hV_sum_M, mul_zero]
  -- Deduce 2 * x ^ 2 * s2 = 0 in R = ZMod (p ^ N)
  have : NeZero (p ^ N) := ⟨(Nat.pow_pos hp.pos).ne'⟩
  have hdvd_s2 : p ^ M ∣ s2.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    have := hs2_modM
    rw [← ZMod.natCast_zmod_val s2, map_natCast] at this
    exact this
  obtain ⟨q, hq⟩ := hdvd_s2
  have hs2_eq : s2 = ((p ^ M : ℕ) : R) * (q : R) := by
    rw [← ZMod.natCast_zmod_val s2, hq, Nat.cast_mul]
  have h2x2s2 : 2 * x ^ 2 * s2 = 0 := by
    rw [hs2_eq]
    have hX2 : x ^ 2 = ((p ^ (2 * r) : ℕ) : R) * ((m ^ 2 : ℕ) : R) := by
      dsimp only [x, X]
      rw [← Nat.cast_pow, ← Nat.cast_mul]
      congr 1
      rw [mul_pow, ← pow_mul, mul_comm r 2]
    rw [hX2]
    have hcoeff : (2 : R) * ((p ^ (2 * r) : ℕ) : R) * ((p ^ M : ℕ) : R) = 0 := by
      rw [show (2 : R) = ((2 : ℕ) : R) by norm_num, ← Nat.cast_mul, ← Nat.cast_mul]
      rw [ZMod.natCast_eq_zero_iff]
      by_cases h2 : p = 2
      · have hN := hN_cond.1 h2
        subst h2
        dsimp only [M]; simp only [true_or, ↓reduceIte]
        rw [hN, mul_assoc, ← pow_add, ← pow_succ']
        have : 3 * r = (2 * r + (r - 1)) + 1 := by omega
        rw [this]
      · by_cases h3 : p = 3
        · have hN := hN_cond.2.1 h3
          subst h3
          dsimp only [M]; simp only [or_true, ↓reduceIte]
          rw [hN, mul_assoc, ← pow_add]
          have : 3 * r - 1 = 2 * r + (r - 1) := by omega
          rw [this]
          exact dvd_mul_left _ 2
        · have hN := hN_cond.2.2 h2 h3
          dsimp only [M]; simp only [h2, h3, or_self, ↓reduceIte]
          rw [hN, mul_assoc, ← pow_add]
          have : 3 * r = 2 * r + r := by omega
          rw [this]
          exact dvd_mul_left _ 2
    calc 2 * (((p ^ (2 * r) : ℕ) : R) * ((m ^ 2 : ℕ) : R)) * (((p ^ M : ℕ) : R) * (q : R))
        = (2 * ((p ^ (2 * r) : ℕ) : R) * ((p ^ M : ℕ) : R)) * (((m ^ 2 : ℕ) : R) * (q : R)) := by ring
      _ = 0 := by rw [hcoeff, zero_mul]
  rw [h2x2s2, sub_zero]

/-! ### Part 6: Prime-power supercongruence for C(2d, d)^2 -/

private lemma choose_sq_sub_dvd (p r m : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (hm : 0 < m) :
    ((p ^ (if p = 2 then 3 * r + 2 else if p = 3 then 3 * r - 1 else 3 * r) : ℕ) : ℤ) ∣
      ((2 * (p ^ r * m)).choose (p ^ r * m) : ℤ) ^ 2 -
      ((2 * (p ^ (r - 1) * m)).choose (p ^ (r - 1) * m) : ℤ) ^ 2 := by
  set k := p ^ (r - 1) * m
  have hpk : p * k = p ^ r * m := by
    dsimp only [k]
    rw [← mul_assoc, ← pow_succ', show r - 1 + 1 = r by omega]
  set X := p ^ r * m
  set U := (Finset.Icc 1 X).filter (fun j => ¬ p ∣ j)
  set P := ∏ j ∈ U, j
  set Q := ∏ j ∈ U, (X + j)
  have hid : (2 * X).choose X * P = (2 * k).choose k * Q := by
    have := choose_mul_prod_coprime p k hp
    rwa [hpk] at this
  have hsq : ((2 * X).choose X : ℤ) ^ 2 * (P : ℤ) ^ 2 =
      ((2 * k).choose k : ℤ) ^ 2 * (Q : ℤ) ^ 2 := by
    have hnat : ((2 * X).choose X * P) ^ 2 = ((2 * k).choose k * Q) ^ 2 := congrArg (· ^ 2) hid
    have hint : (((2 * X).choose X * P) ^ 2 : ℤ) = (((2 * k).choose k * Q) ^ 2 : ℤ) := by
      exact_mod_cast hnat
    linear_combination hint
  set N := if p = 3 then 3 * r - 1 else 3 * r
  have hN_le : N ≤ 3 * r := by dsimp only [N]; split_ifs <;> omega
  have hN_cond : (p = 2 → N = 3 * r) ∧ (p = 3 → N = 3 * r - 1) ∧ (p ≠ 2 → p ≠ 3 → N = 3 * r) := by
    dsimp only [N]
    refine ⟨fun h => by simp [h], fun h => by simp [h], fun _ h3 => by simp [h3]⟩
  have hprod_one : ∏ j ∈ U, (1 + (X : ZMod (p ^ N)) * (j : ZMod (p ^ N))⁻¹) ^ 2 = 1 :=
    prod_one_add_inv_sq_eq_one p r m N hp hr hm hN_le hN_cond
  have hQ_eq_P : (Q : ZMod (p ^ N)) ^ 2 = (P : ZMod (p ^ N)) ^ 2 := by
    have hfactor : (Q : ZMod (p ^ N)) ^ 2 =
        (P : ZMod (p ^ N)) ^ 2 *
          ∏ j ∈ U, (1 + (X : ZMod (p ^ N)) * (j : ZMod (p ^ N))⁻¹) ^ 2 := by
      dsimp only [P, Q]
      rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j hj
      have hcop : Nat.Coprime j (p ^ N) :=
        ((hp.coprime_iff_not_dvd).mpr (Finset.mem_filter.mp hj).2).symm.pow_right N
      have hinv := ZMod.coe_mul_inv_eq_one j hcop
      rw [← mul_pow, Nat.cast_add]
      congr 1
      calc (X : ZMod (p ^ N)) + (j : ZMod (p ^ N))
          = (j : ZMod (p ^ N)) + (X : ZMod (p ^ N)) * ((j : ZMod (p ^ N)) * (j : ZMod (p ^ N))⁻¹) := by
              rw [hinv, mul_one, add_comm]
        _ = (j : ZMod (p ^ N)) * (1 + (X : ZMod (p ^ N)) * (j : ZMod (p ^ N))⁻¹) := by ring
    rw [hfactor, hprod_one, mul_one]
  have hPQ_dvd : ((p ^ N : ℕ) : ℤ) ∣ (Q : ℤ) ^ 2 - (P : ℤ) ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hQ_eq_P, sub_self]
  have hdiff_mul : (((2 * X).choose X : ℤ) ^ 2 - ((2 * k).choose k : ℤ) ^ 2) * (P : ℤ) ^ 2 =
      ((2 * k).choose k : ℤ) ^ 2 * ((Q : ℤ) ^ 2 - (P : ℤ) ^ 2) := by
    linear_combination hsq
  have hP_cop : Nat.Coprime (P ^ 2) p := by
    apply Nat.Coprime.pow_left
    have : ∀ j ∈ U, Nat.Coprime j p := fun j hj =>
      ((hp.coprime_iff_not_dvd).mpr (Finset.mem_filter.mp hj).2).symm
    exact Finset.prod_induction _ (fun x => Nat.Coprime x p) (fun _ _ ha hb => ha.mul_left hb)
      (Nat.coprime_one_left p) this
  set E := if p = 2 then 3 * r + 2 else if p = 3 then 3 * r - 1 else 3 * r
  have hE_dvd_rhs : ((p ^ E : ℕ) : ℤ) ∣ ((2 * k).choose k : ℤ) ^ 2 * ((Q : ℤ) ^ 2 - (P : ℤ) ^ 2) := by
    by_cases h2 : p = 2
    · subst h2
      have hE : E = N + 2 := by dsimp only [E, N]; simp
      have hk_pos : 1 ≤ k := Nat.mul_pos (Nat.pow_pos (by decide)) hm
      obtain ⟨c, hc⟩ := two_dvd_choose_two_mul hk_pos
      have h4 : (4 : ℤ) ∣ ((2 * k).choose k : ℤ) ^ 2 := by
        refine ⟨(c : ℤ) ^ 2, ?_⟩
        rw [hc]; push_cast; ring
      have hpow4 : ((2 ^ (N + 2) : ℕ) : ℤ) = 4 * ((2 ^ N : ℕ) : ℤ) := by
        rw [pow_add]; push_cast; ring
      rw [hE, hpow4]
      exact mul_dvd_mul h4 hPQ_dvd
    · have hEN : E = N := by dsimp only [E, N]; simp [h2]
      rw [hEN]
      exact dvd_mul_of_dvd_right hPQ_dvd _
  rw [← hdiff_mul] at hE_dvd_rhs
  have hcop_int : IsCoprime ((p ^ E : ℕ) : ℤ) ((P ^ 2 : ℕ) : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using (hP_cop.pow_right E).symm
  exact hcop_int.dvd_of_dvd_mul_right (by simpa [Nat.cast_pow] using hE_dvd_rhs)

/-! ### Part 7: Möbius sum reduction and prime-power assembly -/

private lemma moebius_prime_pow_eq_zero {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) :
    ArithmeticFunction.moebius (p ^ j) = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsq
  have h2 : p * p ∣ p ^ j := by
    rw [← sq]
    exact pow_dvd_pow p hj
  exact hp.not_isUnit (hsq p h2)

private lemma S_eq_sum_sub (p r m : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (hm : 0 < m) (hpm : ¬ p ∣ m) :
    S (p ^ r * m) = ∑ e ∈ m.divisors, (ArithmeticFunction.moebius (m / e) : ℤ) *
      (((2 * (p ^ r * e)).choose (p ^ r * e) : ℤ) ^ 2 -
       ((2 * (p ^ (r - 1) * e)).choose (p ^ (r - 1) * e) : ℤ) ^ 2) := by
  unfold S
  have hcop : Nat.Coprime (p ^ r) m := ((hp.coprime_iff_not_dvd).mpr hpm).pow_left r
  have hdiv_mul : (p ^ r * m).divisors =
      ((Finset.range (r + 1)) ×ˢ m.divisors).image (fun x => p ^ x.1 * x.2) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
    constructor
    · rintro ⟨hd_dvd, _⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.mp hd_dvd
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp ha
      exact ⟨i, b, ⟨Nat.lt_succ_of_le hi, hb, hm.ne'⟩, rfl⟩
    · rintro ⟨i, b, ⟨hi, hb, _⟩, rfl⟩
      exact ⟨mul_dvd_mul (pow_dvd_pow p (Nat.lt_succ_iff.mp hi)) hb,
        mul_ne_zero (Nat.pow_pos hp.pos).ne' hm.ne'⟩
  have hinj : Set.InjOn (fun x : ℕ × ℕ => p ^ x.1 * x.2) ↑((Finset.range (r + 1)) ×ˢ m.divisors) := by
    rintro ⟨i1, e1⟩ h1 ⟨i2, e2⟩ h2 heq
    dsimp only at heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range,
      Nat.mem_divisors] at h1 h2
    have he1_nd : ¬ p ∣ e1 := fun h => hpm (dvd_trans h h1.2.1)
    have he2_nd : ¬ p ∣ e2 := fun h => hpm (dvd_trans h h2.2.1)
    have hi : i1 = i2 := by
      have hv1 : (p ^ i1 * e1).factorization p = i1 := by
        rw [Nat.factorization_mul (Nat.pow_pos hp.pos).ne' (Nat.pos_of_dvd_of_pos h1.2.1 hm).ne',
          Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
          Nat.factorization_eq_zero_of_not_dvd he1_nd, add_zero]
      have hv2 : (p ^ i2 * e2).factorization p = i2 := by
        rw [Nat.factorization_mul (Nat.pow_pos hp.pos).ne' (Nat.pos_of_dvd_of_pos h2.2.1 hm).ne',
          Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
          Nat.factorization_eq_zero_of_not_dvd he2_nd, add_zero]
      rw [← hv1, ← hv2, heq]
    subst hi
    have he : e1 = e2 := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hp.pos) heq
    exact Prod.ext rfl he
  rw [hdiv_mul, Finset.sum_image hinj, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have he_dvd : e ∣ m := (Nat.mem_divisors.mp he).1
  have he_pos : 0 < e := Nat.pos_of_dvd_of_pos he_dvd hm
  have hterm : ∀ i ∈ Finset.range (r + 1),
      (ArithmeticFunction.moebius ((p ^ r * m) / (p ^ i * e)) : ℤ) *
        ((2 * (p ^ i * e)).choose (p ^ i * e) : ℤ) ^ 2 =
      (ArithmeticFunction.moebius (p ^ (r - i)) : ℤ) *
        (ArithmeticFunction.moebius (m / e) : ℤ) *
        ((2 * (p ^ i * e)).choose (p ^ i * e) : ℤ) ^ 2 := by
    intro i hi
    have hi_le : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hdiv : (p ^ r * m) / (p ^ i * e) = p ^ (r - i) * (m / e) := by
      have hpos : 0 < p ^ i * e := Nat.mul_pos (Nat.pow_pos hp.pos) he_pos
      apply Nat.eq_of_mul_eq_mul_left hpos
      have hpi_dvd : p ^ i ∣ p ^ r := pow_dvd_pow p hi_le
      rw [Nat.mul_div_cancel' (mul_dvd_mul hpi_dvd he_dvd)]
      symm
      calc (p ^ i * e) * (p ^ (r - i) * (m / e))
          = (p ^ i * p ^ (r - i)) * (e * (m / e)) := by ring
        _ = p ^ r * m := by rw [← pow_add, Nat.add_sub_of_le hi_le, Nat.mul_div_cancel' he_dvd]
    rw [hdiv]
    have hcop_q : Nat.Coprime (p ^ (r - i)) (m / e) :=
      hcop.coprime_dvd_left (pow_dvd_pow p (Nat.sub_le r i)) |>.coprime_dvd_right (Nat.div_dvd_of_dvd he_dvd)
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_q]
  rw [Finset.sum_congr rfl hterm]
  obtain ⟨r', rfl⟩ := Nat.exists_eq_add_of_le' hr
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hzero : ∑ i ∈ Finset.range r',
      (ArithmeticFunction.moebius (p ^ (r' + 1 - i)) : ℤ) *
        (ArithmeticFunction.moebius (m / e) : ℤ) *
        ((2 * (p ^ i * e)).choose (p ^ i * e) : ℤ) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hilt : i < r' := Finset.mem_range.mp hi
    rw [moebius_prime_pow_eq_zero hp (by omega)]
    simp
  rw [hzero, zero_add]
  have hsub1 : r' + 1 - r' = 1 := by omega
  have hsub0 : r' + 1 - (r' + 1) = 0 := by omega
  have hsub_r : r' + 1 - 1 = r' := by omega
  rw [hsub1, hsub0, hsub_r, pow_one, pow_zero, ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_one]
  ring

private lemma prime_pow_dvd_S {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hpn : p ∣ n) :
    let r := n.factorization p
    ((p ^ (if p = 2 then 3 * r + 2 else if p = 3 then 3 * r - 1 else 3 * r) : ℕ) : ℤ) ∣ S n := by
  intro r
  have hn0 : n ≠ 0 := by omega
  have hr : 1 ≤ r := Nat.pos_of_ne_zero (by
    intro h0
    have := (hp.dvd_iff_one_le_factorization hn0).mp hpn
    omega)
  have hpr_dvd : p ^ r ∣ n := Nat.ordProj_dvd n p
  set m := n / p ^ r
  have hn_eq : n = p ^ r * m := (Nat.mul_div_cancel' hpr_dvd).symm
  have hm_pos : 0 < m := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hpr_dvd) (by omega)
  have hpm : ¬ p ∣ m := by
    intro hdvd
    have h1 : p ^ (r + 1) ∣ n := by
      rw [hn_eq, pow_succ]
      exact mul_dvd_mul_left (p ^ r) hdvd
    have h2 : r + 1 ≤ r := (hp.pow_dvd_iff_le_factorization hn0).mp h1
    omega
  rw [hn_eq, S_eq_sum_sub p r m hp hr hm_pos hpm]
  apply Finset.dvd_sum
  intro e he
  have he_pos : 0 < e := Nat.pos_of_mem_divisors he
  exact dvd_mul_of_dvd_right (choose_sq_sub_dvd p r e hp hr he_pos) _

private lemma dvd_int_of_prime_pow_dvd {a : ℕ} {b : ℤ} (ha : a ≠ 0)
    (h : ∀ p : ℕ, p.Prime → ((p ^ a.factorization p : ℕ) : ℤ) ∣ b) : (a : ℤ) ∣ b := by
  rw [Int.natCast_dvd]
  by_cases hb0 : b.natAbs = 0
  · rw [hb0]; exact dvd_zero a
  · rw [← Nat.factorization_le_iff_dvd ha hb0]
    intro p
    by_cases hp0 : a.factorization p = 0
    · rw [hp0]; exact Nat.zero_le _
    · have hp : p.Prime := Nat.prime_of_mem_primeFactors
        (Nat.mem_primeFactors.mpr ⟨by
          have : p ∈ a.factorization.support := Finsupp.mem_support_iff.mpr hp0
          exact Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at this),
          by
            have : p ∈ a.factorization.support := Finsupp.mem_support_iff.mpr hp0
            exact Nat.dvd_of_mem_primeFactors (by rwa [Nat.support_factorization] at this),
          ha⟩)
      have hdvd : p ^ a.factorization p ∣ b.natAbs := Int.natCast_dvd.mp (h p hp)
      exact (hp.pow_dvd_iff_le_factorization hb0).mp hdvd

private lemma factorization_four (p : ℕ) : (4 : ℕ).factorization p = if p = 2 then 2 else 0 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.prime_two.factorization_pow]
  by_cases h : p = 2
  · subst h; simp
  · simp [h, Ne.symm h]

private lemma four_mul_sq_dvd_S {n : ℕ} (hn : 1 ≤ n) : (4 * (n : ℤ) ^ 2) ∣ S n := by
  have hcast : (4 * (n : ℤ) ^ 2) = ((4 * n ^ 2 : ℕ) : ℤ) := by push_cast; rfl
  rw [hcast]
  have ha0 : 4 * n ^ 2 ≠ 0 := by positivity
  apply dvd_int_of_prime_pow_dvd ha0
  intro p hp
  have hfac : (4 * n ^ 2).factorization p = (4 : ℕ).factorization p + 2 * n.factorization p := by
    rw [Nat.factorization_mul (by decide) (by positivity),
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rw [hfac, factorization_four]
  by_cases hpn : p ∣ n
  · have hS := prime_pow_dvd_S hn hp hpn
    set r := n.factorization p
    have hr : 1 ≤ r := (hp.dvd_iff_one_le_factorization (by omega)).mp hpn
    have hle : (if p = 2 then 2 else 0) + 2 * r ≤
        (if p = 2 then 3 * r + 2 else if p = 3 then 3 * r - 1 else 3 * r) := by
      split_ifs <;> omega
    exact dvd_trans (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p hle)) hS
  · have hnr : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
    rw [hnr, mul_zero, add_zero]
    by_cases h2 : p = 2
    · subst h2
      simpa using four_dvd_S n
    · simp [h2]

private lemma four_mul_cube_dvd_three_S {n : ℕ} (hn : 1 ≤ n) : (4 * (n : ℤ) ^ 3) ∣ 3 * S n := by
  have hcast : (4 * (n : ℤ) ^ 3) = ((4 * n ^ 3 : ℕ) : ℤ) := by push_cast; rfl
  rw [hcast]
  have ha0 : 4 * n ^ 3 ≠ 0 := by positivity
  apply dvd_int_of_prime_pow_dvd ha0
  intro p hp
  have hfac : (4 * n ^ 3).factorization p = (4 : ℕ).factorization p + 3 * n.factorization p := by
    rw [Nat.factorization_mul (by decide) (by positivity),
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rw [hfac, factorization_four]
  by_cases hpn : p ∣ n
  · have hS := prime_pow_dvd_S hn hp hpn
    set r := n.factorization p
    have hr : 1 ≤ r := (hp.dvd_iff_one_le_factorization (by omega)).mp hpn
    by_cases h2 : p = 2
    · subst h2
      simp only [↓reduceIte] at hS ⊢
      rw [show 2 + 3 * r = 3 * r + 2 by omega]
      exact dvd_mul_of_dvd_right hS 3
    · simp only [h2, ↓reduceIte, zero_add] at hS ⊢
      by_cases h3 : p = 3
      · subst h3
        simp only [↓reduceIte] at hS
        rw [show (3 ^ (3 * r) : ℕ) = 3 * 3 ^ (3 * r - 1) by
          conv_lhs => rw [show 3 * r = (3 * r - 1) + 1 by omega, pow_succ']]
        push_cast
        exact mul_dvd_mul_left 3 (by simpa using hS)
      · simp only [h3, ↓reduceIte] at hS
        exact dvd_mul_of_dvd_right hS 3
  · have hnr : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
    rw [hnr, mul_zero, add_zero]
    by_cases h2 : p = 2
    · subst h2
      exact dvd_mul_of_dvd_right (by simpa using four_dvd_S n) 3
    · simp [h2]

theorem main_proof : ∀ n : ℕ, 1 ≤ n → (n : ℤ) ∣ a n ∧ (n : ℤ) ^ 2 ∣ 3 * a n := by
  intro n hn
  have h4n_ne : (4 * (n : ℤ)) ≠ 0 := by positivity
  have h2 := four_mul_sq_dvd_S hn
  have h3 := four_mul_cube_dvd_three_S hn
  have h4n_dvd : (4 * (n : ℤ)) ∣ S n :=
    dvd_trans ⟨(n : ℤ), by ring⟩ h2
  have ha_mul : (4 * (n : ℤ)) * a n = S n := by
    unfold a
    exact Int.mul_ediv_cancel' h4n_dvd
  constructor
  · obtain ⟨q, hq⟩ := h2
    refine ⟨q, ?_⟩
    apply mul_left_cancel₀ h4n_ne
    rw [ha_mul, hq]
    ring
  · obtain ⟨q, hq⟩ := h3
    refine ⟨q, ?_⟩
    apply mul_left_cancel₀ h4n_ne
    have : 4 * (n : ℤ) * (3 * a n) = 3 * (4 * (n : ℤ) * a n) := by ring
    rw [this, ha_mul, hq]
    ring

end OMA.A028576Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a028576.main :=
  OMA.A028576Proof.main_proof
