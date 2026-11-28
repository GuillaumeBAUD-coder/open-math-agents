import OMAStatements.S_oeis_a323689
import Mathlib

namespace A323689P

open PowerSeries OMA.S_oeis_a323689

/-- `Sum_q j^q x^(d q)`, as a power series. -/
noncomputable def G {R : Type*} [CommRing R] (j : R) (d : ℕ) : PowerSeries R :=
  mk fun k => if d ∣ k then j ^ (k / d) else 0

lemma one_add_mul_G {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (j : R) (d : ℕ) (hd : 1 ≤ d) :
    (1 + C j * X ^ d) * G j d = 1 := by
  ext k
  rw [add_mul, one_mul, mul_assoc, map_add, coeff_C_mul, coeff_X_pow_mul', G, coeff_mk, coeff_mk,
    coeff_one]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : ¬ d ≤ 0 := by omega
    simp [this]
  · have hk0 : k ≠ 0 := by omega
    have hd0 : 0 < d := by omega
    by_cases hdk : d ∣ k
    · obtain ⟨c, rfl⟩ := hdk
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by
        rcases Nat.eq_zero_or_pos c with h | h
        · subst h; simp at hk0
        · omega⟩
      have hle : d ≤ d * (c' + 1) := Nat.le_mul_of_pos_right d (by omega)
      have hsub : d * (c' + 1) - d = d * c' := by rw [Nat.mul_succ]; omega
      rw [if_pos (dvd_mul_right d _), if_pos hle, hsub, if_pos (dvd_mul_right d _), if_neg hk0,
        Nat.mul_div_cancel_left _ hd0, Nat.mul_div_cancel_left _ hd0]
      calc j ^ (c' + 1) + j * j ^ c' = 2 * j ^ (c' + 1) := by ring
        _ = 0 := by rw [h2, zero_mul]
    · by_cases hle : d ≤ k
      · have hdk' : ¬ d ∣ k - d := fun h => hdk ((Nat.dvd_sub_iff_left hle (dvd_refl d)).1 h)
        rw [if_neg hdk, if_pos hle, if_neg hdk', if_neg hk0]; ring
      · rw [if_neg hdk, if_neg hle, if_neg hk0]; ring

/-- Gaussian integers modulo 2. -/
abbrev Q := GaussianInt ⧸ Ideal.span {(2 : GaussianInt)}

/-- The reduction map. -/
noncomputable abbrev pr : GaussianInt →+* Q := Ideal.Quotient.mk _

lemma two_eq_zero : (2 : Q) = 0 := by
  rw [← map_ofNat pr 2]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

lemma gi_mul_gi : gi * gi = -1 := by decide

lemma j_mul_j : pr gi * pr gi = 1 := by
  rw [← map_mul, gi_mul_gi, map_neg, map_one]
  calc (-1 : Q) = -1 + 2 := by rw [two_eq_zero, add_zero]
    _ = 1 := by ring

lemma map_summand (n : ℕ) (hn : 1 ≤ n) :
    map pr (summand n) = C (pr gi) ^ n * G (pr gi) n := by
  set B : PowerSeries GaussianInt := 1 + C gi * X ^ n with hBdef
  have hu : IsUnit (B ^ (n + 1)) := by
    apply IsUnit.pow
    rw [isUnit_iff_constantCoeff]
    simp [B, zero_pow (by omega : n ≠ 0)]
  have hw : B ^ (n + 1) * Ring.inverse (B ^ (n + 1)) = 1 := Ring.mul_inverse_cancel _ hu
  set v := map pr (Ring.inverse (B ^ (n + 1)))
  set j := pr gi
  have hB : map pr B = 1 + C j * X ^ n := by simp [B, j]
  have hv : (1 + C j * X ^ n) ^ (n + 1) * v = 1 := by
    have := congrArg (map pr) hw
    rw [map_mul, map_pow, hB, map_one] at this
    exact this
  have hg := one_add_mul_G two_eq_zero j n hn
  have hfac : (X ^ n + C j : PowerSeries Q) = C j * (1 + C j * X ^ n) := by
    have : C j * C j = (1 : PowerSeries Q) := by rw [← map_mul, j_mul_j, map_one]
    linear_combination (-X ^ n) * this
  have hs : map pr (summand n) = (X ^ n + C j) ^ n * v := by
    simp only [summand, map_mul, map_pow, map_add, map_X, map_C, v, j]
    rfl
  rw [hs, hfac, mul_pow]
  calc C j ^ n * (1 + C j * X ^ n) ^ n * v
      = C j ^ n * ((1 + C j * X ^ n) ^ n * v) * 1 := by ring
    _ = C j ^ n * ((1 + C j * X ^ n) ^ n * v) * ((1 + C j * X ^ n) * G j n) := by rw [hg]
    _ = C j ^ n * ((1 + C j * X ^ n) ^ (n + 1) * v) * G j n := by ring
    _ = C j ^ n * G j n := by rw [hv, mul_one]

lemma coeff_map_sum (m : ℕ) :
    pr (coeff m (∑ n ∈ Finset.Icc 1 m, summand n)) =
      pr (∑ n ∈ Finset.Icc 1 m, if n ∣ m then gi ^ (n + m / n) else 0) := by
  rw [← coeff_map, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  rw [map_summand n hn.1, ← map_pow, coeff_C_mul, G, coeff_mk, apply_ite pr, map_zero, map_pow]
  by_cases hd : n ∣ m
  · rw [if_pos hd, if_pos hd, pow_add]
  · rw [if_neg hd, if_neg hd, mul_zero]

lemma re_gi_pow : ∀ k : ℕ, (((gi ^ k).re : ℤ) : ZMod 2) = if Even k then 1 else 0
  | 0 => by simp
  | 1 => by simp [gi]
  | k + 2 => by
    have : gi ^ (k + 2) = -gi ^ k := by rw [pow_add, pow_two, gi_mul_gi, mul_neg_one]
    rw [this, Zsqrtd.re_neg, Int.cast_neg, ZMod.neg_eq_self_mod_two, re_gi_pow k]
    simp [Nat.even_add]

lemma sum_antidiag_symm {M : Type*} [AddCommGroup M] (h2 : ∀ x : M, x + x = 0) (N : ℕ)
    (f : ℕ × ℕ → M) (hf : ∀ p, f p.swap = f p) :
    ∑ p ∈ N.divisorsAntidiagonal, f p =
      ∑ p ∈ N.divisorsAntidiagonal.filter (fun p => p.1 = p.2), f p := by
  classical
  set D := N.divisorsAntidiagonal
  rw [← Finset.sum_filter_add_sum_filter_not D (fun p => p.1 < p.2),
    ← Finset.sum_filter_add_sum_filter_not (D.filter fun p => ¬ p.1 < p.2) (fun p => p.1 = p.2),
    Finset.filter_filter, Finset.filter_filter]
  have hgt : ∑ p ∈ D.filter (fun p => ¬ p.1 < p.2 ∧ ¬ p.1 = p.2), f p =
      ∑ p ∈ D.filter (fun p => p.1 < p.2), f p := by
    apply Finset.sum_nbij' Prod.swap Prod.swap
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      refine ⟨Nat.swap_mem_divisorsAntidiagonal.2 hp.1, ?_⟩
      simp only [Prod.fst_swap, Prod.snd_swap]; omega
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      refine ⟨Nat.swap_mem_divisorsAntidiagonal.2 hp.1, ?_⟩
      simp only [Prod.fst_swap, Prod.snd_swap]; omega
    · intro p _; exact Prod.swap_swap p
    · intro p _; exact Prod.swap_swap p
    · intro p _; exact (hf p).symm
  have hfil : D.filter (fun p => ¬ p.1 < p.2 ∧ p.1 = p.2) = D.filter (fun p => p.1 = p.2) := by
    apply Finset.filter_congr
    intro p _
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by omega, h⟩
  rw [hgt, hfil, add_left_comm, h2, add_zero]

open Classical in
lemma card_diag (N : ℕ) (hN : N ≠ 0) :
    (N.divisorsAntidiagonal.filter (fun p => p.1 = p.2)).card = if ∃ d, d * d = N then 1 else 0 := by
  split_ifs with hex
  · obtain ⟨d, hd⟩ := hex
    rw [Finset.card_eq_one]
    refine ⟨(d, d), ?_⟩
    ext p
    rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hp, _⟩, he⟩
      have : p.1 = d := by
        rw [he] at hp
        rw [← hd] at hp
        rw [he]; exact Nat.mul_self_inj.1 hp
      exact Prod.ext this (by rw [← he]; exact this)
    · rintro rfl
      exact ⟨⟨hd, hN⟩, rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp he
    rw [Nat.mem_divisorsAntidiagonal] at hp
    exact hex ⟨p.1, by rw [he] at hp ⊢; exact hp.1⟩

/-- The real part, reduced mod 2, as an additive map. -/
def reMod2 : GaussianInt →+ ZMod 2 where
  toFun z := ((z.re : ℤ) : ZMod 2)
  map_zero' := by simp
  map_add' z w := by rw [Zsqrtd.re_add, Int.cast_add]

open Classical in
lemma a_mod_two (m : ℕ) (hm : 1 ≤ m) :
    ((a m : ℤ) : ZMod 2) = if ∃ d, d * d = m then 1 else 0 := by
  set z := coeff m (∑ n ∈ Finset.Icc 1 m, summand n)
  set w := ∑ n ∈ Finset.Icc 1 m, if n ∣ m then gi ^ (n + m / n) else 0
  have hzw : reMod2 z = reMod2 w := by
    have h := coeff_map_sum m
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
    obtain ⟨t, ht⟩ := h
    have hre := congrArg Zsqrtd.re ht
    rw [Zsqrtd.re_sub, Zsqrtd.re_mul] at hre
    simp only [reMod2, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    have : z.re = w.re + 2 * t.re := by
      have h2re : (2 : GaussianInt).re = 2 := rfl
      have h2im : (2 : GaussianInt).im = 0 := rfl
      rw [h2re, h2im] at hre
      linarith
    rw [this, Int.cast_add, Int.cast_mul]
    have : ((2 : ℤ) : ZMod 2) = 0 := by decide
    rw [this, zero_mul, add_zero]
  have ha : ((a m : ℤ) : ZMod 2) = reMod2 z := by
    simp only [a, if_neg (by omega : m ≠ 0)]; rfl
  rw [ha, hzw, map_sum]
  simp only [apply_ite reMod2, map_zero]
  have hre : ∀ k, reMod2 (gi ^ k) = if Even k then 1 else 0 := fun k => re_gi_pow k
  simp only [hre]
  have key := Nat.sum_divisorsAntidiagonal (fun d e => (if Even (d + e) then 1 else 0 : ZMod 2))
    (n := m)
  have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by ext x; simp
  rw [Nat.divisors, Finset.sum_filter, ← hIcc] at key
  rw [← key, sum_antidiag_symm (fun x => by decide +revert) m
    (fun p => (if Even (p.1 + p.2) then 1 else 0 : ZMod 2))
    (fun p => by simp only [Prod.fst_swap, Prod.snd_swap, add_comm])]
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ZMod 2)), Finset.sum_const, nsmul_eq_mul, mul_one,
    card_diag m (by omega)]
  · split_ifs <;> simp
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [if_pos (by rw [hp.2]; exact ⟨p.2, rfl⟩)]

end A323689P

open A323689P OMA.S_oeis_a323689 in
theorem OMA.solution : type_of% @OMA.S_oeis_a323689.main := by
  intro m hm
  rw [← ZMod.intCast_eq_one_iff_odd, a_mod_two m hm]
  constructor
  · intro h
    split_ifs at h with hex
    · obtain ⟨d, hd⟩ := hex
      exact ⟨d, by rw [← hd, pow_two]⟩
    · exact absurd h (by decide)
  · rintro ⟨k, rfl⟩
    rw [if_pos ⟨k, by rw [pow_two]⟩]
