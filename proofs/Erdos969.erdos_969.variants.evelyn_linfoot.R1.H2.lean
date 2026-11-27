import OMAReductions.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1
import Mathlib

-- Step Erdos969.erdos_969.variants.evelyn_linfoot.R1.H2: hypothesis H2 of reduction
-- Erdos969.erdos_969.variants.evelyn_linfoot.R1
-- Credit: @ivillar
--
-- Proof. Q(n) - Q(n - 1) is the indicator of squarefree n for n ≥ 1. Every n ≥ 1 is uniquely
-- a squarefree number times a square (the squarefree part is read off the parities of the
-- exponents), so the Dirichlet convolution of the squarefree indicator with the indicator of
-- the squares is the constant 1 on n ≥ 1. The L-series of the squares indicator at s is
-- ζ(2 s) (reindex by m ↦ m ^ 2), both indicators are bounded so their L-series converge
-- absolutely for Re s > 1, and the L-series of 1 is ζ(s).

open LSeries Complex Finset

namespace OMA.Erdos969H2

open scoped Classical

/-- The indicator of the squarefree numbers. -/
noncomputable def sqf (n : ℕ) : ℂ := if Squarefree n then 1 else 0

/-- The indicator of the perfect squares. -/
noncomputable def sqi (n : ℕ) : ℂ := if IsSquare n then 1 else 0

lemma count_diff (n : ℕ) (hn : n ≠ 0) :
    ((Erdos969.squarefreeCounting n : ℂ) - (Erdos969.squarefreeCounting (n - 1) : ℂ)) = sqf n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Erdos969.squarefreeCounting]
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ m + 1), Finset.filter_insert]
  have hnot : m + 1 ∉ Finset.Icc 1 m := by simp
  unfold sqf
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hnot])]
    push_cast
    ring
  · ring

lemma sqf_bound (n : ℕ) : ‖sqf n‖ ≤ 1 := by
  unfold sqf; split_ifs <;> simp

lemma sqi_bound (n : ℕ) : ‖sqi n‖ ≤ 1 := by
  unfold sqi; split_ifs <;> simp

/-- A squarefree number times a square determines the squarefree number. -/
lemma sqf_part_unique {a a' b b' : ℕ} (ha : Squarefree a) (ha' : Squarefree a')
    (hb : b ≠ 0) (hb' : b' ≠ 0) (h : a * b ^ 2 = a' * b' ^ 2) : a = a' := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have ha0' : a' ≠ 0 := ha'.ne_zero
  apply Nat.eq_of_factorization_eq ha0 ha0'
  intro p
  have hf := congrArg (fun x => Nat.factorization x p) h
  simp only [Nat.factorization_mul ha0 (pow_ne_zero 2 hb),
    Nat.factorization_mul ha0' (pow_ne_zero 2 hb'), Nat.factorization_pow, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul] at hf
  have h1 := ha.natFactorization_le_one p
  have h2 := ha'.natFactorization_le_one p
  omega

lemma conv_eq_one (n : ℕ) (hn : n ≠ 0) : (LSeries.convolution sqf sqi) n = 1 := by
  rw [convolution_def]
  simp only
  have hterm : ∀ p ∈ n.divisorsAntidiagonal, sqf p.1 * sqi p.2 =
      if (Squarefree p.1 ∧ IsSquare p.2) then 1 else 0 := by
    intro p _
    unfold sqf sqi
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
  obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn)
  have hfilter : n.divisorsAntidiagonal.filter (fun p => Squarefree p.1 ∧ IsSquare p.2) =
      {(a, b ^ 2)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hxy, -⟩, hx, ⟨c, rfl⟩⟩
      have hc : c ≠ 0 := by
        rintro rfl
        simp at hxy
        exact hn hxy.symm
      have hxa : x = a := sqf_part_unique hx hsq hc hb.ne' (by rw [show x * c ^ 2 = x * (c * c) by ring, hxy, ← hab]; ring)
      subst hxa
      refine ⟨rfl, ?_⟩
      have : x * (c * c) = x * b ^ 2 := by rw [hxy, ← hab]; ring
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hx.ne_zero) this
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨by rw [← hab]; ring, hn⟩, hsq, ⟨b, by ring⟩⟩
  rw [hfilter, Finset.card_singleton]
  simp

lemma LSeries_sqi {s : ℂ} (hs : 1 < s.re) : LSeries sqi s = riemannZeta (2 * s) := by
  have h2s : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  rw [← LSeries_one_eq_riemannZeta h2s, LSeries, LSeries]
  have hinj : Function.Injective (fun m : ℕ => m ^ 2) := Nat.pow_left_injective (by norm_num)
  have hsupp : Function.support (term sqi s) ⊆ Set.range (fun m : ℕ => m ^ 2) := by
    intro n hn
    rw [Function.mem_support] at hn
    by_contra hnot
    apply hn
    rw [term_def]
    split_ifs with h0
    · rfl
    · have : ¬ IsSquare n := by
        rintro ⟨r, rfl⟩
        exact hnot ⟨r, by ring⟩
      simp [sqi, this]
  rw [← hinj.tsum_eq hsupp]
  congr 1
  ext m
  simp only [term_def]
  by_cases hm : m = 0
  · subst hm
    simp
  · have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
    rw [if_neg hm2, if_neg hm]
    have hsq : IsSquare (m ^ 2) := ⟨m, by ring⟩
    simp only [sqi, hsq, if_true, Pi.one_apply]
    congr 1
    rw [Nat.cast_pow]
    have := natCast_cpow_natCast_mul m 2 s
    push_cast at this
    rw [this]

end OMA.Erdos969H2

open OMA.Erdos969H2 in
theorem OMA.solution : OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1.H2 := by
  unfold OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1.H2
  intro s hs
  have hF : LSeries (fun n : ℕ => (Erdos969.squarefreeCounting n : ℂ) -
      (Erdos969.squarefreeCounting (n - 1) : ℂ)) s = LSeries sqf s :=
    LSeries_congr (fun {n} hn => count_diff n hn) s
  have hf : LSeriesSummable sqf s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => sqf_bound n) hs
  have hg : LSeriesSummable sqi s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => sqi_bound n) hs
  have hconv : LSeries (LSeries.convolution sqf sqi) s = LSeries 1 s :=
    LSeries_congr (fun {n} hn => by rw [conv_eq_one n hn]; rfl) s
  rw [hF, ← LSeries_sqi hs, ← LSeries_convolution' hf hg, hconv, LSeries_one_eq_riemannZeta hs]
