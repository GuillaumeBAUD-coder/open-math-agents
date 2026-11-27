import OMAReductions.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1
import Mathlib.NumberTheory.LSeries.Dirichlet

open Finset

namespace OMASqfree

/-- Indicator of squarefree numbers. -/
noncomputable def f (n : ℕ) : ℂ := if Squarefree n then 1 else 0

/-- Indicator of positive perfect squares. -/
noncomputable def g (n : ℕ) : ℂ := if n ≠ 0 ∧ IsSquare n then 1 else 0

lemma diff_eq (n : ℕ) (hn : n ≠ 0) :
    (Erdos969.squarefreeCounting n : ℂ) - (Erdos969.squarefreeCounting (n - 1) : ℂ) = f n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hI : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : k + 1 ∉ (Finset.Icc 1 k).filter Squarefree := by
    simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  unfold Erdos969.squarefreeCounting f
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [hI, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem hnot]; push_cast; ring
  · ring

lemma sqfree_unique {d d' m m' : ℕ} (hd : Squarefree d) (hd' : Squarefree d')
    (hm : m ≠ 0) (hm' : m' ≠ 0) (h : d * (m * m) = d' * (m' * m')) : d = d' := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have hd0' : d' ≠ 0 := hd'.ne_zero
  apply Nat.eq_of_factorization_eq hd0 hd0'
  intro p
  have h1 : (d * (m * m)).factorization p = (d' * (m' * m')).factorization p := by rw [h]
  rw [Nat.factorization_mul hd0 (mul_ne_zero hm hm), Nat.factorization_mul hm hm,
    Nat.factorization_mul hd0' (mul_ne_zero hm' hm'), Nat.factorization_mul hm' hm'] at h1
  simp only [Finsupp.coe_add, Pi.add_apply] at h1
  have h2 := hd.natFactorization_le_one p
  have h3 := hd'.natFactorization_le_one p
  omega

lemma conv_eq (n : ℕ) (hn : n ≠ 0) : LSeries.convolution f g n = (1 : ℕ → ℂ) n := by
  rw [LSeries.convolution_def]
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab; exact hn hab.symm
  have hmem : (a, b ^ 2) ∈ n.divisorsAntidiagonal := by
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨by rw [← hab]; ring, hn⟩
  simp only [Pi.one_apply]
  rw [Finset.sum_eq_single (a, b ^ 2)]
  · have hsq : IsSquare (b ^ 2) := ⟨b, by ring⟩
    simp [f, g, ha, hb0, hsq]
  · intro p hp hne
    rw [Nat.mem_divisorsAntidiagonal] at hp
    by_cases h1 : Squarefree p.1
    · by_cases h2 : p.2 ≠ 0 ∧ IsSquare p.2
      · exfalso
        obtain ⟨h20, m, hm⟩ := h2
        have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact h20 hm
        have hEq : p.1 * (m * m) = a * (b * b) := by
          rw [← hm, hp.1, ← hab]; ring
        have hpa : p.1 = a := sqfree_unique h1 ha hm0 hb0 hEq
        have ha0 : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
        have h2' : p.2 = b ^ 2 := by
          have : a * p.2 = a * b ^ 2 := by
            calc a * p.2 = p.1 * p.2 := by rw [hpa]
              _ = n := hp.1
              _ = a * b ^ 2 := by rw [← hab]; ring
          exact Nat.eq_of_mul_eq_mul_left ha0 this
        exact hne (Prod.ext hpa h2')
      · simp [g, h2]
    · simp [f, h1]
  · intro h; exact absurd hmem h

lemma lseries_g (s : ℂ) (hs : 1 < s.re) : LSeries g s = riemannZeta (2 * s) := by
  have hs2 : 1 < (2 * s).re := by simp; linarith
  have hs0 : (2 * s) ≠ 0 := by
    intro h; rw [h] at hs2; simp at hs2; linarith
  rw [zeta_eq_tsum_one_div_nat_cpow hs2]
  unfold LSeries
  have hinj : Function.Injective (fun m : ℕ => m * m) := by
    intro x y hxy
    exact Nat.mul_self_inj.1 hxy
  have hsupp : Function.support (LSeries.term g s) ⊆ Set.range (fun m : ℕ => m * m) := by
    intro n hn
    rw [Function.mem_support] at hn
    by_cases h0 : n = 0
    · subst h0; simp at hn
    · rw [LSeries.term_of_ne_zero h0] at hn
      by_cases hg : n ≠ 0 ∧ IsSquare n
      · obtain ⟨_, m, hm⟩ := hg
        exact ⟨m, hm.symm⟩
      · simp [g, hg] at hn
  rw [← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  · subst hm
    simp [Complex.zero_cpow hs0]
  · have hmm : m * m ≠ 0 := mul_ne_zero hm hm
    have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    rw [LSeries.term_of_ne_zero hmm]
    have hgv : g (m * m) = 1 := by
      unfold g; rw [if_pos ⟨hmm, m, rfl⟩]
    rw [hgv, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, two_mul, Complex.cpow_add _ _ hmc]

end OMASqfree

theorem OMA.solution : OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1.H2 := by
  intro s hs
  have h1 : LSeries (fun n : ℕ => (Erdos969.squarefreeCounting n : ℂ) -
      (Erdos969.squarefreeCounting (n - 1) : ℂ)) s = LSeries OMASqfree.f s :=
    LSeries_congr (fun {n} hn => OMASqfree.diff_eq n hn) s
  have hf : LSeriesSummable OMASqfree.f s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro n _
    unfold OMASqfree.f
    split_ifs <;> simp
  have hg : LSeriesSummable OMASqfree.g s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro n _
    unfold OMASqfree.g
    split_ifs <;> simp
  rw [h1, ← OMASqfree.lseries_g s hs, ← LSeries_convolution' hf hg,
    ← LSeries_one_eq_riemannZeta hs]
  exact LSeries_congr (fun {n} hn => OMASqfree.conv_eq n hn) s
