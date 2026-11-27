import OMAReductions.R_Erdos688_erdos_688_variants_lglglg_over_lglg_is_big_o_R1
import Mathlib.NumberTheory.Chebyshev

open Filter Finset

namespace OMACheb

lemma count_add (m n : ℕ) (hmn : m ≤ n) :
    ((Finset.Ioc m n).filter Nat.Prime).card + Nat.primeCounting m = Nat.primeCounting n := by
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting]
  have hdisj : Disjoint ((Finset.Ioc m n).filter Nat.Prime) (Nat.primesLE m) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    have := Nat.le_of_mem_primesLE hq
    omega
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext p
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
  constructor
  · rintro (⟨⟨_, h2⟩, h3⟩ | ⟨h1, h2⟩)
    · exact ⟨h2, h3⟩
    · exact ⟨h1.trans hmn, h2⟩
  · rintro ⟨h1, h2⟩
    by_cases h : p ≤ m
    · right; exact ⟨h, h2⟩
    · left; exact ⟨⟨by omega, h1⟩, h2⟩

end OMACheb

theorem OMA.solution : OMA.R_Erdos688_erdos_688_variants_lglglg_over_lglg_is_big_o_R1.H3 := by
  have ht : Tendsto (fun n : ℕ => ((n / 4 : ℕ) : ℝ)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨4 * ⌈b⌉₊, fun n hn => ?_⟩
    have h1 : ⌈b⌉₊ ≤ n / 4 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      omega
    exact (Nat.le_ceil b).trans (by exact_mod_cast h1)
  have hB := ht.eventually (Chebyshev.eventually_primeCounting_le (ε := 1 / 100) (by norm_num))
  have hL : ∀ᶠ n : ℕ in atTop, 44 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 44
  have hsmall : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ 1 / 200 * (n : ℝ) := by
    have hb := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 200 by norm_num)
    have hb' := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually hb
    filter_upwards [hb'] with n hn
    have h1 : Real.log (n : ℝ) ≤ ‖Real.log (n : ℝ)‖ := Real.le_norm_self _
    have h2 : ‖(id (n : ℝ))‖ = n := by simp
    rw [h2] at hn
    linarith
  filter_upwards [hB, hL, hsmall, eventually_ge_atTop 8] with n hBn hLn hsm hn8
  simp only [Nat.floor_natCast] at hBn
  have hl2a : (0.6931 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hl2b : Real.log 2 < (0.6932 : ℝ) := by
    have := Real.log_two_lt_d9; linarith
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (n : ℝ) := ⟨_, rfl⟩
  rw [← hLdef] at hLn hsm ⊢
  have hLpos : 0 < L := by linarith
  -- lower bound for π n
  have hA := Chebyshev.pi_ge n
  rw [← hLdef, div_le_iff₀ hLpos] at hA
  have hlog1 : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + L := by
    rw [hLdef, ← Real.log_mul (by norm_num) hn0.ne']
    apply Real.log_le_log (by linarith)
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    linarith
  -- upper bound for π (n / 4)
  obtain ⟨m, hm⟩ : ∃ m, m = n / 4 := ⟨_, rfl⟩
  rw [← hm] at hBn ⊢
  have hm1 : (m : ℝ) ≤ (n : ℝ) / 4 := by
    rw [hm]; exact Nat.cast_div_le
  have hm2 : (n : ℝ) / 8 ≤ (m : ℝ) := by
    have h : n ≤ 8 * m := by omega
    have h' : (n : ℝ) ≤ 8 * (m : ℝ) := by exact_mod_cast h
    linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hlogm : L / 1.05 ≤ Real.log (m : ℝ) := by
    have h1 : Real.log ((n : ℝ) / 8) ≤ Real.log (m : ℝ) := Real.log_le_log (by positivity) hm2
    rw [Real.log_div hn0.ne' (by norm_num), ← hLdef, hl8] at h1
    have h2 : L / 1.05 ≤ L - 3 * Real.log 2 := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    linarith
  have hlogm0 : 0 < L / 1.05 := by positivity
  have hpm : (Nat.primeCounting m : ℝ) ≤ 0.366555 * (n : ℝ) / L := by
    have h1 : (Real.log 4 + 1 / 100) * (m : ℝ) / Real.log (m : ℝ) ≤
        1.3964 * ((n : ℝ) / 4) / (L / 1.05) := by
      apply div_le_div₀ (by positivity) _ hlogm0 hlogm
      rw [hl4]
      have : (2 * Real.log 2 + 1 / 100) * (m : ℝ) ≤ 1.3964 * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hm0.le
      nlinarith
    have h2 : (1.3964 : ℝ) * ((n : ℝ) / 4) / (L / 1.05) = 0.366555 * (n : ℝ) / L := by
      field_simp
      ring
    linarith
  have hpmL : (Nat.primeCounting m : ℝ) * L ≤ 0.366555 * (n : ℝ) := by
    rwa [le_div_iff₀ hLpos] at hpm
  -- combine
  have hcount := OMACheb.count_add m n (by omega)
  have hcountR : (((Finset.Ioc m n).filter Nat.Prime).card : ℝ) + (Nat.primeCounting m : ℝ) =
      (Nat.primeCounting n : ℝ) := by exact_mod_cast hcount
  rw [div_le_iff₀ (by positivity)]
  have hn44 : (44 : ℝ) ≤ 1 / 200 * (n : ℝ) := by linarith
  have key : (n : ℝ) / 4 ≤ (((Finset.Ioc m n).filter Nat.Prime).card : ℝ) * L := by
    have h3 : (((Finset.Ioc m n).filter Nat.Prime).card : ℝ) * L =
        (Nat.primeCounting n : ℝ) * L - (Nat.primeCounting m : ℝ) * L := by
      rw [← hcountR]; ring
    have h4 : 0.6931 * (n : ℝ) ≤ (n : ℝ) * Real.log 2 :=
      by nlinarith
    rw [h3]
    linarith
  linarith
