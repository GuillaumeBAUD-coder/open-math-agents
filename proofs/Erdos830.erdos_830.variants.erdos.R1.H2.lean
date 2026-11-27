import OMAReductions.R_Erdos830_erdos_830_variants_erdos_R1
import Mathlib.Tactic

/-! Proof of H2 for `Erdos830.erdos_830.variants.erdos.R1` (Erdős, Lemma 3):
the contribution from divisors above `B` is small in density. -/

open scoped ArithmeticFunction.sigma Classical
open Finset Filter

namespace Erdos830R1H2

private lemma card_filter_dvd_le (N d : ℕ) (hd : 0 < d) :
    ((Icc 1 N).filter (fun n => d ∣ n)).card ≤ N / d := by
  have hmaps : Set.MapsTo (fun n => n / d)
      ((((Icc 1 N).filter (fun n => d ∣ n)) : Finset ℕ) : Set ℕ)
      (((Icc 1 (N / d)) : Finset ℕ) : Set ℕ) := by
    intro n hn
    simp only [mem_coe, mem_filter, mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hnN⟩, hdvd⟩ := hn
    refine ⟨?_, Nat.div_le_div_right hnN⟩
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd
  have hinj : Set.InjOn (fun n => n / d)
      ((((Icc 1 N).filter (fun n => d ∣ n)) : Finset ℕ) : Set ℕ) := by
    intro a ha b hb hab
    dsimp only at hab
    simp only [mem_coe, mem_filter] at ha hb
    have h1 : d * (a / d) = a := Nat.mul_div_cancel' ha.2
    have h2 : d * (b / d) = b := Nat.mul_div_cancel' hb.2
    rw [← h1, ← h2, hab]
  calc
    ((Icc 1 N).filter (fun n => d ∣ n)).card
        ≤ (Icc 1 (N / d)).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = N / d := by simp

private lemma sum_inv_sq_le (B : ℕ) (hB : 0 < B) :
    ∀ N : ℕ, ∑ d ∈ Icc (B + 1) N, (1 : ℝ) / ((d : ℝ) * (d : ℝ)) ≤
      1 / (B : ℝ) - 1 / ((max B N : ℕ) : ℝ)
  | 0 => by
    simp
  | N + 1 => by
    by_cases h : N + 1 ≤ B
    · have hemp : Icc (B + 1) (N + 1) = ∅ := by
        ext x
        simp only [mem_Icc, notMem_empty, iff_false, not_and, not_le]
        omega
      rw [hemp, sum_empty, Nat.max_eq_left h, sub_self]
    · have hBN : B ≤ N := by omega
      have hmax1 : max B N = N := Nat.max_eq_right hBN
      have hmax2 : max B (N + 1) = N + 1 := Nat.max_eq_right (by omega)
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le hB hBN)
      have hN1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      have hins : Icc (B + 1) (N + 1) = insert (N + 1) (Icc (B + 1) N) := by
        ext x
        simp only [mem_Icc, mem_insert]
        omega
      have hnotmem : N + 1 ∉ Icc (B + 1) N := by
        simp only [mem_Icc, not_and, not_le]
        omega
      have ih := sum_inv_sq_le B hB N
      rw [hmax1] at ih
      rw [hins, sum_insert hnotmem, hmax2]
      have hstep : (1 : ℝ) / (((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ)) ≤
          1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ) := by
        have hle : (N : ℝ) * ((N + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) := by
          have h1 : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
          nlinarith
        have hdiv : (1 : ℝ) / (((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ)) ≤
            1 / ((N : ℝ) * ((N + 1 : ℕ) : ℝ)) :=
          one_div_le_one_div_of_le (by positivity) hle
        have hdiff : (1 : ℝ) / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ) =
            1 / ((N : ℝ) * ((N + 1 : ℕ) : ℝ)) := by
          push_cast
          field_simp
          ring
        linarith
      linarith

end Erdos830R1H2

theorem OMA.solution : OMA.R_Erdos830_erdos_830_variants_erdos_R1.H2 := by
  intro η ε hη hε
  let B : ℕ := Nat.ceil ((η * ε)⁻¹) + 1
  have hBpos : 0 < B := Nat.succ_pos _
  have hB_gt : (η * ε)⁻¹ < (B : ℝ) := by
    have h1 : (η * ε)⁻¹ ≤ (Nat.ceil ((η * ε)⁻¹) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil ((η * ε)⁻¹) : ℝ) < (B : ℝ) := by
      dsimp only [B]
      push_cast
      linarith
    linarith
  have hB_inv : (1 : ℝ) / (B : ℝ) ≤ η * ε := by
    have hηε : 0 < η * ε := mul_pos hη hε
    have hB_posR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hBpos
    rw [div_le_iff₀ hB_posR]
    have hmul : (η * ε) * (η * ε)⁻¹ < (η * ε) * (B : ℝ) :=
      mul_lt_mul_of_pos_left hB_gt hηε
    rw [mul_inv_cancel₀ hηε.ne'] at hmul
    linarith
  refine ⟨B, Filter.Eventually.of_forall fun N => ?_⟩
  let f (n : ℕ) : ℝ :=
    ((σ 1 n : ℝ) / n) - ∑ d ∈ n.divisors.filter (· ≤ B), (1 : ℝ) / d
  let S := (Icc 1 N).filter (fun n => η ≤ f n)
  have hf_eq : ∀ n ∈ Icc 1 N,
      f n = ∑ d ∈ n.divisors.filter (fun d => B < d), (1 : ℝ) / d := by
    intro n hn
    have hn_pos : 0 < n := (mem_Icc.mp hn).1
    dsimp only [f]
    rw [OMA.R_Erdos830_erdos_830_variants_erdos_R1.ratio_eq hn_pos]
    have hsplit := Finset.sum_filter_add_sum_filter_not n.divisors (· ≤ B) (fun d => (1 : ℝ) / d)
    have hfilt : n.divisors.filter (fun d => ¬ d ≤ B) = n.divisors.filter (fun d => B < d) := by
      ext d
      simp only [mem_filter, Nat.not_le]
    rw [hfilt] at hsplit
    linarith
  have hmarkov : (S.card : ℝ) * η ≤ ∑ n ∈ Icc 1 N, f n := by
    have h1 : (S.card : ℝ) * η = ∑ _n ∈ S, η := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ _n ∈ S, η ≤ ∑ n ∈ S, f n := by
      refine Finset.sum_le_sum fun n hn => (mem_filter.mp hn).2
    have h3 : ∑ n ∈ S, f n ≤ ∑ n ∈ Icc 1 N, f n := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n hn _ => ?_
      rw [hf_eq n hn]
      exact Finset.sum_nonneg fun d _ => by positivity
    linarith
  have hdouble : ∑ n ∈ Icc 1 N, f n =
      ∑ d ∈ Icc (B + 1) N,
        (((Icc 1 N).filter (fun n => d ∣ n)).card : ℝ) * ((1 : ℝ) / d) := by
    calc
      ∑ n ∈ Icc 1 N, f n
          = ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors.filter (fun d => B < d), (1 : ℝ) / d := by
            refine Finset.sum_congr rfl fun n hn => hf_eq n hn
      _ = ∑ n ∈ Icc 1 N, ∑ d ∈ (Icc (B + 1) N).filter (fun d => d ∣ n), (1 : ℝ) / d := by
            refine Finset.sum_congr rfl fun n hn => ?_
            have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
            have hnN : n ≤ N := (mem_Icc.mp hn).2
            congr 1
            ext d
            simp only [mem_filter, Nat.mem_divisors, mem_Icc]
            constructor
            · rintro ⟨⟨hdvd, _⟩, hBd⟩
              have hdn : d ≤ n := Nat.le_of_dvd (by omega) hdvd
              exact ⟨⟨by omega, le_trans hdn hnN⟩, hdvd⟩
            · rintro ⟨⟨hBd, _⟩, hdvd⟩
              exact ⟨⟨hdvd, by omega⟩, by omega⟩
      _ = ∑ n ∈ Icc 1 N, ∑ d ∈ Icc (B + 1) N, if d ∣ n then (1 : ℝ) / d else 0 := by
            refine Finset.sum_congr rfl fun n _ => Finset.sum_filter _ _
      _ = ∑ d ∈ Icc (B + 1) N, ∑ n ∈ Icc 1 N, if d ∣ n then (1 : ℝ) / d else 0 :=
            Finset.sum_comm
      _ = ∑ d ∈ Icc (B + 1) N,
            (((Icc 1 N).filter (fun n => d ∣ n)).card : ℝ) * ((1 : ℝ) / d) := by
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hbound_sum : ∑ n ∈ Icc 1 N, f n ≤ (N : ℝ) * (1 / (B : ℝ)) := by
    rw [hdouble]
    have hterm : ∑ d ∈ Icc (B + 1) N,
        (((Icc 1 N).filter (fun n => d ∣ n)).card : ℝ) * ((1 : ℝ) / d) ≤
        ∑ d ∈ Icc (B + 1) N, (N : ℝ) * ((1 : ℝ) / ((d : ℝ) * (d : ℝ))) := by
      refine Finset.sum_le_sum fun d hd => ?_
      have hd_pos : 0 < d := by
        have := (mem_Icc.mp hd).1
        omega
      have hcard : (((Icc 1 N).filter (fun n => d ∣ n)).card : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
        have hnat : ((Icc 1 N).filter (fun n => d ∣ n)).card ≤ N / d :=
          Erdos830R1H2.card_filter_dvd_le N d hd_pos
        exact le_trans (by exact_mod_cast hnat) Nat.cast_div_le
      have hmul := mul_le_mul_of_nonneg_right hcard (show (0 : ℝ) ≤ 1 / (d : ℝ) by positivity)
      calc
        (((Icc 1 N).filter (fun n => d ∣ n)).card : ℝ) * ((1 : ℝ) / d)
            ≤ ((N : ℝ) / d) * ((1 : ℝ) / d) := hmul
        _ = (N : ℝ) * ((1 : ℝ) / ((d : ℝ) * (d : ℝ))) := by ring
    have htel := Erdos830R1H2.sum_inv_sq_le B hBpos N
    have htel' : ∑ d ∈ Icc (B + 1) N, (1 : ℝ) / ((d : ℝ) * (d : ℝ)) ≤ 1 / (B : ℝ) := by
      have hnonneg : (0 : ℝ) ≤ 1 / ((max B N : ℕ) : ℝ) := by positivity
      linarith
    calc
      ∑ d ∈ Icc (B + 1) N,
          (((Icc 1 N).filter (fun n => d ∣ n)).card : ℝ) * ((1 : ℝ) / d)
          ≤ ∑ d ∈ Icc (B + 1) N, (N : ℝ) * ((1 : ℝ) / ((d : ℝ) * (d : ℝ))) := hterm
      _ = (N : ℝ) * ∑ d ∈ Icc (B + 1) N, (1 : ℝ) / ((d : ℝ) * (d : ℝ)) := by
            rw [← Finset.mul_sum]
      _ ≤ (N : ℝ) * (1 / (B : ℝ)) :=
            mul_le_mul_of_nonneg_left htel' (by positivity)
  have hfinal : (S.card : ℝ) * η ≤ (ε * (N : ℝ)) * η := by
    calc
      (S.card : ℝ) * η ≤ ∑ n ∈ Icc 1 N, f n := hmarkov
      _ ≤ (N : ℝ) * (1 / (B : ℝ)) := hbound_sum
      _ ≤ (N : ℝ) * (η * ε) := mul_le_mul_of_nonneg_left hB_inv (by positivity)
      _ = (ε * (N : ℝ)) * η := by ring
  exact le_of_mul_le_mul_right hfinal hη
