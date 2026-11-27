import FormalConjectures.ErdosProblems.«1160»

-- Reduction Erdos1160.erdos_1160.variants.sum.R2 of Erdős Problem 1160 — sum
-- Credit: @exehamza
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Filter Finset Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R2

def H1 : Prop :=
  ∀ᶠ m : ℕ in atTop, 2 * ∑ k ∈ Finset.range m, g (2 ^ k) ≤ g (2 ^ m)

def H2 : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ n ∈ Finset.Ico 1 (2 ^ m), (¬ ∃ k : ℕ, n = 2 ^ k) →
    g n ≤ 2 ^ (m - 1) * g (2 ^ (m - 2))

def H3 : Prop :=
  ∀ᶠ m : ℕ in atTop, 2 ^ (2 * m) * g (2 ^ (m - 2)) ≤ g (2 ^ m)

theorem main : H1 → H2 → H3 → type_of% @Erdos1160.erdos_1160.variants.sum := by
  intro h_pow2 h_non_pow2 h_step
  filter_upwards [h_pow2, h_non_pow2, h_step, eventually_ge_atTop 1] with
    m hm_pow2 hm_non_pow2 hm_step hm1
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 (2 ^ m)) (fun n => ∃ k : ℕ, n = 2 ^ k)]
  have h1 :
      2 * ∑ n ∈ (Finset.Ico 1 (2 ^ m)).filter (fun n => ∃ k : ℕ, n = 2 ^ k), g n ≤
        g (2 ^ m) := by
    have h_subset :
        (Finset.Ico 1 (2 ^ m)).filter (fun n => ∃ k : ℕ, n = 2 ^ k) ⊆
          (Finset.range m).image (fun k => 2 ^ k) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, Finset.mem_range] at hn ⊢
      rcases hn with ⟨⟨_, hn_lt⟩, k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hn_lt
    have h_sum_le :
        ∑ n ∈ (Finset.Ico 1 (2 ^ m)).filter (fun n => ∃ k : ℕ, n = 2 ^ k), g n ≤
          ∑ k ∈ Finset.range m, g (2 ^ k) := by
      calc
        ∑ n ∈ (Finset.Ico 1 (2 ^ m)).filter (fun n => ∃ k : ℕ, n = 2 ^ k), g n
          ≤ ∑ n ∈ (Finset.range m).image (fun k => 2 ^ k), g n :=
            Finset.sum_le_sum_of_subset h_subset
        _ = ∑ k ∈ Finset.range m, g (2 ^ k) := by
            refine Finset.sum_image (fun a _ b _ hab => ?_)
            by_contra hne
            rcases lt_trichotomy a b with hlt | rfl | hgt
            · exact ((Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mpr hlt).ne hab
            · exact hne rfl
            · exact ((Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mpr hgt).ne hab.symm
    omega
  have h2 :
      2 * ∑ n ∈ (Finset.Ico 1 (2 ^ m)).filter (fun n => ¬ ∃ k : ℕ, n = 2 ^ k), g n ≤
        g (2 ^ m) := by
    set S := (Finset.Ico 1 (2 ^ m)).filter (fun n => ¬ ∃ k : ℕ, n = 2 ^ k)
    have h_exp : (m + 1) + (m - 1) = 2 * m := by omega
    have h_pointwise : ∀ n ∈ S, 2 ^ (m + 1) * g n ≤ g (2 ^ m) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      calc
        2 ^ (m + 1) * g n
          ≤ 2 ^ (m + 1) * (2 ^ (m - 1) * g (2 ^ (m - 2))) :=
            Nat.mul_le_mul_left _ (hm_non_pow2 n hn.1 hn.2)
        _ = 2 ^ ((m + 1) + (m - 1)) * g (2 ^ (m - 2)) := by
            rw [← mul_assoc, ← pow_add]
        _ = 2 ^ (2 * m) * g (2 ^ (m - 2)) := by
            rw [h_exp]
        _ ≤ g (2 ^ m) := hm_step
    have h_sum :
        2 ^ (m + 1) * ∑ n ∈ S, g n ≤ S.card * g (2 ^ m) := by
      rw [Finset.mul_sum]
      calc
        ∑ n ∈ S, 2 ^ (m + 1) * g n
          ≤ ∑ _n ∈ S, g (2 ^ m) := Finset.sum_le_sum h_pointwise
        _ = S.card * g (2 ^ m) := by rw [Finset.sum_const, smul_eq_mul]
    have h_card : S.card ≤ 2 ^ m := by
      calc
        S.card ≤ (Finset.Ico 1 (2 ^ m)).card := Finset.card_filter_le _ _
        _ = 2 ^ m - 1 := Nat.card_Ico 1 (2 ^ m)
        _ ≤ 2 ^ m := Nat.sub_le _ _
    have h_mul :
        2 ^ m * (2 * ∑ n ∈ S, g n) ≤ 2 ^ m * g (2 ^ m) := by
      calc
        2 ^ m * (2 * ∑ n ∈ S, g n)
          = 2 ^ (m + 1) * ∑ n ∈ S, g n := by
            rw [pow_succ, mul_assoc]
        _ ≤ S.card * g (2 ^ m) := h_sum
        _ ≤ 2 ^ m * g (2 ^ m) := Nat.mul_le_mul_right _ h_card
    exact Nat.le_of_mul_le_mul_left h_mul (Nat.two_pow_pos m)
  omega

end OMA.R_Erdos1160_erdos_1160_variants_sum_R2
