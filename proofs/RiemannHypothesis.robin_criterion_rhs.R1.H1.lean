import OMAReductions.R_RiemannHypothesis_robin_criterion_rhs_R1

namespace RobinH1Aux
open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Sum of `d + n / d` over divisors `d < k` of `n` with `d * d ≤ n`. -/
def T (n k : ℕ) : ℕ := ∑ d ∈ range k, if d ∣ n ∧ d * d ≤ n then d + n / d else 0

theorem sigma_le_T (n : ℕ) (hn : n ≠ 0) : σ 1 n ≤ T n (n + 1) := by
  classical
  rw [sigma_one_apply]
  set S := n.divisors.filter (fun d => d * d ≤ n) with hS
  have hsub : n.divisors ⊆ S ∪ S.image (fun d => n / d) := by
    intro e he
    have hen : e ∣ n := Nat.dvd_of_mem_divisors he
    by_cases hee : e * e ≤ n
    · exact mem_union_left _ (mem_filter.mpr ⟨he, hee⟩)
    · apply mem_union_right
      obtain ⟨d, hd⟩ := hen
      have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; exact hn hd)
      have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; exact hn hd)
      refine mem_image.mpr ⟨d, mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨e, by rw [hd]; ring⟩, hn⟩, ?_⟩, ?_⟩
      · have hlt : d < e := by
          by_contra hc; rw [not_lt] at hc
          apply hee; rw [hd]; exact Nat.mul_le_mul_left _ hc
        rw [hd]; exact Nat.mul_le_mul_right _ hlt.le
      · rw [hd, Nat.mul_div_cancel _ hd0]
  calc ∑ d ∈ n.divisors, d ≤ ∑ d ∈ S ∪ S.image (fun d => n / d), d :=
        sum_le_sum_of_subset hsub
    _ ≤ ∑ d ∈ S, d + ∑ d ∈ S.image (fun d => n / d), d := by
        rw [← sum_union_inter]; exact Nat.le_add_right _ _
    _ ≤ ∑ d ∈ S, d + ∑ d ∈ S, n / d := by
        gcongr
        exact sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
    _ = ∑ d ∈ S, (d + n / d) := by rw [sum_add_distrib]
    _ = T n (n + 1) := by
        unfold T
        rw [← sum_filter]
        apply sum_congr _ (fun _ _ => rfl)
        ext d
        simp only [hS, mem_filter, Nat.mem_divisors, mem_range]
        constructor
        · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h1), h1, h2⟩
        · rintro ⟨_, h1, h2⟩; exact ⟨⟨h1, hn⟩, h2⟩

theorem T_stable (n K : ℕ) (hK : n < K * K) : ∀ j, T n (K + j) = T n K := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← add_assoc, T, sum_range_succ, ← T, ih]
    have : ¬ ((K + j) ∣ n ∧ (K + j) * (K + j) ≤ n) := by
      rintro ⟨_, h⟩
      have := Nat.mul_le_mul (Nat.le_add_right K j) (Nat.le_add_right K j)
      omega
    rw [if_neg this, add_zero]

def tl (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => tl n k + (if Nat.beq (n % k) 0 && Nat.ble (k * k) n then k + n / k else 0)

theorem tl_eq (n : ℕ) : ∀ k, tl n k = T n k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [tl, T, sum_range_succ, ← T, ih]
    congr 1
    have e : (Nat.beq (n % k) 0 && Nat.ble (k * k) n) = true ↔ (k ∣ n ∧ k * k ≤ n) := by
      rw [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.dvd_iff_mod_eq_zero]
    by_cases h : k ∣ n ∧ k * k ≤ n
    · rw [if_pos (e.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (e.mp h')), if_neg h]

theorem sigma_le_tl (n : ℕ) (hn : n ≠ 0) (hle : n ≤ 5040) : σ 1 n ≤ tl n 72 := by
  rw [tl_eq]
  have h1 := T_stable n 72 (by omega) (n + 1)
  have h2 := T_stable n (n + 1) (by nlinarith) 72
  rw [add_comm (n + 1) 72] at h2
  rw [← h1, h2]
  exact sigma_le_T n hn

def good (n : ℕ) : Bool :=
  Nat.blt ((tl n 72 * 55440) ^ 28 * 55440) ((232128 * n) ^ 28 * n)

def allUpTo : ℕ → Bool
  | 0 => true
  | n + 1 => good (n + 1) && allUpTo n

theorem allUpTo_spec : ∀ N, allUpTo N = true → ∀ n, 1 ≤ n → n ≤ N → good n = true := by
  intro N
  induction N with
  | zero => intro _ n h1 h2; omega
  | succ N ih =>
    intro h n h1 h2
    simp only [allUpTo, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge n (N + 1) with hl | hl
    · exact ih h.2 n h1 (by omega)
    · have : n = N + 1 := by omega
      subst this
      exact h.1

set_option maxHeartbeats 0 in
theorem check : allUpTo 5040 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem sigma_55440 : σ 1 55440 = 232128 := by decide +kernel

end RobinH1Aux

open scoped ArithmeticFunction.sigma in
theorem OMA.solution : OMA.R_RiemannHypothesis_robin_criterion_rhs_R1.H1 := by
  intro n hn hle
  have hg : RobinH1Aux.good n = true := RobinH1Aux.allUpTo_spec 5040 RobinH1Aux.check n
    (Nat.pos_of_ne_zero hn) hle
  have hlt := Nat.blt_eq.mp hg
  rw [RobinH1Aux.sigma_55440]
  have hs := RobinH1Aux.sigma_le_tl n hn hle
  calc (σ 1 n * 55440) ^ 28 * 55440 ≤ (RobinH1Aux.tl n 72 * 55440) ^ 28 * 55440 := by gcongr
    _ < _ := hlt
