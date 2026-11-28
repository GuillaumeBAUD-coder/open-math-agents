import OMAStatements.S_oeis_a325691
import Mathlib

-- The argument follows the accepted proof of OEIS A325695 (the template entry).
-- Proof: for fixed u (a = u+1) the admissible v are those with n - 4a <= 2v and 3a + 2v <= n,
-- so the inner count is F' - G' with F' = (n-3a)/2 + 1 (if 3a <= n) and G' = (n-4a+1)/2.
-- Shifting u by 4 in F' and by 3 in G' gives the explicit step
-- term (n+12) + (G'(n+12,0) + G'(n+12,1) + G'(n+12,2)) = term n + (F'(n+12,0) + ... + F'(n+12,3)).
-- The order-9 recurrence then follows by induction in steps of 12 (omega for the step,
-- kernel evaluation for k < 12), and the generating function identity is the recurrence
-- read coefficientwise, with the coefficients of degree at most 8 checked directly.

namespace OMA.P_a325691
open OMA.S_oeis_a325691 PowerSeries

def F' (n u : ℕ) : ℕ := if 3*(u+1) ≤ n then (n - 3*(u+1))/2 + 1 else 0
def G' (n u : ℕ) : ℕ := (n - 4*(u+1) + 1)/2

lemma allowed_iff (n u v : ℕ) :
    allowed n u v = true ↔ 3*(u+1)+2*v ≤ n ∧ n ≤ 4*(u+1)+2*v := by
  simp only [allowed, decide_eq_true_eq]
  omega

lemma card_eq (n u : ℕ) :
    ((Finset.range (n+1)).filter (fun v => allowed n u v)).card + G' n u = F' n u := by
  unfold F' G'
  split_ifs with h
  · have hs : (Finset.range (n+1)).filter (fun v => allowed n u v) =
        Finset.Ico ((n - 4*(u+1) + 1)/2) ((n - 3*(u+1))/2 + 1) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, allowed_iff]
      omega
    rw [hs, Nat.card_Ico]
    omega
  · have hs : (Finset.range (n+1)).filter (fun v => allowed n u v) = ∅ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, allowed_iff, Finset.notMem_empty,
        iff_false]
      omega
    rw [hs, Finset.card_empty]
    omega

lemma term_eq (n : ℕ) :
    term n + ∑ u ∈ Finset.range (n+1), G' n u = ∑ u ∈ Finset.range (n+1), F' n u := by
  simp only [term, ← Finset.sum_add_distrib, card_eq]

lemma sumF_ext (n j : ℕ) :
    ∑ u ∈ Finset.range (n+1+j), F' n u = ∑ u ∈ Finset.range (n+1), F' n u := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show n+1+(j+1) = (n+1+j)+1 by omega, Finset.sum_range_succ, ih]
    have : F' n (n+1+j) = 0 := by unfold F'; split_ifs <;> omega
    rw [this, add_zero]

lemma sumG_ext (n j : ℕ) :
    ∑ u ∈ Finset.range (n+1+j), G' n u = ∑ u ∈ Finset.range (n+1), G' n u := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show n+1+(j+1) = (n+1+j)+1 by omega, Finset.sum_range_succ, ih]
    have : G' n (n+1+j) = 0 := by unfold G'; omega
    rw [this, add_zero]

lemma sumF_shift (n : ℕ) :
    ∑ u ∈ Finset.range (n+12+1), F' (n+12) u = ∑ u ∈ Finset.range (n+1), F' n u +
      (F' (n+12) 0 + F' (n+12) 1 + F' (n+12) 2 + F' (n+12) 3) := by
  rw [show n+12+1 = 4 + (n+1+8) by omega, Finset.sum_range_add]
  have : ∀ u, F' (n+12) (4+u) = F' n u := by
    intro u; unfold F'
    have h1 : (3*(4+u+1) ≤ n+12) ↔ 3*(u+1) ≤ n := by omega
    have h2 : n + 12 - 3*(4+u+1) = n - 3*(u+1) := by omega
    simp only [h1, h2]
  simp only [this]
  rw [sumF_ext]
  have hs : ∑ u ∈ Finset.range 4, F' (n+12) u =
      F' (n+12) 0 + F' (n+12) 1 + F' (n+12) 2 + F' (n+12) 3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hs]
  ring

lemma sumG_shift (n : ℕ) :
    ∑ u ∈ Finset.range (n+12+1), G' (n+12) u = ∑ u ∈ Finset.range (n+1), G' n u +
      (G' (n+12) 0 + G' (n+12) 1 + G' (n+12) 2) := by
  rw [show n+12+1 = 3 + (n+1+9) by omega, Finset.sum_range_add]
  have : ∀ u, G' (n+12) (3+u) = G' n u := by
    intro u; unfold G'
    have h2 : n + 12 - 4*(3+u+1) = n - 4*(u+1) := by omega
    rw [h2]
  simp only [this]
  rw [sumG_ext]
  have hs : ∑ u ∈ Finset.range 3, G' (n+12) u = G' (n+12) 0 + G' (n+12) 1 + G' (n+12) 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hs]
  ring

lemma key (n : ℕ) :
    term (n+12) + ((n+9)/2 + (n+5)/2 + (n+1)/2) =
      term n + ((n+9)/2 + 1 + ((n+6)/2 + 1) + ((n+3)/2 + 1) + (n/2 + 1)) := by
  have h1 := term_eq (n+12)
  have h2 := term_eq n
  rw [sumF_shift, sumG_shift] at h1
  have hG : G' (n+12) 0 + G' (n+12) 1 + G' (n+12) 2 = (n+9)/2 + (n+5)/2 + (n+1)/2 := by
    unfold G'; omega
  have hF : F' (n+12) 0 + F' (n+12) 1 + F' (n+12) 2 + F' (n+12) 3 =
      (n+9)/2 + 1 + ((n+6)/2 + 1) + ((n+3)/2 + 1) + (n/2 + 1) := by
    unfold F'; split_ifs <;> omega
  omega

set_option maxRecDepth 100000 in
lemma base (k : ℕ) (hk : k < 12) :
    term (k+9)+term (k+4)+term (k+3)+term (k+2) =
      term (k+7)+term (k+6)+term (k+5)+term k := by
  interval_cases k <;> decide +kernel

lemma recur : ∀ k : ℕ, term (k+9)+term (k+4)+term (k+3)+term (k+2) =
      term (k+7)+term (k+6)+term (k+5)+term k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < 12
    · exact base k hk
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 12 := ⟨k - 12, by omega⟩
      have IH := ih j (by omega)
      have e1 := key (j+9)
      have e2 := key (j+4)
      have e3 := key (j+3)
      have e4 := key (j+2)
      have e5 := key (j+7)
      have e6 := key (j+6)
      have e7 := key (j+5)
      have e8 := key j
      rw [show j+12+9 = j+9+12 by omega, show j+12+4 = j+4+12 by omega,
        show j+12+3 = j+3+12 by omega, show j+12+2 = j+2+12 by omega,
        show j+12+7 = j+7+12 by omega, show j+12+6 = j+6+12 by omega,
        show j+12+5 = j+5+12 by omega]
      omega

set_option maxRecDepth 100000 in
lemma small : term 0 = 0 ∧ term 1 = 0 ∧ term 2 = 0 ∧ term 3 = 1 ∧ term 4 = 1 ∧
    term 5 = 1 ∧ term 6 = 2 ∧ term 7 = 2 ∧ term 8 = 3 := by
  decide +kernel

lemma poly_eq : ((1-X)^3*(1+X)^2*(1+X^2)*(1+X+X^2) : PowerSeries ℚ) =
    1 - X^2 - X^3 - X^4 + X^5 + X^6 + X^7 - X^9 := by ring

lemma gf : ((1-X)^3*(1+X)^2*(1+X^2)*(1+X+X^2))*series =
    (X^3*(1+X-X^4) : PowerSeries ℚ) := by
  rw [poly_eq, show (X^3*(1+X-X^4) : PowerSeries ℚ) = X^3 + X^4 - X^7 by ring]
  ext n
  simp only [sub_mul, add_mul, one_mul, map_sub, map_add, coeff_X_pow_mul', series, coeff_mk,
    coeff_X_pow]
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8⟩ := small
  by_cases hn : 9 ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    have h := recur k
    have h' : ((term (k+9) : ℚ) + term (k+4) + term (k+3) + term (k+2)) =
        term (k+7) + term (k+6) + term (k+5) + term k := by exact_mod_cast h
    simp only [show 2 ≤ k+9 by omega, show 3 ≤ k+9 by omega, show 4 ≤ k+9 by omega,
      show 5 ≤ k+9 by omega, show 6 ≤ k+9 by omega, show 7 ≤ k+9 by omega,
      show 9 ≤ k+9 by omega, if_true, show k+9 ≠ 3 by omega, show k+9 ≠ 4 by omega,
      show k+9 ≠ 7 by omega, if_false,
      show k+9-2 = k+7 by omega, show k+9-3 = k+6 by omega, show k+9-4 = k+5 by omega,
      show k+9-5 = k+4 by omega, show k+9-6 = k+3 by omega, show k+9-7 = k+2 by omega,
      show k+9-9 = k by omega]
    linarith
  · interval_cases n <;> simp [s0, s1, s2, s3, s4, s5, s6, s7, s8] <;> norm_num

end OMA.P_a325691

theorem OMA.solution : type_of% @OMA.S_oeis_a325691.main :=
  ⟨OMA.P_a325691.recur, OMA.P_a325691.gf⟩
