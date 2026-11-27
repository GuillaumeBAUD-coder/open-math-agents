import OMAReductions.R_Erdos389_erdos_389_R1_H2_R1
import Mathlib

/-! Compare large-prime valuations by translating divisible entries between blocks. -/
open Finset
namespace ConsecutiveValuations

private theorem val_count (p c k : ℕ) (hp : p.Prime) (hc : 0 < c)
    (high : c+k-1 < p^2) :
    padicValNat p (∏ i ∈ range k, (c+i)) = ((range k).filter (fun i => p ∣ c+i)).card := by
  rw [← Nat.factorization_def _ hp,
    Nat.factorization_prod_apply (S := range k) (g := fun i => c+i) (fun i _ => (show 0 < c+i by omega).ne')]
  trans ∑ i ∈ range k, if p ∣ c+i then 1 else 0
  · apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    have cp : c+i ≠ 0 := by omega
    rw [Nat.factorization_def _ hp]
    by_cases hd : p ∣ c+i
    · rw [if_pos hd]
      have lower : 1 ≤ padicValNat p (c+i) :=
        (Nat.pow_dvd_iff_le_padicValNat hp.ne_one cp).mp (by simpa using hd)
      have upper : ¬ 2 ≤ padicValNat p (c+i) := by
        intro hh
        have hdiv := (Nat.pow_dvd_iff_le_padicValNat hp.ne_one cp).mpr hh
        have hle := Nat.le_of_dvd (show 0 < c+i by omega) hdiv
        omega
      omega
    · simp [hd, padicValNat.eq_zero_of_not_dvd]
  · simp

theorem compare (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hsmooth : ∀ s : ℕ, n-1 < 2*s → s ≤ n-1 → ∀ p : ℕ, p.Prime → p ∣ k+s →
      p ≤ max (n-1) (Nat.sqrt (n+2*k-1)))
    (p : ℕ) (hp : p.Prime) (big : max (n-1) (Nat.sqrt (n+2*k-1)) < p) :
    padicValNat p (∏ i ∈ range k, (n+i)) ≤
      padicValNat p (∏ i ∈ range k, (n+k+i)) := by
  have hnp : n ≤ p := by have := (le_max_left (n-1) (Nat.sqrt (n+2*k-1))).trans_lt big; omega
  have hsq := Nat.sqrt_lt'.mp ((le_max_right (n-1) (Nat.sqrt (n+2*k-1))).trans_lt big)
  rw [val_count p n k hp (by omega) (by omega), val_count p (n+k) k hp (by omega) (by omega)]
  let A := (range k).filter (fun i => p ∣ n+i)
  let B := (range k).filter (fun i => p ∣ n+k+i)
  change A.card ≤ B.card
  let b := k % p
  have hb : b < p := Nat.mod_lt _ hp.pos
  have hdivEq : b+p*(k/p) = k := Nat.mod_add_div _ _
  have left {i : ℕ} (hi : i ∈ A) : i < k ∧ p ∣ n+i := by simpa [A] using hi
  have right {i : ℕ} (hi : i < k) (hd : p ∣ n+k+i) : i ∈ B :=
    mem_filter.mpr ⟨mem_range.mpr hi,hd⟩
  by_cases zero : b = 0
  · have hkdiv : p ∣ k := Nat.dvd_of_mod_eq_zero zero
    apply card_le_card
    intro i hi
    obtain ⟨hi',hd⟩ := left hi
    exact right hi' (by simpa [add_assoc, add_comm, add_left_comm] using dvd_add hd hkdiv)
  let s := p-b
  have sb : s+b = p := by omega
  have shift : p ∣ k+s := by
    refine ⟨k/p+1,?_⟩
    rw [Nat.mul_succ]
    omega
  by_cases far : n ≤ s
  · have hbi {i : ℕ} (hi : i ∈ A) : b ≤ i := by
      by_contra! ht
      have hle := Nat.le_of_dvd (show 0 < n+i by omega) (left hi).2
      omega
    have hkdiv : p ∣ k-b := ⟨k/p,by omega⟩
    apply card_le_card_of_injOn (fun i : ℕ => i-b)
    · intro i hi
      have h := left hi
      have lower := hbi hi
      apply right (i := i-b) (by omega)
      have eq : n+i+(k-b) = n+k+(i-b) := by omega
      rw [← eq]
      exact dvd_add h.2 hkdiv
    · intro i hi j hj eq
      have lo := hbi hi
      have lo' := hbi hj
      change i-b = j-b at eq
      omega
  · have short : 2*s ≤ n-1 := by
      by_contra! h
      exact big.not_ge (hsmooth s h (by omega) p hp shift)
    have inside {i : ℕ} (hi : i ∈ A) : i+s < k := by
      obtain ⟨hit,hd⟩ := left hi
      by_contra! hbad
      have hz : 0 < n+i-(k+s) := by omega
      have hz' := Nat.le_of_dvd hz (Nat.dvd_sub hd shift)
      omega
    apply card_le_card_of_injOn (fun i : ℕ => i+s)
    · intro i hi
      apply right (i := i+s) (inside hi)
      simpa only [add_assoc, add_comm, add_left_comm] using dvd_add (left hi).2 shift
    · intro i _ j _ eq
      exact Nat.add_right_cancel eq

end ConsecutiveValuations

theorem OMA.solution : OMA.R_Erdos389_erdos_389_R1_H2_R1.H1 := ConsecutiveValuations.compare