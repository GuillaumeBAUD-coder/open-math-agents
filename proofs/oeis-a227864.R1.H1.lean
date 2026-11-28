import OMAReductions.R_oeis_a227864_R1
import Mathlib

open OMA.S_oeis_a227864

def primeCert (n : ℕ) : Bool :=
  decide (2 ≤ n) && decide (n < 1000000) &&
    (List.range' 2 998).all (fun m => decide (n < m*m) || n % m != 0)

lemma prime_of_primeCert {n : ℕ} (h : primeCert n = true) : Nat.Prime n := by
  unfold primeCert at h
  rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff] at h
  obtain ⟨⟨h2, hbound⟩, hall⟩ := h
  rw [decide_eq_true_eq] at h2 hbound
  rw [List.all_eq_true] at hall
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm2 hmle hdiv => ?_⟩
  have hsqrt : n.sqrt < 1000 := Nat.sqrt_lt'.mpr hbound
  have hmem : m ∈ List.range' 2 998 := by
    rw [List.mem_range']
    refine ⟨m - 2, by omega, by omega⟩
  have hz := hall m hmem
  rw [Bool.or_eq_true_iff] at hz
  have hsq : m * m ≤ n := by
    exact (Nat.mul_le_mul hmle hmle).trans (Nat.sqrt_le n)
  rcases hz with hlt | hmodnz
  · have : n < m * m := of_decide_eq_true hlt
    omega
  · have hmod : n % m = 0 := Nat.mod_eq_zero_of_dvd hdiv
    rw [hmod] at hmodnz
    contradiction

def cand (p b : ℕ) : Bool :=
  decide (2 ≤ b ∧ b ≤ p^2) && primeCert ((p^2 % b)*b + p^2/b)
def found (p : ℕ) : Bool := (List.range' (p+2) 17).any (cand p)

lemma found_sound {p : ℕ} (hp : 3 ≤ p) (h : found p = true) :
    ∃ b : ℕ, 2 ≤ b ∧ (reversal b (p^2)).Prime := by
  rw [found, List.any_eq_true] at h
  obtain ⟨b, hbmem, hb⟩ := h
  rw [cand, Bool.and_eq_true_iff] at hb
  obtain ⟨hboth, hpc⟩ := hb
  obtain ⟨hb2, hble⟩ := of_decide_eq_true hboth
  obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hbmem
  simp only [one_mul] at hb2 hble hpc
  have lo : p < p + 2 + i := by omega
  refine ⟨p + 2 + i, hb2, ?_⟩
  rw [OMA.R_oeis_a227864_R1.two_digit_reversal p (p+2+i) (by omega) lo hble]
  exact prime_of_primeCert hpc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
theorem OMA.solution : OMA.R_oeis_a227864_R1.H1 := by
  intro p hp3 hple hpp
  apply found_sound hp3
  interval_cases p <;> first
    | solve | norm_num at hpp
    | rfl
