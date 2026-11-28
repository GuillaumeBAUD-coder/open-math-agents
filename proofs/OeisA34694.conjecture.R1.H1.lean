import OMAReductions.R_OeisA34694_conjecture_R1

namespace A34694Aux

def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

theorem noDiv_spec (p : ℕ) : ∀ f d, noDiv p f d = true → (∀ m, 2 ≤ m → m < d → ¬ m ∣ p) →
    ∀ m, 2 ≤ m → m * m ≤ p → ¬ m ∣ p := by
  intro f
  induction f with
  | zero => intro d h; simp [noDiv] at h
  | succ f ih =>
    intro d h hd m hm hmm
    simp only [noDiv] at h
    by_cases h1 : Nat.blt p (d * d) = true
    · have hlt : p < d * d := Nat.blt_eq.mp h1
      apply hd m hm
      by_contra hc
      rw [not_lt] at hc
      have := Nat.mul_le_mul hc hc
      omega
    · rw [if_neg h1] at h
      by_cases h2 : Nat.beq (p % d) 0 = true
      · rw [if_pos h2] at h; exact absurd h (by simp)
      · rw [if_neg h2] at h
        have hnd : ¬ d ∣ p := by
          intro hdp
          apply h2
          rw [Nat.mod_eq_zero_of_dvd hdp]
          rfl
        apply ih (d + 1) h _ m hm hmm
        intro k hk hkd
        rcases Nat.lt_succ_iff_lt_or_eq.mp hkd with hk' | hk'
        · exact hd k hk hk'
        · subst hk'; exact hnd

def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p p 2

theorem isPrimeB_spec (p : ℕ) (h : isPrimeB p = true) : p.Prime := by
  simp only [isPrimeB, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hp : 2 ≤ p := Nat.le_of_ble_eq_true h1
  have key := noDiv_spec p p 2 h2 (fun m hm hm2 => by omega)
  by_contra hnp
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hmp : (Nat.minFac p).Prime := Nat.minFac_prime (by omega)
  exact key _ hmp.two_le (by nlinarith) (Nat.minFac_dvd p)

def findK (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, k => if isPrimeB (k * n + 1) then true else findK n f (k + 1)

theorem findK_spec (n : ℕ) : ∀ f k, findK n f k = true →
    ∃ j, k ≤ j ∧ j < k + f ∧ (j * n + 1).Prime := by
  intro f
  induction f with
  | zero => intro k h; simp [findK] at h
  | succ f ih =>
    intro k h
    simp only [findK] at h
    by_cases h1 : isPrimeB (k * n + 1) = true
    · exact ⟨k, le_refl _, by omega, isPrimeB_spec _ h1⟩
    · rw [if_neg h1] at h
      obtain ⟨j, hj1, hj2, hj3⟩ := ih (k + 1) h
      exact ⟨j, by omega, by omega, hj3⟩

def allRange (lo : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => findK (lo + k) (lo + k - 1) 1 && allRange lo k

theorem allRange_spec (lo : ℕ) : ∀ len, allRange lo len = true → ∀ n, lo ≤ n → n < lo + len →
    findK n (n - 1) 1 = true := by
  intro len
  induction len with
  | zero => intro _ n h1 h2; omega
  | succ L ih =>
    intro h n h1 h2
    simp only [allRange, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge n (lo + L) with hl | hl
    · exact ih h.2 n h1 hl
    · have : n = lo + L := by omega
      subst this
      exact h.1

set_option maxHeartbeats 0 in
theorem c0 : allRange 2 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c1 : allRange 502 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c2 : allRange 1002 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c3 : allRange 1502 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c4 : allRange 2002 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c5 : allRange 2502 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c6 : allRange 3002 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c7 : allRange 3502 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c8 : allRange 4002 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c9 : allRange 4502 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c10 : allRange 5002 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c11 : allRange 5502 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c12 : allRange 6002 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c13 : allRange 6502 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c14 : allRange 7002 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c15 : allRange 7502 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c16 : allRange 8002 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c17 : allRange 8502 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c18 : allRange 9002 500 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem c19 : allRange 9502 500 = true := by decide +kernel

theorem all_chunks : ∀ i, i < 20 → allRange (2 + 500 * i) 500 = true := by
  intro i hi
  interval_cases i
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5
  · exact c6
  · exact c7
  · exact c8
  · exact c9
  · exact c10
  · exact c11
  · exact c12
  · exact c13
  · exact c14
  · exact c15
  · exact c16
  · exact c17
  · exact c18
  · exact c19

theorem findK_ok (n : ℕ) (h1 : 1 < n) (h2 : n ≤ 10000) : findK n (n - 1) 1 = true := by
  have hi : (n - 2) / 500 < 20 := by omega
  apply allRange_spec _ 500 (all_chunks _ hi) n
  · have := Nat.div_mul_le_self (n - 2) 500
    omega
  · have := Nat.lt_div_mul_add (a := n - 2) (b := 500) (by norm_num)
    omega

end A34694Aux

theorem OMA.solution : OMA.R_OeisA34694_conjecture_R1.H1 := by
  intro n hn hle
  obtain ⟨j, hj1, hj2, hj3⟩ := A34694Aux.findK_spec n (n - 1) 1 (A34694Aux.findK_ok n hn hle)
  have hmem : j * n + 1 ∈ {p : ℕ | Nat.Prime p ∧ n ∣ (p - 1)} :=
    ⟨hj3, by simp⟩
  have hle' := Nat.sInf_le hmem
  unfold OeisA34694.a
  have h3 : j * n ≤ (n - 1) * n := Nat.mul_le_mul_right _ (by omega)
  have h4 : (n - 1) * n + 1 < n ^ 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  omega
