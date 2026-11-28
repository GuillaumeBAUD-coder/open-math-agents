import OMAReductions.R_OeisA2326_conjecture2_R1_H2_R1

/-! Adapt the bounded kernel check from PR #12421 to scan odd integers. -/
namespace A2326BelowMillion

def check (start : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
    let p := start + 2 * count
    (2 ^ (p - 1) % p ^ 3 != 1) && check start count

lemma check_spec (start count : ℕ) (h : check start count = true) (j : ℕ) (hj : j < count) :
    2 ^ (start + 2 * j - 1) % (start + 2 * j) ^ 3 ≠ 1 := by
  induction count with
  | zero => omega
  | succ count ih =>
    simp only [check, Bool.and_eq_true, bne_iff_ne] at h
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
    · exact ih h.2 hlt
    · exact h.1

-- Keep each kernel computation to 20,000 odd integers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem blocks (b : Fin 25) : check (3 + 40000 * b.val) 20000 = true := by
  fin_cases b <;> decide +kernel

lemma odd_residue (j : ℕ) (hj : j < 500000) :
    2 ^ (3 + 2 * j - 1) % (3 + 2 * j) ^ 3 ≠ 1 := by
  let b : Fin 25 := ⟨j / 20000, by omega⟩
  have h := check_spec _ _ (blocks b) (j % 20000) (Nat.mod_lt _ (by decide))
  have hstart : 3 + 40000 * b.val + 2 * (j % 20000) = 3 + 2 * j := by
    dsimp [b]
    omega
  rwa [hstart] at h

end A2326BelowMillion

theorem OMA.solution : OMA.R_OeisA2326_conjecture2_R1_H2_R1.H1 := by
  intro p hp hbound _ hdiv
  rcases hp.eq_two_or_odd with rfl | hodd
  · exact (by decide : ¬ (2 : ℕ) ^ 3 ∣ 2 ^ (2 - 1) - 1) hdiv
  have htwo := hp.two_le
  have hresidue : 2 ^ (p - 1) % p ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := hdiv
    have heq : 2 ^ (p - 1) = p ^ 3 * k + 1 := by
      have := Nat.one_le_two_pow (n := p - 1)
      omega
    have hmod : 1 < p ^ 3 := Nat.one_lt_pow (by decide) (by omega)
    rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt hmod]
  let j := (p - 3) / 2
  have hj : j < 500000 := by dsimp [j]; omega
  have hindex : 3 + 2 * j = p := by dsimp [j]; omega
  have h := A2326BelowMillion.odd_residue j hj
  rw [hindex] at h
  exact h hresidue
