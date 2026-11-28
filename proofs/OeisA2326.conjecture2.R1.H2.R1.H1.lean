import OMAReductions.R_OeisA2326_conjecture2_R1_H2_R1

-- No prime p below 1000000 has p^3 dividing 2^(p-1) - 1.
-- Original proof by kernel computation: for every integer p with 2 <= p < 1000000 (prime or not) the kernel
-- evaluates 2^(p-1) modulo p^3 and finds a value other than 1. The range is cut into blocks of 20000 values.
-- A verified range of an open problem (the two known Wieferich primes 1093 and 3511 lie in it), not progress
-- on the general statement.

namespace OMA.A2326

/-- For `p = b, ..., b + f - 1`: `2^(p-1)` is not `1` modulo `p^3`. -/
def wf : ℕ → ℕ → Bool
  | 0, _ => true
  | f + 1, b => (2 ^ (b + f - 1) % (b + f) ^ 3 != 1) && wf f b

lemma wf_spec : ∀ (f b : ℕ), wf f b = true → ∀ p, b ≤ p → p < b + f → 2 ^ (p - 1) % p ^ 3 ≠ 1 := by
  intro f
  induction f with
  | zero => intro b _ p h1 h2; omega
  | succ f ih =>
    intro b h p h1 h2
    rw [wf, Bool.and_eq_true, bne_iff_ne] at h
    by_cases hp : p = b + f
    · subst hp; exact h.1
    · exact ih b h.2 p h1 (by omega)

lemma mod_eq_one {p : ℕ} (hp : 2 ≤ p) (h : p ^ 3 ∣ 2 ^ (p - 1) - 1) : 2 ^ (p - 1) % p ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
  have h2 : 2 ^ (p - 1) = p ^ 3 * k + 1 := by omega
  have h3 : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
  rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt h3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c0 : ∀ i < 10, wf 20000 (20000 * i + 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1 : ∀ i < 10, wf 20000 (20000 * i + 200002) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c2 : ∀ i < 10, wf 20000 (20000 * i + 400002) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3 : ∀ i < 10, wf 20000 (20000 * i + 600002) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4 : ∀ i < 10, wf 20000 (20000 * i + 800002) = true := by decide +kernel

lemma all_ne (p : ℕ) (h2 : 2 ≤ p) (hN : p < 1000000) : 2 ^ (p - 1) % p ^ 3 ≠ 1 := by
  have k (b) (h : ∀ i < 10, wf 20000 (20000 * i + b) = true) (h1 : b ≤ p) (h3 : p < b + 200000) :=
    wf_spec _ _ (h ((p - b) / 20000) (by omega)) p (by omega) (by omega)
  have := k 2 c0; have := k 200002 c1; have := k 400002 c2; have := k 600002 c3; have := k 800002 c4
  omega

end OMA.A2326

theorem OMA.solution : OMA.R_OeisA2326_conjecture2_R1_H2_R1.H1 := by
  intro p hp hlt _ hcube
  exact OMA.A2326.all_ne p hp.two_le hlt (OMA.A2326.mod_eq_one hp.two_le hcube)
