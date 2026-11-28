import OMAReductions.R_OeisA5153_conjecture_R1

/-!
# Proof of `OeisA5153.conjecture.R1.H1`

Proves that if `n - 2 ^ k` or `n - 3 * 2 ^ (k + 1)` is prime, then `n` is the sum of a prime and
a practical number (`OeisA5153.A`).

Doubling preserves practicality: for any `m ≤ 2 * q`, writing `m = 2 * (m / 2) + (m % 2)` and
doubling a distinct-divisor representation of `m / 2 ≤ q` yields a distinct-divisor
representation of `2 * (m / 2)` consisting exclusively of even divisors of `2 * q`, to which `1`
can be adjoined when `m` is odd. Since `1` and `6` are practical (`OeisA5153.a_1`,
`OeisA5153.a_6`), induction shows that `2 ^ k` and `3 * 2 ^ (k + 1)` are practical for all `k`.
-/

namespace OeisA5153R1H1Proof

private lemma practical_two_mul {q : ℕ} (hq : OeisA5153.A q) : OeisA5153.A (2 * q) := by
  have hq_pos : 0 < q := hq.1
  refine ⟨by omega, fun m hm => ?_⟩
  have h2q_ne : 2 * q ≠ 0 := by omega
  have ha_le : m / 2 ≤ q := by omega
  obtain ⟨s, hs_sub, hs_sum⟩ := hq.2 (m / 2) ha_le
  have hs_sub' : s ⊆ q.divisors := Finset.coe_subset.mp hs_sub
  let s2 : Finset ℕ := s.image (2 * ·)
  have hs2_sub : s2 ⊆ (2 * q).divisors := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    have hx_dvd : x ∣ q := (Nat.mem_divisors.mp (hs_sub' hx)).1
    exact Nat.mem_divisors.mpr ⟨mul_dvd_mul_left 2 hx_dvd, h2q_ne⟩
  have hs2_sum : ∑ y ∈ s2, y = 2 * (m / 2) := by
    rw [Finset.sum_image (fun a _ b _ h => by omega), ← Finset.mul_sum, hs_sum]
  by_cases hmod : m % 2 = 0
  · refine ⟨s2, Finset.coe_subset.mpr hs2_sub, ?_⟩
    rw [hs2_sum]
    omega
  · have h1_not : (1 : ℕ) ∉ s2 := by
      intro h1
      rcases Finset.mem_image.mp h1 with ⟨x, _, hx⟩
      omega
    have h1_mem : (1 : ℕ) ∈ (2 * q).divisors := Nat.mem_divisors.mpr ⟨one_dvd _, h2q_ne⟩
    refine ⟨insert 1 s2, Finset.coe_subset.mpr (Finset.insert_subset h1_mem hs2_sub), ?_⟩
    rw [Finset.sum_insert h1_not, hs2_sum]
    omega

private lemma practical_pow_two : ∀ k : ℕ, OeisA5153.A (2 ^ k)
  | 0 => by simpa using OeisA5153.a_1
  | k + 1 => by
    rw [pow_succ']
    exact practical_two_mul (practical_pow_two k)

private lemma practical_three_mul_pow_two : ∀ k : ℕ, OeisA5153.A (3 * 2 ^ (k + 1))
  | 0 => by simpa using OeisA5153.a_6
  | k + 1 => by
    have heq : 3 * 2 ^ (k + 1 + 1) = 2 * (3 * 2 ^ (k + 1)) := by ring
    rw [heq]
    exact practical_two_mul (practical_three_mul_pow_two k)

end OeisA5153R1H1Proof

theorem OMA.solution : OMA.R_OeisA5153_conjecture_R1.H1 := by
  intro n k h
  rcases h with hp | hp
  · have hpos : 0 < n - 2 ^ k := hp.pos
    exact ⟨n - 2 ^ k, 2 ^ k, hp, OeisA5153R1H1Proof.practical_pow_two k, by omega⟩
  · have hpos : 0 < n - 3 * 2 ^ (k + 1) := hp.pos
    exact ⟨n - 3 * 2 ^ (k + 1), 3 * 2 ^ (k + 1), hp,
      OeisA5153R1H1Proof.practical_three_mul_pow_two k, by omega⟩
