import OMAStatements.S_oeis_a243937
import Mathlib

namespace A243937Proof

open OMA.S_oeis_a243937

theorem lb (m k : ℕ) (hm : m ≠ 1) (h : ∀ p, p < k → p.Prime → ¬ p ∣ m) : k ≤ m.minFac := by
  by_contra hc
  exact h _ (not_le.mp hc) (Nat.minFac_prime hm) (Nat.minFac_dvd m)

theorem lb5 (m : ℕ) (h2 : m % 2 = 1) (h3 : m % 3 ≠ 0) (hm : 2 ≤ m) : 5 ≤ m.minFac := by
  apply lb m 5 (by omega)
  intro p hp hpp hd
  have := Nat.mod_eq_zero_of_dvd hd
  interval_cases p
  · exact Nat.not_prime_zero hpp
  · exact Nat.not_prime_one hpp
  · omega
  · omega
  · omega

theorem lb7 (m : ℕ) (h2 : m % 2 = 1) (h3 : m % 3 ≠ 0) (h5 : m % 5 ≠ 0) (hm : 2 ≤ m) :
    7 ≤ m.minFac := by
  apply lb m 7 (by omega)
  intro p hp hpp hd
  have := Nat.mod_eq_zero_of_dvd hd
  interval_cases p
  · exact Nat.not_prime_zero hpp
  · exact Nat.not_prime_one hpp
  · omega
  · omega
  · omega
  · omega
  · omega

theorem ub (m k : ℕ) (hk : 2 ≤ k) (h : m % k = 0) : m.minFac ≤ k :=
  Nat.minFac_le_of_dvd hk (Nat.dvd_of_mod_eq_zero h)

theorem mem0 (n : ℕ) (h : n % 6 = 0) (hn : 6 ≤ n) : n ∈ S := by
  refine ⟨hn, Nat.even_iff.mpr (by omega), ?_⟩
  have h1 := ub (n - 3) 3 (by norm_num) (by omega)
  have h2 := lb5 (n - 1) (by omega) (by omega) (by omega)
  omega

theorem notmem4 (n : ℕ) (h : n % 6 = 4) : n ∉ S := by
  rintro ⟨hn, -, hlt⟩
  have h1 := ub (n - 1) 3 (by norm_num) (by omega)
  have h2 := lb (n - 3) 3 (by omega) (by
    intro p hp hpp hd
    have := Nat.mod_eq_zero_of_dvd hd
    interval_cases p
    · exact Nat.not_prime_zero hpp
    · exact Nat.not_prime_one hpp
    · omega)
  omega

theorem mem8 (n : ℕ) (h : n % 30 = 8) : n ∈ S := by
  refine ⟨by omega, Nat.even_iff.mpr (by omega), ?_⟩
  have h1 := ub (n - 3) 5 (by norm_num) (by omega)
  have h2 := lb7 (n - 1) (by omega) (by omega) (by omega) (by omega)
  omega

theorem notmem26 (n : ℕ) (h : n % 30 = 26) : n ∉ S := by
  rintro ⟨hn, -, hlt⟩
  have h1 := ub (n - 1) 5 (by norm_num) (by omega)
  have h2 := lb7 (n - 3) (by omega) (by omega) (by omega) (by omega)
  omega

theorem even_of_mem (n : ℕ) (h : n ∈ S) : n % 2 = 0 := Nat.even_iff.mp h.2.1

theorem inf : (Set.ofPred (· ∈ S)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have := hB (mem0 (6 * (B + 1)) (by omega) (by omega))
  omega

/-- The terms counted from 0. -/
noncomputable def b (i : ℕ) : ℕ := Nat.nth (· ∈ S) i

theorem b_mem (i : ℕ) : b i ∈ S := Nat.nth_mem_of_infinite inf i

theorem b_lt (i : ℕ) : b i < b (i + 1) := (Nat.nth_lt_nth inf).mpr (Nat.lt_succ_self i)

theorem b_least (i z : ℕ) (hz : z ∈ S) (h : b i < z) : b (i + 1) ≤ z := by
  by_contra hc
  have := Nat.le_nth_of_lt_nth_succ (p := (· ∈ S)) (k := i) (not_le.mp hc) hz
  unfold b at h
  omega

theorem step (i j : ℕ) (hj : j = i + 1) :
    b j ∈ S ∧ ((b i % 6 = 0 ∧ (b j = b i + 2 ∨ (b j = b i + 6 ∧ b i + 2 ∉ S))) ∨
      (b i % 6 = 2 ∧ b j = b i + 4)) := by
  subst hj
  refine ⟨b_mem _, ?_⟩
  have hx := b_mem i
  have hy := b_mem (i + 1)
  have hlt := b_lt i
  have ex := even_of_mem _ hx
  have ey := even_of_mem _ hy
  have hx6 : 6 ≤ b i := hx.1
  have n4x : b i % 6 ≠ 4 := fun h => notmem4 _ h hx
  have n4y : b (i + 1) % 6 ≠ 4 := fun h => notmem4 _ h hy
  have hl := b_least i
  rcases (show b i % 6 = 0 ∨ b i % 6 = 2 by omega) with h | h
  · left
    have h6 := hl (b i + 6) (mem0 _ (by omega) (by omega)) (by omega)
    refine ⟨h, ?_⟩
    by_cases h2 : b i + 2 ∈ S
    · have := hl _ h2 (by omega)
      left; omega
    · rcases (show b (i + 1) = b i + 2 ∨ b (i + 1) = b i + 6 by omega) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, h2⟩
  · right
    have h4 := hl (b i + 4) (mem0 _ (by omega) (by omega)) (by omega)
    exact ⟨h, by omega⟩

theorem dval (n i j : ℕ) (hn : n = i + 1) (hj : j = i + 1) : d n = b j - b i := by
  subst hn hj
  rfl

theorem part1 (n : ℕ) (hn : 1 ≤ n) : d n = 2 ∨ d n = 4 ∨ d n = 6 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [dval _ m (m + 1) rfl rfl]
  have := step m (m + 1) rfl
  omega

theorem part2 (n : ℕ) (hn : 1 ≤ n) : ¬ (d n = 2 ∧ d (n + 1) = 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [dval _ m (m + 1) rfl rfl, dval _ (m + 1) (m + 2) rfl rfl]
  have s0 := step m (m + 1) rfl
  have s1 := step (m + 1) (m + 2) rfl
  omega

theorem part3 (n : ℕ) (hn : 1 ≤ n) : ¬ (d n = 4 ∧ d (n + 1) = 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [dval _ m (m + 1) rfl rfl, dval _ (m + 1) (m + 2) rfl rfl]
  have s0 := step m (m + 1) rfl
  have s1 := step (m + 1) (m + 2) rfl
  omega

theorem part4 (n : ℕ) (hn : 1 ≤ n) : ¬ (∀ i : ℕ, i < 5 → d (n + i) = 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro h
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  have h4 := h 4 (by norm_num)
  rw [dval _ m (m + 1) (by omega) rfl] at h0
  rw [dval _ (m + 1) (m + 2) (by omega) rfl] at h1
  rw [dval _ (m + 2) (m + 3) (by omega) rfl] at h2
  rw [dval _ (m + 3) (m + 4) (by omega) rfl] at h3
  rw [dval _ (m + 4) (m + 5) (by omega) rfl] at h4
  obtain ⟨-, s0⟩ := step m (m + 1) rfl
  obtain ⟨-, s1⟩ := step (m + 1) (m + 2) rfl
  obtain ⟨-, s2⟩ := step (m + 2) (m + 3) rfl
  obtain ⟨-, s3⟩ := step (m + 3) (m + 4) rfl
  obtain ⟨-, s4⟩ := step (m + 4) (m + 5) rfl
  have n0 : b m + 2 ∉ S := by
    rcases s0 with ⟨-, e | ⟨-, e⟩⟩ | e
    · omega
    · exact e
    · omega
  have n1 : b (m + 1) + 2 ∉ S := by
    rcases s1 with ⟨-, e | ⟨-, e⟩⟩ | e
    · omega
    · exact e
    · omega
  have n2 : b (m + 2) + 2 ∉ S := by
    rcases s2 with ⟨-, e | ⟨-, e⟩⟩ | e
    · omega
    · exact e
    · omega
  have n3 : b (m + 3) + 2 ∉ S := by
    rcases s3 with ⟨-, e | ⟨-, e⟩⟩ | e
    · omega
    · exact e
    · omega
  have n4 : b (m + 4) + 2 ∉ S := by
    rcases s4 with ⟨-, e | ⟨-, e⟩⟩ | e
    · omega
    · exact e
    · omega
  rcases (show b m % 30 = 6 ∨ b m % 30 = 0 ∨ b m % 30 = 24 ∨ b m % 30 = 18 ∨ b m % 30 = 12 by
    omega) with c | c | c | c | c
  · exact n0 (mem8 _ (by omega))
  · exact n1 (mem8 _ (by omega))
  · exact n2 (mem8 _ (by omega))
  · exact n3 (mem8 _ (by omega))
  · exact n4 (mem8 _ (by omega))

theorem part5 (n : ℕ) (hn : 1 ≤ n) :
    ¬ (∀ i : ℕ, i < 5 → d (n + 2 * i) = 2 ∧ d (n + 2 * i + 1) = 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro h
  obtain ⟨h0, k0⟩ := h 0 (by norm_num)
  obtain ⟨h1, k1⟩ := h 1 (by norm_num)
  obtain ⟨h2, k2⟩ := h 2 (by norm_num)
  obtain ⟨h3, k3⟩ := h 3 (by norm_num)
  obtain ⟨h4, k4⟩ := h 4 (by norm_num)
  rw [dval _ m (m + 1) (by omega) rfl] at h0
  rw [dval _ (m + 1) (m + 2) (by omega) rfl] at k0
  rw [dval _ (m + 2) (m + 3) (by omega) rfl] at h1
  rw [dval _ (m + 3) (m + 4) (by omega) rfl] at k1
  rw [dval _ (m + 4) (m + 5) (by omega) rfl] at h2
  rw [dval _ (m + 5) (m + 6) (by omega) rfl] at k2
  rw [dval _ (m + 6) (m + 7) (by omega) rfl] at h3
  rw [dval _ (m + 7) (m + 8) (by omega) rfl] at k3
  rw [dval _ (m + 8) (m + 9) (by omega) rfl] at h4
  obtain ⟨t0, s0⟩ := step m (m + 1) rfl
  obtain ⟨t2, -⟩ := step (m + 2) (m + 3) rfl
  obtain ⟨t4, -⟩ := step (m + 4) (m + 5) rfl
  obtain ⟨t6, -⟩ := step (m + 6) (m + 7) rfl
  obtain ⟨t8, -⟩ := step (m + 8) (m + 9) rfl
  have c0 : b m % 6 = 0 := by omega
  rcases (show b m % 30 = 24 ∨ b m % 30 = 18 ∨ b m % 30 = 12 ∨ b m % 30 = 6 ∨ b m % 30 = 0 by
    omega) with c | c | c | c | c
  · exact notmem26 _ (by omega) t0
  · exact notmem26 _ (by omega) t2
  · exact notmem26 _ (by omega) t4
  · exact notmem26 _ (by omega) t6
  · exact notmem26 _ (by omega) t8

end A243937Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a243937.main :=
  ⟨A243937Proof.part1, A243937Proof.part2, A243937Proof.part3, A243937Proof.part4,
    A243937Proof.part5⟩
