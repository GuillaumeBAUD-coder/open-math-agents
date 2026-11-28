import FormalConjectures.ErdosProblems.«409»

/-! # Erdős Problem 409, part i

Let `c(n)` be the least `i` such that the `i`-th iterate of `n ↦ φ(n) + 1` starting at
`n` is prime (OEIS A039651).  The answer is the explicit recursive function

  c(0) = 0,  c(1) = 1,  c(p) = 0 for prime p,  c(n) = 1 + c(φ(n) + 1) for composite n.

Termination of the recursion: if `n ≥ 2` is composite then `φ n < n` and `φ n ≠ n - 1`
(otherwise `n` would be prime by `Nat.totient_eq_iff_prime`), hence `φ n + 1 < n`, so the
recursion is well founded on the value of `n` (this is the same decrease used in the
upstream proved test theorem `erdos_409.variants.termination`).

The proof that `c n` is the *least* such exponent is by strong induction on `n`:
for prime `n` the least exponent is `0`; for `n = 1` it is `1` (as `1 ↦ 2`); for composite
`n ≥ 2` the iterates from `n` are `n` itself followed by the iterates from `φ n + 1`, and
`φ n + 1 < n`, so the induction hypothesis applies (`OMA.main`).
-/

open scoped Nat

/-- `OMA.answer n` is the least `i` with `(n ↦ φ(n) + 1)^[i] n` prime (OEIS A039651). -/
def OMA.answer : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => if h : (n + 2).Prime then 0 else 1 + OMA.answer (φ (n + 2) + 1)
  termination_by n => n
  decreasing_by
    simp_wf
    have h1 : 1 < n + 2 := by omega
    have hlt : φ (n + 2) < n + 2 := Nat.totient_lt _ h1
    have hne : φ (n + 2) ≠ n + 2 - 1 := by
      intro hh
      exact h ((Nat.totient_eq_iff_prime (by omega)).1 hh)
    omega

lemma OMA.step_lt : ∀ n : ℕ, 1 < n → ¬ n.Prime → φ n + 1 < n := by
  intro n h1 hp
  have hlt : φ n < n := Nat.totient_lt _ h1
  have hne : φ n ≠ n - 1 := fun hh => hp ((Nat.totient_eq_iff_prime (by omega)).1 hh)
  omega

lemma OMA.answer_prime : ∀ n : ℕ, n.Prime → OMA.answer n = 0 := by
  intro n hp
  match n with
  | 0 => exact absurd hp Nat.not_prime_zero
  | 1 => exact absurd hp Nat.not_prime_one
  | k + 2 => rw [OMA.answer]; simp [hp]

lemma OMA.answer_comp : ∀ n : ℕ, 2 ≤ n → ¬ n.Prime → OMA.answer n = 1 + OMA.answer (φ n + 1) := by
  intro n h2 hp
  match n with
  | 0 => omega
  | 1 => omega
  | k + 2 => rw [OMA.answer]; simp [hp]

lemma OMA.answer_one : OMA.answer 1 = 1 := by rw [OMA.answer]

theorem OMA.main : ∀ n : ℕ, 0 < n → IsLeast { i | ((φ · + 1)^[i] n).Prime } (OMA.answer n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hp : n.Prime
    · rw [OMA.answer_prime n hp]
      refine ⟨?_, fun b _ => Nat.zero_le b⟩
      simpa using hp
    · have hn1 : n = 1 ∨ 2 ≤ n := by omega
      rcases hn1 with h1 | h2
      · subst h1
        rw [OMA.answer_one]
        refine ⟨?_, ?_⟩
        · simp only [Set.mem_ofPred_eq]
          rw [Function.iterate_one]
          norm_num [Nat.totient_one]
        · intro b hb
          rcases Nat.eq_zero_or_pos b with hb0 | hbpos
          · exfalso
            subst hb0
            simp only [Set.mem_ofPred_eq] at hb
            simp at hb
          · omega
      · set m := φ n + 1 with hm
        have hm_lt : m < n := by
          have hs := OMA.step_lt n (by omega) hp
          omega
        have hm_pos : 0 < m := by omega
        rw [OMA.answer_comp n h2 hp, ← hm]
        obtain ⟨ihmem, ihmin⟩ := ih m hm_lt hm_pos
        refine ⟨?_, ?_⟩
        · simp only [Set.mem_ofPred_eq]
          rw [Nat.add_comm 1 (OMA.answer m), Function.iterate_succ_apply]
          change Nat.Prime ((φ · + 1)^[OMA.answer m] (φ n + 1))
          rw [← hm]
          exact ihmem
        · intro b hb
          rcases Nat.eq_zero_or_pos b with hb0 | hbpos
          · exfalso
            subst hb0
            simp only [Set.mem_ofPred_eq] at hb
            simp at hb
            exact absurd hb hp
          · obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
            simp only [Set.mem_ofPred_eq] at hb
            rw [Function.iterate_succ_apply] at hb
            change Nat.Prime ((φ · + 1)^[b'] (φ n + 1)) at hb
            rw [← hm] at hb
            have hle := ihmin hb
            omega

theorem OMA.solution : Erdos409.erdos_409.parts.i.answer = OMA.answer →
    type_of% @Erdos409.erdos_409.parts.i := by
  intro h
  rw [h]
  exact OMA.main
