import FormalConjectures.ErdosProblems.«477»

-- Problem: Erdős Problem 477 — S sq
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/477.lean (declaration Erdos477.erdos_477.variants.S_sq)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA477

/-- If every integer is uniquely `a + k^2` with `a ∈ A`, then distinct elements of `A`
differ by `2 mod 4`, since every odd number and every multiple of `4` is a difference of
two squares. -/
lemma diff_mod (A : Set ℤ)
    (huniq : ∀ a ∈ A, ∀ a' ∈ A, ∀ k k' : ℤ, a + k ^ 2 = a' + k' ^ 2 → a = a')
    {a a' : ℤ} (ha : a ∈ A) (ha' : a' ∈ A) (hne : a ≠ a') : (a - a') % 4 = 2 := by
  have hdiv := Int.emod_add_mul_ediv (a - a') 4
  set q := (a - a') / 4
  have h0 : 0 ≤ (a - a') % 4 := Int.emod_nonneg _ (by norm_num)
  have h4 : (a - a') % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  set r := (a - a') % 4 with hr
  interval_cases r
  · -- a - a' = 4q = (q+1)^2 - (q-1)^2
    exact absurd (huniq a ha a' ha' (q - 1) (q + 1) (by nlinarith)) hne
  · -- a - a' = 4q + 1 = (2q+1)^2 - (2q)^2
    exact absurd (huniq a ha a' ha' (2 * q) (2 * q + 1) (by nlinarith)) hne
  · rfl
  · -- a - a' = 4q + 3 = (2q+2)^2 - (2q+1)^2
    exact absurd (huniq a ha a' ha' (2 * q + 1) (2 * q + 2) (by nlinarith)) hne

end OMA477

theorem OMA.solution : type_of% @Erdos477.erdos_477.variants.S_sq := by
  intro A
  have hS : (Set.range fun x : ℤ => Polynomial.eval x (Polynomial.X ^ 2 : Polynomial ℤ)) =
      Set.range (fun k : ℤ => k ^ 2) := by
    ext y
    simp
  rw [hS]
  by_contra hcon
  push Not at hcon
  -- uniqueness of representations
  have huniq : ∀ a ∈ A, ∀ a' ∈ A, ∀ k k' : ℤ, a + k ^ 2 = a' + k' ^ 2 → a = a' := by
    intro a ha a' ha' k k' h
    obtain ⟨p, -, hp⟩ := hcon (a + k ^ 2)
    have e1 := hp (a, k ^ 2) ⟨⟨ha, k, rfl⟩, rfl⟩
    have e2 := hp (a', k' ^ 2) ⟨⟨ha', k', rfl⟩, h⟩
    have := e1.trans e2.symm
    exact (Prod.mk.inj this).1
  -- every integer is `≥` some element of `A`
  have hbelow : ∀ z : ℤ, ∃ a ∈ A, a ≤ z := by
    intro z
    obtain ⟨p, ⟨⟨hp1, k, hk⟩, hpz⟩, -⟩ := hcon z
    refine ⟨p.1, hp1, ?_⟩
    have : 0 ≤ p.2 := by rw [← hk]; positivity
    linarith
  obtain ⟨a0, h0, -⟩ := hbelow 0
  obtain ⟨a1, h1, h1le⟩ := hbelow (a0 - 1)
  obtain ⟨a2, h2, h2le⟩ := hbelow (a1 - 1)
  have d01 := OMA477.diff_mod A huniq h0 h1 (by omega)
  have d12 := OMA477.diff_mod A huniq h1 h2 (by omega)
  have d02 := OMA477.diff_mod A huniq h0 h2 (by omega)
  omega
