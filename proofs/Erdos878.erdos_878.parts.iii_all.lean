import FormalConjectures.ErdosProblems.«878»

/-!
# `max f ≠ max F` at `x = 210` (Barreto)

For every `n ≤ 210` we have `f n ≤ 441` (the maximum is `f 210 = 128 + 81 + 125 + 49 = 383`); this
is a finite check done by the kernel. On the other hand `{128, 189, 125}` is a set of pairwise
coprime integers in `[2, 210]` whose prime factors all divide `210 = 2 * 3 * 5 * 7`, so
`F 210 ≥ 128 + 189 + 125 = 442`.
-/

namespace OMA.E878

open Erdos878

set_option maxRecDepth 100000 in
lemma f_le : ∀ n ∈ Finset.range 211, f n ≤ 441 := by decide +kernel

lemma F_ge : 442 ≤ F 210 := by
  unfold F
  refine le_trans ?_ (Finset.le_sup (b := ({128, 189, 125} : Finset ℕ)) ?_)
  · decide
  · simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨by decide, by decide, ?_, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hab
          | (show Nat.Coprime _ _; decide)
    · intro a ha p hp hpa
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · have h : p ∣ 2 ^ 7 := by norm_num; exact hpa
        have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
        subst hp2
        decide
      · have h : p ∣ 3 ^ 3 * 7 := by norm_num; exact hpa
        rcases hp.dvd_mul.1 h with h3 | h7
        · have hp3 : p = 3 :=
            (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
          subst hp3
          decide
        · have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7
          subst hp7
          decide
      · have h : p ∣ 5 ^ 3 := by norm_num; exact hpa
        have hp5 : p = 5 :=
          (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h)
        subst hp5
        decide

end OMA.E878

theorem OMA.solution : type_of% @Erdos878.erdos_878.parts.iii_all := by
  intro h
  have h1 : Erdos878.maxUpTo Erdos878.f 210 ≤ 441 := by
    unfold Erdos878.maxUpTo
    exact Finset.sup_le OMA.E878.f_le
  have h2 : 442 ≤ Erdos878.maxUpTo Erdos878.F 210 := by
    unfold Erdos878.maxUpTo
    exact le_trans OMA.E878.F_ge
      (Finset.le_sup (f := Erdos878.F) (Finset.mem_range.2 (by norm_num)))
  have h3 := h 210
  omega
