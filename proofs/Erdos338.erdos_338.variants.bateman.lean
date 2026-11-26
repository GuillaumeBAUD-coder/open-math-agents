import FormalConjectures.ErdosProblems.«338»

-- Problem: Erdős Problem 338 — bateman
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/338.lean:165 (declaration Erdos338.erdos_338.variants.bateman)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E338

open Filter

/-- A multiset of ones and positive multiples of `h` sums to `c + h * k`, where `c` counts the
ones, and if `k ≠ 0` at least one further summand was used. -/
lemma multiset_form (h : ℕ) (S : Multiset ℕ) (hS : ∀ x ∈ S, x = 1 ∨ (0 < x ∧ h ∣ x)) :
    ∃ c k, S.sum = c + h * k ∧ c + (if k = 0 then 0 else 1) ≤ S.card := by
  induction S using Multiset.induction_on with
  | empty => exact ⟨0, 0, by simp, by simp⟩
  | cons x S ih =>
    obtain ⟨c, k, hsum, hcard⟩ := ih (fun y hy => hS y (Multiset.mem_cons_of_mem hy))
    rcases hS x (Multiset.mem_cons_self x S) with rfl | ⟨hx0, j, rfl⟩
    · refine ⟨c + 1, k, by rw [Multiset.sum_cons, hsum]; ring, ?_⟩
      rw [Multiset.card_cons]
      omega
    · refine ⟨c, k + j, by rw [Multiset.sum_cons, hsum]; ring, ?_⟩
      rw [Multiset.card_cons]
      have hj : j ≠ 0 := by
        rintro rfl
        simp at hx0
      have hkj : k + j ≠ 0 := by omega
      rw [if_neg hkj]
      split_ifs at hcard <;> omega

lemma not_rep {h h' m : ℕ} (hh : 3 ≤ h) (hh' : h' < h) (hm : h ≤ m) (hmod : m % h = h - 1)
    (S : Multiset ℕ) (hS : ∀ x ∈ S, x = 1 ∨ (0 < x ∧ h ∣ x)) (hc : S.card ≤ h')
    (hsum : S.sum = m) : False := by
  obtain ⟨c, k, e, hck⟩ := multiset_form h S hS
  rw [hsum] at e
  have hcle : c ≤ h' := by
    have : c ≤ S.card := by
      split_ifs at hck <;> omega
    omega
  have hcmod : c % h = h - 1 := by
    rw [e, Nat.add_mul_mod_self_left] at hmod
    exact hmod
  rw [Nat.mod_eq_of_lt (by omega)] at hcmod
  by_cases hk : k = 0
  · subst hk
    omega
  · rw [if_neg hk] at hck
    omega

lemma finset_mod (h : ℕ) (hh : 3 ≤ h) (S : Finset ℕ)
    (hS : ∀ x ∈ S, x = 1 ∨ (0 < x ∧ h ∣ x)) : (∑ x ∈ S, x) % h ≤ 1 := by
  by_cases h1 : 1 ∈ S
  · rw [← Finset.add_sum_erase S (fun x => x) h1]
    have hd : h ∣ ∑ x ∈ S.erase 1, x := Finset.dvd_sum (fun x hx => by
      rcases hS x (Finset.mem_of_mem_erase hx) with rfl | ⟨_, hd⟩
      · exact absurd rfl (Finset.ne_of_mem_erase hx)
      · exact hd)
    obtain ⟨k, hk⟩ := hd
    rw [hk, Nat.add_mul_mod_self_left]
    exact Nat.mod_le 1 h
  · have hd : h ∣ ∑ x ∈ S, x := Finset.dvd_sum (fun x hx => by
      rcases hS x hx with rfl | ⟨_, hd⟩
      · exact absurd hx h1
      · exact hd)
    rw [Nat.mod_eq_zero_of_dvd hd]
    omega

end OMA.E338

open Filter OMA.E338 in
theorem OMA.solution : type_of% @Erdos338.erdos_338.variants.bateman := by
  intro h hh
  have hA : Erdos338.HasOrder (insert 1 {x : ℕ | 0 < x ∧ h ∣ x}) h := by
    rw [Erdos338.HasOrder, eventually_atTop]
    refine ⟨h, fun m hm => ?_⟩
    refine ⟨(m / h * h) ::ₘ Multiset.replicate (m % h) 1, ?_, ?_, ?_⟩
    · intro x hx
      rw [Multiset.mem_cons] at hx
      rcases hx with rfl | hx
      · right
        exact ⟨Nat.mul_pos (Nat.div_pos hm (by omega)) (by omega), Nat.dvd_mul_left _ _⟩
      · left
        exact Multiset.eq_of_mem_replicate hx
    · rw [Multiset.card_cons, Multiset.card_replicate]
      have := Nat.mod_lt m (by omega : 0 < h)
      omega
    · rw [Multiset.sum_cons, Multiset.sum_replicate, smul_eq_mul, mul_one]
      exact Nat.div_add_mod' m h
  constructor
  · apply le_antisymm
    · exact iInf₂_le h hA
    · apply le_iInf₂
      intro h' hh'
      by_contra hlt
      have hlt' : h' < h := by
        have h3 := not_le.mp hlt
        exact_mod_cast h3
      rw [Erdos338.HasOrder, eventually_atTop] at hh'
      obtain ⟨N, hN⟩ := hh'
      obtain ⟨S, hS, hc, hsum⟩ := hN (h * (N + 1) + (h - 1)) (by nlinarith)
      refine not_rep hh hlt' (by nlinarith) ?_ S hS hc hsum
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  · rintro ⟨t, ht⟩
    rw [Erdos338.HasRestrictedOrder, eventually_atTop] at ht
    obtain ⟨N, hN⟩ := ht
    obtain ⟨S, hS, -, hsum⟩ := hN (h * N + 2) (by nlinarith)
    have h4 := finset_mod h hh S hS
    rw [hsum, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)] at h4
    omega
