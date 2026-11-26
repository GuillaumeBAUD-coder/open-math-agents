import FormalConjectures.ErdosProblems.«358»

-- Problem: Erdős Problem 358
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/358.lean:66 (declaration Erdos358.f_id)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E358

open Finset Erdos358

lemma sumIcc (u k : ℕ) : 2 * ∑ i ∈ Icc u (u + k), i = (k + 1) * (2 * u + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

lemma mem_iff (n u v : ℕ) :
    (u, v) ∈ intervalRepresentations id n ↔ 0 < u ∧ 0 < v ∧ n = ∑ i ∈ Icc u v, i :=
  Iff.rfl

lemma rep_param {n u v : ℕ} (hn : 0 < n) (h : (u, v) ∈ intervalRepresentations id n) :
    ∃ k, v = u + k ∧ 0 < u ∧ 2 * n = (k + 1) * (2 * u + k) := by
  rw [mem_iff] at h
  obtain ⟨hu, hv, hs⟩ := h
  have hle : u ≤ v := by
    by_contra hc
    rw [Finset.Icc_eq_empty hc, Finset.sum_empty] at hs
    omega
  refine ⟨v - u, by omega, hu, ?_⟩
  have h2 := sumIcc u (v - u)
  rw [show u + (v - u) = v by omega] at h2
  rw [hs, h2]

lemma rep_of {n u k : ℕ} (hu : 0 < u) (h : 2 * n = (k + 1) * (2 * u + k)) :
    (u, u + k) ∈ intervalRepresentations id n := by
  rw [mem_iff]
  refine ⟨hu, by omega, ?_⟩
  have h2 := sumIcc u k
  omega

/-- The odd divisor attached to a representation. -/
def g (p : ℕ × ℕ) : ℕ := if Odd (p.2 - p.1 + 1) then p.2 - p.1 + 1 else p.1 + p.2

lemma g_odd {u k : ℕ} (h : Odd (k + 1)) : g (u, u + k) = k + 1 := by
  have e : u + k - u + 1 = k + 1 := by omega
  simp only [g, e, if_pos h]

lemma g_even {u k : ℕ} (h : ¬ Odd (k + 1)) : g (u, u + k) = 2 * u + k := by
  have e : u + k - u + 1 = k + 1 := by omega
  simp only [g, e, if_neg h]
  omega

lemma odd_dvd {a b n : ℕ} (h : 2 * n = a * b) (ha : Odd a) : a ∣ n :=
  (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr ha)) ⟨b, h⟩

lemma g_mem {n u k : ℕ} (hn : 0 < n) (h : 2 * n = (k + 1) * (2 * u + k)) :
    g (u, u + k) ∣ n ∧ Odd (g (u, u + k)) := by
  by_cases ho : Odd (k + 1)
  · rw [g_odd ho]
    exact ⟨odd_dvd h ho, ho⟩
  · rw [g_even ho]
    have ho2 : Odd (2 * u + k) := by
      rw [Nat.not_odd_iff_even] at ho
      obtain ⟨j, hj⟩ := ho
      exact ⟨u + j - 1, by omega⟩
    exact ⟨odd_dvd (by rw [h, mul_comm]) ho2, ho2⟩

lemma g_inj {n u k u' k' : ℕ} (hu : 0 < u) (hu' : 0 < u')
    (h : 2 * n = (k + 1) * (2 * u + k)) (h' : 2 * n = (k' + 1) * (2 * u' + k'))
    (hg : g (u, u + k) = g (u', u' + k')) : u = u' ∧ k = k' := by
  have hE : (k + 1) * (2 * u + k) = (k' + 1) * (2 * u' + k') := by rw [← h, ← h']
  by_cases ho : Odd (k + 1) <;> by_cases ho' : Odd (k' + 1)
  · rw [g_odd ho, g_odd ho'] at hg
    have hk : k = k' := by omega
    subst hk
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < k + 1) hE
    omega
  · rw [g_odd ho, g_even ho'] at hg
    rw [hg, mul_comm] at hE
    have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * u' + k') hE
    omega
  · rw [g_even ho, g_odd ho'] at hg
    rw [hg, mul_comm] at hE
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < k' + 1) hE
    omega
  · rw [g_even ho, g_even ho'] at hg
    rw [hg] at hE
    have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * u' + k') hE
    omega

lemma g_surj {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) (ho : Odd d) :
    ∃ u k, 0 < u ∧ 2 * n = (k + 1) * (2 * u + k) ∧ g (u, u + k) = d := by
  obtain ⟨c, rfl⟩ := hd
  obtain ⟨j, rfl⟩ := ho
  have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  by_cases hlt : j < c
  · refine ⟨c - j, 2 * j, by omega, ?_, ?_⟩
    · have : 2 * (c - j) + 2 * j = 2 * c := by omega
      rw [this]; ring
    · exact g_odd ⟨j, rfl⟩
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hev : ¬ Odd (2 * c' + 1 + 1) := by
      rw [Nat.not_odd_iff_even]; exact ⟨c' + 1, by omega⟩
    refine ⟨j - c', 2 * c' + 1, by omega, ?_, ?_⟩
    · have : 2 * (j - c') + (2 * c' + 1) = 2 * j + 1 := by omega
      rw [this]; ring
    · rw [g_even hev]; omega

end OMA.E358

open Finset Erdos358 OMA.E358 in
theorem OMA.solution : type_of% @Erdos358.f_id := by
  funext n
  show Nat.card (intervalRepresentations id n) = _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hinf : (intervalRepresentations id 0).Infinite := by
      refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k + 2, 1)) ?_ ?_
      · intro a b hab
        simp only [Prod.mk.injEq] at hab
        omega
      · intro k
        rw [mem_iff]
        refine ⟨by omega, by omega, ?_⟩
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    have := hinf.to_subtype
    rw [Nat.card_eq_zero_of_infinite]
    simp
  · rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    refine Set.ncard_congr (fun p _ => g p) ?_ ?_ ?_
    · rintro ⟨u, v⟩ hp
      obtain ⟨k, rfl, hu, h⟩ := rep_param hn hp
      have := g_mem hn h
      simp only [Finset.coe_filter, Finset.mem_filter, Nat.mem_divisors, Set.mem_setOf_eq]
      exact ⟨⟨this.1, by omega⟩, this.2⟩
    · rintro ⟨u, v⟩ ⟨u', v'⟩ hp hp' hg
      obtain ⟨k, rfl, hu, h⟩ := rep_param hn hp
      obtain ⟨k', rfl, hu', h'⟩ := rep_param hn hp'
      obtain ⟨rfl, rfl⟩ := g_inj hu hu' h h' hg
      rfl
    · intro d hd
      simp only [Finset.coe_filter, Finset.mem_filter, Nat.mem_divisors, Set.mem_setOf_eq] at hd
      obtain ⟨u, k, hu, h, hgd⟩ := g_surj hn hd.1.1 hd.2
      exact ⟨(u, u + k), rep_of hu h, hgd⟩
