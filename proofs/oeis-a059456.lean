import OMAStatements.S_oeis_a059456
import Mathlib

open OMA.S_oeis_a059456

private lemma chain_parent {q : ℕ} {p : Fin q} {k : ℕ} (hk : 1 ≤ k)
    (hq : q = 2 ^ k * (p.val + 1) - 1)
    (hp : Kept p.val)
    (hchain : ∀ j ∈ Finset.Icc 1 k, (2 ^ j * (p.val + 1) - 1).Prime) :
    ((q - 1) / 2).Prime := by
  cases k with
  | zero => omega
  | succ k =>
    have hpos : 0 < 2 ^ k * (p.val + 1) := by positivity
    have hq' : q = 2 * (2 ^ k * (p.val + 1)) - 1 := by
      refine hq.trans (congrArg (fun x : ℕ => x - 1) ?_)
      rw [pow_succ]
      ring
    have heq : (q - 1) / 2 = 2 ^ k * (p.val + 1) - 1 := by omega
    rw [heq]
    cases k with
    | zero => simpa using (Kept.eq_1 p.val ▸ hp).1
    | succ k =>
      apply hchain
      apply Finset.mem_Icc.mpr
      omega

private lemma extend_chain {q p : ℕ} (hpq : q = 2 * p + 1) (hp : p.Prime)
    (hq : q.Prime) :
    ∃ r : Fin q, Kept r.val ∧ ∃ k : ℕ, 1 ≤ k ∧ q = 2 ^ k * (r.val + 1) - 1 ∧
      ∀ j ∈ Finset.Icc 1 k, (2 ^ j * (r.val + 1) - 1).Prime := by
  classical
  by_cases h : Kept p
  · have e : q = 2 ^ 1 * (p + 1) - 1 := by omega
    refine ⟨⟨p, by omega⟩, h, 1, le_rfl, e, ?_⟩
    intro j hj
    obtain rfl : j = 1 := by have := Finset.mem_Icc.mp hj; omega
    exact e ▸ hq
  · rw [Kept.eq_1] at h
    push Not at h
    obtain ⟨r, hr, k, hk, he, hall⟩ := h hp
    have hpos : 0 < 2 ^ k * (r.val + 1) := by positivity
    have hnext : q = 2 ^ (k + 1) * (r.val + 1) - 1 := by
      rw [pow_succ, show 2 ^ k * 2 * (r.val + 1) = 2 * (2 ^ k * (r.val + 1)) by ring]
      omega
    refine ⟨⟨r.val, lt_trans r.isLt (by omega)⟩, hr, k + 1, by omega, hnext, ?_⟩
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    by_cases hjk : j ≤ k
    · exact hall j (Finset.mem_Icc.mpr ⟨hj1, hjk⟩)
    · obtain rfl : j = k + 1 := by omega
      exact hnext ▸ hq

theorem OMA.solution : type_of% @OMA.S_oeis_a059456.main := by
  intro q
  rw [Kept.eq_1]
  constructor
  · rintro ⟨hq, hnone⟩
    refine ⟨hq, ?_⟩
    rintro ⟨_, hp⟩
    rcases hq.eq_two_or_odd with htwo | hodd
    · subst q
      exact (by decide : ¬ Nat.Prime ((2 - 1) / 2)) hp
    · exact hnone (extend_chain (by omega) hp hq)
  · rintro ⟨hq, hnot⟩
    refine ⟨hq, ?_⟩
    rintro ⟨p, hp, k, hk, he, hchain⟩
    exact hnot ⟨hq, chain_parent hk he hp hchain⟩
