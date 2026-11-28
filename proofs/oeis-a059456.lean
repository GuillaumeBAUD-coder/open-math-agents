import OMAStatements.S_oeis_a059456
import Mathlib

namespace OMA.A059456Proof

open OMA.S_oeis_a059456

/-- `q` is removed by the sieve. -/
def Removed (q : ℕ) : Prop :=
  ∃ p : Fin q, Kept p.val ∧ ∃ k : ℕ, 1 ≤ k ∧ q = 2 ^ k * (p.val + 1) - 1 ∧
    ∀ j ∈ Finset.Icc 1 k, (2 ^ j * (p.val + 1) - 1).Prime

lemma kept_iff (q : ℕ) : Kept q ↔ q.Prime ∧ ¬ Removed q := by
  rw [Kept]
  rfl

lemma removed_iff (q : ℕ) (IH : ∀ r < q, (Kept r ↔ r.Prime ∧ ¬ IsSafePrime r) ∧
      (r.Prime → (Removed r ↔ ((r - 1) / 2).Prime)))
    (hq : q.Prime) : Removed q ↔ ((q - 1) / 2).Prime := by
  constructor
  · rintro ⟨p, hp, k, hk, hqk, hall⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hpr := ((kept_iff p.val).mp hp).1
      have : (q - 1) / 2 = p.val := by
        simp at hqk
        omega
      rw [this]
      exact hpr
    · have hN : 1 ≤ 2 ^ m * (p.val + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have e : 2 ^ (m + 1) * (p.val + 1) = 2 * (2 ^ m * (p.val + 1)) := by ring
      rw [e] at hqk
      have : (q - 1) / 2 = 2 ^ m * (p.val + 1) - 1 := by omega
      rw [this]
      exact hall m (Finset.mem_Icc.mpr ⟨hm, by omega⟩)
  · intro hr
    set r := (q - 1) / 2 with hrdef
    have hr2 := hr.two_le
    have hodd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · omega
      · exact h
    have hqr : q = 2 * r + 1 := by omega
    have hrq : r < q := by omega
    by_cases hs : IsSafePrime r
    · obtain ⟨p, hp, k, hk, hrk, hall⟩ := ((IH r hrq).2 hr).mpr hs.2
      refine ⟨⟨p.val, by omega⟩, hp, k + 1, by omega, ?_, ?_⟩
      · have hN : 1 ≤ 2 ^ k * (p.val + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        have e : 2 ^ (k + 1) * (p.val + 1) = 2 * (2 ^ k * (p.val + 1)) := by ring
        simp only
        rw [e]
        omega
      · intro j hj
        simp only at hj ⊢
        rcases Finset.mem_Icc.mp hj with ⟨hj1, hj2⟩
        rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
        · exact hall j (Finset.mem_Icc.mpr ⟨hj1, by omega⟩)
        · have hjk' : j = k + 1 := by omega
          subst hjk'
          have hN : 1 ≤ 2 ^ k * (p.val + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
          have e : 2 ^ (k + 1) * (p.val + 1) = 2 * (2 ^ k * (p.val + 1)) := by ring
          rw [e]
          have : 2 * (2 ^ k * (p.val + 1)) - 1 = q := by omega
          rw [this]
          exact hq
    · have hk : Kept r := ((IH r hrq).1).mpr ⟨hr, hs⟩
      refine ⟨⟨r, hrq⟩, hk, 1, le_rfl, ?_, ?_⟩
      · simp only
        omega
      · intro j hj
        have : j = 1 := by
          rcases Finset.mem_Icc.mp hj with ⟨h1, h2⟩
          omega
        subst this
        simp only
        have : 2 ^ 1 * (r + 1) - 1 = q := by omega
        rw [this]
        exact hq

lemma both (q : ℕ) : (Kept q ↔ q.Prime ∧ ¬ IsSafePrime q) ∧
    (q.Prime → (Removed q ↔ ((q - 1) / 2).Prime)) := by
  induction q using Nat.strong_induction_on with
  | _ q IH =>
    have h2 : q.Prime → (Removed q ↔ ((q - 1) / 2).Prime) := removed_iff q IH
    refine ⟨?_, h2⟩
    rw [kept_iff]
    constructor
    · rintro ⟨hq, hnr⟩
      exact ⟨hq, fun hs => hnr ((h2 hq).mpr hs.2)⟩
    · rintro ⟨hq, hns⟩
      exact ⟨hq, fun hr => hns ⟨hq, (h2 hq).mp hr⟩⟩

theorem main_proof : ∀ q : ℕ, Kept q ↔ (q.Prime ∧ ¬ IsSafePrime q) := fun q => (both q).1

end OMA.A059456Proof

open OMA.A059456Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a059456.main := main_proof
