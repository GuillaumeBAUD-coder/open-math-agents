import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1
import Mathlib.FieldTheory.Finite.Basic

/-! Giuga's local divisibility criteria. For p prime, split the power sum into
complete blocks of p residues and evaluate one block using the units of ZMod p.
Lean formalization by @Deldor14. -/

namespace OMA.Giuga
open AgohGiuga Finset

private theorem omitZero (p n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    ∑ a ∈ Ioo 0 n, (a : ZMod p)^k = ∑ a ∈ range n, (a : ZMod p)^k := by
  have hs : (range n).erase 0 = Ioo 0 n := by
    ext a
    simp
  rw [← hs, ← Finset.add_sum_erase (range n) (fun a => (a : ZMod p)^k) (by simpa using hn : 0 ∈ range n)]
  simp [zero_pow hk.ne']

private theorem blocks (p t k : ℕ) :
    ∑ a ∈ range (p*t), (a : ZMod p)^k = (t : ZMod p) * ∑ a ∈ range p, (a : ZMod p)^k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Nat.cast_succ, add_mul, one_mul]
    simp

private theorem residueSum (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    ∑ a ∈ range p, (a : ZMod p)^k = if p-1 ∣ k then -1 else 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hsum : (∑ u : (ZMod p)ˣ, (u : ZMod p)^k) =
      ∑ a ∈ Ioo 0 p, (a : ZMod p)^k := by
    refine Finset.sum_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p).val) ?_ ?_ ?_ ?_
    · intro u _
      exact Finset.mem_Ioo.mpr ⟨(ZMod.val_pos.mpr u.ne_zero), ZMod.val_lt _⟩
    · intro a _ b _ he
      exact Units.ext (ZMod.val_injective _ he)
    · intro j hj
      obtain ⟨hj0,hjp⟩ := Finset.mem_Ioo.mp hj
      have hj' : (j : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt hj0 hjp
      exact ⟨Units.mk0 _ hj', Finset.mem_univ _, ZMod.val_cast_of_lt hjp⟩
    · intro u _
      simp
  rw [← omitZero p p k hp.pos hk, ← hsum, FiniteField.sum_pow_units, ZMod.card]

private theorem localConditions {n : ℕ} (hs : IsStrongGiuga n) {p t : ℕ} (hp : p.Prime)
    (hn : n = p*t) : p-1 ∣ n-1 ∧ (t : ZMod p) = 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hn' := hs.1.1
  have hk : 0 < n-1 := by omega
  have hpd : p ∣ n := ⟨t,hn⟩
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr (hpd.trans hs.2)
  push_cast at hz
  rw [omitZero p n (n-1) (by omega) hk] at hz
  conv at hz => enter [1,2,1,1]; rw [hn]
  rw [blocks, residueSum p (n-1) hp hk] at hz
  by_cases h : p-1 ∣ n-1
  · refine ⟨h, ?_⟩
    simp [h] at hz
    linear_combination -hz
  · simp [h] at hz

end OMA.Giuga

open OMA.Giuga

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1.H1 := by
  intro n hn
  refine (AgohGiuga.korselts_criterion n hn.1).2 ⟨?_, ?_⟩
  · apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp hpp
    obtain ⟨m, hm⟩ := hpp
    let _ : Fact p.Prime := ⟨hp⟩
    have h := (localConditions hn hp (by simpa [mul_assoc] using hm :
      n = p*(p*m))).2
    simp at h
  · intro p hp hd
    obtain ⟨t,ht⟩ := hd
    exact (localConditions hn hp ht).1
