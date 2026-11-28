import OMAStatements.S_arxiv_2610_07102
import Mathlib

/-!
# The carousel tournament T_9 has no cyclic Hamilton cycle decomposition

So the answer to Problem 1.2 of arXiv 2610.07102 is not every odd n: it fails at n = 9.

Suppose F is a Hamilton decomposition of T_9 invariant under translation by 1, and let σ be the
cycle of F through the arc from 0 to 3. Its translates c_k(x) = σ(x - k) + k, k = 0, ..., 8, all lie
in F, and the arc of c_k out of 0 goes to one of 1, 2, 3, 4. By the pigeonhole principle two of
them, c_i and c_j with i ≠ j, share that arc, so c_i = c_j because every arc lies on exactly one
cycle of F. Hence σ(y + m) = σ(y) + m for all y, with m = i - j ≠ 0 in Z_9, and since some multiple
of m equals 3, also σ(y + 3) = σ(y) + 3. Then σ(0) = 3, σ(3) = 6 and σ(6) = 0, so σ^3 fixes 0.
For a cycle this forces σ^3 = 1, while a Hamilton cycle of T_9 has order 9.
-/

namespace OMA.P2610

open OMA.S_arxiv_2610_07102

/-- The translation by 1 on Z_9. -/
abbrev t : Equiv.Perm (ZMod 9) := Equiv.addRight 1

lemma t_pow_apply (k : ℕ) (x : ZMod 9) : (t ^ k) x = x + k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, ih]; simp [t]; ring

lemma t_pow_inv_apply (k : ℕ) (x : ZMod 9) : (t ^ k)⁻¹ x = x - k := by
  rw [Equiv.Perm.inv_eq_iff_eq, t_pow_apply]; ring

lemma conj_apply (σ : Equiv.Perm (ZMod 9)) (k : ℕ) (x : ZMod 9) :
    ((t ^ k) * σ * (t ^ k)⁻¹) x = σ (x - k) + k := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, t_pow_inv_apply, t_pow_apply]

lemma conj_mem {F : Set (Equiv.Perm (ZMod 9))}
    (hF : ∀ σ ∈ F, Equiv.addRight (1 : ZMod 9) * σ * (Equiv.addRight (1 : ZMod 9))⁻¹ ∈ F)
    {σ : Equiv.Perm (ZMod 9)} (hσ : σ ∈ F) (k : ℕ) : (t ^ k) * σ * (t ^ k)⁻¹ ∈ F := by
  induction k with
  | zero => simpa using hσ
  | succ k ih =>
    have h := hF _ ih
    have e : (t ^ (k + 1)) * σ * (t ^ (k + 1))⁻¹ = t * ((t ^ k) * σ * (t ^ k)⁻¹) * t⁻¹ := by
      rw [pow_succ', mul_inv_rev]; group
    rw [e]; exact h

lemma arc_vals (v : ZMod 9) (h : IsArc 9 0 v) : v ∈ ({1, 2, 3, 4} : Finset (ZMod 9)) := by
  unfold IsArc at h
  rw [sub_zero] at h
  revert v; decide

lemma step_three (σ : Equiv.Perm (ZMod 9)) (m : ZMod 9) (hm : m ≠ 0)
    (h : ∀ y, σ (y + m) = σ y + m) : ∀ y, σ (y + 3) = σ y + 3 := by
  have hk : ∀ k : ℕ, ∀ y, σ (y + k * m) = σ y + k * m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro y
      have := h (y + k * m)
      push_cast
      rw [show y + (k + 1) * m = y + k * m + m by ring, this, ih]; ring
  have key : ∀ m : ZMod 9, m ≠ 0 → ∃ k ∈ Finset.range 9, (k : ZMod 9) * m = 3 := by decide
  obtain ⟨k, -, hk3⟩ := key m hm
  intro y
  have := hk k y
  rwa [hk3] at this

end OMA.P2610

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2610_07102.main) := by
  intro hmain
  obtain ⟨F, hham, huniq, hinv⟩ := hmain 9 (by decide) (by norm_num)
  -- the cycle of F through the arc from 0 to 3
  obtain ⟨σ, ⟨hσF, hσ0⟩, -⟩ := huniq 0 3 (by unfold OMA.S_arxiv_2610_07102.IsArc; decide)
  -- its translates
  set c : ℕ → Equiv.Perm (ZMod 9) := fun k => (OMA.P2610.t ^ k) * σ * (OMA.P2610.t ^ k)⁻¹ with hc
  have hcF : ∀ k, c k ∈ F := fun k => OMA.P2610.conj_mem hinv hσF k
  -- pigeonhole on the arc out of 0
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range 9) (t := ({1, 2, 3, 4} : Finset (ZMod 9))) (f := fun k => c k 0)
    (by decide) (fun k _ => OMA.P2610.arc_vals _ ((hham _ (hcF k)).2.2 0))
  have hcij : c i = c j := by
    obtain ⟨τ, -, hτ⟩ := huniq 0 (c i 0) ((hham _ (hcF i)).2.2 0)
    have e1 := hτ (c i) ⟨hcF i, rfl⟩
    have e2 := hτ (c j) ⟨hcF j, heq.symm⟩
    rw [e1, e2]
  have hm : ((i : ZMod 9) - j) ≠ 0 := by
    intro h0
    apply hij
    have : (i : ZMod 9) = j := sub_eq_zero.mp h0
    rw [ZMod.natCast_eq_natCast_iff'] at this
    rw [Finset.mem_range] at hi hj
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  have hshift : ∀ y, σ (y + ((i : ZMod 9) - j)) = σ y + ((i : ZMod 9) - j) := by
    intro y
    have h := congrArg (fun p : Equiv.Perm (ZMod 9) => p (y + i)) hcij
    simp only [hc, OMA.P2610.conj_apply] at h
    rw [show y + (i : ZMod 9) - i = y by ring] at h
    rw [show y + ((i : ZMod 9) - j) = y + i - j by ring, ← sub_eq_iff_eq_add.mpr h.symm]
    ring
  have h3 := OMA.P2610.step_three σ _ hm hshift
  have hσ3 : σ 3 = 6 := by
    have := h3 0; rw [zero_add, hσ0] at this; rw [this]; decide
  have hσ6 : σ 6 = 0 := by
    have := h3 3; rw [hσ3] at this; rw [show (6 : ZMod 9) = 3 + 3 by decide, this]; decide
  have hpow : (σ ^ 3) 0 = 0 := by
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, hσ0, hσ3, hσ6]
  obtain ⟨hcyc, hmove, -⟩ := hham σ hσF
  have hone : σ ^ 3 = 1 := hcyc.pow_eq_one_iff.mpr ⟨0, hmove 0, hpow⟩
  have hord : orderOf σ = 9 := by
    rw [hcyc.orderOf]
    have : σ.support = Finset.univ := by
      ext x; simp [Equiv.Perm.mem_support, hmove x]
    rw [this, Finset.card_univ, ZMod.card]
  have := orderOf_dvd_of_pow_eq_one hone
  rw [hord] at this
  norm_num at this
