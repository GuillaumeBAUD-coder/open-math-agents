import OMAStatements.S_mo_138509
import Mathlib

namespace OMA.S_mo_138509

open Equiv Finset

theorem usmul (ε : ℤˣ) (x : ZMod 2) : ε • x = x := by
  rcases Int.units_eq_one_or ε with h | h <;> subst h
  · simp
  · have : (-1 : ZMod 2) = 1 := by decide
    simp [Units.smul_def, this]

theorem det_zero (V : Type) [Fintype V] [DecidableEq V] (A : Matrix V V (ZMod 2))
    (hs : A.IsSymm) (hd : ∀ i, A i i = 0) (hodd : Odd (Fintype.card V)) : A.det = 0 := by
  rw [Matrix.det_apply]
  refine Finset.sum_involution (fun σ _ => σ⁻¹) ?_ ?_ (fun _ _ => Finset.mem_univ _)
    (fun σ _ => inv_inv σ)
  · intro σ _
    have h1 : ∏ i, A (σ⁻¹ i) i = ∏ i, A (σ i) i := by
      rw [← Equiv.prod_comp σ]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      have := congrFun (congrFun hs.eq (σ i)) i
      simpa [Matrix.transpose_apply] using this
    rw [usmul, usmul, h1]
    exact CharTwo.add_self_eq_zero _
  · intro σ _ hne heq
    apply hne
    have h2 : σ ^ 2 = 1 := by
      rw [pow_two]; nth_rewrite 1 [← heq]; exact inv_mul_cancel σ
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnd : ¬ 2 ∣ Fintype.card V := by
      intro h; exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
    obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hnd
      (by simpa using h2)
    rw [usmul]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by rw [ha]; exact hd a)

end OMA.S_mo_138509

theorem OMA.solution : type_of% @OMA.S_mo_138509.main := by
  classical
  intro V _ G h
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  let A : Matrix V V (ZMod 2) := fun i j => if G.Adj i j then 1 else 0
  have hdet : A.det = 0 := OMA.S_mo_138509.det_zero V A
    (by
      unfold Matrix.IsSymm
      ext i j
      have h' : G.Adj j i ↔ G.Adj i j := G.adj_comm j i
      rw [Matrix.transpose_apply]
      show (if G.Adj j i then (1 : ZMod 2) else 0) = if G.Adj i j then 1 else 0
      simp only [h'])
    (fun i => by simp [A])
    hodd
  obtain ⟨v, hv, hAv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := A)).mpr hdet
  have hv1 : ∀ i, v i = 0 ∨ v i = 1 := fun i => by
    generalize v i = x; revert x; decide
  obtain ⟨ω, hω⟩ := h {i | v i = 1} (by
    by_contra hne
    apply hv
    ext i
    rcases hv1 i with h0 | h1
    · simpa using h0
    · exact absurd ⟨i, h1⟩ hne)
  have := congrFun hAv ω
  simp only [Matrix.mulVec, dotProduct, A, Pi.zero_apply] at this
  have h3 : ∑ i, (if G.Adj ω i then (1 : ZMod 2) else 0) * v i
      = ((Set.ncard {i | v i = 1 ∧ G.Adj ω i} : ℕ) : ZMod 2) := by
    have hs : {i | v i = 1 ∧ G.Adj ω i} = ↑(Finset.univ.filter fun i => v i = 1 ∧ G.Adj ω i) := by
      ext; simp
    rw [hs, Set.ncard_coe_finset, Finset.cast_card, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hv1 i with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [h3] at this
  rw [ZMod.natCast_eq_zero_iff_even] at this
  exact (Nat.not_even_iff_odd.mpr hω) this
