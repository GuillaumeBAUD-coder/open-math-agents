import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.Sylow

/-!
Fixed-cofactor enumeration via group extensions. Su and Xia, arXiv:2610.11092v1,
prove the fixed-outer-action bound in Lemma 8.8 and sum over Sylow cores and
outer actions in Proposition 8.9. A template below fixes the kernel, quotient
and representatives of an outer action. Its weight counts the possible central
factor sets. The group-theoretic estimate left in the second step concerns
the total weight of the templates needed, allowing duplicate templates.
-/

open CategoryTheory Filter Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1

/-- With kernel, quotient and outer action fixed, inequivalent extensions can
be encoded by central corrections to a reference factor set. -/
def H1 : Prop :=
  ∀ (N H : FiniteGrp.{0}) (I : Type 1) (D : I → FiniteGrp.{0})
    (S : ∀ i, GroupExtension N (D i) H) (action : H → MulAut N),
    (∀ i h, ∃ e : D i, ∃ n : N, (S i).rightHom e = h ∧
      MulAut.conj n * (S i).conjAct e = action h) →
    (∀ i j, Nonempty ((S i).Equiv (S j)) → i = j) →
    Nonempty (I ↪ (H × H → Subgroup.center N))

/-- Bound the total weight of a family of Sylow-core outer actions covering
the groups of the stipulated order. Keeping the kernel equal to the normal
core forces the quotient to have order dividing the factorial of the Sylow index. -/
def H2 : Prop :=
  ∀ r q : ℕ, 0 < r → 0 < q → q < 2 ^ r → ∀ᶠ k : ℕ in atTop,
    ∃ (B : ℕ) (N H : Fin B → FiniteGrp.{0}) (action : ∀ b, H b → MulAut (N b)),
      (∀ (G : FiniteGrp.{0}) (P : Sylow 2 G), Nat.card G = 2 ^ k * q →
        ∃ (b : Fin B) (S : GroupExtension (N b) G (H b)),
          S.inl.range = P.normalCore ∧ ∀ h, ∃ e : G, ∃ n : N b, S.rightHom e = h ∧
            MulAut.conj n * S.conjAct e = action b h) ∧
      2 ^ (k+r) * (∑ b, Nat.card (Subgroup.center (N b)) ^ (Nat.card (H b) ^ 2)) ≤ g (2 ^ (k+r))

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3.H2 := by
  classical
  intro henc hcount r q hr hq hqr
  filter_upwards [hcount r q hr hq hqr] with k hk
  obtain ⟨B,N,H,action,covered,budget⟩ := hk
  let C := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = 2 ^ k * q}
  let rep (i : C) : FiniteGrp.{0} := i.property.choose
  have spec (i : C) : Nat.card (rep i) = 2 ^ k * q ∧
      Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (rep i) = i.val := i.property.choose_spec
  have assign (i : C) := covered (rep i) (Classical.arbitrary (Sylow 2 (rep i))) (spec i).1
  let j (i : C) : Fin B := (assign i).choose
  let F (b : Fin B) := {i : C // j i = b}
  have encode (b : Fin B) : Nonempty (F b ↪ (H b × H b → Subgroup.center (N b))) := by
    have data (i : F b) : ∃ S : GroupExtension (N b) (rep i.val) (H b),
        ∀ h, ∃ e : rep i.val, ∃ n : N b, S.rightHom e = h ∧
          MulAut.conj n * S.conjAct e = action b h := by
      rw [← i.property]
      obtain ⟨S, _, hs⟩ := (assign i.val).choose_spec
      exact ⟨S,hs⟩
    choose seq hseq using data
    apply henc (N b) (H b) (F b) (fun i => rep i.val) seq (action b) hseq
    intro i t hiso
    obtain ⟨e⟩ := hiso
    apply Subtype.ext
    apply Subtype.ext
    rw [← (spec i.val).2, ← (spec t.val).2]
    exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := (rep i.val).toGrp) (Y := (rep t.val).toGrp) e.toMulEquiv)⟩
  letI (b : Fin B) : Finite (F b) := Finite.of_injective _ (encode b).some.injective
  apply le_trans (Nat.mul_le_mul_left _ ?_) budget
  calc
    g (2 ^ k * q) = Nat.card C := rfl
    _ = Nat.card ((b : Fin B) × F b) := (Nat.card_congr (Equiv.sigmaFiberEquiv j)).symm
    _ = ∑ b, Nat.card (F b) := Nat.card_sigma
    _ ≤ ∑ b, Nat.card (Subgroup.center (N b)) ^ (Nat.card (H b) ^ 2) := by
      apply Finset.sum_le_sum
      intro b _
      have hb := Nat.card_le_card_of_injective _ (encode b).some.injective
      simpa only [Nat.card_fun, Nat.card_prod, pow_two] using hb

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1
