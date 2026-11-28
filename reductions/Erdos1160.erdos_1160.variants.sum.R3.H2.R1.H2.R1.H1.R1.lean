import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1_H2_R1

-- Reduction Erdos1160.erdos_1160.variants.sum.R3.H2.R1.H2.R1.H1.R1 of step Erdos1160.erdos_1160.variants.sum.R3.H2.R1.H2.R1.H1
-- Credit: @ahmeterdempmk

/-!
# Automorphism moments of 2-groups: roots and non-roots

The step asks for the moment bound `Σ_{|P| = 2^b} |Aut P|^t ≤ 2^(2b³/27 + 2tb²/9 - 8b²/27 + O(b))`
(Su–Xia, arXiv:2610.11092, Prop. 8.5, which even gives `λ(b) + 2tb²/9 + O(b)` with
`λ(b) = 2b³/27 - 4b²/9`). As in the paper (and as in the merged reduction
`Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R1` of the plain count), split the isomorphism
classes into *roots*, the groups whose Frattini subgroup is central of exponent dividing 2, and
the rest; each half must satisfy the same bound, with its own constant.

* `H1`: the moment over roots. Here `|Aut Q| = 2^{ds} |S_Q|` and the sum of `|S_Q|^t` is a Burnside
  count over `(t+1)`-tuples of `GL(d,2) × GL(s,2)` (Su–Xia §8.1), extending the fixed-point
  counting used for the solved root count `...R1.H2.R1.H2.R1.H1`.
* `H2`: the moment over non-roots (descendants of roots, Su–Xia §8.2–8.3).

The proof is a disjoint split of the `Σ`-type plus `(a + c)^27 ≤ 2^27 max(a, c)^27`.
-/

open Filter Erdos1160 CategoryTheory

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1_H2_R1_H1_R1

/-- Automorphism moments over roots: groups whose Frattini subgroup is central and elementary
abelian. -/
def H1 : Prop := ∀ t : ℕ, ∃ C : ℕ, ∀ b : ℕ,
  Nat.card (Σ x : {x : (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2 ^ b}) //
        frattini (Quotient.out x.1 : FiniteGrp.{0}) ≤ Subgroup.center (Quotient.out x.1 : FiniteGrp.{0}) ∧
        ∀ y : frattini (Quotient.out x.1 : FiniteGrp.{0}), y * y = 1},
      (Fin t → MulAut (Quotient.out x.1.1 : FiniteGrp.{0}))) ^ 27 * 2 ^ (8 * b ^ 2) ≤
    2 ^ (2 * b ^ 3 + 6 * t * b ^ 2 + C * (b + 1))

/-- Automorphism moments over non-roots: groups whose Frattini subgroup is not central of
exponent dividing 2. -/
def H2 : Prop := ∀ t : ℕ, ∃ C : ℕ, ∀ b : ℕ,
  Nat.card (Σ x : {x : (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2 ^ b}) //
        ¬ (frattini (Quotient.out x.1 : FiniteGrp.{0}) ≤ Subgroup.center (Quotient.out x.1 : FiniteGrp.{0}) ∧
          ∀ y : frattini (Quotient.out x.1 : FiniteGrp.{0}), y * y = 1)},
      (Fin t → MulAut (Quotient.out x.1.1 : FiniteGrp.{0}))) ^ 27 * 2 ^ (8 * b ^ 2) ≤
    2 ^ (2 * b ^ 3 + 6 * t * b ^ 2 + C * (b + 1))

open Classical in
/-- A `Σ`-type splits along a predicate on its base. -/
noncomputable def splitEquiv {S : Type*} (P : S → Prop) (F : S → Type*) :
    (Σ x, F x) ≃ (Σ x : {x // P x}, F x.1) ⊕ (Σ x : {x // ¬P x}, F x.1) where
  toFun p := if h : P p.1 then Sum.inl ⟨⟨p.1, h⟩, p.2⟩ else Sum.inr ⟨⟨p.1, h⟩, p.2⟩
  invFun := Sum.elim (fun p => ⟨p.1.1, p.2⟩) (fun p => ⟨p.1.1, p.2⟩)
  left_inv := by
    rintro ⟨x, f⟩
    by_cases h : P x <;> simp [h]
  right_inv := by
    rintro (⟨⟨x, h⟩, f⟩ | ⟨⟨x, h⟩, f⟩) <;> simp [h]

/-- Either the `Σ`-type is infinite (so `Nat.card = 0`) or its cardinality is the sum of the two
parts. -/
lemma card_split {S : Type*} (P : S → Prop) (F : S → Type*) :
    Nat.card (Σ x, F x) = 0 ∨
      Nat.card (Σ x, F x) =
        Nat.card (Σ x : {x // P x}, F x.1) + Nat.card (Σ x : {x // ¬P x}, F x.1) := by
  rw [Nat.card_congr (splitEquiv P F)]
  by_cases hf : Finite ((Σ x : {x // P x}, F x.1) ⊕ (Σ x : {x // ¬P x}, F x.1))
  · right
    have : Finite (Σ x : {x // P x}, F x.1) :=
      Finite.of_injective (β := (Σ x : {x // P x}, F x.1) ⊕ (Σ x : {x // ¬P x}, F x.1))
        Sum.inl Sum.inl_injective
    have : Finite (Σ x : {x // ¬P x}, F x.1) :=
      Finite.of_injective (β := (Σ x : {x // P x}, F x.1) ⊕ (Σ x : {x // ¬P x}, F x.1))
        Sum.inr Sum.inr_injective
    exact Nat.card_sum
  · left
    have := not_finite_iff_infinite.mp hf
    exact Nat.card_eq_zero_of_infinite

/-- Two bounds with constants `Ca`, `Cc` give a bound for the sum with constant `Ca + Cc + 27`. -/
lemma combine (a c k E Ca Cc b : ℕ) (ha : a ^ 27 * k ≤ 2 ^ (E + Ca * (b + 1)))
    (hc : c ^ 27 * k ≤ 2 ^ (E + Cc * (b + 1))) :
    (a + c) ^ 27 * k ≤ 2 ^ (E + (Ca + Cc + 27) * (b + 1)) := by
  have key : ∀ x C, a + c ≤ 2 * x → x ^ 27 * k ≤ 2 ^ (E + C * (b + 1)) → C ≤ Ca + Cc →
      (a + c) ^ 27 * k ≤ 2 ^ (E + (Ca + Cc + 27) * (b + 1)) := by
    intro x C hx h hC
    have h1 : C * (b + 1) ≤ (Ca + Cc) * (b + 1) := Nat.mul_le_mul_right _ hC
    calc (a + c) ^ 27 * k ≤ (2 * x) ^ 27 * k := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hx 27)
      _ = 2 ^ 27 * (x ^ 27 * k) := by ring
      _ ≤ 2 ^ 27 * 2 ^ (E + C * (b + 1)) := Nat.mul_le_mul_left _ h
      _ = 2 ^ (27 + (E + C * (b + 1))) := by rw [← pow_add]
      _ ≤ 2 ^ (E + (Ca + Cc + 27) * (b + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (by nlinarith [h1])
  rcases le_total c a with h | h
  · exact key a Ca (by omega) ha (by omega)
  · exact key c Cc (by omega) hc (by omega)

/-- Main reduction: the root and non-root moment bounds give the full moment bound. -/
theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1_H2_R1.H1 := by
  intro ha hc t
  obtain ⟨Ca, hCa⟩ := ha t
  obtain ⟨Cc, hCc⟩ := hc t
  refine ⟨Ca + Cc + 27, fun b => ?_⟩
  rcases card_split (S := ↥(Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2 ^ b}))
      (fun x => frattini (Quotient.out x.1 : FiniteGrp.{0}) ≤
          Subgroup.center (Quotient.out x.1 : FiniteGrp.{0}) ∧
        ∀ y : frattini (Quotient.out x.1 : FiniteGrp.{0}), y * y = 1)
      (fun x => Fin t → MulAut (Quotient.out x.1 : FiniteGrp.{0})) with h | h
  · rw [h]; simp
  · rw [h]; exact combine _ _ _ _ _ _ _ (hCa b) (hCc b)

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1_H2_R1_H1_R1
