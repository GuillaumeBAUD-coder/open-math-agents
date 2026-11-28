import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Set.Card

-- Reduction Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H1.R1.H2.R1 of step Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H1.R1.H2
-- Credit: @TheLittleOne1234

/- The step bounds the classes of groups of order 2^m in the complement of the central interval, with the
generous error 216*(m+1)^2. Any subset of the classes of order 2^m is bounded by the full count
g(2^m), and g(2^m)^27 * 2^(9*m^2) <= 2^(2*m^3) eventually.

H1, H2, H3 and H4 are, word for word, the hypotheses of the merged reduction
Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R2, and each has a merged proof
(proofs/Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R2.H1.lean ... H4.lean, @kamaleshanantha,
PRs 2283, 2310, 2379, 2452). The lemmas count_from_cover and max_budget and the proof of
sharp_upper are copied from that reduction file; card_out and classes_finite are copied from
reduction Erdos1160.erdos_1160.variants.sum.R3.H2.R2.H1.R1 (@michelzerasafadaum-gif). -/

open Filter Erdos1160 CategoryTheory
open scoped commutatorElement
namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1_H2_R1


def H1 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    K = ⊥}
  (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)

def H2 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    Nat.card F ≤ 2^192000*Nat.card K}
  (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)

def H3 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ 2^192000*Nat.card K < Nat.card F ∧ (1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)

def H4 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)

lemma count_from_cover {X : Type*} (B C D E : Set X)
    (cover : ∀x, x∈B ∨ x∈C ∨ x∈D ∨ x∈E) :
    Nat.card X ≤ B.ncard+C.ncard+D.ncard+E.ncard := by
  classical
  by_cases h : Finite X
  · let _ := h
    have eq : Set.univ = (B∪C∪D∪E) := by
      ext x
      simpa only [Set.mem_univ,Set.mem_union,true_iff,or_assoc] using cover x
    rw [←Set.ncard_univ,eq]
    have a := Set.ncard_union_le (B∪C∪D) E
    have b := Set.ncard_union_le (B∪C) D
    have c := Set.ncard_union_le B C
    omega
  · let _ : Infinite X := not_finite_iff_infinite.mp h
    simp

lemma max_budget (a b c d n f z : ℕ) (h : n≤a+b+c+d)
    (ha : (4*a)^27*f≤z) (hb : (4*b)^27*f≤z)
    (hc : (4*c)^27*f≤z) (hd : (4*d)^27*f≤z) : n^27*f≤z := by
  let T := max (max a b) (max c d)
  have H : (4*T)^27*f≤z := by
    have hT : T=a ∨ T=b ∨ T=c ∨ T=d := by dsimp [T];omega
    rcases hT with e|e|e|e <;> rw [e] <;> assumption
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by dsimp [T];omega : n≤4*T) 27)).trans H


theorem nonempty_mulEquiv_of_iso {X Y : FiniteGrp.{0}} (i : X ≅ Y) : Nonempty (X ≃* Y) :=
  ⟨Iso.groupIsoToMulEquiv ((inducedFunctor FiniteGrp.toGrp).mapIso i)⟩

/-- The chosen representative of a class of groups of order `n` has order `n`. -/
theorem card_out {n : ℕ} {x : Quotient (isIsomorphicSetoid FiniteGrp.{0})}
    (hx : x ∈ Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n}) :
    Nat.card (Quotient.out x : FiniteGrp.{0}) = n := by
  obtain ⟨G, hG, rfl⟩ := hx
  have h : Nonempty (Quotient.out (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) G) ≅ G) :=
    Quotient.mk_out (s := isIsomorphicSetoid FiniteGrp.{0}) G
  obtain ⟨i⟩ := h
  obtain ⟨e⟩ := nonempty_mulEquiv_of_iso i
  rw [Nat.card_congr e.toEquiv]
  exact hG

/-- There are finitely many classes of groups of order `n`: transporting the multiplication of a
representative to `Fin n` gives a table, and classes with equal tables are equal. -/
theorem classes_finite (n : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n}).Finite := by
  classical
  set S := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n} with hS
  let e : ∀ x : S, (Quotient.out x.1 : FiniteGrp.{0}) ≃ Fin n := fun x =>
    (Finite.equivFin _).trans (finCongr (card_out x.2))
  let tab : S → Fin n → Fin n → Fin n := fun x a b => e x ((e x).symm a * (e x).symm b)
  have hinj : Function.Injective tab := by
    intro x y hxy
    let f : (Quotient.out x.1 : FiniteGrp.{0}) ≃* (Quotient.out y.1 : FiniteGrp.{0}) :=
      { toEquiv := (e x).trans (e y).symm
        map_mul' := fun a b => by
          have h := congrFun (congrFun hxy (e x a)) (e x b)
          simp only [tab, Equiv.symm_apply_apply] at h
          show (e y).symm (e x (a * b)) = (e y).symm (e x a) * (e y).symm (e x b)
          rw [h, Equiv.symm_apply_apply] }
    apply Subtype.ext
    calc x.1 = Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (Quotient.out x.1) :=
          (Quotient.out_eq _).symm
      _ = Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (Quotient.out y.1) :=
          Quotient.sound ⟨InducedCategory.isoMk (MulEquiv.toGrpIso
            (X := (Quotient.out x.1).toGrp) (Y := (Quotient.out y.1).toGrp) f)⟩
      _ = y.1 := Quotient.out_eq _
  have : Finite S := Finite.of_injective tab hinj
  exact Set.toFinite S

theorem sharp_upper (roots : H1) (narrow : H2) (wide : H3) (outer : H4) :
    ∀ᶠ m : ℕ in atTop, g (2^m)^27 * 2 ^ (9 * m^2) ≤ 2 ^ (2 * m^3) := by
  filter_upwards [roots,narrow,wide,outer] with m hr hn hw ho
  classical
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let B : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    K = ⊥}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    Nat.card F ≤ 2^192000*Nat.card K}
  let D : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ 2^192000*Nat.card K < Nat.card F ∧ (1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  let E : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  have cover (x : A) : x∈B ∨ x∈C ∨ x∈D ∨ x∈E := by
    dsimp only [B,C,D,E,Set.mem_ofPred_eq]
    let G := x.property.choose
    let F := Subgroup.closure (Set.range (fun y : G => y*y))
    let K := Subgroup.closure (Set.range (fun y : F => y.val*y.val) ∪ Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    by_cases root : K=⊥
    · exact .inl root
    · right
      by_cases small : Nat.card F ≤ 2^192000*Nat.card K
      · exact .inl small
      · right
        by_cases strip : (1000*(2*m-3*d)≤2*d ∧ 1000*(3*d-2*m)≤2*d)
        · exact .inl ⟨root,lt_of_not_ge small,strip⟩
        · exact .inr ⟨root,strip⟩
  exact max_budget _ _ _ _ _ _ _ (count_from_cover B C D E cover) hr hn hw ho

theorem subset_bound (m : ℕ) (hm : g (2^m)^27 * 2 ^ (9 * m^2) ≤ 2 ^ (2 * m^3))
    (C : Set (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^m})) :
    C.ncard^27 ≤ 2^(2*m^3 + 216*(m+1)^2) := by
  haveI : Finite (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^m}) := (classes_finite (2^m)).to_subtype
  have hc : C.ncard ≤ g (2^m) := (Set.ncard_le_card C).trans_eq (Nat.card_coe_set_eq _)
  calc C.ncard^27 ≤ g (2^m)^27 := Nat.pow_le_pow_left hc 27
    _ ≤ g (2^m)^27 * 2 ^ (9 * m^2) := Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ 2 ^ (2 * m^3) := hm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1.H2 := by
  intro h1 h2 h3 h4
  filter_upwards [sharp_upper h1 h2 h3 h4] with m hm
  intro A C
  exact subset_bound m hm _

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1_H2_R1
