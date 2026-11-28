import Mathlib

namespace OMA.S_arxiv_2310_02647

/-- A discrete dynamical system `(X, f)` is a set `X : Type` equipped with an endofunction
`f : X → X` (equivalently a presheaf on the additive monoid `ℕ`). -/
structure DDS where
  carrier : Type
  step : carrier → carrier

/-- A morphism of discrete dynamical systems commutes with the endofunctions. -/
structure DDSHom (X Y : DDS) where
  toFun : X.carrier → Y.carrier
  comm : ∀ x : X.carrier, toFun (X.step x) = Y.step (toFun x)

/-- Isomorphism of discrete dynamical systems. -/
def DDSIso (X Y : DDS) : Prop :=
  ∃ (f : DDSHom X Y) (g : DDSHom Y X),
    (∀ x : X.carrier, g.toFun (f.toFun x) = x) ∧
    (∀ y : Y.carrier, f.toFun (g.toFun y) = y)

/-- Terminal discrete dynamical system `(1, id)`. -/
abbrev ddsUnit : DDS where
  carrier := PUnit
  step := id

/-- Binary product of discrete dynamical systems. -/
abbrev ddsProd (X Y : DDS) : DDS where
  carrier := X.carrier × Y.carrier
  step := fun p => (X.step p.1, Y.step p.2)

/-- Equalizer of two parallel morphisms of discrete dynamical systems. -/
abbrev ddsEq {X Y : DDS} (f g : DDSHom X Y) : DDS where
  carrier := { x : X.carrier // f.toFun x = g.toFun x }
  step := fun x => ⟨X.step x.1, by rw [f.comm, g.comm, x.2]⟩

/-- Small coproduct of a family of discrete dynamical systems. -/
abbrev ddsCoprod {I : Type} (F : I → DDS) : DDS where
  carrier := Σ i : I, (F i).carrier
  step := fun p => ⟨p.1, (F p.1).step p.2⟩

/-- Coequalizer of two parallel morphisms of discrete dynamical systems. -/
abbrev ddsCoeq {X Y : DDS} (f g : DDSHom X Y) : DDS where
  carrier := Quot (fun y₁ y₂ : Y.carrier => ∃ x : X.carrier, f.toFun x = y₁ ∧ g.toFun x = y₂)
  step := Quot.lift (fun y => Quot.mk _ (Y.step y)) (by
    rintro _ _ ⟨x, rfl, rfl⟩
    exact Quot.sound ⟨X.step x, f.comm x, g.comm x⟩)

/-- A prequotient of `Set^ℕ` (Definition 4.3 of arXiv:2310.02647): a class of discrete dynamical
systems closed under isomorphisms, finite limits (terminal object, binary products, equalizers),
and small colimits (small coproducts, coequalizers). -/
def IsPrequotient (P : DDS → Prop) : Prop :=
  (∀ X Y : DDS, DDSIso X Y → P X → P Y) ∧
  P ddsUnit ∧
  (∀ X Y : DDS, P X → P Y → P (ddsProd X Y)) ∧
  (∀ (X Y : DDS) (f g : DDSHom X Y), P X → P Y → P (ddsEq f g)) ∧
  (∀ (I : Type) (F : I → DDS), (∀ i : I, P (F i)) → P (ddsCoprod F)) ∧
  (∀ (X Y : DDS) (f g : DDSHom X Y), P X → P Y → P (ddsCoeq f g))

/-- A quotient topos of `Set^ℕ` (Definition 3.2 of arXiv:2310.02647): a prequotient whose
inclusion functor admits a right adjoint (equivalently a coreflective full subcategory closed
under finite limits). -/
def IsQuotient (P : DDS → Prop) : Prop :=
  IsPrequotient P ∧
  ∀ X : DDS, ∃ (R : DDS) (ε : DDSHom R X), P R ∧
    ∀ (Y : DDS), P Y → ∀ φ : DDSHom Y X,
      ∃! ψ : DDSHom Y R, ∀ y : Y.carrier, ε.toFun (ψ.toFun y) = φ.toFun y

/-- Product partial order on `ℕ × ℕ^div`: usual order on the first coordinate and divisibility
order on the second coordinate (`0` is the top element of `ℕ^div`). -/
def divLe (x y : ℕ × ℕ) : Prop :=
  x.1 ≤ y.1 ∧ x.2 ∣ y.2

/-- An order ideal of the join-semilattice `ℕ × ℕ^div` (Definition 5.11 of arXiv:2310.02647):
a nonempty downward-closed subset closed under binary joins `(max a₁ a₂, lcm b₁ b₂)`. -/
def IsIdealNN (I : Set (ℕ × ℕ)) : Prop :=
  (0, 1) ∈ I ∧
  (∀ x y : ℕ × ℕ, divLe x y → y ∈ I → x ∈ I) ∧
  (∀ x y : ℕ × ℕ, x ∈ I → y ∈ I → (max x.1 y.1, Nat.lcm x.2 y.2) ∈ I)

/-- Canonical connected discrete dynamical system `T_{a, b}` (Definition 5.1 of arXiv:2310.02647):
a cycle `(ZMod b, +1)` (which is `(ℤ, +1)` when `b = 0`) with a tail of length `a`. -/
abbrev canonT (a b : ℕ) : DDS where
  carrier := Fin a ⊕ ZMod b
  step
    | Sum.inl ⟨0, _⟩ => Sum.inr 0
    | Sum.inl ⟨k + 1, hk⟩ => Sum.inl ⟨k, Nat.lt_of_succ_lt hk⟩
    | Sum.inr z => Sum.inr (z + 1)

/-- Quotient via prime exponents `α : Option ℕ → WithTop ℕ` (Proposition 3.9 of arXiv:2310.02647,
where `α none` bounds the height and `α (some p)` bounds the `p`-adic valuation of the period). -/
def primeQuotient (α : Option ℕ → WithTop ℕ) (X : DDS) : Prop :=
  ∀ x : X.carrier, ∃ (a b : ℕ), 0 < b ∧
    (a : WithTop ℕ) ≤ α none ∧
    (∀ p : ℕ, Nat.Prime p → ∀ k : ℕ, p ^ k ∣ b → (k : WithTop ℕ) ≤ α (some p)) ∧
    X.step^[a + b] x = X.step^[a] x

/-- Quotient of eventual bijections of height at most `a` (Proposition 3.12 of arXiv:2310.02647):
`f` restricts to a bijection on `Im(f^a)`. -/
def eventualBijQuotient (a : ℕ) (X : DDS) : Prop :=
  (∀ x₁ x₂ : X.carrier, X.step^[a + 1] x₁ = X.step^[a + 1] x₂ → X.step^[a] x₁ = X.step^[a] x₂) ∧
  (∀ x : X.carrier, ∃ y : X.carrier, X.step^[a + 1] y = X.step^[a] x)

/-- Main Classification Theorem of Hora and Kamio (arXiv:2310.02647, Theorem 5.13 and
Corollaries 3.13 & 5.14, settling Lawvere's open problem on quotient toposes for `Set^ℕ`):
1. Every prequotient of `Set^ℕ` is a quotient topos (`PQ_{Set^ℕ} = Q_{Set^ℕ}`).
2. Every prequotient is either `Set^ℕ` itself, an eventual-bijection quotient `eventualBijQuotient a`,
   or a prime-exponent hyperconnected quotient `primeQuotient α`.
3. Sending a quotient `P` to `{(a, b) ∈ ℕ × ℕ | T_{a, b} ∈ P}` is an order isomorphism between
   the poset of quotient toposes of `Set^ℕ` and the poset of ideals of `ℕ × ℕ^div`. -/
theorem main :
    (∀ P : DDS → Prop, IsPrequotient P ↔ IsQuotient P) ∧
    (∀ P : DDS → Prop, IsPrequotient P →
      (∀ X : DDS, P X) ∨
      (∃ a : ℕ, ∀ X : DDS, P X ↔ eventualBijQuotient a X) ∨
      (∃ α : Option ℕ → WithTop ℕ, ∀ X : DDS, P X ↔ primeQuotient α X)) ∧
    (∃ toIdeal : { P : DDS → Prop // IsQuotient P } → { I : Set (ℕ × ℕ) // IsIdealNN I },
      Function.Bijective toIdeal ∧
      (∀ P : { P : DDS → Prop // IsQuotient P }, ∀ ab : ℕ × ℕ,
        ab ∈ (toIdeal P).1 ↔ P.1 (canonT ab.1 ab.2)) ∧
      (∀ P Q : { P : DDS → Prop // IsQuotient P },
        (∀ X : DDS, P.1 X → Q.1 X) ↔ (toIdeal P).1 ⊆ (toIdeal Q).1)) := by sorry

end OMA.S_arxiv_2310_02647
