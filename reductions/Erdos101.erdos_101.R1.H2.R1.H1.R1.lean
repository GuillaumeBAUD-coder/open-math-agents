import OMAReductions.R_Erdos101_erdos_101_R1_H2_R1
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Order.Interval.Set.Infinite

-- Reduction Erdos101.erdos_101.R1.H2.R1.H1.R1 of step Erdos101.erdos_101.R1.H2.R1.H1
-- Credit: @eskrishnaram-ai

/-!
# Elekes-Szabó curve rigidity: surface extraction and group-law arcs

We reduce the single-component degree `≥ 4` incidence bound
`OMA.R_Erdos101_erdos_101_R1_H2_R1.H1` along the two core ingredients of
Elekes and Szabó, *On Triple Lines and Cubic Curves* (Theorem 4.1 and Lemma 2):

1. We eliminate vertical lines (proving at most `S.card` four-point lines can share a
   first coordinate between two points, leaving at least `(ε / 2) n^2` non-vertical
   four-point lines), and reduce to `H1`: any irreducible curve of degree
   `2 ≤ deg F ≤ d` supporting a dense family of non-vertical collinear triples on
   distinct lines admits a planar affine chart `(α, β, γ)` forming a standard system
   of continuous functions on `(-r, r)` whose collinearity is locally described by `(ℝ, +)`.
2. `H2` (Elekes-Szabó Lemma 2) asserts that any standard system with `(ℝ, +)`
   collinearity vanishes on a nonzero cubic curve over a non-empty open neighborhood `(-r', r')`.
3. In `main`, we pull `F` back through the inverse affine equivalence `e.symm`, prove
   by Gauss's lemma and resultants that an irreducible curve sharing an open arc with a
   nonzero cubic must divide it, and contradict `4 ≤ F.totalDegree`.
-/

namespace OMA.R_Erdos101_erdos_101_R1_H2_R1_H1_R1

open EuclideanGeometry MvPolynomial
open scoped Classical Polynomial

/-- Surface-theorem extraction on an irreducible algebraic curve of degree `2 ≤ deg F ≤ d`:
a quadratic-density family of non-vertical collinear triples on distinct lines yields an
affine change of coordinates in which three open arcs of `{F = 0}` form a standard system
of continuous functions whose collinearity is described additively over `ℝ`. -/
def H1 : Prop :=
  ∀ d : ℕ, ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ S : Finset ℝ², S.card ≤ n →
      ∀ F : MvPolynomial (Fin 2) ℝ, Irreducible F → 2 ≤ F.totalDegree → F.totalDegree ≤ d →
        (∀ p ∈ S, eval (fun i => p i) F = 0) →
        ∀ T : Finset (S × S × S), δ * (n : ℝ)^2 ≤ T.card →
          (T : Set (S × S × S)).InjOn (fun t => line[ℝ, (t.1 : ℝ²), (t.2.1 : ℝ²)]) →
          (∀ t ∈ T, (t.1 : ℝ²) 0 ≠ (t.2.1 : ℝ²) 0 ∧ (t.1 : ℝ²) 0 ≠ (t.2.2 : ℝ²) 0 ∧
            (t.2.1 : ℝ²) 0 ≠ (t.2.2 : ℝ²) 0 ∧
            Collinear ℝ ({(t.1 : ℝ²), (t.2.1 : ℝ²), (t.2.2 : ℝ²)} : Set ℝ²)) →
          ∃ (e : ℝ² ≃ᵃ[ℝ] ℝ²) (r : ℝ) (α β γ f₁ f₂ f₃ : ℝ → ℝ),
            0 < r ∧
            let I := Set.Ioo (-r) r
            ContinuousOn α I ∧ ContinuousOn β I ∧ ContinuousOn γ I ∧
            ContinuousOn f₁ I ∧ ContinuousOn f₂ I ∧ ContinuousOn f₃ I ∧
            Set.InjOn f₁ I ∧ Set.InjOn f₂ I ∧ Set.InjOn f₃ I ∧
            (∀ x ∈ I, α x < β x ∧ β x < γ x) ∧
            (∀ x ∈ I,
              eval (fun i => e.symm !₂[x, α x] i) F = 0 ∧
              eval (fun i => e.symm !₂[x, β x] i) F = 0 ∧
              eval (fun i => e.symm !₂[x, γ x] i) F = 0) ∧
            (∀ L : AffineSubspace ℝ ℝ², ∀ p₁ p₂ q : ℝ², p₁ ≠ p₂ → p₁ ∈ L → p₂ ∈ L → q ∈ L →
              ∀ x₁ ∈ I, ∀ x₂ ∈ I, ∀ y ∈ I,
                ¬ ((p₁ = !₂[x₁, α x₁] ∧ p₂ = !₂[x₂, α x₂] ∧ (q = !₂[y, β y] ∨ q = !₂[y, γ y])) ∨
                   (p₁ = !₂[x₁, β x₁] ∧ p₂ = !₂[x₂, β x₂] ∧ (q = !₂[y, α y] ∨ q = !₂[y, γ y])) ∨
                   (p₁ = !₂[x₁, γ x₁] ∧ p₂ = !₂[x₂, γ x₂] ∧ (q = !₂[y, α y] ∨ q = !₂[y, β y])))) ∧
            (∀ x₁ ∈ I, ∀ x₂ ∈ I, ∀ x₃ ∈ I,
              Collinear ℝ ({!₂[x₁, α x₁], !₂[x₂, β x₂], !₂[x₃, γ x₃]} : Set ℝ²) ↔
                f₁ x₁ + f₂ x₂ + f₃ x₃ = 0)

/-- Elekes-Szabó Lemma 2: if collinearity between the graphs of a standard system of
continuous real functions is described additively via continuous injections into `(ℝ, +)`,
then their graphs agree on an open interval around `0` with a nonzero cubic curve. -/
def H2 : Prop :=
  ∀ (r : ℝ) (α β γ f₁ f₂ f₃ : ℝ → ℝ),
    0 < r →
    let I := Set.Ioo (-r) r
    ContinuousOn α I → ContinuousOn β I → ContinuousOn γ I →
    ContinuousOn f₁ I → ContinuousOn f₂ I → ContinuousOn f₃ I →
    Set.InjOn f₁ I → Set.InjOn f₂ I → Set.InjOn f₃ I →
    (∀ x ∈ I, α x < β x ∧ β x < γ x) →
    (∀ L : AffineSubspace ℝ ℝ², ∀ p₁ p₂ q : ℝ², p₁ ≠ p₂ → p₁ ∈ L → p₂ ∈ L → q ∈ L →
      ∀ x₁ ∈ I, ∀ x₂ ∈ I, ∀ y ∈ I,
        ¬ ((p₁ = !₂[x₁, α x₁] ∧ p₂ = !₂[x₂, α x₂] ∧ (q = !₂[y, β y] ∨ q = !₂[y, γ y])) ∨
           (p₁ = !₂[x₁, β x₁] ∧ p₂ = !₂[x₂, β x₂] ∧ (q = !₂[y, α y] ∨ q = !₂[y, γ y])) ∨
           (p₁ = !₂[x₁, γ x₁] ∧ p₂ = !₂[x₂, γ x₂] ∧ (q = !₂[y, α y] ∨ q = !₂[y, β y])))) →
    (∀ x₁ ∈ I, ∀ x₂ ∈ I, ∀ x₃ ∈ I,
      Collinear ℝ ({!₂[x₁, α x₁], !₂[x₂, β x₂], !₂[x₃, γ x₃]} : Set ℝ²) ↔
        f₁ x₁ + f₂ x₂ + f₃ x₃ = 0) →
    ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧
      ∃ P : MvPolynomial (Fin 2) ℝ, P ≠ 0 ∧ P.totalDegree ≤ 3 ∧
        ∀ x ∈ Set.Ioo (-r') r',
          eval (fun i => !₂[x, α x] i) P = 0 ∧
          eval (fun i => !₂[x, β x] i) P = 0 ∧
          eval (fun i => !₂[x, γ x] i) P = 0

/-- An affine line determined by two distinct points sharing their first coordinate
consists precisely of all points with that first coordinate. -/
lemma vertical_line_eq {p q : ℝ²} (hpq : p ≠ q) (h0 : p 0 = q 0) :
    (line[ℝ, p, q] : Set ℝ²) = {z : ℝ² | z 0 = p 0} := by
  have h1 : p 1 ≠ q 1 := by
    intro h1eq
    apply hpq
    ext i
    fin_cases i
    · exact h0
    · exact h1eq
  ext z
  constructor
  · intro hz
    have hmem : z -ᵥ p ∈ vectorSpan ℝ ({p, q} : Set ℝ²) := by
      rw [← direction_affineSpan ℝ ({p, q} : Set ℝ²)]
      exact AffineSubspace.vsub_mem_direction hz (left_mem_affineSpan_pair ℝ p q)
    rw [vectorSpan_pair ℝ p q] at hmem
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    have hzp : z = t • (p -ᵥ q) +ᵥ p := by rw [ht, vsub_vadd]
    rw [hzp]
    change (t • (p -ᵥ q) +ᵥ p) 0 = p 0
    simp [h0]
  · intro hz
    change z 0 = p 0 at hz
    let t : ℝ := (z 1 - p 1) / (q 1 - p 1)
    have hline : t • (q -ᵥ p) +ᵥ p = z := by
      ext i
      fin_cases i
      · simp [h0, hz]
      · simp only [vadd_eq_add, vsub_eq_sub, PiLp.add_apply, PiLp.smul_apply,
          smul_eq_mul, PiLp.sub_apply]
        have hsub : q 1 - p 1 ≠ 0 := sub_ne_zero.mpr h1.symm
        dsimp [t]
        field_simp
        ring
    rw [← hline]
    exact AffineSubspace.smul_vsub_vadd_mem line[ℝ, p, q] t
      (right_mem_affineSpan_pair ℝ p q) (left_mem_affineSpan_pair ℝ p q)
      (left_mem_affineSpan_pair ℝ p q)

/-- At most `S.card` four-point lines of `S` contain two distinct points with equal
first coordinate. -/
lemma vertical_lines_card_le (S : Finset ℝ²) :
    let A := (OMA.R_Erdos101_erdos_101_R1.four_lines_finite S).toFinset
    let V := A.filter (fun L => ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ p 0 = q 0)
    V.card ≤ S.card := by
  intro A V
  have hx (L) (hL : L ∈ V) : ∃ a ∈ S.image (fun p => p 0),
      (L : Set ℝ²) = {z : ℝ² | z 0 = a} := by
    obtain ⟨hLA, p, hpS, q, hqS, hpq, hpL, hqL, h0⟩ := Finset.mem_filter.mp hL
    have hm := (OMA.R_Erdos101_erdos_101_R1.four_lines_finite S).mem_toFinset.mp hLA
    have hspan := OMA.R_Erdos101_erdos_101_R1.line_through hm hpL hqL hpq
    refine ⟨p 0, Finset.mem_image_of_mem _ hpS, ?_⟩
    rw [← hspan]
    exact vertical_line_eq hpq h0
  let coord : AffineSubspace ℝ ℝ² → ℝ := fun L => if h : L ∈ V then (hx L h).choose else 0
  have hcoord_mem (L) (hL : L ∈ V) : coord L ∈ S.image (fun p => p 0) := by
    simp only [coord, dif_pos hL]
    exact (hx L hL).choose_spec.1
  have hcoord_eq (L) (hL : L ∈ V) : (L : Set ℝ²) = {z : ℝ² | z 0 = coord L} := by
    simp only [coord, dif_pos hL]
    exact (hx L hL).choose_spec.2
  have hinj : Set.InjOn coord (V : Set (AffineSubspace ℝ ℝ²)) := by
    intro L₁ hL₁ L₂ hL₂ heq
    have hset : (L₁ : Set ℝ²) = (L₂ : Set ℝ²) := by
      rw [hcoord_eq L₁ hL₁, hcoord_eq L₂ hL₂, heq]
    exact SetLike.coe_injective hset
  have hmaps : Set.MapsTo coord (V : Set (AffineSubspace ℝ ℝ²))
      (S.image (fun p => p 0) : Set ℝ) := fun L hL => hcoord_mem L hL
  exact (Finset.card_le_card_of_injOn coord hmaps hinj).trans Finset.card_image_le

/-- Three points lying on the affine line spanned by the first two are collinear. -/
lemma collinear_of_mem_line {p q w : ℝ²} (hw : w ∈ line[ℝ, p, q]) :
    Collinear ℝ ({p, q, w} : Set ℝ²) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨p, p -ᵥ q, ?_⟩
  intro z hz
  rcases hz with rfl | rfl | hzw
  · exact ⟨0, by simp⟩
  · exact ⟨-1, by simp [vsub_eq_sub, vadd_eq_add]⟩
  · subst hzw
    have hmem : z -ᵥ p ∈ vectorSpan ℝ ({p, q} : Set ℝ²) := by
      rw [← direction_affineSpan ℝ ({p, q} : Set ℝ²)]
      exact AffineSubspace.vsub_mem_direction hw (left_mem_affineSpan_pair ℝ p q)
    rw [vectorSpan_pair ℝ p q] at hmem
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨t, by rw [ht, vsub_vadd]⟩

/-- From non-vertical four-point lines of `S`, select one collinear triple per line,
preserving cardinality and pairwise-distinct first coordinates. -/
lemma nonvertical_triples (S : Finset ℝ²) :
    let A := (OMA.R_Erdos101_erdos_101_R1.four_lines_finite S).toFinset
    let U := A \ A.filter (fun L => ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ p 0 = q 0)
    ∃ T : Finset (S × S × S), T.card = U.card ∧
      (T : Set (S × S × S)).InjOn (fun t => line[ℝ, (t.1 : ℝ²), (t.2.1 : ℝ²)]) ∧
      (∀ t ∈ T, (t.1 : ℝ²) 0 ≠ (t.2.1 : ℝ²) 0 ∧ (t.1 : ℝ²) 0 ≠ (t.2.2 : ℝ²) 0 ∧
        (t.2.1 : ℝ²) 0 ≠ (t.2.2 : ℝ²) 0 ∧
        Collinear ℝ ({(t.1 : ℝ²), (t.2.1 : ℝ²), (t.2.2 : ℝ²)} : Set ℝ²)) := by
  intro A U
  have hpick (L) (hL : L ∈ U) : ∃ t : S × S × S,
      line[ℝ, (t.1 : ℝ²), (t.2.1 : ℝ²)] = L ∧
      (t.1 : ℝ²) 0 ≠ (t.2.1 : ℝ²) 0 ∧ (t.1 : ℝ²) 0 ≠ (t.2.2 : ℝ²) 0 ∧
      (t.2.1 : ℝ²) 0 ≠ (t.2.2 : ℝ²) 0 ∧
      Collinear ℝ ({(t.1 : ℝ²), (t.2.1 : ℝ²), (t.2.2 : ℝ²)} : Set ℝ²) := by
    obtain ⟨hLA, hnotV⟩ := Finset.mem_sdiff.mp hL
    have hm := (OMA.R_Erdos101_erdos_101_R1.four_lines_finite S).mem_toFinset.mp hLA
    have hcard := OMA.R_Erdos101_erdos_101_R1.four_points hm
    obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ :=
      Finset.two_lt_card_iff.mp (show 2 < (S.filter (fun x => x ∈ L)).card by omega)
    obtain ⟨hpS, hpL⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqS, hqL⟩ := Finset.mem_filter.mp hq
    obtain ⟨hrS, hrL⟩ := Finset.mem_filter.mp hr
    have h0 (a b : ℝ²) (haS : a ∈ S) (hbS : b ∈ S) (haL : a ∈ L) (hbL : b ∈ L)
        (hab : a ≠ b) : a 0 ≠ b 0 := by
      intro heq
      apply hnotV
      exact Finset.mem_filter.mpr ⟨hLA, a, haS, b, hbS, hab, haL, hbL, heq⟩
    have hspan : line[ℝ, p, q] = L :=
      OMA.R_Erdos101_erdos_101_R1.line_through hm hpL hqL hpq
    refine ⟨(⟨p, hpS⟩, ⟨q, hqS⟩, ⟨r, hrS⟩), hspan,
      h0 p q hpS hqS hpL hqL hpq, h0 p r hpS hrS hpL hrL hpr, h0 q r hqS hrS hqL hrL hqr, ?_⟩
    exact collinear_of_mem_line (hspan ▸ hrL)
  let enc : {L // L ∈ U} → S × S × S := fun L => (hpick L.1 L.2).choose
  have henc_span (L : {L // L ∈ U}) :
      line[ℝ, ((enc L).1 : ℝ²), ((enc L).2.1 : ℝ²)] = L.1 :=
    (hpick L.1 L.2).choose_spec.1
  have henc_props (L : {L // L ∈ U}) :
      ((enc L).1 : ℝ²) 0 ≠ ((enc L).2.1 : ℝ²) 0 ∧
      ((enc L).1 : ℝ²) 0 ≠ ((enc L).2.2 : ℝ²) 0 ∧
      ((enc L).2.1 : ℝ²) 0 ≠ ((enc L).2.2 : ℝ²) 0 ∧
      Collinear ℝ ({((enc L).1 : ℝ²), ((enc L).2.1 : ℝ²), ((enc L).2.2 : ℝ²)} : Set ℝ²) :=
    (hpick L.1 L.2).choose_spec.2
  have henc_inj : Function.Injective enc := by
    intro L₁ L₂ heq
    have hsp : line[ℝ, ((enc L₁).1 : ℝ²), ((enc L₁).2.1 : ℝ²)] =
        line[ℝ, ((enc L₂).1 : ℝ²), ((enc L₂).2.1 : ℝ²)] := by
      rw [heq]
    rw [henc_span L₁, henc_span L₂] at hsp
    exact Subtype.ext hsp
  refine ⟨U.attach.image enc, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective U.attach henc_inj, Finset.card_attach]
  · intro t₁ ht₁ t₂ ht₂ hsp
    obtain ⟨L₁, _, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨L₂, _, rfl⟩ := Finset.mem_image.mp ht₂
    dsimp only at hsp
    rw [henc_span L₁, henc_span L₂] at hsp
    have : L₁ = L₂ := Subtype.ext hsp
    rw [this]
  · intro t ht
    obtain ⟨L, _, rfl⟩ := Finset.mem_image.mp ht
    exact henc_props L

/-- Coordinate expansion in `ℝ²` along the standard basis vectors. -/
lemma vec_expand (p : ℝ²) : p = p 0 • !₂[1, 0] + p 1 • !₂[0, 1] := by
  ext i
  fin_cases i <;> simp

/-- `AlgEquiv` preserves irreducibility. -/
lemma algEquiv_irreducible_iff {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℝ A] [Algebra ℝ B] (e : A ≃ₐ[ℝ] B) (x : A) :
    Irreducible (e x) ↔ Irreducible x := by
  constructor
  · intro h
    refine ⟨fun hu => h.not_isUnit (hu.map e.toRingHom), fun a b hab => ?_⟩
    have hab' : e x = e a * e b := by rw [← map_mul, hab]
    rcases h.isUnit_or_isUnit hab' with ha | hb
    · left
      simpa using ha.map e.symm.toRingHom
    · right
      simpa using hb.map e.symm.toRingHom
  · intro h
    refine ⟨fun hu => h.not_isUnit (by simpa using hu.map e.symm.toRingHom), fun a b hab => ?_⟩
    have hab' : x = e.symm a * e.symm b := by
      apply e.injective
      rw [map_mul, e.apply_symm_apply, e.apply_symm_apply, hab]
    rcases h.isUnit_or_isUnit hab' with ha | hb
    · left
      simpa using ha.map e.toRingHom
    · right
      simpa using hb.map e.toRingHom

/-- A substitution by polynomials of total degree at most `1` does not increase `totalDegree`. -/
lemma totalDegree_aeval_le_of_le_one (u : Fin 2 → MvPolynomial (Fin 2) ℝ)
    (hu : ∀ i, (u i).totalDegree ≤ 1) (F : MvPolynomial (Fin 2) ℝ) :
    (aeval u F).totalDegree ≤ F.totalDegree := by
  have hsum : ∀ (s : Finset (Fin 2 →₀ ℕ)) (g : (Fin 2 →₀ ℕ) → MvPolynomial (Fin 2) ℝ),
      (∀ m ∈ s, (g m).totalDegree ≤ F.totalDegree) →
      (∑ m ∈ s, g m).totalDegree ≤ F.totalDegree := by
    intro s g hg
    induction s using Finset.induction_on with
    | empty => simp
    | @insert m s hm ih =>
      rw [Finset.sum_insert hm]
      exact (totalDegree_add _ _).trans (max_le (hg m (Finset.mem_insert_self m s))
        (ih fun k hk => hg k (Finset.mem_insert_of_mem hk)))
  conv_lhs => rw [F.as_sum, map_sum]
  apply hsum
  intro m hm
  have hm_eq : monomial m (F.coeff m) = C (F.coeff m) * ∏ i : Fin 2, X i ^ m i := by
    rw [monomial_eq, Finsupp.prod_fintype m
      (fun i k => (X i : MvPolynomial (Fin 2) ℝ) ^ k) (fun _ => pow_zero _)]
  rw [hm_eq, map_mul, map_prod, aeval_C]
  have hpow : ∀ i : Fin 2, ((u i) ^ m i).totalDegree ≤ m i := by
    intro i
    exact (totalDegree_pow (u i) (m i)).trans (by simpa using Nat.mul_le_mul_left (m i) (hu i))
  have hprod : (∏ i : Fin 2, aeval u ((X i : MvPolynomial (Fin 2) ℝ) ^ m i)).totalDegree ≤ m 0 + m 1 := by
    have h01 : (∏ i : Fin 2, aeval u ((X i : MvPolynomial (Fin 2) ℝ) ^ m i)) =
        (u 0 ^ m 0) * (u 1 ^ m 1) := by
      simp [Fin.prod_univ_two]
    rw [h01]
    exact (totalDegree_mul _ _).trans (Nat.add_le_add (hpow 0) (hpow 1))
  have hmdeg : m 0 + m 1 ≤ F.totalDegree := by
    have := MvPolynomial.le_totalDegree hm
    rwa [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at this
  exact (totalDegree_mul _ _).trans (by
    rw [algebraMap_eq, totalDegree_C, zero_add]
    exact hprod.trans hmdeg)

/-- Pullback of a bivariate polynomial by an affine equivalence `φ : ℝ² ≃ᵃ[ℝ] ℝ²`
preserves irreducibility and total degree. -/
lemma affine_pullback (φ : ℝ² ≃ᵃ[ℝ] ℝ²) (F : MvPolynomial (Fin 2) ℝ) :
    ∃ G : MvPolynomial (Fin 2) ℝ,
      (Irreducible F ↔ Irreducible G) ∧
      G.totalDegree = F.totalDegree ∧
      ∀ p : ℝ², eval (fun i => p i) G = eval (fun i => φ p i) F := by
  let L : (ℝ² →ᵃ[ℝ] ℝ²) → Fin 2 → MvPolynomial (Fin 2) ℝ := fun ψ i =>
    C (ψ 0 i) + C (ψ.linear !₂[1, 0] i) * X 0 + C (ψ.linear !₂[0, 1] i) * X 1
  have hdeg (ψ : ℝ² →ᵃ[ℝ] ℝ²) (i : Fin 2) : (L ψ i).totalDegree ≤ 1 := by
    dsimp [L]
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le ?_ ?_)) ?_)
    · simp
    · exact (totalDegree_mul _ _).trans (by simp [totalDegree_X])
    · exact (totalDegree_mul _ _).trans (by simp [totalDegree_X])
  have heval (ψ : ℝ² →ᵃ[ℝ] ℝ²) (p : ℝ²) (i : Fin 2) :
      eval (fun k => p k) (L ψ i) = (ψ p) i := by
    have hp : ψ p = p 0 • ψ.linear !₂[1, 0] + p 1 • ψ.linear !₂[0, 1] + ψ 0 := by
      have h1 : ψ (p +ᵥ (0 : ℝ²)) = ψ.linear p +ᵥ ψ 0 := ψ.map_vadd 0 p
      rw [vadd_eq_add, add_zero, vadd_eq_add] at h1
      rw [h1]
      conv_lhs => rw [vec_expand p, map_add, map_smul, map_smul]
    simp only [L, map_add, map_mul, eval_C, eval_X, hp, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
    ring
  let Φ : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ := aeval (L (φ : ℝ² →ᵃ[ℝ] ℝ²))
  let Ψ : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ := aeval (L (φ.symm : ℝ² →ᵃ[ℝ] ℝ²))
  have hΦeval (Q : MvPolynomial (Fin 2) ℝ) (p : ℝ²) :
      eval (fun k => p k) (Φ Q) = eval (fun i => (φ p) i) Q := by
    change ((eval (fun k => p k)).comp Φ.toRingHom) Q = eval (fun i => (φ p) i) Q
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Φ]
    · intro i
      simpa [Φ] using heval (φ : ℝ² →ᵃ[ℝ] ℝ²) p i
  have hΨeval (Q : MvPolynomial (Fin 2) ℝ) (p : ℝ²) :
      eval (fun k => p k) (Ψ Q) = eval (fun i => (φ.symm p) i) Q := by
    change ((eval (fun k => p k)).comp Ψ.toRingHom) Q = eval (fun i => (φ.symm p) i) Q
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Ψ]
    · intro i
      simpa [Ψ] using heval (φ.symm : ℝ² →ᵃ[ℝ] ℝ²) p i
  have hΦΨ : Φ.comp Ψ = AlgHom.id ℝ (MvPolynomial (Fin 2) ℝ) := by
    apply MvPolynomial.algHom_ext
    intro i
    apply MvPolynomial.funext
    intro v
    let p : ℝ² := !₂[v 0, v 1]
    have hp : (fun k => p k) = v := by
      funext k
      fin_cases k <;> rfl
    rw [AlgHom.comp_apply, AlgHom.id_apply, ← hp, hΦeval, hΨeval]
    simp [φ.symm_apply_apply]
  have hΨΦ : Ψ.comp Φ = AlgHom.id ℝ (MvPolynomial (Fin 2) ℝ) := by
    apply MvPolynomial.algHom_ext
    intro i
    apply MvPolynomial.funext
    intro v
    let p : ℝ² := !₂[v 0, v 1]
    have hp : (fun k => p k) = v := by
      funext k
      fin_cases k <;> rfl
    rw [AlgHom.comp_apply, AlgHom.id_apply, ← hp, hΨeval, hΦeval]
    simp [φ.apply_symm_apply]
  let E : MvPolynomial (Fin 2) ℝ ≃ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
    AlgEquiv.ofAlgHom Φ Ψ hΦΨ hΨΦ
  refine ⟨Φ F, (algEquiv_irreducible_iff E F).symm, ?_, fun p => hΦeval F p⟩
  apply le_antisymm
  · exact totalDegree_aeval_le_of_le_one _ (hdeg (φ : ℝ² →ᵃ[ℝ] ℝ²)) F
  · have hback : Ψ (Φ F) = F := DFunLike.congr_fun hΨΦ F
    conv_lhs => rw [← hback]
    exact totalDegree_aeval_le_of_le_one _ (hdeg (φ.symm : ℝ² →ᵃ[ℝ] ℝ²)) (Φ F)

/-- Two bivariate polynomials over `ℝ` vanishing on an open graph arc
`{(x, α x) | x ∈ Ioo a b}` (`a < b`) cannot be irreducible of degree `≥ 4` and
nonzero of degree `≤ 3`. -/
lemma open_arc_contradiction (F P : MvPolynomial (Fin 2) ℝ)
    (hF : Irreducible F) (hFdeg : 4 ≤ F.totalDegree)
    (hP : P ≠ 0) (hPdeg : P.totalDegree ≤ 3)
    (α : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hvan : ∀ x ∈ Set.Ioo a b,
      eval (fun i => !₂[x, α x] i) F = 0 ∧ eval (fun i => !₂[x, α x] i) P = 0) :
    False := by
  let E : MvPolynomial (Fin 2) ℝ ≃ₐ[ℝ] Polynomial (Polynomial ℝ) :=
    (MvPolynomial.renameEquiv ℝ (Equiv.swap (0 : Fin 2) 1)).trans
      ((MvPolynomial.finSuccEquiv ℝ 1).trans
        (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1))))
  have hevalE (Q : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
      ((E Q).map (Polynomial.evalRingHom x)).eval y = eval (fun i => !₂[x, y] i) Q := by
    let lhs : MvPolynomial (Fin 2) ℝ →+* ℝ :=
      (Polynomial.evalRingHom y).comp
        ((Polynomial.mapRingHom (Polynomial.evalRingHom x)).comp E.toRingHom)
    let rhs : MvPolynomial (Fin 2) ℝ →+* ℝ := eval (fun i => !₂[x, y] i)
    change lhs Q = rhs Q
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro r
      have hCr : E (C r) = Polynomial.C (Polynomial.C r) := by
        rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
        rfl
      change Polynomial.eval y (Polynomial.map (Polynomial.evalRingHom x) (E (C r))) =
        eval (fun i => !₂[x, y] i) (C r)
      rw [hCr]
      simp
    · intro i
      fin_cases i <;> dsimp
      · have hX0 : E (X 0) = Polynomial.C Polynomial.X := by
          dsimp [E]
          have hsw : renameEquiv ℝ (Equiv.swap (0 : Fin 2) 1) (X 0) = X 1 := by
            simp [renameEquiv_apply, rename_X]
          rw [hsw, show (1 : Fin 2) = Fin.succ 0 by rfl, finSuccEquiv_X_succ]
          change Polynomial.map (uniqueAlgEquiv ℝ (Fin 1)).toRingHom
            (Polynomial.C (X 0)) = Polynomial.C Polynomial.X
          rw [Polynomial.map_C]
          congr 1
          change (uniqueAlgEquiv ℝ (Fin 1)) (monomial (Finsupp.single 0 1) 1) = Polynomial.X
          rw [MvPolynomial.uniqueAlgEquiv_monomial]
          ext k
          simp [Polynomial.coeff_monomial, Polynomial.coeff_X, eq_comm]
        change Polynomial.eval y (Polynomial.map (Polynomial.evalRingHom x) (E (X 0))) =
          eval (fun i => !₂[x, y] i) (X 0)
        rw [hX0]
        simp
      · have hX1 : E (X 1) = Polynomial.X := by
          dsimp [E]
          have hsw : renameEquiv ℝ (Equiv.swap (0 : Fin 2) 1) (X 1) = X 0 := by
            simp [renameEquiv_apply, rename_X]
          rw [hsw, finSuccEquiv_X_zero]
          simp
        change Polynomial.eval y (Polynomial.map (Polynomial.evalRingHom x) (E (X 1))) =
          eval (fun i => !₂[x, y] i) (X 1)
        rw [hX1]
        simp
  let F₁ : Polynomial (Polynomial ℝ) := E F
  let P₁ : Polynomial (Polynomial ℝ) := E P
  have hF₁_irr : Irreducible F₁ := (algEquiv_irreducible_iff E F).mpr hF
  have hF₁_deg : 0 < F₁.natDegree := by
    by_contra! hzero
    have h0 : F₁.natDegree = 0 := Nat.eq_zero_of_le_zero hzero
    let r : Polynomial ℝ := F₁.coeff 0
    have hFr : F₁ = Polynomial.C r := Polynomial.eq_C_of_natDegree_eq_zero h0
    have hr_ne : r ≠ 0 := by
      intro hr0
      apply hF₁_irr.ne_zero
      rw [hFr, hr0, Polynomial.C_0]
    have hroots : Set.Ioo a b ⊆ (r.roots.toFinset : Set ℝ) := by
      intro x hx
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hr_ne]
      have hf := (hvan x hx).1
      rw [← hevalE F x (α x)] at hf
      change (F₁.map (Polynomial.evalRingHom x)).eval (α x) = 0 at hf
      rw [hFr] at hf
      simpa using hf
    exact (Set.Ioo_infinite hab) (r.roots.toFinset.finite_toSet.subset hroots)
  have hprim : F₁.IsPrimitive := hF₁_irr.isPrimitive hF₁_deg.ne'
  let ι : Polynomial ℝ →+* FractionRing (Polynomial ℝ) :=
    algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ))
  have hFK : Irreducible (F₁.map ι) :=
    (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map hprim).mp hF₁_irr
  have hndvd : ¬ (F₁.map ι ∣ P₁.map ι) := by
    intro hdvd
    have hdvd1 : F₁ ∣ P₁ := hprim.dvd_of_fraction_map_dvd_fraction_map hdvd
    have hFP : F ∣ P := by
      obtain ⟨Q₁, hQ₁⟩ := hdvd1
      refine ⟨E.symm Q₁, ?_⟩
      apply E.injective
      rw [map_mul, E.apply_symm_apply, ← hQ₁]
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hFP hP
    omega
  have hcop : IsCoprime (F₁.map ι) (P₁.map ι) :=
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hFK).coprime_iff_not_dvd.mpr hndvd
  let R : Polynomial ℝ := F₁.resultant P₁
  have hR_ne : R ≠ 0 := by
    intro hR0
    have hinj := FaithfulSMul.algebraMap_injective (Polynomial ℝ) (FractionRing (Polynomial ℝ))
    have hres : (F₁.map ι).resultant (P₁.map ι) = 0 := by
      have hm : (F₁.map ι).natDegree = F₁.natDegree :=
        Polynomial.natDegree_map_eq_of_injective hinj F₁
      have hn : (P₁.map ι).natDegree = P₁.natDegree :=
        Polynomial.natDegree_map_eq_of_injective hinj P₁
      change (F₁.map ι).resultant (P₁.map ι) (F₁.map ι).natDegree (P₁.map ι).natDegree = 0
      rw [hm, hn, Polynomial.resultant_map_map]
      change ι R = 0
      rw [hR0, map_zero]
    exact (Polynomial.resultant_ne_zero _ _ hcop) hres
  obtain ⟨u, v, _, _, huv⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant F₁ P₁ le_rfl le_rfl (Or.inl hF₁_deg.ne')
  have hRroots : Set.Ioo a b ⊆ (R.roots.toFinset : Set ℝ) := by
    intro x hx
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hR_ne]
    let φx := Polynomial.evalRingHom x
    have hmul := congrArg (fun W => (W.map φx).eval (α x)) huv
    have hF0 : (F₁.map φx).eval (α x) = 0 := by
      rw [hevalE F x (α x)]
      exact (hvan x hx).1
    have hP0 : (P₁.map φx).eval (α x) = 0 := by
      rw [hevalE P x (α x)]
      exact (hvan x hx).2
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add,
      Polynomial.eval_mul, hF0, hP0, zero_mul, add_zero, Polynomial.map_C,
      Polynomial.eval_C] at hmul
    exact hmul.symm
  exact (Set.Ioo_infinite hab) (R.roots.toFinset.finite_toSet.subset hRroots)

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R1_H2_R1.H1 := by
  intro h₁ h₂ d ε hε
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨N₁, hN₁⟩ := h₁ d δ hδ
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / ε)
  refine ⟨max N₁ (max K 1), ?_⟩
  intro n hn S hSn hcap F hF hFdeg4 hFd hzero
  by_contra! hdense
  let hfin := OMA.R_Erdos101_erdos_101_R1.four_lines_finite S
  let A := hfin.toFinset
  rw [Set.ncard_eq_toFinset_card _ hfin] at hdense
  let V := A.filter (fun L => ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ p 0 = q 0)
  let U := A \ V
  have hVcard : V.card ≤ n := (vertical_lines_card_le S).trans hSn
  have hVreal : (V.card : ℝ) ≤ n := by exact_mod_cast hVcard
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnK : (K : ℝ) ≤ n := by exact_mod_cast (show K ≤ n by omega)
  have htwo : (2 : ℝ) < ε * n := by
    have := (div_lt_iff₀ hε).mp hK
    linarith [mul_le_mul_of_nonneg_left hnK hε.le]
  have hn_sq : (n : ℝ) < δ * (n : ℝ)^2 := by
    dsimp [δ]
    nlinarith [show 0 < (n : ℝ) by linarith]
  have hUadd : A.card ≤ V.card + U.card := by
    have : A ⊆ V ∪ U := fun L hL => by
      by_cases hv : L ∈ V <;> simp [U, hv, hL]
    exact (Finset.card_le_card this).trans (Finset.card_union_le ..)
  have hUreal : δ * (n : ℝ)^2 ≤ (U.card : ℝ) := by
    have : (A.card : ℝ) ≤ V.card + U.card := by exact_mod_cast hUadd
    dsimp [δ] at hdense hn_sq ⊢
    linarith
  obtain ⟨T, hTU, hTinj, hTprops⟩ := nonvertical_triples S
  have hTcard : δ * (n : ℝ)^2 ≤ (T.card : ℝ) := by
    rw [hTU]
    exact hUreal
  have hFdeg2 : 2 ≤ F.totalDegree := by omega
  obtain ⟨e, r, α, β, γ, f₁, f₂, f₃, hr,
      hα, hβ, hγ, hf₁, hf₂, hf₃, hi₁, hi₂, hi₃, hord, hcurve, hstd, hgrp⟩ :=
    hN₁ n (by omega) S hSn F hF hFdeg2 hFd hzero T hTcard hTinj hTprops
  obtain ⟨r', hr', hrr', P, hPne, hPdeg, hPvan⟩ :=
    h₂ r α β γ f₁ f₂ f₃ hr hα hβ hγ hf₁ hf₂ hf₃ hi₁ hi₂ hi₃ hord hstd hgrp
  obtain ⟨G, hGirr_iff, hGdeg, hGeval⟩ := affine_pullback e.symm F
  have hGirr : Irreducible G := hGirr_iff.mp hF
  have hGdeg4 : 4 ≤ G.totalDegree := hGdeg ▸ hFdeg4
  refine open_arc_contradiction G P hGirr hGdeg4 hPne hPdeg α (-r') r' (by linarith) ?_
  intro x hx
  have hx' : x ∈ Set.Ioo (-r) r := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  refine ⟨?_, (hPvan x hx).1⟩
  rw [hGeval !₂[x, α x]]
  exact (hcurve x hx').1

end OMA.R_Erdos101_erdos_101_R1_H2_R1_H1_R1
