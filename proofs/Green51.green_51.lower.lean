import FormalConjectures.GreensOpenProblems.«51»
import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
A dense set in a binary vector space has a sumset containing a subspace of dimension
linear in the ambient dimension. We iterate the hyperplane restriction of Sanders,
“Green's sumset problem at density one half”, Lemma 4.2 (arXiv:1003.5649).
-/

open scoped BigOperators Pointwise
open Finset Module

open scoped Classical
noncomputable section

namespace DenseSumset

private abbrev K := ZMod 2

variable {V : Type*} [AddCommGroup V] [Module K V]

private lemma add_self₂ (x : V) : x + x = 0 := by
  calc
    x + x = (2 : K) • x := (two_smul K x).symm
    _ = 0 := by rw [show (2 : K) = 0 by decide, zero_smul]

private def sign (χ : Module.Dual K V) (v : V) : ℝ :=
  if χ v = 0 then 1 else -1

private lemma sign_zero (v : V) : sign (0 : Module.Dual K V) v = 1 := by
  simp [sign]

private lemma sign_at_zero (χ : Module.Dual K V) : sign χ 0 = 1 := by
  simp [sign]

private lemma zero_or_one : ∀ a : K, a = 0 ∨ a = 1 := by decide

private lemma sign_add (χ : Module.Dual K V) (v w : V) :
    sign χ (v + w) = sign χ v * sign χ w := by
  unfold sign
  rw [map_add]
  generalize χ v = a
  generalize χ w = b
  rcases zero_or_one a with rfl | rfl <;> rcases zero_or_one b with rfl | rfl <;>
    simp [show (1 : K) + 1 = 0 by decide]

private lemma sign_add_dual (χ ψ : Module.Dual K V) (v : V) :
    sign (χ + ψ) v = sign χ v * sign ψ v := by
  unfold sign
  rw [LinearMap.add_apply]
  generalize χ v = a
  generalize ψ v = b
  rcases zero_or_one a with rfl | rfl <;> rcases zero_or_one b with rfl | rfl <;>
    simp [show (1 : K) + 1 = 0 by decide]

private lemma sign_sq (χ : Module.Dual K V) (v : V) : sign χ v * sign χ v = 1 := by
  rw [← sign_add, add_self₂, sign_at_zero]

variable [Fintype V]

private local instance finiteDual : Finite (Module.Dual K V) :=
  Finite.of_injective (fun f : Module.Dual K V => (f : V → K)) DFunLike.coe_injective

private local instance fintypeDual : Fintype (Module.Dual K V) := Fintype.ofFinite _

private lemma dual_card : Fintype.card (Module.Dual K V) = Fintype.card V := by
  rw [Module.card_eq_pow_finrank (K := K) (V := Module.Dual K V),
    Module.card_eq_pow_finrank (K := K) (V := V), Subspace.dual_finrank_eq]

private lemma sign_sum (v : V) :
    ∑ χ : Module.Dual K V, sign χ v = if v = 0 then (Fintype.card V : ℝ) else 0 := by
  classical
  by_cases hv : v = 0
  · simp [hv, sign_at_zero, dual_card]
  · obtain ⟨χ, hχ⟩ := Projective.exists_dual_eq_one K hv
    have hs : sign χ v = -1 := by simp [sign, hχ]
    have hneg : (∑ ψ : Module.Dual K V, sign ψ v) = -(∑ ψ : Module.Dual K V, sign ψ v) := by
      calc
        _ = ∑ ψ : Module.Dual K V, sign (χ + ψ) v :=
          (Fintype.sum_equiv (Equiv.addLeft χ) _ _ fun ψ => rfl).symm
        _ = -(∑ ψ : Module.Dual K V, sign ψ v) := by
          simp_rw [sign_add_dual, hs, neg_one_mul]
          rw [sum_neg_distrib]
    simp only [if_neg hv]
    linarith

private lemma sign_orthogonal (v w : V) :
    ∑ χ : Module.Dual K V, sign χ v * sign χ w =
      if v = w then (Fintype.card V : ℝ) else 0 := by
  simp_rw [← sign_add, sign_sum]
  congr 1
  apply propext
  constructor
  · intro hvw
    calc
      v = (v + w) + w := by rw [add_assoc, add_self₂, add_zero]
      _ = w := by rw [hvw, zero_add]
  · rintro rfl
    exact add_self₂ v


variable {G : Type*} [AddCommGroup G] [Module K G] [Fintype G]

private def coefficient (C : V → ℝ) (χ : Module.Dual K V) : ℝ :=
  ∑ v : V, C v * sign χ v

private def correlation (ι : V →ₗ[K] G) (I : G → ℝ) (v : V) : ℝ :=
  ∑ x : G, I x * I (x + ι v)

private lemma coefficient_square (ι : V →ₗ[K] G) (I : G → ℝ)
    (χ : Module.Dual K V) :
    (Fintype.card V : ℝ) * coefficient (correlation ι I) χ =
      ∑ x : G, (∑ v : V, I (x + ι v) * sign χ v) ^ 2 := by
  let f (x : G) (v : V) := I (x + ι v) * sign χ v
  have hrow (x : G) (u : V) :
      (∑ v : V, f x u * f x v) =
        ∑ w : V, I (x + ι u) * I ((x + ι u) + ι w) * sign χ w := by
    refine (Fintype.sum_equiv (Equiv.addLeft u) _ _ ?_).symm
    intro w
    change I (x + ι u) * I (x + ι u + ι w) * sign χ w =
      I (x + ι u) * sign χ u * (I (x + ι (u + w)) * sign χ (u + w))
    rw [map_add, ← add_assoc, sign_add]
    calc
      _ = I (x + ι u) * I (x + ι u + ι w) * (sign χ u * sign χ u) * sign χ w := by
        rw [sign_sq, mul_one]
      _ = _ := by ring
  symm
  change (∑ x : G, (∑ v : V, f x v) ^ 2) = _
  simp_rw [pow_two, sum_mul, mul_sum, hrow]
  rw [sum_comm]
  calc
    _ = ∑ u : V, coefficient (correlation ι I) χ := by
      apply sum_congr rfl
      intro u _
      calc
        _ = ∑ x : G, ∑ w : V, I x * I (x + ι w) * sign χ w := by
          let row (x : G) := ∑ w : V, I x * I (x + ι w) * sign χ w
          exact Fintype.sum_equiv (Equiv.addRight (ι u)) (fun x => row (x + ι u)) row
            (fun _ => rfl)
        _ = _ := by
          rw [sum_comm (s := (univ : Finset G)) (t := (univ : Finset V))]
          simp [coefficient, correlation, sum_mul]
    _ = _ := by simp [nsmul_eq_mul]

private lemma coefficient_nonneg (ι : V →ₗ[K] G) (I : G → ℝ)
    (χ : Module.Dual K V) : 0 ≤ coefficient (correlation ι I) χ := by
  apply nonneg_of_mul_nonneg_right ?_ (by positivity : (0 : ℝ) < Fintype.card V)
  rw [coefficient_square]
  exact sum_nonneg fun _ _ => sq_nonneg _

private lemma coefficient_sum (C : V → ℝ) :
    ∑ χ : Module.Dual K V, coefficient C χ = (Fintype.card V : ℝ) * C 0 := by
  simp_rw [coefficient]
  rw [sum_comm]
  simp [← mul_sum, sign_sum, mul_comm]

private lemma coefficient_pairing (C : V → ℝ) (S : Finset V) :
    ∑ χ : Module.Dual K V, coefficient C χ * (∑ w ∈ S, sign χ w) =
      (Fintype.card V : ℝ) * ∑ w ∈ S, C w := by
  calc
    _ = ∑ χ : Module.Dual K V, ∑ w ∈ S, ∑ v : V,
        C v * (sign χ v * sign χ w) := by
      simp_rw [mul_sum, coefficient, sum_mul, mul_assoc]
    _ = ∑ w ∈ S, ∑ v : V, C v * (∑ χ : Module.Dual K V,
        sign χ v * sign χ w) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro w hw
      rw [sum_comm]
      simp_rw [mul_sum]
    _ = _ := by
      simp_rw [sign_orthogonal, mul_ite, mul_zero]
      simp [← sum_mul, mul_comm]

private def indicator (A : Finset G) (x : G) : ℝ := if x ∈ A then 1 else 0

omit [AddCommGroup G] [Module K G] in
private lemma sum_indicator (A : Finset G) : ∑ x : G, indicator A x = A.card := by
  simp [indicator]

omit [Fintype V] in
private lemma correlation_zero (ι : V →ₗ[K] G) (A : Finset G) :
    correlation ι (indicator A) 0 = A.card := by
  unfold correlation
  simp_rw [map_zero, add_zero]
  convert sum_indicator A using 1
  apply sum_congr rfl
  intro x hx
  by_cases h : x ∈ A <;> simp [indicator, h]

omit [Fintype V] in
private lemma correlation_vanish (ι : V →ₗ[K] G) (A : Finset G) {v : V}
    (hv : ι v ∉ A + A) : correlation ι (indicator A) v = 0 := by
  unfold correlation
  apply sum_eq_zero
  intro x hx
  by_cases ha : x ∈ A
  · have hb : x + ι v ∉ A := by
      intro h
      apply hv
      rw [← zero_add (ι v), ← add_self₂ x, add_assoc]
      exact Finset.mem_add.mpr ⟨x, ha, x + ι v, h, rfl⟩
    simp [indicator, hb]
  · simp [indicator, ha]

private lemma coefficient_zero_bound (ι : V →ₗ[K] G) (A : Finset G) (α : ℝ)
    (hA : α * (Fintype.card G : ℝ) ≤ A.card) :
    α * ((Fintype.card V : ℝ) * A.card) ≤ coefficient (correlation ι (indicator A)) 0 := by
  let T (x : G) := ∑ v : V, indicator A (x + ι v)
  have hsum : ∑ x : G, T x = (Fintype.card V : ℝ) * A.card := by
    change (∑ x : G, ∑ v : V, indicator A (x + ι v)) = _
    rw [sum_comm]
    have h (v : V) : (∑ x : G, indicator A (x + ι v)) = A.card := by
      calc
        _ = ∑ x : G, indicator A x := Fintype.sum_equiv (Equiv.addRight (ι v)) _ _ fun _ => rfl
        _ = _ := sum_indicator A
    simp [h, nsmul_eq_mul]
  have hsquare := sq_sum_le_card_mul_sum_sq (s := (univ : Finset G)) (f := T)
  simp only [hsum, card_univ] at hsquare
  have hcoeff := coefficient_square ι (indicator A) (0 : Module.Dual K V)
  simp only [sign_zero, mul_one] at hcoeff
  change (Fintype.card V : ℝ) * coefficient (correlation ι (indicator A)) 0 =
    ∑ x : G, T x ^ 2 at hcoeff
  rw [← hcoeff] at hsquare
  have hV : (0 : ℝ) < Fintype.card V := by positivity
  have hG : (0 : ℝ) < Fintype.card G := by positivity
  have hproduct := mul_le_mul_of_nonneg_left hA
    (show 0 ≤ (Fintype.card V : ℝ) ^ 2 * A.card by positivity)
  apply le_of_mul_le_mul_left _ (mul_pos hG hV)
  nlinarith only [hsquare, hproduct]

omit [Fintype V] in
private lemma sign_filter_sum (χ : Module.Dual K V) (S : Finset V) :
    (∑ v ∈ S, sign χ v) = 2 * ((S.filter fun v => χ v = 0).card : ℝ) - S.card := by
  have hsplit : (∑ v ∈ S with χ v = 0, sign χ v) +
      (∑ v ∈ S with ¬χ v = 0, sign χ v) = (∑ v ∈ S, sign χ v) :=
    sum_filter_add_sum_filter_not _ _ _
  have hzero : (∑ v ∈ S with χ v = 0, sign χ v) = (S.filter fun v => χ v = 0).card := by
    calc
      _ = ∑ v ∈ S with χ v = 0, (1 : ℝ) := by
        apply sum_congr rfl
        intro v hv
        simp [sign, (mem_filter.mp hv).2]
      _ = _ := by simp
  have hone : (∑ v ∈ S with ¬χ v = 0, sign χ v) =
      -((S.filter fun v => ¬χ v = 0).card : ℝ) := by
    calc
      _ = ∑ v ∈ S with ¬χ v = 0, (-1 : ℝ) := by
        apply sum_congr rfl
        intro v hv
        simp [sign, (mem_filter.mp hv).2]
      _ = _ := by simp [nsmul_eq_mul]
  have hcard := card_filter_add_card_filter_not (s := S) (p := fun v => χ v = 0)
  have hcardR := congrArg (fun n : ℕ => (n : ℝ)) hcard
  push_cast at hcardR
  linarith

private lemma find_cut (ι : V →ₗ[K] G) (A : Finset G) (S : Finset V) (α : ℝ)
    (ha : 0 < α) (hA : α * (Fintype.card G : ℝ) ≤ A.card)
    (hS : S.Nonempty) (hbad : ∀ v ∈ S, ι v ∉ A + A) :
    ∃ χ : Module.Dual K V, χ ≠ 0 ∧
      ((S.filter fun v => χ v = 0).card : ℝ) ≤ ((1 - α/2) / 2) * S.card := by
  let c := coefficient (correlation ι (indicator A))
  let t (χ : Module.Dual K V) := ∑ w ∈ S, sign χ w
  let M := (Fintype.card V : ℝ) * A.card
  have hM : 0 < M := by
    have hg : (0 : ℝ) < Fintype.card G := by positivity
    exact mul_pos (by positivity) ((mul_pos ha hg).trans_le hA)
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hcn (χ : Module.Dual K V) : 0 ≤ c χ := coefficient_nonneg ι (indicator A) χ
  have hc0 : α * M ≤ c 0 := coefficient_zero_bound ι A α hA
  have hsc : ∑ χ : Module.Dual K V, c χ = M := by
    rw [show c = coefficient (correlation ι (indicator A)) from rfl,
      coefficient_sum, correlation_zero]
  have hst : ∑ χ : Module.Dual K V, c χ * t χ = 0 := by
    change (∑ χ : Module.Dual K V, coefficient (correlation ι (indicator A)) χ *
      (∑ w ∈ S, sign χ w)) = 0
    rw [coefficient_pairing, sum_eq_zero fun v hv => correlation_vanish ι A (hbad v hv), mul_zero]
  have ht0 : t 0 = S.card := by simp [t, sign_zero]
  have hθ : 0 < α/2 := by positivity
  suffices ∃ χ : Module.Dual K V, χ ≠ 0 ∧ t χ ≤ -(α/2) * S.card by
    obtain ⟨χ, hχ, ht⟩ := this
    refine ⟨χ, hχ, ?_⟩
    change (∑ w ∈ S, sign χ w) ≤ _ at ht
    rw [sign_filter_sum] at ht
    linarith
  by_contra! h
  let f (χ : Module.Dual K V) := c χ * (t χ + (α/2) * S.card)
  have hfn (χ : Module.Dual K V) : 0 ≤ f χ := by
    apply mul_nonneg (hcn χ)
    by_cases hχ : χ = 0
    · rw [hχ, ht0]
      positivity
    · linarith [h χ hχ]
  have hsingle : f 0 ≤ ∑ χ : Module.Dual K V, f χ :=
    single_le_sum (fun χ _ => hfn χ) (mem_univ _)
  have hsum : ∑ χ : Module.Dual K V, f χ = M * ((α/2) * S.card) := by
    simp only [f, mul_add, sum_add_distrib, ← sum_mul, hsc, hst, zero_add]
  rw [hsum] at hsingle
  have hpos : 0 < (α/2) * (M * S.card) := mul_pos hθ (mul_pos hM hcard)
  have hle : α * M * S.card ≤ f 0 := by
    calc
      α * M * S.card ≤ c 0 * S.card := mul_le_mul_of_nonneg_right hc0 hcard.le
      _ ≤ _ := by
        change c 0 * S.card ≤ c 0 * (t 0 + (α/2) * S.card)
        rw [ht0]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (hcn 0)
  linarith only [hsingle, hpos, hle]

private local instance fintypeSubspace (W : Submodule K G) : Fintype W := Fintype.ofFinite _

private def missing (A : Finset G) (W : Submodule K G) : Finset W :=
  univ.filter fun v => (v : G) ∉ A + A

private lemma mem_missing {A : Finset G} {W : Submodule K G} {v : W} :
    v ∈ missing A W ↔ (v : G) ∉ A + A := by simp [missing]

private lemma restrict_missing (A : Finset G) (W : Submodule K G)
    (χ : Module.Dual K W) :
    (missing A ((LinearMap.ker χ).map W.subtype)).card =
      ((missing A W).filter fun v => χ v = 0).card := by
  let W' : Submodule K G := (LinearMap.ker χ).map W.subtype
  have hle : W' ≤ W := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    exact w.property
  let e : W' ↪ W := ⟨fun v => ⟨v, hle v.property⟩,
    fun _ _ h => Subtype.ext (congrArg (fun w : W => (w : G)) h)⟩
  suffices h : (missing A W').map e = (missing A W).filter fun v => χ v = 0 by
    simpa only [card_map] using congrArg card h
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hv
    refine mem_filter.mpr ⟨mem_missing.mpr ((mem_missing (W := W')).mp hw), ?_⟩
    obtain ⟨u, hu, hwu⟩ := Submodule.mem_map.mp w.property
    have he : e w = u := Subtype.ext hwu.symm
    rw [he]
    exact LinearMap.mem_ker.mp hu
  · intro hv
    obtain ⟨hv, hχ⟩ := mem_filter.mp hv
    have hvW : (v : G) ∈ W' := Submodule.mem_map.mpr ⟨v, LinearMap.mem_ker.mpr hχ, rfl⟩
    exact mem_map.mpr ⟨⟨v, hvW⟩, mem_missing.mpr ((mem_missing (W := W)).mp hv), Subtype.ext rfl⟩

private lemma restrict_rank (W : Submodule K G) (χ : Module.Dual K W) (hχ : χ ≠ 0) :
    finrank K ((LinearMap.ker χ).map W.subtype : Submodule K G) + 1 = finrank K W := by
  have hx : ∃ x : W, χ x = 1 := by
    by_contra! hx
    apply hχ
    ext x
    exact (zero_or_one (χ x)).resolve_right (hx x)
  obtain ⟨x, hx⟩ := hx
  have hsurj : Function.Surjective χ := by
    intro y
    rcases zero_or_one y with rfl | rfl
    · exact ⟨0, map_zero χ⟩
    · exact ⟨x, hx⟩
  have hd := LinearMap.finrank_range_add_finrank_ker χ
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_self] at hd
  rw [← (Submodule.equivMapOfInjective W.subtype Subtype.val_injective _).finrank_eq,
    add_comm]
  exact hd

private lemma sumset_restrict (A : Finset G) (α : ℝ) (ha : 0 < α)
    (hA : α * (Fintype.card G : ℝ) ≤ A.card) (W : Submodule K G)
    (hW : (missing A W).Nonempty) :
    ∃ W' : Submodule K G, finrank K W' + 1 = finrank K W ∧
      ((missing A W').card : ℝ) ≤ (1 - α/2) / 2 * (missing A W).card := by
  obtain ⟨χ, hχ, hc⟩ := find_cut W.subtype A (missing A W) α ha hA hW
    (fun _ h => mem_missing.mp h)
  exact ⟨(LinearMap.ker χ).map W.subtype, restrict_rank W χ hχ,
    (by rw [restrict_missing]; exact hc)⟩

private lemma iterate_restrict (A : Finset G) (α : ℝ) (ha : 0 < α) (ha' : α ≤ 1)
    (hA : α * (Fintype.card G : ℝ) ≤ A.card) (i : ℕ) :
    ∃ W : Submodule K G, finrank K G - i ≤ finrank K W ∧
      ((missing A W).card : ℝ) ≤ Fintype.card G * ((1 - α/2) / 2) ^ i := by
  have hr : 0 ≤ (1 - α/2) / 2 := by linarith
  induction i with
  | zero =>
      refine ⟨⊤, by simp, ?_⟩
      simpa using (show ((missing A (⊤ : Submodule K G)).card : ℝ) ≤ Fintype.card G by
        exact_mod_cast (card_le_univ (s := missing A (⊤ : Submodule K G))).trans_eq
          (Fintype.card_congr (Submodule.topEquiv : (⊤ : Submodule K G) ≃ₗ[K] G).toEquiv))
  | succ i ih =>
      obtain ⟨W, hd, hs⟩ := ih
      by_cases h : (missing A W).Nonempty
      · obtain ⟨W', hd', hs'⟩ := sumset_restrict A α ha hA W h
        refine ⟨W', by omega, ?_⟩
        calc
          _ ≤ (1 - α/2) / 2 * (missing A W).card := hs'
          _ ≤ (1 - α/2) / 2 * (Fintype.card G * ((1 - α/2) / 2) ^ i) :=
            mul_le_mul_of_nonneg_left hs hr
          _ = _ := by rw [pow_succ]; ring
      · refine ⟨W, by omega, ?_⟩
        have he := not_nonempty_iff_eq_empty.mp h
        rw [he, card_empty, Nat.cast_zero]
        positivity

private lemma dim_vector (n : ℕ) : finrank K (𝔽₂ n) = n := by
  rw [Module.finrank_pi, Fintype.card_fin]

private lemma card_vector (n : ℕ) : Fintype.card (𝔽₂ n) = 2 ^ n := by
  simp [𝔽₂, 𝔽, ZMod.card]

private lemma coset_lower (n B : ℕ) (α : ℝ) (ha : 0 < α) (ha' : α ≤ 1)
    (hB : 1 ≤ B) (hn : 2 * B ≤ n) (hp : (1 - α/2) ^ (B-1) < 1/2)
    (A : Finset (𝔽₂ n)) (hA : α ≤ A.dens) :
    n / B ≤ maxCosetDim K (𝔽₂ n) ↑(A + A) := by
  let d := n / B
  have hd : 0 < d := Nat.div_pos (by omega : B ≤ n) (by omega)
  have hdle : d ≤ n := Nat.div_le_self n B
  have hBd : d * B ≤ n := Nat.div_mul_le_self n B
  have hExp : (B-1)*d ≤ n-d := by
    have hEq : (B-1)*d + d = d*B := by
      rw [← Nat.add_one_mul, Nat.sub_add_cancel hB, mul_comm]
    omega
  have hU : α * (Fintype.card (𝔽₂ n) : ℝ) ≤ A.card := by
    have H := mul_le_mul_of_nonneg_right hA
      (show 0 ≤ (Fintype.card (𝔽₂ n) : ℝ) by positivity)
    exact H.trans_eq (Finset.nnratCast_dens_mul_natCast_card A)
  obtain ⟨W, hdim, hcard⟩ := iterate_restrict A α ha ha' hU (n-d)
  rw [dim_vector] at hdim
  rw [card_vector, Nat.cast_pow, Nat.cast_ofNat] at hcard
  have hr₀ : 0 ≤ 1 - α/2 := by linarith
  have hr₁ : 1 - α/2 ≤ 1 := by linarith
  have hratio : (2:ℝ)^n * ((1 - α/2)/2)^(n-d) = 2^d * (1-α/2)^(n-d) := by
    rw [div_pow]
    calc
      _ = (2^d * 2^(n-d)) * ((1-α/2)^(n-d) / 2^(n-d)) := by
        rw [← pow_add, Nat.add_sub_of_le hdle]
      _ = _ := by field_simp
  have hc : ((missing A W).card : ℝ) < 1 := by
    calc
      _ ≤ (2:ℝ)^n * ((1-α/2)/2)^(n-d) := hcard
      _ = 2^d * (1-α/2)^(n-d) := hratio
      _ ≤ 2^d * (1-α/2)^((B-1)*d) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr₀ hr₁ hExp) (by positivity)
      _ = (2 * (1-α/2)^(B-1))^d := by rw [pow_mul, mul_pow]
      _ < 1 := by
        simpa using pow_lt_pow_left₀ (by linarith : 2 * (1-α/2)^(B-1) < (1:ℝ))
          (by positivity : 0 ≤ 2 * (1-α/2)^(B-1)) (Nat.ne_of_gt hd)
  have hzero : (missing A W).card < 1 := by exact_mod_cast hc
  have he : missing A W = ∅ := card_eq_zero.mp (by omega)
  have hw : (W.toAffineSubspace : Set (𝔽₂ n)) ⊆ ↑(A + A) := by
    intro x hx
    by_contra hx'
    have hmem : (⟨x, hx⟩ : W) ∈ missing A W := by
      apply mem_missing.mpr
      intro hsum
      apply hx'
      change x ∈ A + A
      obtain ⟨a, ha, b, hb, hab⟩ := (@Finset.mem_add (𝔽₂ n) (Classical.decEq _) _ A A x).mp hsum
      exact Finset.mem_add.mpr ⟨a, ha, b, hb, hab⟩
    simp [he] at hmem
  have hmono := maxCosetDim_mono K (𝔽₂ n) hw
  rw [maxCosetDim_affineSubspace, Submodule.toAffineSubspace_direction] at hmono
  exact (by omega : d ≤ finrank K W).trans hmono

end DenseSumset

open Filter DenseSumset

theorem OMA.solution : type_of% @Green51.green_51.lower := by
  intro α ha ha'
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (by norm_num : (0:ℝ) < 1/2)
    (show 1-α/2 < 1 by linarith)
  let B := t+1
  have hB : 1 ≤ B := Nat.succ_pos _
  have hBR : (0:ℝ) < B := by exact_mod_cast hB
  refine ⟨1 / (2 * (B:ℝ)), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * B)] with n hn
  have hNe : { maxCosetDim (ZMod 2) (𝔽₂ n) ↑(A + A) |
      (A : Finset (𝔽₂ n)) (_h : A.dens ≥ α) }.Nonempty :=
    ⟨_, ⟨univ, by simpa using ha', rfl⟩⟩
  have hlower : n / B ≤ Green51.guaranteedMaxCosetDim n α := by
    apply le_csInf hNe
    rintro _ ⟨A, hA, rfl⟩
    exact coset_lower n B α ha ha' hB hn (by simpa [B] using ht) A hA
  have hdpos : 0 < n / B := Nat.div_pos (by omega : B ≤ n) (by omega)
  have hrem := Nat.mod_lt n (by omega : 0 < B)
  have hdecomp := Nat.mod_add_div n B
  have hsmall : n ≤ 2 * (B * (n / B)) := by
    have hm : B ≤ B * (n / B) := by simpa using Nat.mul_le_mul_left B hdpos
    omega
  have hsmallR := Nat.cast_le (α := ℝ).mpr hsmall
  push_cast at hsmallR
  refine le_trans (b := ((n / B : ℕ) : ℝ)) ?_ (by exact_mod_cast hlower)
  rw [one_div, inv_mul_eq_div]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (B:ℝ))).2
  linarith