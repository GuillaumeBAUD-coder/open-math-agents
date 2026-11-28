import Mathlib

/-!
# Brumer–Stark conjecture

Source: https://en.wikipedia.org/wiki/Brumer–Stark_conjecture
Credit: @iancbaer

Setting (number field case; the function field analogue is a theorem of Tate and Deligne).
`K/k` is a finite abelian extension of number fields with group `G = Gal(K/k)`, and `S` is a finite
set of places of `k` containing the archimedean places and the primes that ramify in `K`. Here `S`
is given by its finite part: a finite set of nonzero primes of `𝓞 k` containing every ramified one.
`W` is the number of roots of unity in `K`.

For `σ ∈ G` the partial zeta function is `ζ_S(s, σ) = ∑ N(𝔞)^(-s)`, the sum over the nonzero
integral ideals `𝔞` of `k` prime to `S` whose Artin symbol `(𝔞, K/k)` is `σ`. It converges for
`Re s > 1` and continues analytically to `ℂ ∖ {1}`. The Brumer–Stickelberger element is
`θ(s) = ∑_σ ζ_S(s, σ) σ⁻¹` (Tate's convention, with arithmetic Frobenius elements). By
Deligne–Ribet and Cassou-Noguès, `W θ(0) ∈ ℤ[G]`.

Conjecture (Brumer–Stark, in Tate's form): for each nonzero fractional ideal `𝔞` of `K` there is
an anti-unit `ε ∈ K` (all archimedean absolute values equal to `1`) such that
1. `𝔞^(W θ(0)) = (ε)`, and
2. `K(ε^(1/W))` is an abelian extension of `k`.

Formalization notes.
* The Artin symbol of an ideal prime to `S` is the product of the Frobenius elements of its prime
  factors, with multiplicity. `G` is commutative, so the order of the factors is irrelevant.
* The analytic continuation is not constructed: `main` quantifies over every family `Z` of
  functions, holomorphic on `ℂ ∖ {1}`, that agrees with the partial zeta series for `Re s > 1`.
  Such a family exists and is unique, so `Z σ 0` is `ζ_S(0, σ)`.
* `n σ` is the integer `W ζ_S(0, σ)`, so `W θ(0) = ∑_σ n σ • σ⁻¹`. Integrality is the theorem quoted
  above; it appears as a hypothesis, as it does in the conjecture.
* `𝔞^(W θ(0)) = ∏_σ (σ⁻¹ 𝔞)^(n σ)`. The equality with `(ε)` is stated prime by prime: for every
  nonzero prime `𝔓` of `K`, `v_𝔓(ε) = ∑_σ n σ * v_(σ 𝔓)(𝔞)`, using `v_𝔓(σ⁻¹ 𝔞) = v_(σ 𝔓)(𝔞)`.
  Two nonzero fractional ideals with the same valuation at every prime are equal.
* `K(ε^(1/W))` is any field generated over `K` by a `W`-th root of `ε`; `K` contains the `W`-th
  roots of unity, so the choice of root does not matter.
* `S` is required to contain at least two places, counting the archimedean ones. The source does
  not say so, but with a single place the statement fails: for `K = k = ℚ` and `S = {∞}` one has
  `θ(0) = ζ(0) = -1/2` and `W = 2`, so the ideal `(2)^(-1)` would need a generator of absolute
  value `1`. In the usual setting (`k` totally real, `K` a CM field) there are always two places.
-/

namespace OMA.S_wp_brumer_stark_conjecture

open NumberField IsDedekindDomain Classical
open scoped nonZeroDivisors

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The automorphism of `𝓞 K` induced by `σ ∈ Gal(K/k)`. -/
noncomputable def res (σ : K ≃ₐ[k] K) : 𝓞 K ≃ₐ[𝓞 k] 𝓞 K :=
  galRestrict (𝓞 k) k K (𝓞 K) σ

/-- `σ` is a Frobenius element at the prime `p` of `k`: `σ x ≡ x ^ N(p)` modulo every prime of
`K` above `p`. -/
def IsFrobAt (σ : K ≃ₐ[k] K) (p : Ideal (𝓞 k)) : Prop :=
  ∀ P : Ideal (𝓞 K), P.IsPrime → P.under (𝓞 k) = p →
    ∀ x : 𝓞 K, res k K σ x - x ^ Ideal.absNorm p ∈ P

/-- The Frobenius element at `p` (the identity when there is none). -/
noncomputable def frob (p : Ideal (𝓞 k)) : K ≃ₐ[k] K :=
  if h : ∃ σ : K ≃ₐ[k] K, IsFrobAt k K σ p then h.choose else 1

/-- The Artin symbol of an integral ideal: the product of the Frobenius elements of its prime
factors, counted with multiplicity. -/
noncomputable def artin (I : Ideal (𝓞 k)) : K ≃ₐ[k] K :=
  ((UniqueFactorizationMonoid.normalizedFactors I).toList.map (frob k K)).prod

/-- The prime `p` of `k` ramifies in `K`. -/
def IsRamified (p : Ideal (𝓞 k)) : Prop :=
  ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P.under (𝓞 k) = p ∧
    Ideal.map (algebraMap (𝓞 k) (𝓞 K)) p ≤ P ^ 2

/-- The partial zeta series `∑ N(I)^(-s)` over the nonzero integral ideals `I` of `k` prime to
`S` with Artin symbol `σ`. -/
noncomputable def partialZetaSeries (S : Finset (Ideal (𝓞 k))) (σ : K ≃ₐ[k] K) (s : ℂ) : ℂ :=
  ∑' I : Ideal (𝓞 k),
    if I ≠ ⊥ ∧ (∀ p ∈ S, ¬ I ≤ p) ∧ artin k K I = σ then (Ideal.absNorm I : ℂ) ^ (-s) else 0

/-- `Z σ` is the analytic continuation to `ℂ ∖ {1}` of the partial zeta function of `σ`. -/
def IsPartialZeta (S : Finset (Ideal (𝓞 k))) (Z : (K ≃ₐ[k] K) → ℂ → ℂ) : Prop :=
  ∀ σ : K ≃ₐ[k] K, DifferentiableOn ℂ (Z σ) {s : ℂ | s ≠ 1} ∧
    ∀ s : ℂ, 1 < s.re → Z σ s = partialZetaSeries k K S σ s

/-- Every field generated over `K` by a `W`-th root of `ε` is an abelian extension of `k`. -/
def AbelianRootExtension (ε : K) (W : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (r : L),
    r ^ W = algebraMap K L ε → Algebra.adjoin K {r} = ⊤ →
      IsGalois k L ∧ ∀ f g : L ≃ₐ[k] L, f * g = g * f

theorem main :
    ∀ (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
      [IsGalois k K], (∀ σ τ : K ≃ₐ[k] K, σ * τ = τ * σ) →
    ∀ S : Finset (Ideal (𝓞 k)),
      (∀ p ∈ S, p.IsPrime ∧ p ≠ ⊥) →
      (∀ p : Ideal (𝓞 k), p.IsPrime → p ≠ ⊥ → IsRamified k K p → p ∈ S) →
      2 ≤ Fintype.card (InfinitePlace k) + S.card →
    ∀ Z : (K ≃ₐ[k] K) → ℂ → ℂ, IsPartialZeta k K S Z →
    ∀ n : (K ≃ₐ[k] K) → ℤ, (∀ σ, (Units.torsionOrder K : ℂ) * Z σ 0 = n σ) →
    ∀ I : FractionalIdeal (𝓞 K)⁰ K, I ≠ 0 →
      ∃ ε : K, (∀ φ : K →+* ℂ, ‖φ ε‖ = 1) ∧
        (∀ v : HeightOneSpectrum (𝓞 K),
          FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ ε) =
            ∑ σ : K ≃ₐ[k] K, n σ * FractionalIdeal.count K
              (HeightOneSpectrum.equivOfRingEquiv (res k K σ).toRingEquiv v) I) ∧
        AbelianRootExtension k K ε (Units.torsionOrder K) := by
  sorry

end OMA.S_wp_brumer_stark_conjecture
