import FormalConjectures.GreensOpenProblems.«21»
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Reduction `Green21.green_21.variants.fox_kleitman_modular.R2` of the modular Fox-Kleitman
conjecture (`Green21.green_21.variants.fox_kleitman_modular`).

Unconditionally proved in-file (zero `sorry`, standard axioms only):
1. Prefix-sum pigeonhole bound `k < p`, complete solutions for `k = 1` (`1` colour) and `k = 2`
   (`3` colours via finite-abelian cyclic-coset colouring `tri_col`), and unit normalization
   `u 0 = 1`.
2. **Signed Bounded-`L^1` Theorem (`solve_signed_L1`)**: For every arity `k >= 1`, bound `B >= 1`,
   and prime `p > 2 * B`, completely solves every admissible tuple admitting a scaling
   `m : (ZMod p)ˣ` with signed `L^1`-norm `∑ i, min (m * u i).val (p - (m * u i).val) <= B`
   (including all fixed-height signed integer equations such as `x + y - 3z = 0` and
   `x + 3y - 7z = 0` across all primes `p`) in at most `4 * B^2 + 4 * B` colours, via
   root-neighborhood separation and a base-`q` lowest-nonzero-digit colouring (`B < q <= 2 * B`
   by Bertrand's postulate).
3. **Universal Bohr-Averaging Independence Bounds (`exists_large_solution_free_set`,
   `exists_large_solution_free_equal_pair`)**: Proves unconditionally for every `k >= 1`, prime
   `p > k`, and tuple `u` with `∑ u i ≠ 0` that `(ZMod p)ˣ` contains a solution-free subset `A`
   with `p ^ (k - 1) * A.card >= ((p - 1) / k) ^ k` (ruling out any `α / p -> 0` disproof and
   bounding the fractional chromatic number `χ_f <= k^k + o(1)`), plus the sharper 2-frequency
   bound `p * A.card >= L * (p - 1 - 2 * L)` (`L = (p - 1) / 4`, density `~ 1/8`) when `k = 3`
   has two equal coefficients.
4. **Vertex-Transitive Multiplicative-Dilate Greedy Colouring (`exists_dilate_colouring_of_indep`)**:
   Proves unconditionally that any solution-free subset of size `s > 0` yields an `r`-colouring
   whenever `(p - 1 - s) ^ r * (p - 1) < (p - 1) ^ r`, giving an unconditional `O_k(log p)`
   chromatic-number upper bound.
5. **3-Variable Fourier Bias Certificate (`fourier_bias_of_solution_free_k3`)**: Proves
   unconditionally that every solution-free subset `A ⊆ (ZMod p)ˣ` at `k = 3` has a non-trivial
   Fourier coefficient of magnitude at least `|A|^2 / p`.

Remaining open cores:
- `H1`: Arity `k = 3`, equal-pair 2-frequency regime (`54 < p`, `u 0 = u 1 = 1`, `u 2 ≠ 1`,
  signed `L^1 > 27` under every scaling).
- `H2`: Arity `k = 3`, pairwise-distinct 3-frequency regime (`54 < p`, `u 0 = 1`, pairwise distinct,
  signed `L^1 > 27` under every scaling).
- `H3`: Higher arity `4 <= k` (`2 * k^2 < p`, `u 0 = 1`, signed `L^1 > k^2` under every scaling).
-/

-- Reduction Green21.green_21.variants.fox_kleitman_modular.R2 of Ben Green's Open Problem 21
-- Credit: @paynebrowning

namespace OMA.R_Green21_green_21_variants_fox_kleitman_modular_R2

def H1 : Prop :=
  ∃ C : ℕ, ∀ (p : ℕ), p.Prime → 54 < p →
    ∀ u : Fin 3 → (ZMod p)ˣ, u 0 = 1 → u 1 = 1 → u 2 ≠ 1 →
      (∀ I : Finset (Fin 3), I.Nonempty → ∑ i ∈ I, (u i : ZMod p) ≠ 0) →
      (∀ m : (ZMod p)ˣ,
        27 < ∑ i : Fin 3, min (((m * u i : (ZMod p)ˣ) : ZMod p).val)
          (p - ((m * u i : (ZMod p)ˣ) : ZMod p).val)) →
      ∃ col : (ZMod p)ˣ → Fin C, ∀ x : Fin 3 → (ZMod p)ˣ,
        (∀ i j, col (x i) = col (x j)) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0

def H2 : Prop :=
  ∃ C : ℕ, ∀ (p : ℕ), p.Prime → 54 < p →
    ∀ u : Fin 3 → (ZMod p)ˣ, u 0 = 1 → u 0 ≠ u 1 → u 0 ≠ u 2 → u 1 ≠ u 2 →
      (∀ I : Finset (Fin 3), I.Nonempty → ∑ i ∈ I, (u i : ZMod p) ≠ 0) →
      (∀ m : (ZMod p)ˣ,
        27 < ∑ i : Fin 3, min (((m * u i : (ZMod p)ˣ) : ZMod p).val)
          (p - ((m * u i : (ZMod p)ˣ) : ZMod p).val)) →
      ∃ col : (ZMod p)ˣ → Fin C, ∀ x : Fin 3 → (ZMod p)ˣ,
        (∀ i j, col (x i) = col (x j)) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0

def H3 : Prop :=
  ∃ f : ℕ → ℕ, ∀ (k p : ℕ) (hk : 4 ≤ k), p.Prime → 2 * k ^ 2 < p →
    ∀ u : Fin k → (ZMod p)ˣ, u ⟨0, Nat.lt_of_lt_of_le (by norm_num) hk⟩ = 1 →
      (∀ I : Finset (Fin k), I.Nonempty → ∑ i ∈ I, (u i : ZMod p) ≠ 0) →
      (∀ m : (ZMod p)ˣ,
        k ^ 2 < ∑ i : Fin k, min (((m * u i : (ZMod p)ˣ) : ZMod p).val)
          (p - ((m * u i : (ZMod p)ˣ) : ZMod p).val)) →
      ∃ col : (ZMod p)ˣ → Fin (f k), ∀ x : Fin k → (ZMod p)ˣ,
        (∀ i j, col (x i) = col (x j)) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0

section ReductionProofs

/- ### Module 1: Basic Modular Helpers, k = 1, 2, Small Primes, and Normalization -/

private lemma not_dvd_of_no_zero_subset {k p : ℕ} {a : Fin k → ℤ}
    (ha : ∀ I : Finset (Fin k), (p : ℤ) ∣ ∑ i ∈ I, a i → I = ∅) (i : Fin k) :
    ¬ (p : ℤ) ∣ a i := by
  intro hd
  have hsing : ({i} : Finset (Fin k)) = ∅ := ha {i} (by simpa using hd)
  exact Finset.singleton_ne_empty i hsing

private lemma isUnit_of_not_dvd_prime {p : ℕ} (hp : p.Prime) {z : ℤ}
    (hz : ¬ (p : ℤ) ∣ z) : IsUnit (z : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  refine isUnit_iff_ne_zero.mpr ?_
  intro h0
  exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp h0)

private lemma k_lt_prime_of_no_zero_subset {k p : ℕ} (hp : p.Prime)
    {a : Fin k → ℤ} (ha : ∀ I : Finset (Fin k), (p : ℤ) ∣ ∑ i ∈ I, a i → I = ∅) :
    k < p := by
  by_contra hle
  have hpk : p ≤ k := Nat.le_of_not_lt hle
  let S : Fin (k + 1) → ZMod p := fun j =>
    ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < j.val), (a i : ZMod p)
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin (k + 1)) := by
    rw [ZMod.card, Fintype.card_fin]
    omega
  obtain ⟨j1, j2, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt S hcard
  have hval_ne : j1.val ≠ j2.val := fun h => hne (Fin.ext h)
  wlog hlt : j1.val < j2.val generalizing j1 j2
  · exact this j2 j1 hne.symm heq.symm hval_ne.symm (by omega)
  let I : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => j1.val ≤ i.val ∧ i.val < j2.val)
  have hI_nonempty : I.Nonempty :=
    ⟨⟨j1.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hlt⟩⟩
  have hsplit : Finset.univ.filter (fun i : Fin k => i.val < j2.val) =
      Finset.univ.filter (fun i : Fin k => i.val < j1.val) ∪ I := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, I]
    omega
  have hdisj : Disjoint (Finset.univ.filter (fun i : Fin k => i.val < j1.val)) I := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, I] at hi1 hi2
    omega
  have hsum_eq : (∑ i ∈ I, (a i : ZMod p)) = S j2 - S j1 := by
    dsimp [S]
    rw [hsplit, Finset.sum_union hdisj, add_sub_cancel_left]
  have hsum_zero : ((∑ i ∈ I, a i : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [hsum_eq, heq, sub_self]
  exact hI_nonempty.ne_empty (ha I ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hsum_zero))

private lemma tri_col {G : Type*} [CommGroup G] [Finite G] (g : G) (hg : g ≠ 1) :
    ∃ χ : G → Fin 3, ∀ u, χ (g * u) ≠ χ u := by
  classical
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  have hn : 2 ≤ orderOf g := by
    have h0 : 0 < orderOf g := hfin.orderOf_pos
    have h1 : orderOf g ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    omega
  let r : G → G := fun u => (QuotientGroup.mk u : G ⧸ Subgroup.zpowers g).out
  have hr : ∀ u, ∃ j : ℕ, g ^ j * r u = u := by
    intro u
    have h1 : (QuotientGroup.mk (r u) : G ⧸ Subgroup.zpowers g) = QuotientGroup.mk u :=
      QuotientGroup.out_eq' _
    rw [QuotientGroup.eq] at h1
    obtain ⟨j, hj⟩ := (mem_powers_iff_mem_zpowers).mpr h1
    refine ⟨j, ?_⟩
    change g ^ j = _ at hj
    rw [hj, mul_comm, mul_inv_cancel_left]
  have hrg : ∀ u, r (g * u) = r u := by
    intro u
    have hq : (QuotientGroup.mk (g * u) : G ⧸ Subgroup.zpowers g) = QuotientGroup.mk u := by
      rw [QuotientGroup.eq]
      have hid : (g * u)⁻¹ * u = g⁻¹ := by
        rw [mul_inv_rev, mul_assoc, mul_comm g⁻¹ u, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hid]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers g)
    simp only [r, hq]
  let j : G → ℕ := fun u => Nat.find (hr u)
  have hj : ∀ u, g ^ j u * r u = u := fun u => Nat.find_spec (hr u)
  have hjmin : ∀ u m, g ^ m * r u = u → j u ≤ m := fun u m h => Nat.find_min' (hr u) h
  have hjlt : ∀ u, j u < orderOf g := by
    intro u
    by_contra hcon
    have hcon' : orderOf g ≤ j u := by omega
    have h1 : g ^ (j u - orderOf g) * r u = u := by
      have hju := hj u
      rw [← Nat.sub_add_cancel hcon', pow_add, pow_orderOf_eq_one, mul_one] at hju
      exact hju
    have hle := hjmin u _ h1
    have h0 : 0 < orderOf g := hfin.orderOf_pos
    omega
  let χ : G → Fin 3 := fun u => if j u = orderOf g - 1 then 2 else ⟨j u % 2, by omega⟩
  refine ⟨χ, fun u => ?_⟩
  have hu := hjlt u
  by_cases hA : j u + 1 < orderOf g
  · have e1 : g ^ (j u + 1) * r (g * u) = g * u := by
      rw [hrg, pow_succ, mul_comm (g ^ j u) g, mul_assoc, hj]
    have e2 : g ^ j (g * u) * r u = g ^ (j u + 1) * r u := by
      have hgu := hj (g * u)
      rw [hrg] at hgu
      rw [hgu, ← hrg u, e1]
    have e3 : g ^ j (g * u) = g ^ (j u + 1) := mul_right_cancel e2
    have e4 : j (g * u) = j u + 1 := pow_injOn_Iio_orderOf (hjlt _) hA e3
    simp only [χ, e4]
    split_ifs with h1 h2 h2
    · omega
    · simp [Fin.ext_iff]; omega
    · simp [Fin.ext_iff]; omega
    · simp only [ne_eq, Fin.mk.injEq]; omega
  · have hB : j u + 1 = orderOf g := by omega
    have e1 : g * u = r u := by
      have hju := hj u
      calc g * u = g * (g ^ j u * r u) := by rw [hju]
        _ = g ^ (j u + 1) * r u := by rw [pow_succ', mul_assoc]
        _ = r u := by rw [hB, pow_orderOf_eq_one, one_mul]
    have e2 : j (g * u) = 0 := by
      have hle := hjmin (g * u) 0 (by rw [pow_zero, one_mul, hrg, e1])
      omega
    simp only [χ, e2]
    split_ifs with h1 h2
    · omega
    · omega
    · simp [Fin.ext_iff]
    · omega

private lemma solve_k_one {p : ℕ} (hp : p.Prime) (a : Fin 1 → ℤ)
    (ha : ∀ I : Finset (Fin 1), (p : ℤ) ∣ ∑ i ∈ I, a i → I = ∅) :
    ∃ col : (ZMod p)ˣ → Fin 1, ∀ x : Fin 1 → (ZMod p)ˣ,
      (∀ i j, col (x i) = col (x j)) → ∑ i, (a i : ZMod p) * (x i : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨fun _ => 0, fun x _ hsum => ?_⟩
  rw [Fin.sum_univ_one] at hsum
  have ha0 : IsUnit (a 0 : ZMod p) :=
    isUnit_of_not_dvd_prime hp (not_dvd_of_no_zero_subset ha 0)
  exact (ha0.mul (x 0).isUnit).ne_zero hsum

private lemma solve_k_two {p : ℕ} (hp : p.Prime) (a : Fin 2 → ℤ)
    (ha : ∀ I : Finset (Fin 2), (p : ℤ) ∣ ∑ i ∈ I, a i → I = ∅) :
    ∃ col : (ZMod p)ˣ → Fin 3, ∀ x : Fin 2 → (ZMod p)ˣ,
      (∀ i j, col (x i) = col (x j)) → ∑ i, (a i : ZMod p) * (x i : ZMod p) ≠ 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have ha0 := isUnit_of_not_dvd_prime hp (not_dvd_of_no_zero_subset ha 0)
  have ha1 := isUnit_of_not_dvd_prime hp (not_dvd_of_no_zero_subset ha 1)
  let u0 : (ZMod p)ˣ := ha0.unit
  let u1 : (ZMod p)ˣ := ha1.unit
  have hu0 : (u0 : ZMod p) = a 0 := ha0.unit_spec
  have hu1 : (u1 : ZMod p) = a 1 := ha1.unit_spec
  let g : (ZMod p)ˣ := -(u1 * u0⁻¹)
  have hg : g ≠ 1 := by
    intro hg1
    have hval : ((g : (ZMod p)ˣ) : ZMod p) = 1 := by rw [hg1]; rfl
    simp only [g, Units.val_neg, Units.val_mul] at hval
    have h01 : ((a 0 + a 1 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [← hu0, ← hu1]
      have hmul : (u0 : ZMod p) * ((u0⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := Units.mul_inv u0
      linear_combination -(u0 : ZMod p) * hval - (u1 : ZMod p) * hmul
    have hdvd : (p : ℤ) ∣ a 0 + a 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h01
    have hfull : (Finset.univ : Finset (Fin 2)) = ∅ :=
      ha Finset.univ (by simpa [Fin.sum_univ_two] using hdvd)
    exact Finset.univ_nonempty.ne_empty hfull
  obtain ⟨χ, hχ⟩ := tri_col g hg
  refine ⟨χ, fun x hcol hsum => ?_⟩
  rw [Fin.sum_univ_two] at hsum
  apply hχ (x 1)
  rw [← hcol 0 1]
  congr 1
  apply Units.ext
  simp only [g, Units.val_neg, Units.val_mul]
  rw [← hu0, ← hu1] at hsum
  have hmul : ((u0⁻¹ : (ZMod p)ˣ) : ZMod p) * (u0 : ZMod p) = 1 := Units.inv_mul u0
  linear_combination -((u0⁻¹ : (ZMod p)ˣ) : ZMod p) * hsum + ((x 0 : (ZMod p)ˣ) : ZMod p) * hmul

private lemma solve_small_prime {k p M : ℕ} (hk : 0 < k) (hp : p.Prime) (hle : p ≤ M)
    (u : Fin k → (ZMod p)ˣ)
    (hu : ∀ I : Finset (Fin k), I.Nonempty → ∑ i ∈ I, (u i : ZMod p) ≠ 0) :
    ∃ col : (ZMod p)ˣ → Fin M, ∀ x : Fin k → (ZMod p)ˣ,
      (∀ i j, col (x i) = col (x j)) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let col : (ZMod p)ˣ → Fin M := fun x => ⟨(x : ZMod p).val, lt_of_lt_of_le (ZMod.val_lt _) hle⟩
  refine ⟨col, fun x hcol hsum => ?_⟩
  let i0 : Fin k := ⟨0, hk⟩
  have hx_eq : ∀ i : Fin k, (x i : ZMod p) = (x i0 : ZMod p) := fun i =>
    ZMod.val_injective p (by simpa [col] using congrArg Fin.val (hcol i i0))
  have hsum' : (∑ i : Fin k, (u i : ZMod p)) * (x i0 : ZMod p) = 0 := by
    rw [Finset.sum_mul]
    convert hsum using 1
    exact Finset.sum_congr rfl fun i _ => by rw [hx_eq i]
  exact hu Finset.univ ⟨i0, Finset.mem_univ i0⟩ (((x i0).isUnit.mul_left_eq_zero).mp hsum')

private lemma normalize_units {k p : ℕ} (hk : 0 < k) (hp : p.Prime)
    (a : Fin k → ℤ)
    (ha : ∀ I : Finset (Fin k), (p : ℤ) ∣ ∑ i ∈ I, a i → I = ∅) :
    ∃ (c : (ZMod p)ˣ) (u : Fin k → (ZMod p)ˣ),
      u ⟨0, hk⟩ = 1 ∧
      (∀ i : Fin k, (a i : ZMod p) = (c : ZMod p) * (u i : ZMod p)) ∧
      (∀ I : Finset (Fin k), I.Nonempty → ∑ i ∈ I, (u i : ZMod p) ≠ 0) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hunit : ∀ i : Fin k, IsUnit (a i : ZMod p) :=
    fun i => isUnit_of_not_dvd_prime hp (not_dvd_of_no_zero_subset ha i)
  let c : (ZMod p)ˣ := (hunit ⟨0, hk⟩).unit
  let u : Fin k → (ZMod p)ˣ := fun i => c⁻¹ * (hunit i).unit
  refine ⟨c, u, inv_mul_cancel c, fun i => ?_, fun I hIne hsum => ?_⟩
  · have hci : (c : ZMod p) * (u i : ZMod p) = ((hunit i).unit : ZMod p) := by
      simp only [u, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
    rw [hci, IsUnit.unit_spec]
  · have hsum_a : ((∑ i ∈ I, a i : ℤ) : ZMod p) = 0 := by
      push_cast
      have hterm : ∀ i ∈ I, (a i : ZMod p) = (c : ZMod p) * (u i : ZMod p) := fun i _ => by
        simp only [u, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul, IsUnit.unit_spec]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum, mul_zero]
    exact hIne.ne_empty (ha I ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hsum_a))

/- ### Module 2: Signed Bounded-L^1 Theorem via Base-q Digit + Root-Neighborhood Separation -/

private lemma base_q_no_int_sol {k q : ℕ} (hk : 0 < k) (hq : q.Prime)
    (b : Fin k → ℤ)
    (hb : ∀ I : Finset (Fin k), I.Nonempty → ¬ (q : ℤ) ∣ ∑ i ∈ I, b i)
    (δ : Fin k → ℕ) (hδpos : ∀ i, 0 < δ i)
    (hdig : ∀ i j : Fin k, (ordCompl[q] (δ i)) % q = (ordCompl[q] (δ j)) % q) :
    ∑ i : Fin k, b i * (δ i : ℤ) ≠ 0 := by
  intro hsum
  have hne_univ : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  let e : ℕ := Finset.univ.inf' hne_univ fun i => (δ i).factorization q
  have he_le : ∀ i : Fin k, e ≤ (δ i).factorization q := fun i =>
    Finset.inf'_le (fun j => (δ j).factorization q) (Finset.mem_univ i)
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_inf' hne_univ (fun i => (δ i).factorization q)
  let I : Finset (Fin k) := Finset.univ.filter fun i => (δ i).factorization q = e
  have hIne : I.Nonempty := ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hi0.symm⟩⟩
  let m : Fin k → ℕ := fun i => q ^ ((δ i).factorization q - e) * ordCompl[q] (δ i)
  have hδ_eq : ∀ i : Fin k, δ i = q ^ e * m i := fun i => by
    dsimp only [m]
    rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (he_le i)]
    exact (Nat.ordProj_mul_ordCompl_eq_self (δ i) q).symm
  have hsum_m : ∑ i : Fin k, b i * (m i : ℤ) = 0 := by
    have hmul : (q ^ e : ℤ) * ∑ i : Fin k, b i * (m i : ℤ) = 0 := by
      rw [Finset.mul_sum]
      convert hsum using 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hδ_eq i]
      push_cast
      ring
    have hqe : (q ^ e : ℤ) ≠ 0 := by exact_mod_cast (pow_pos hq.pos e).ne'
    exact (mul_eq_zero.mp hmul).resolve_left hqe
  let d : ℕ := (ordCompl[q] (δ i0)) % q
  have hd_not_dvd : ¬ q ∣ d := by
    have h1 : ¬ q ∣ ordCompl[q] (δ i0) := Nat.not_dvd_ordCompl hq (hδpos i0).ne'
    intro hdvd
    apply h1
    exact (Nat.dvd_mod_iff dvd_rfl).mp hdvd
  have hm_mod : ∀ i : Fin k, (q : ℤ) ∣ (m i : ℤ) - if i ∈ I then (d : ℤ) else 0 := by
    intro i
    by_cases hi : i ∈ I
    · rw [if_pos hi]
      have hfac : (δ i).factorization q = e := (Finset.mem_filter.mp hi).2
      have hmi : m i = ordCompl[q] (δ i) := by
        simp [m, hfac]
      rw [hmi]
      have hmod : (ordCompl[q] (δ i)) % q = d := hdig i i0
      have hdiv : (ordCompl[q] (δ i) : ℤ) - (d : ℤ) = (q : ℤ) * (ordCompl[q] (δ i) / q : ℤ) := by
        have h : ordCompl[q] (δ i) = q * (ordCompl[q] (δ i) / q) + d := by
          rw [← hmod]
          exact (Nat.div_add_mod (ordCompl[q] (δ i)) q).symm
        zify at h
        linarith
      exact ⟨ordCompl[q] (δ i) / q, hdiv⟩
    · rw [if_neg hi, sub_zero]
      have hfac : e < (δ i).factorization q := by
        have hne : (δ i).factorization q ≠ e := fun h =>
          hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
        have := he_le i
        omega
      have hsub : 1 ≤ (δ i).factorization q - e := by omega
      have hqdvd : q ∣ m i := dvd_mul_of_dvd_left (dvd_pow_self q (by omega)) _
      exact_mod_cast hqdvd
  have hdvd_dsum : (q : ℤ) ∣ (d : ℤ) * ∑ i ∈ I, b i := by
    have hdiff : (q : ℤ) ∣ ∑ i : Fin k, b i * ((m i : ℤ) - if i ∈ I then (d : ℤ) else 0) :=
      Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (hm_mod i) (b i)
    have hrew : (∑ i : Fin k, b i * ((m i : ℤ) - if i ∈ I then (d : ℤ) else 0)) =
        -((d : ℤ) * ∑ i ∈ I, b i) := by
      have h1 : ∀ i : Fin k, b i * ((m i : ℤ) - if i ∈ I then (d : ℤ) else 0) =
          b i * (m i : ℤ) - if i ∈ I then b i * (d : ℤ) else 0 := fun i => by
        split_ifs <;> ring
      rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, hsum_m, zero_sub,
        Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hrew, dvd_neg] at hdiff
    exact hdiff
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  rcases hqp.dvd_or_dvd hdvd_dsum with hqd | hqs
  · exact hd_not_dvd (Int.ofNat_dvd.mp hqd)
  · exact hb I hIne hqs

private lemma solve_signed_L1_regionB {k p B D : ℕ} (hB : 1 ≤ B) (hp : p.Prime)
    (b : Fin k → ℤ) (hb_sum_abs : ∑ i : Fin k, (b i).natAbs ≤ B)
    (hD_cast : (D : ℤ) = ∑ i : Fin k, b i)
    (i0 : Fin k) (hbi0_ne : b i0 ≠ 0)
    (x : Fin k → (ZMod p)ˣ)
    (hsum_b : ∑ i : Fin k, (b i : ZMod p) * (x i : ZMod p) = 0)
    (hA1 : ¬ 2 * B * ((D * (x i0 : ZMod p).val) % p) < p)
    (hA2 : ¬ 2 * B * (p - (D * (x i0 : ZMod p).val) % p) < p)
    (hbin : ∀ i : Fin k,
      (4 * B ^ 2 * (x i : ZMod p).val) / p = (4 * B ^ 2 * (x i0 : ZMod p).val) / p) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  let r0 : ℕ := (D * (x i0 : ZMod p).val) % p
  have hr0_lt : r0 < p := Nat.mod_lt _ hp.pos
  have hdiff_lt : ∀ i : Fin k,
      |(4 * B ^ 2 : ℤ) * (((x i : ZMod p).val : ℤ) - ((x i0 : ZMod p).val : ℤ))| < (p : ℤ) := by
    intro i
    let c0 : ℕ := (4 * B ^ 2 * (x i0 : ZMod p).val) / p
    have hi_lo : c0 * p ≤ 4 * B ^ 2 * (x i : ZMod p).val := by
      dsimp only [c0]; rw [← hbin i]; exact Nat.div_mul_le_self _ p
    have hi_hi : 4 * B ^ 2 * (x i : ZMod p).val < c0 * p + p := by
      have hraw := Nat.lt_div_mul_add hp.pos (a := 4 * B ^ 2 * (x i : ZMod p).val)
      rw [hbin i] at hraw
      exact hraw
    have h0_lo : c0 * p ≤ 4 * B ^ 2 * (x i0 : ZMod p).val := Nat.div_mul_le_self _ p
    have h0_hi : 4 * B ^ 2 * (x i0 : ZMod p).val < c0 * p + p :=
      Nat.lt_div_mul_add hp.pos (a := 4 * B ^ 2 * (x i0 : ZMod p).val)
    zify at hi_lo hi_hi h0_lo h0_hi
    rw [abs_lt]
    constructor <;> linarith
  let q0 : ℕ := (D * (x i0 : ZMod p).val) / p
  have hD_decomp : (D : ℤ) * ((x i0 : ZMod p).val : ℤ) = (q0 : ℤ) * (p : ℤ) + (r0 : ℤ) := by
    have h : D * (x i0 : ZMod p).val = p * q0 + r0 :=
      (Nat.div_add_mod (D * (x i0 : ZMod p).val) p).symm
    zify at h
    linarith
  let Δ : ℤ := ∑ i : Fin k, b i * ((4 * B ^ 2 : ℤ) * (((x i : ZMod p).val : ℤ) - ((x i0 : ZMod p).val : ℤ)))
  have hΔ_abs : |Δ| < (B : ℤ) * (p : ℤ) := by
    have hb_pos : 0 < (b i0).natAbs := Int.natAbs_pos.mpr hbi0_ne
    have h1 : |Δ| ≤ ∑ i : Fin k, ((b i).natAbs : ℤ) *
        |(4 * B ^ 2 : ℤ) * (((x i : ZMod p).val : ℤ) - ((x i0 : ZMod p).val : ℤ))| := by
      calc |Δ| ≤ ∑ i : Fin k, |b i * ((4 * B ^ 2 : ℤ) *
            (((x i : ZMod p).val : ℤ) - ((x i0 : ZMod p).val : ℤ)))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = _ := Finset.sum_congr rfl fun i _ => by rw [abs_mul, Int.abs_eq_natAbs]
    have h2 : ∑ i : Fin k, ((b i).natAbs : ℤ) *
        |(4 * B ^ 2 : ℤ) * (((x i : ZMod p).val : ℤ) - ((x i0 : ZMod p).val : ℤ))| <
        ∑ i : Fin k, ((b i).natAbs : ℤ) * (p : ℤ) := by
      refine Finset.sum_lt_sum (fun i _ => ?_) ?_
      · exact mul_le_mul_of_nonneg_left (hdiff_lt i).le (Int.natCast_nonneg _)
      · exact ⟨i0, Finset.mem_univ i0, mul_lt_mul_of_pos_left (hdiff_lt i0) (by exact_mod_cast hb_pos)⟩
    have h3 : ∑ i : Fin k, ((b i).natAbs : ℤ) * (p : ℤ) ≤ (B : ℤ) * (p : ℤ) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hb_sum_abs) (by omega)
    linarith
  have hexpand : (4 * B ^ 2 : ℤ) * ∑ i : Fin k, b i * ((x i : ZMod p).val : ℤ) =
      (4 * B ^ 2 : ℤ) * (q0 : ℤ) * (p : ℤ) + ((4 * B ^ 2 : ℤ) * (r0 : ℤ) + Δ) := by
    have h1 : (4 * B ^ 2 : ℤ) * ∑ i : Fin k, b i * ((x i : ZMod p).val : ℤ) =
        (4 * B ^ 2 : ℤ) * ((∑ i : Fin k, b i) * ((x i0 : ZMod p).val : ℤ)) + Δ := by
      dsimp only [Δ]
      rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, ← hD_cast, hD_decomp]
    ring
  have hlo_r : (p : ℤ) ≤ (2 * B : ℤ) * (r0 : ℤ) := by
    have : p ≤ 2 * B * r0 := Nat.le_of_not_lt hA1
    exact_mod_cast this
  have hhi_r : (p : ℤ) ≤ (2 * B : ℤ) * ((p : ℤ) - (r0 : ℤ)) := by
    have : p ≤ 2 * B * (p - r0) := Nat.le_of_not_lt hA2
    have hz : (p : ℤ) ≤ (2 * B : ℤ) * ((p - r0 : ℕ) : ℤ) := by exact_mod_cast this
    rw [Nat.cast_sub hr0_lt.le] at hz
    exact hz
  have hlo_strict : (4 * B ^ 2 : ℤ) * (q0 : ℤ) * (p : ℤ) <
      (4 * B ^ 2 : ℤ) * ∑ i : Fin k, b i * ((x i : ZMod p).val : ℤ) := by
    rw [hexpand]
    have hΔ_lo : -((B : ℤ) * (p : ℤ)) < Δ := (abs_lt.mp hΔ_abs).1
    nlinarith [hB, hp.pos]
  have hhi_strict : (4 * B ^ 2 : ℤ) * ∑ i : Fin k, b i * ((x i : ZMod p).val : ℤ) <
      (4 * B ^ 2 : ℤ) * ((q0 : ℤ) + 1) * (p : ℤ) := by
    rw [hexpand]
    have hΔ_hi : Δ < (B : ℤ) * (p : ℤ) := (abs_lt.mp hΔ_abs).2
    nlinarith [hB, hp.pos]
  have hzmod : ((∑ i : Fin k, b i * ((x i : ZMod p).val : ℤ) : ℤ) : ZMod p) = 0 := by
    push_cast
    simpa only [ZMod.natCast_zmod_val] using hsum_b
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hzmod
  rw [ht] at hlo_strict hhi_strict
  have h4B2p : (0 : ℤ) < (4 * B ^ 2 : ℤ) * (p : ℤ) := by nlinarith [hB, hp.pos]
  have ht_lo : (q0 : ℤ) < t := by nlinarith
  have ht_hi : t < (q0 : ℤ) + 1 := by nlinarith
  omega

private lemma solve_signed_L1 {k p B : ℕ} (hk : 0 < k) (hB : 1 ≤ B) (hp : p.Prime)
    (hBp : 2 * B < p) (u : Fin k → (ZMod p)ˣ)
    (hu : ∀ I : Finset (Fin k), I.Nonempty → ∑ i ∈ I, (u i : ZMod p) ≠ 0)
    (m : (ZMod p)ˣ)
    (hm : ∑ i : Fin k, min (((m * u i : (ZMod p)ˣ) : ZMod p).val)
      (p - ((m * u i : (ZMod p)ˣ) : ZMod p).val) ≤ B) :
    ∃ col : (ZMod p)ˣ → Fin (4 * B ^ 2 + 4 * B), ∀ x : Fin k → (ZMod p)ˣ,
      (∀ i j, col (x i) = col (x j)) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  -- Pick signed integer representatives b₀ i ∈ (-p/2, p/2) of m * u i
  let b0 : Fin k → ℤ := fun i =>
    if 2 * ((m * u i : (ZMod p)ˣ) : ZMod p).val < p then
      (((m * u i : (ZMod p)ˣ) : ZMod p).val : ℤ)
    else
      (((m * u i : (ZMod p)ˣ) : ZMod p).val : ℤ) - (p : ℤ)
  have hb0_cast : ∀ i : Fin k, (b0 i : ZMod p) = ((m * u i : (ZMod p)ˣ) : ZMod p) := fun i => by
    dsimp only [b0]
    split_ifs <;> simp
  have hb0_abs : ∀ i : Fin k, (b0 i).natAbs =
      min (((m * u i : (ZMod p)ˣ) : ZMod p).val) (p - ((m * u i : (ZMod p)ˣ) : ZMod p).val) := fun i => by
    dsimp only [b0]
    have hlt := ZMod.val_lt ((m * u i : (ZMod p)ˣ) : ZMod p)
    split_ifs with h <;> omega
  have hb0_sum_abs : ∑ i : Fin k, (b0 i).natAbs ≤ B := by
    simpa [hb0_abs] using hm
  -- Adjust global sign so S = ∑ b i > 0
  let sgn : ℤ := if 0 ≤ ∑ i : Fin k, b0 i then 1 else -1
  let b : Fin k → ℤ := fun i => sgn * b0 i
  have hsgn_abs : sgn.natAbs = 1 := by dsimp only [sgn]; split_ifs <;> decide
  have hb_abs : ∀ i : Fin k, (b i).natAbs = (b0 i).natAbs := fun i => by
    dsimp only [b]
    rw [Int.natAbs_mul, hsgn_abs, one_mul]
  have hb_sum_abs : ∑ i : Fin k, (b i).natAbs ≤ B := by
    simpa [hb_abs] using hb0_sum_abs
  have hb_cast : ∀ i : Fin k, (b i : ZMod p) = (sgn : ZMod p) * ((m * u i : (ZMod p)ˣ) : ZMod p) := fun i => by
    dsimp only [b]
    rw [Int.cast_mul, hb0_cast]
  have hsgn_ne : (sgn : ZMod p) ≠ 0 := by
    dsimp only [sgn]
    split_ifs <;> simp
  have hb_subset_ne : ∀ I : Finset (Fin k), I.Nonempty → ∑ i ∈ I, b i ≠ 0 := by
    intro I hIne hzero
    have hz : ((∑ i ∈ I, b i : ℤ) : ZMod p) = 0 := by rw [hzero]; simp
    push_cast at hz
    have hfac : ((sgn : ZMod p) * (m : ZMod p)) * ∑ i ∈ I, (u i : ZMod p) = 0 := by
      rw [Finset.mul_sum]
      convert hz using 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb_cast i, Units.val_mul, mul_assoc]
    have hsm : (sgn : ZMod p) * (m : ZMod p) ≠ 0 := mul_ne_zero hsgn_ne m.ne_zero
    exact hu I hIne ((mul_eq_zero.mp hfac).resolve_left hsm)
  have hS_pos : 0 < ∑ i : Fin k, b i := by
    have hne : ∑ i : Fin k, b i ≠ 0 := hb_subset_ne Finset.univ ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    have hnonneg : 0 ≤ ∑ i : Fin k, b i := by
      dsimp only [b, sgn]
      rw [← Finset.mul_sum]
      split_ifs with h
      · simpa using h
      · linarith
    omega
  let D : ℕ := (∑ i : Fin k, b i).natAbs
  have hD_cast : (D : ℤ) = ∑ i : Fin k, b i := by
    dsimp only [D]
    exact Int.natAbs_of_nonneg (le_of_lt hS_pos)
  have hD_pos : 0 < D := by omega
  have hD_le_B : D ≤ B := by
    have h1 : (D : ℤ) ≤ ∑ i : Fin k, ((b i).natAbs : ℤ) := by
      rw [hD_cast]
      exact Finset.sum_le_sum fun i _ => Int.le_natAbs
    have h2 : (∑ i : Fin k, ((b i).natAbs : ℤ)) ≤ (B : ℤ) := by exact_mod_cast hb_sum_abs
    omega
  -- Prime q with B < q ≤ 2 * B via Bertrand's postulate
  obtain ⟨q, hq_prime, hBq, hq2B⟩ := Nat.exists_prime_lt_and_le_two_mul B (by omega)
  have hq_not_dvd : ∀ I : Finset (Fin k), I.Nonempty → ¬ (q : ℤ) ∣ ∑ i ∈ I, b i := by
    intro I hIne hdvd
    have hne : ∑ i ∈ I, b i ≠ 0 := hb_subset_ne I hIne
    have hle1 : (∑ i ∈ I, b i).natAbs ≤ ∑ i ∈ I, (b i).natAbs := by
      have := Finset.abs_sum_le_sum_abs b I
      have hcast : ∀ s : Finset (Fin k), (∑ i ∈ s, |b i|) = ∑ i ∈ s, ((b i).natAbs : ℤ) :=
        fun _ => Finset.sum_congr rfl fun _ _ => Int.abs_eq_natAbs _
      rw [Int.abs_eq_natAbs, hcast] at this
      exact_mod_cast this
    have hle2 : ∑ i ∈ I, (b i).natAbs ≤ B :=
      le_trans (Finset.sum_le_sum_of_subset (Finset.subset_univ I)) hb_sum_abs
    have hnat_dvd : q ∣ (∑ i ∈ I, b i).natAbs := Int.natCast_dvd.mp hdvd
    have hpos : 0 < (∑ i ∈ I, b i).natAbs := Int.natAbs_pos.mpr hne
    have hqle : q ≤ (∑ i ∈ I, b i).natAbs := Nat.le_of_dvd hpos hnat_dvd
    omega
  -- Define colouring in Fin (4 * B ^ 2 + 4 * B):
  --   Region A1 (2 * B * r_x < p):           color 4 * B^2 + (ordCompl[q] r_x % q)
  --   Region A2 (2 * B * (p - r_x) < p):     color 4 * B^2 + 2 * B + (ordCompl[q] (p - r_x) % q)
  --   Region B  (both >= p):                 color (4 * B^2 * v_x) / p
  let r_of : (ZMod p)ˣ → ℕ := fun x => (D * (x : ZMod p).val) % p
  let col : (ZMod p)ˣ → Fin (4 * B ^ 2 + 4 * B) := fun x =>
    if 2 * B * r_of x < p then
      ⟨4 * B ^ 2 + (ordCompl[q] (r_of x)) % q, by
        have hlt := Nat.mod_lt (ordCompl[q] (r_of x)) hq_prime.pos
        omega⟩
    else if 2 * B * (p - r_of x) < p then
      ⟨4 * B ^ 2 + 2 * B + (ordCompl[q] (p - r_of x)) % q, by
        have hlt := Nat.mod_lt (ordCompl[q] (p - r_of x)) hq_prime.pos
        omega⟩
    else
      ⟨(4 * B ^ 2 * (x : ZMod p).val) / p, by
        have h1 : 4 * B ^ 2 * (x : ZMod p).val < p * (4 * B ^ 2) := by
          have hlt := ZMod.val_lt (x : ZMod p)
          nlinarith [hp.pos]
        have h2 : (4 * B ^ 2 * (x : ZMod p).val) / p < 4 * B ^ 2 := Nat.div_lt_of_lt_mul h1
        omega⟩
  refine ⟨col, fun x hmon hsum => ?_⟩
  -- Transfer ∑ u_i x_i = 0 to ∑ b_i x_i = 0 in ZMod p
  have hsum_b : ∑ i : Fin k, (b i : ZMod p) * (x i : ZMod p) = 0 := by
    have hfac : ((sgn : ZMod p) * (m : ZMod p)) * ∑ i : Fin k, (u i : ZMod p) * (x i : ZMod p) = 0 := by
      rw [hsum, mul_zero]
    rw [Finset.mul_sum] at hfac
    convert hfac using 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb_cast i, Units.val_mul]
    ring
  have hr_pos : ∀ i : Fin k, 0 < r_of (x i) := fun i => by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have hpdvd : p ∣ D * (x i : ZMod p).val := Nat.dvd_of_mod_eq_zero h0
    rcases hp.dvd_mul.mp hpdvd with hpD | hpX
    · have := Nat.le_of_dvd hD_pos hpD; omega
    · have hXpos : 0 < (x i : ZMod p).val := Nat.pos_of_ne_zero fun hz =>
        (x i).ne_zero ((ZMod.val_eq_zero _).mp hz)
      have := Nat.le_of_dvd hXpos hpX
      have := ZMod.val_lt (x i : ZMod p)
      omega
  have hr_lt : ∀ i : Fin k, r_of (x i) < p := fun i => Nat.mod_lt _ hp.pos
  let i0 : Fin k := ⟨0, hk⟩
  -- Case split on which region x i0 lies in; monochromaticity forces all x i into the same region!
  by_cases hA1 : 2 * B * r_of (x i0) < p
  · have hallA1 : ∀ i : Fin k, 2 * B * r_of (x i) < p ∧
        (ordCompl[q] (r_of (x i))) % q = (ordCompl[q] (r_of (x i0))) % q := by
      intro i
      have hci := congrArg Fin.val (hmon i i0)
      dsimp only [col] at hci
      rw [if_pos hA1] at hci
      have hmod0 := Nat.mod_lt (ordCompl[q] (r_of (x i0))) hq_prime.pos
      split_ifs at hci with h1 h2 <;> simp only at hci
      · exact ⟨h1, by omega⟩
      · have hmod2 := Nat.mod_lt (ordCompl[q] (p - r_of (x i))) hq_prime.pos
        omega
      · have hlt_v : (4 * B ^ 2 * (x i : ZMod p).val) / p < 4 * B ^ 2 := by
          refine Nat.div_lt_of_lt_mul ?_
          have := ZMod.val_lt (x i : ZMod p); nlinarith [hp.pos]
        omega
    -- Show ∑ b_i * r_of(x_i) = 0 in ℤ, contradicting base_q_no_int_sol
    have hzmod : ((∑ i : Fin k, b i * (r_of (x i) : ℤ) : ℤ) : ZMod p) = 0 := by
      push_cast
      have hterm : ∀ i : Fin k, (b i : ZMod p) * ((r_of (x i) : ℕ) : ZMod p) =
          (D : ZMod p) * ((b i : ZMod p) * (x i : ZMod p)) := fun i => by
        dsimp only [r_of]
        rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_zmod_val]
        ring
      rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, hsum_b, mul_zero]
    have hpdvd : (p : ℤ) ∣ ∑ i : Fin k, b i * (r_of (x i) : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hzmod
    have habs_lt : |∑ i : Fin k, b i * (r_of (x i) : ℤ)| < (p : ℤ) := by
      have h1 : (2 * B : ℤ) * |∑ i : Fin k, b i * (r_of (x i) : ℤ)| ≤
          ∑ i : Fin k, ((b i).natAbs : ℤ) * ((2 * B * r_of (x i) : ℕ) : ℤ) := by
        calc (2 * B : ℤ) * |∑ i : Fin k, b i * (r_of (x i) : ℤ)|
            ≤ (2 * B : ℤ) * ∑ i : Fin k, |b i * (r_of (x i) : ℤ)| :=
              mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by omega)
          _ = ∑ i : Fin k, ((b i).natAbs : ℤ) * ((2 * B * r_of (x i) : ℕ) : ℤ) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [abs_mul, Int.abs_eq_natAbs, abs_of_nonneg (Int.natCast_nonneg _)]
              push_cast; ring
      have h2 : ∑ i : Fin k, ((b i).natAbs : ℤ) * ((2 * B * r_of (x i) : ℕ) : ℤ) ≤
          ∑ i : Fin k, ((b i).natAbs : ℤ) * (p : ℤ) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (by exact_mod_cast (hallA1 i).1.le) (Int.natCast_nonneg _)
      have h3 : ∑ i : Fin k, ((b i).natAbs : ℤ) * (p : ℤ) ≤ (B : ℤ) * (p : ℤ) := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hb_sum_abs) (by omega)
      nlinarith [hp.pos]
    have hzero : ∑ i : Fin k, b i * (r_of (x i) : ℤ) = 0 := by
      obtain ⟨t, ht⟩ := hpdvd
      rw [ht, abs_mul, abs_of_pos (by exact_mod_cast hp.pos : (0 : ℤ) < p)] at habs_lt
      have habs_t : |t| < 1 := by nlinarith [hp.pos]
      have ht0 : t = 0 := by have := abs_lt.mp habs_t; omega
      rw [ht, ht0, mul_zero]
    exact base_q_no_int_sol hk hq_prime b hq_not_dvd (fun i => r_of (x i)) hr_pos
      (fun i j => (hallA1 i).2.trans (hallA1 j).2.symm) hzero
  · by_cases hA2 : 2 * B * (p - r_of (x i0)) < p
    · have hallA2 : ∀ i : Fin k, 2 * B * (p - r_of (x i)) < p ∧
          (ordCompl[q] (p - r_of (x i))) % q = (ordCompl[q] (p - r_of (x i0))) % q := by
        intro i
        have hci := congrArg Fin.val (hmon i i0)
        dsimp only [col] at hci
        rw [if_neg hA1, if_pos hA2] at hci
        have hmod0 := Nat.mod_lt (ordCompl[q] (p - r_of (x i0))) hq_prime.pos
        split_ifs at hci with h1 h2 <;> simp only at hci
        · have hmod1 := Nat.mod_lt (ordCompl[q] (r_of (x i))) hq_prime.pos
          omega
        · exact ⟨h2, by omega⟩
        · have hlt_v : (4 * B ^ 2 * (x i : ZMod p).val) / p < 4 * B ^ 2 := by
            refine Nat.div_lt_of_lt_mul ?_
            have := ZMod.val_lt (x i : ZMod p); nlinarith [hp.pos]
          omega
      have hzmod : ((∑ i : Fin k, b i * ((p - r_of (x i) : ℕ) : ℤ) : ℤ) : ZMod p) = 0 := by
        push_cast
        have hterm : ∀ i : Fin k, (b i : ZMod p) * (((p - r_of (x i) : ℕ) : ZMod p)) =
            -(D : ZMod p) * ((b i : ZMod p) * (x i : ZMod p)) := fun i => by
          rw [Nat.cast_sub (hr_lt i).le, ZMod.natCast_self, zero_sub]
          dsimp only [r_of]
          rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_zmod_val]
          ring
        rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, hsum_b, mul_zero]
      have hpdvd : (p : ℤ) ∣ ∑ i : Fin k, b i * ((p - r_of (x i) : ℕ) : ℤ) :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hzmod
      have habs_lt : |∑ i : Fin k, b i * ((p - r_of (x i) : ℕ) : ℤ)| < (p : ℤ) := by
        have h1 : (2 * B : ℤ) * |∑ i : Fin k, b i * ((p - r_of (x i) : ℕ) : ℤ)| ≤
            ∑ i : Fin k, ((b i).natAbs : ℤ) * ((2 * B * (p - r_of (x i)) : ℕ) : ℤ) := by
          calc (2 * B : ℤ) * |∑ i : Fin k, b i * ((p - r_of (x i) : ℕ) : ℤ)|
              ≤ (2 * B : ℤ) * ∑ i : Fin k, |b i * ((p - r_of (x i) : ℕ) : ℤ)| :=
                mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by omega)
            _ = ∑ i : Fin k, ((b i).natAbs : ℤ) * ((2 * B * (p - r_of (x i)) : ℕ) : ℤ) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [abs_mul, Int.abs_eq_natAbs, abs_of_nonneg (Int.natCast_nonneg _)]
                push_cast; ring
        have h2 : ∑ i : Fin k, ((b i).natAbs : ℤ) * ((2 * B * (p - r_of (x i)) : ℕ) : ℤ) ≤
            ∑ i : Fin k, ((b i).natAbs : ℤ) * (p : ℤ) :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (by exact_mod_cast (hallA2 i).1.le) (Int.natCast_nonneg _)
        have h3 : ∑ i : Fin k, ((b i).natAbs : ℤ) * (p : ℤ) ≤ (B : ℤ) * (p : ℤ) := by
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hb_sum_abs) (by omega)
        nlinarith [hp.pos]
      have hzero : ∑ i : Fin k, b i * ((p - r_of (x i) : ℕ) : ℤ) = 0 := by
        obtain ⟨t, ht⟩ := hpdvd
        rw [ht, abs_mul, abs_of_pos (by exact_mod_cast hp.pos : (0 : ℤ) < p)] at habs_lt
        have habs_t : |t| < 1 := by nlinarith [hp.pos]
        have ht0 : t = 0 := by have := abs_lt.mp habs_t; omega
        rw [ht, ht0, mul_zero]
      exact base_q_no_int_sol hk hq_prime b hq_not_dvd (fun i => p - r_of (x i))
        (fun i => by have := hr_lt i; omega)
        (fun i j => (hallA2 i).2.trans (hallA2 j).2.symm) hzero
    · -- Region B: p ≤ 2 * B * r_of (x i0) and p ≤ 2 * B * (p - r_of (x i0)), all share same bin c
      have hbin : ∀ i : Fin k,
          (4 * B ^ 2 * (x i : ZMod p).val) / p = (4 * B ^ 2 * (x i0 : ZMod p).val) / p := by
        intro i
        have hci := congrArg Fin.val (hmon i i0)
        dsimp only [col] at hci
        rw [if_neg hA1, if_neg hA2] at hci
        have hlt0 : (4 * B ^ 2 * (x i0 : ZMod p).val) / p < 4 * B ^ 2 := by
          refine Nat.div_lt_of_lt_mul ?_
          have := ZMod.val_lt (x i0 : ZMod p); nlinarith [hp.pos]
        split_ifs at hci with h1 h2 <;> simp only at hci
        · omega
        · omega
        · exact hci
      have hbi0_ne : b i0 ≠ 0 := by simpa using hb_subset_ne {i0} (Finset.singleton_nonempty i0)
      exact solve_signed_L1_regionB hB hp b hb_sum_abs hD_cast i0 hbi0_ne x hsum_b hA1 hA2 hbin

/- ### Module 3: Universal Bohr-Averaging Independence Bounds & Greedy Dilate Colouring -/

private lemma exists_large_solution_free_set {k p : ℕ} (hk : 0 < k) (hp : p.Prime)
    (u : Fin k → (ZMod p)ˣ) (hsum_ne : ∑ i : Fin k, (u i : ZMod p) ≠ 0) :
    ∃ A : Finset (ZMod p)ˣ,
      p ^ (k - 1) * A.card ≥ ((p - 1) / k) ^ k ∧
      ∀ x : Fin k → (ZMod p)ˣ, (∀ i, x i ∈ A) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let L : ℕ := (p - 1) / k
  have hkL : k * L < p := by
    have h1 : k * L ≤ p - 1 := Nat.mul_div_le (p - 1) k
    have h2 := hp.two_le
    omega
  -- Parametrize shifts t : Fin (k - 1) → ZMod p; last shift is -(∑ t)
  let iLast : Fin k := ⟨k - 1, by omega⟩
  let shiftOf : (Fin (k - 1) → ZMod p) → Fin k → ZMod p := fun t i =>
    if h : i.val < k - 1 then t ⟨i.val, h⟩ else -(∑ j : Fin (k - 1), t j)
  have hshift_sum : ∀ t : Fin (k - 1) → ZMod p, ∑ i : Fin k, shiftOf t i = 0 := by
    intro t
    have hsplit : (Finset.univ : Finset (Fin k)) =
        insert iLast (Finset.univ.erase iLast) := (Finset.insert_erase (Finset.mem_univ iLast)).symm
    rw [hsplit, Finset.sum_insert (Finset.notMem_erase _ _)]
    have hlast : shiftOf t iLast = -(∑ j : Fin (k - 1), t j) := by
      dsimp only [shiftOf, iLast]; simp
    have hrest : ∑ i ∈ Finset.univ.erase iLast, shiftOf t i = ∑ j : Fin (k - 1), t j := by
      refine Finset.sum_bij (fun i hi => ⟨i.val, by
        have hne : i ≠ iLast := (Finset.mem_erase.mp hi).1
        have hlt : i.val < k := i.isLt
        have : i.val ≠ k - 1 := fun heq => hne (Fin.ext heq)
        omega⟩) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro a _ b _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
      · intro j _
        refine ⟨⟨j.val, by omega⟩, Finset.mem_erase.mpr ⟨fun h => by
          have := congrArg Fin.val h; dsimp [iLast] at this; omega, Finset.mem_univ _⟩, rfl⟩
      · intro i hi
        have hne : i ≠ iLast := (Finset.mem_erase.mp hi).1
        have hlt : i.val < k - 1 := by
          have : i.val ≠ k - 1 := fun heq => hne (Fin.ext heq)
          omega
        dsimp only [shiftOf]
        rw [dif_pos hlt]
    rw [hlast, hrest, neg_add_cancel]
  let A_of : (Fin (k - 1) → ZMod p) → Finset (ZMod p)ˣ := fun t =>
    Finset.univ.filter fun x => ∀ i : Fin k,
      1 ≤ ((u i : ZMod p) * (x : ZMod p) - shiftOf t i).val ∧
      ((u i : ZMod p) * (x : ZMod p) - shiftOf t i).val ≤ L
  have hsf : ∀ t : Fin (k - 1) → ZMod p,
      ∀ x : Fin k → (ZMod p)ˣ, (∀ i, x i ∈ A_of t) →
        ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0 := by
    intro t x hx hzero
    have hmem : ∀ i : Fin k,
        1 ≤ ((u i : ZMod p) * (x i : ZMod p) - shiftOf t i).val ∧
        ((u i : ZMod p) * (x i : ZMod p) - shiftOf t i).val ≤ L :=
      fun i => (Finset.mem_filter.mp (hx i)).2 i
    have hsum_val_pos : 0 < ∑ i : Fin k, ((u i : ZMod p) * (x i : ZMod p) - shiftOf t i).val := by
      let i0 : Fin k := ⟨0, hk⟩
      have hle : ((u i0 : ZMod p) * (x i0 : ZMod p) - shiftOf t i0).val ≤
          ∑ i : Fin k, ((u i : ZMod p) * (x i : ZMod p) - shiftOf t i).val :=
        Finset.single_le_sum (f := fun i => ((u i : ZMod p) * (x i : ZMod p) - shiftOf t i).val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i0)
      exact lt_of_lt_of_le Nat.zero_lt_one (le_trans (hmem i0).1 hle)
    have hsum_val_lt : ∑ i : Fin k, ((u i : ZMod p) * (x i : ZMod p) - shiftOf t i).val < p := by
      calc ∑ i : Fin k, ((u i : ZMod p) * (x i : ZMod p) - shiftOf t i).val
          ≤ ∑ _i : Fin k, L := Finset.sum_le_sum fun i _ => (hmem i).2
        _ = k * L := by simp
        _ < p := hkL
    have hzmod : ((∑ i : Fin k, ((u i : ZMod p) * (x i : ZMod p) - shiftOf t i).val : ℕ) : ZMod p) = 0 := by
      push_cast
      simp only [ZMod.natCast_zmod_val]
      rw [Finset.sum_sub_distrib, hzero, hshift_sum t, sub_zero]
    have hpdvd : p ∣ ∑ i : Fin k, ((u i : ZMod p) * (x i : ZMod p) - shiftOf t i).val :=
      (ZMod.natCast_eq_zero_iff _ p).mp hzmod
    have := Nat.le_of_dvd hsum_val_pos hpdvd
    omega
  -- Exact averaging: ∑ t, (A_of t).card = L ^ k
  have havg : ∑ t : Fin (k - 1) → ZMod p, (A_of t).card = L ^ k := by
    let R : Finset (ZMod p) := Finset.univ.filter fun r => 1 ≤ r.val ∧ r.val ≤ L
    have hRcard : R.card = L := by
      have hbij : R.card = (Finset.Icc 1 L).card := by
        refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
        · intro r hr
          obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hr).2
          exact Finset.mem_Icc.mpr ⟨h1, h2⟩
        · intro a _ b _ h; exact ZMod.val_injective p h
        · intro n hn
          obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
          have hnp : n < p := by
            have : L < p := by nlinarith [hk]
            omega
          refine ⟨(n : ZMod p), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ZMod.val_natCast_of_lt hnp⟩
          rw [ZMod.val_natCast_of_lt hnp]; exact ⟨h1, h2⟩
      rw [hbij, Nat.card_Icc, Nat.add_sub_cancel]
    let S_u : (ZMod p)ˣ := (isUnit_iff_ne_zero.mpr hsum_ne).unit
    have hSu_val : (S_u : ZMod p) = ∑ i : Fin k, (u i : ZMod p) := IsUnit.unit_spec _
    -- Rewrite ∑ t, (A_of t).card as cardinality of pairs (t, x) where x ∈ A_of t
    -- Map (t, x) ↦ (r : Fin (k - 1) → ZMod p, rLast : ZMod p) where r j = u j * x - t j and rLast = u iLast * x - shiftOf t iLast
    have hpair : (∑ t : Fin (k - 1) → ZMod p, (A_of t).card) =
        ((Finset.univ.filter fun p_tx : (Fin (k - 1) → ZMod p) × (ZMod p)ˣ =>
          p_tx.2 ∈ A_of p_tx.1)).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp
    rw [hpair]
    let target : Finset ((Fin (k - 1) → ZMod p) × ZMod p) :=
      (Fintype.piFinset fun _ : Fin (k - 1) => R) ×ˢ R
    have htarget_card : target.card = L ^ k := by
      dsimp only [target]
      rw [Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_fin, hRcard]
      rw [← pow_succ, Nat.sub_add_cancel hk]
    rw [← htarget_card]
    refine Finset.card_bij
      (fun (p_tx : (Fin (k - 1) → ZMod p) × (ZMod p)ˣ) _ =>
        (fun j : Fin (k - 1) => (u ⟨j.val, by omega⟩ : ZMod p) * (p_tx.2 : ZMod p) - p_tx.1 j,
         (u iLast : ZMod p) * (p_tx.2 : ZMod p) - shiftOf p_tx.1 iLast))
      ?_ ?_ ?_
    · rintro ⟨t, x⟩ htx
      have hx := (Finset.mem_filter.mp (Finset.mem_filter.mp htx).2).2
      dsimp only [target]
      rw [Finset.mem_product, Fintype.mem_piFinset]
      refine ⟨fun j => ?_, ?_⟩
      · have hj := hx ⟨j.val, by omega⟩
        dsimp only [shiftOf] at hj
        rw [dif_pos j.isLt] at hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx iLast⟩
    · rintro ⟨t1, x1⟩ h1 ⟨t2, x2⟩ h2 heq
      have hfst : ∀ j : Fin (k - 1),
          (u ⟨j.val, by omega⟩ : ZMod p) * (x1 : ZMod p) - t1 j =
          (u ⟨j.val, by omega⟩ : ZMod p) * (x2 : ZMod p) - t2 j :=
        fun j => congrFun (congrArg Prod.fst heq) j
      have hsnd : (u iLast : ZMod p) * (x1 : ZMod p) - shiftOf t1 iLast =
          (u iLast : ZMod p) * (x2 : ZMod p) - shiftOf t2 iLast := congrArg Prod.snd heq
      -- Sum all k components to recover S_u * x1 = S_u * x2
      have hsum_eq : ∀ t : Fin (k - 1) → ZMod p, ∀ x : (ZMod p)ˣ,
          (∑ j : Fin (k - 1), ((u ⟨j.val, by omega⟩ : ZMod p) * (x : ZMod p) - t j)) +
          ((u iLast : ZMod p) * (x : ZMod p) - shiftOf t iLast) =
          (S_u : ZMod p) * (x : ZMod p) := fun t x => by
        rw [Finset.sum_sub_distrib]
        have hlast : shiftOf t iLast = -(∑ j : Fin (k - 1), t j) := by dsimp only [shiftOf, iLast]; simp
        rw [hlast, sub_neg_eq_add]
        have hu_split : (∑ j : Fin (k - 1), (u ⟨j.val, by omega⟩ : ZMod p) * (x : ZMod p)) +
            (u iLast : ZMod p) * (x : ZMod p) = (∑ i : Fin k, (u i : ZMod p)) * (x : ZMod p) := by
          rw [Finset.sum_mul]
          have hsp : (Finset.univ : Finset (Fin k)) = insert iLast (Finset.univ.erase iLast) :=
            (Finset.insert_erase (Finset.mem_univ iLast)).symm
          rw [hsp, Finset.sum_insert (Finset.notMem_erase _ _), add_comm]
          congr 1
          refine Finset.sum_bij (fun j _ => ⟨j.val, by omega⟩) ?_ ?_ ?_ (fun _ _ => rfl)
          · intro j _
            exact Finset.mem_erase.mpr ⟨fun h => by
              have := congrArg Fin.val h; dsimp [iLast] at this; omega, Finset.mem_univ _⟩
          · intro a _ b _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
          · intro i hi
            have hne : i ≠ iLast := (Finset.mem_erase.mp hi).1
            have hlt : i.val < k - 1 := by
              have : i.val ≠ k - 1 := fun heq => hne (Fin.ext heq)
              omega
            exact ⟨⟨i.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
        rw [← hSu_val] at hu_split
        linear_combination hu_split
      have hSx : (S_u : ZMod p) * (x1 : ZMod p) = (S_u : ZMod p) * (x2 : ZMod p) := by
        rw [← hsum_eq t1 x1, ← hsum_eq t2 x2, hsnd]
        congr 1
        exact Finset.sum_congr rfl fun j _ => hfst j
      have hx_eq : x1 = x2 := Units.ext (mul_left_cancel₀ S_u.ne_zero hSx)
      subst hx_eq
      ext j
      · have hj := hfst j
        exact sub_right_injective hj
      · rfl
    · rintro ⟨r, rL⟩ hmem
      dsimp only [target] at hmem
      rw [Finset.mem_product, Fintype.mem_piFinset] at hmem
      obtain ⟨hr, hrL⟩ := hmem
      -- Sum of all k entries lies in [k, k * L] ⊆ [1, p - 1], hence nonzero in ZMod p!
      have htot_ne : (∑ j : Fin (k - 1), r j) + rL ≠ 0 := by
        have hpos : 0 < (∑ j : Fin (k - 1), (r j).val) + rL.val := by
          have h1 : 1 ≤ rL.val := (Finset.mem_filter.mp hrL).2.1
          omega
        have hlt : (∑ j : Fin (k - 1), (r j).val) + rL.val < p := by
          have h1 : ∑ j : Fin (k - 1), (r j).val ≤ (k - 1) * L := by
            calc ∑ j : Fin (k - 1), (r j).val ≤ ∑ _j : Fin (k - 1), L :=
                  Finset.sum_le_sum fun j _ => (Finset.mem_filter.mp (hr j)).2.2
              _ = (k - 1) * L := by simp
          have h2 : rL.val ≤ L := (Finset.mem_filter.mp hrL).2.2
          have h3 : (k - 1) * L + L = k * L := by
            have : (k - 1 + 1) * L = k * L := by rw [Nat.sub_add_cancel hk]
            linarith
          omega
        intro hz
        have hcast : (((∑ j : Fin (k - 1), (r j).val) + rL.val : ℕ) : ZMod p) = 0 := by
          push_cast; simp only [ZMod.natCast_zmod_val]; exact hz
        have hdvd := (ZMod.natCast_eq_zero_iff _ p).mp hcast
        have := Nat.le_of_dvd hpos hdvd
        omega
      let x : (ZMod p)ˣ := S_u⁻¹ * (isUnit_iff_ne_zero.mpr htot_ne).unit
      have hx_val : (S_u : ZMod p) * (x : ZMod p) = (∑ j : Fin (k - 1), r j) + rL := by
        dsimp only [x]
        rw [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul, IsUnit.unit_spec]
      let t : Fin (k - 1) → ZMod p := fun j => (u ⟨j.val, by omega⟩ : ZMod p) * (x : ZMod p) - r j
      have hlast_eq : (u iLast : ZMod p) * (x : ZMod p) - shiftOf t iLast = rL := by
        have hlast : shiftOf t iLast = -(∑ j : Fin (k - 1), t j) := by dsimp only [shiftOf, iLast]; simp
        rw [hlast, sub_neg_eq_add]
        have hu_split : (∑ j : Fin (k - 1), (u ⟨j.val, by omega⟩ : ZMod p) * (x : ZMod p)) +
            (u iLast : ZMod p) * (x : ZMod p) = (S_u : ZMod p) * (x : ZMod p) := by
          rw [hSu_val, Finset.sum_mul]
          have hsp : (Finset.univ : Finset (Fin k)) = insert iLast (Finset.univ.erase iLast) :=
            (Finset.insert_erase (Finset.mem_univ iLast)).symm
          rw [hsp, Finset.sum_insert (Finset.notMem_erase _ _), add_comm]
          congr 1
          refine Finset.sum_bij (fun j _ => ⟨j.val, by omega⟩) ?_ ?_ ?_ (fun _ _ => rfl)
          · intro j _
            exact Finset.mem_erase.mpr ⟨fun h => by
              have := congrArg Fin.val h; dsimp [iLast] at this; omega, Finset.mem_univ _⟩
          · intro a _ b _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
          · intro i hi
            have hne : i ≠ iLast := (Finset.mem_erase.mp hi).1
            have hlt : i.val < k - 1 := by
              have : i.val ≠ k - 1 := fun heq => hne (Fin.ext heq)
              omega
            exact ⟨⟨i.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
        have ht_sum : ∑ j : Fin (k - 1), t j =
            (∑ j : Fin (k - 1), (u ⟨j.val, by omega⟩ : ZMod p) * (x : ZMod p)) - ∑ j : Fin (k - 1), r j := by
          dsimp only [t]; rw [Finset.sum_sub_distrib]
        rw [ht_sum]
        linear_combination hu_split + hx_val
      refine ⟨(t, x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩, ?_⟩
      · intro i
        by_cases hlt : i.val < k - 1
        · dsimp only [shiftOf]; rw [dif_pos hlt]
          have heq : (u i : ZMod p) * (x : ZMod p) - t ⟨i.val, hlt⟩ = r ⟨i.val, hlt⟩ := by
            dsimp only [t]; exact sub_sub_cancel _ _
          rw [heq]
          exact (Finset.mem_filter.mp (hr ⟨i.val, hlt⟩)).2
        · have hi_eq : i = iLast := Fin.ext (by dsimp [iLast]; omega)
          rw [hi_eq, hlast_eq]
          exact (Finset.mem_filter.mp hrL).2
      · ext j
        · dsimp only [t]; exact sub_sub_cancel _ _
        · exact hlast_eq
  -- Pigeonhole over t : Fin (k - 1) → ZMod p
  have hne_t : (Finset.univ : Finset (Fin (k - 1) → ZMod p)).Nonempty :=
    ⟨fun _ => 0, Finset.mem_univ _⟩
  obtain ⟨t_max, -, ht_max⟩ := Finset.exists_max_image Finset.univ (fun t => (A_of t).card) hne_t
  refine ⟨A_of t_max, ?_, hsf t_max⟩
  calc L ^ k = ∑ t : Fin (k - 1) → ZMod p, (A_of t).card := havg.symm
    _ ≤ ∑ _t : Fin (k - 1) → ZMod p, (A_of t_max).card :=
        Finset.sum_le_sum fun t _ => ht_max t (Finset.mem_univ t)
    _ = p ^ (k - 1) * (A_of t_max).card := by
        simp [Fintype.card_pi, ZMod.card]

private lemma exists_large_solution_free_equal_pair {p : ℕ} (hp : p.Prime)
    (u : Fin 3 → (ZMod p)ˣ) (hu0 : u 0 = 1) (hu1 : u 1 = 1)
    (hsum_ne : (2 : ZMod p) + (u 2 : ZMod p) ≠ 0) :
    ∃ A : Finset (ZMod p)ˣ,
      p * A.card ≥ ((p - 1) / 4) * (p - 1 - 2 * ((p - 1) / 4)) ∧
      ∀ x : Fin 3 → (ZMod p)ˣ, (∀ i, x i ∈ A) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let L : ℕ := (p - 1) / 4
  have h2L : 2 * L ≤ p - 1 := by
    have := Nat.mul_div_le (p - 1) 4; omega
  let A_of : ZMod p → Finset (ZMod p)ˣ := fun t =>
    Finset.univ.filter fun x =>
      1 ≤ ((x : ZMod p) - t).val ∧ ((x : ZMod p) - t).val ≤ L ∧
      2 * L + 1 ≤ (-(u 2 : ZMod p) * (x : ZMod p) - 2 * t).val
  have hsf : ∀ t : ZMod p, ∀ x : Fin 3 → (ZMod p)ˣ, (∀ i, x i ∈ A_of t) →
      ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0 := by
    intro t x hx hzero
    have h0 := (Finset.mem_filter.mp (hx 0)).2
    have h1 := (Finset.mem_filter.mp (hx 1)).2
    have h2 := (Finset.mem_filter.mp (hx 2)).2
    have heq : ((x 0 : ZMod p) - t) + ((x 1 : ZMod p) - t) =
        -(u 2 : ZMod p) * (x 2 : ZMod p) - 2 * t := by
      rw [Fin.sum_univ_three, hu0, hu1, Units.val_one, one_mul, one_mul] at hzero
      linear_combination hzero
    have hsum_lt : ((x 0 : ZMod p) - t).val + ((x 1 : ZMod p) - t).val < p := by
      have := hp.two_le; omega
    have hval_add : (((x 0 : ZMod p) - t) + ((x 1 : ZMod p) - t)).val =
        ((x 0 : ZMod p) - t).val + ((x 1 : ZMod p) - t).val := by
      rw [ZMod.val_add, Nat.mod_eq_of_lt hsum_lt]
    rw [heq] at hval_add
    omega
  -- Average over t ∈ ZMod p: ∑ t, (A_of t).card = L * (p - 1 - 2 * L)
  have havg : ∑ t : ZMod p, (A_of t).card = L * (p - 1 - 2 * L) := by
    let R1 : Finset (ZMod p) := Finset.univ.filter fun r => 1 ≤ r.val ∧ r.val ≤ L
    let R2 : Finset (ZMod p) := Finset.univ.filter fun r => 2 * L + 1 ≤ r.val
    have hR1 : R1.card = L := by
      have hbij : R1.card = (Finset.Icc 1 L).card := by
        refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
        · intro r hr; exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hr).2
        · intro a _ b _ h; exact ZMod.val_injective p h
        · intro n hn
          obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
          have hnp : n < p := by omega
          refine ⟨(n : ZMod p), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ZMod.val_natCast_of_lt hnp⟩
          rw [ZMod.val_natCast_of_lt hnp]; exact ⟨h1, h2⟩
      rw [hbij, Nat.card_Icc, Nat.add_sub_cancel]
    have hR2 : R2.card = p - 1 - 2 * L := by
      have hbij : R2.card = (Finset.Icc (2 * L + 1) (p - 1)).card := by
        refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
        · intro r hr
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hr).2, Nat.le_sub_one_of_lt (ZMod.val_lt r)⟩
        · intro a _ b _ h; exact ZMod.val_injective p h
        · intro n hn
          obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
          have hnp : n < p := by have := hp.two_le; omega
          refine ⟨(n : ZMod p), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ZMod.val_natCast_of_lt hnp⟩
          rw [ZMod.val_natCast_of_lt hnp]; exact h1
      rw [hbij, Nat.card_Icc]; omega
    let S_u : (ZMod p)ˣ := (isUnit_iff_ne_zero.mpr hsum_ne).unit
    have hSu : (S_u : ZMod p) = (2 : ZMod p) + (u 2 : ZMod p) := IsUnit.unit_spec _
    have hpair : (∑ t : ZMod p, (A_of t).card) =
        ((Finset.univ.filter fun p_tx : ZMod p × (ZMod p)ˣ => p_tx.2 ∈ A_of p_tx.1)).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun t _ => by simp
    rw [hpair, ← hR2, ← hR1, ← Finset.card_product]
    refine Finset.card_bij
      (fun (p_tx : ZMod p × (ZMod p)ˣ) _ =>
        ((p_tx.2 : ZMod p) - p_tx.1, -(u 2 : ZMod p) * (p_tx.2 : ZMod p) - 2 * p_tx.1))
      ?_ ?_ ?_
    · rintro ⟨t, x⟩ htx
      obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp htx).2).2
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩⟩
    · rintro ⟨t1, x1⟩ _ ⟨t2, x2⟩ _ heq
      have h1 : (x1 : ZMod p) - t1 = (x2 : ZMod p) - t2 := congrArg Prod.fst heq
      have h2 : -(u 2 : ZMod p) * (x1 : ZMod p) - 2 * t1 =
          -(u 2 : ZMod p) * (x2 : ZMod p) - 2 * t2 := congrArg Prod.snd heq
      have hSx : (S_u : ZMod p) * (x1 : ZMod p) = (S_u : ZMod p) * (x2 : ZMod p) := by
        rw [hSu]; linear_combination 2 * h1 - h2
      have hx : x1 = x2 := Units.ext (mul_left_cancel₀ S_u.ne_zero hSx)
      subst hx
      ext
      · exact sub_right_injective h1
      · rfl
    · rintro ⟨r1, r2⟩ hr
      obtain ⟨hr1, hr2⟩ := Finset.mem_product.mp hr
      dsimp only at hr1 hr2
      obtain ⟨h1a, h1b⟩ := (Finset.mem_filter.mp hr1).2
      have h2a := (Finset.mem_filter.mp hr2).2
      -- 2 * r1 - r2 ≠ 0 in ZMod p since 2 * r1.val ≤ 2 * L < 2 * L + 1 ≤ r2.val < p
      have hne : (2 : ZMod p) * r1 - r2 ≠ 0 := by
        intro hz
        have heq : (2 : ZMod p) * r1 = r2 := sub_eq_zero.mp hz
        have hv : ((2 : ZMod p) * r1).val = 2 * r1.val := by
          have hlt : 2 * r1.val < p := by have := hp.two_le; omega
          have hcast : ((2 * r1.val : ℕ) : ZMod p) = (2 : ZMod p) * r1 := by push_cast; simp
          rw [← hcast, ZMod.val_natCast_of_lt hlt]
        rw [heq] at hv
        omega
      let x : (ZMod p)ˣ := S_u⁻¹ * (isUnit_iff_ne_zero.mpr hne).unit
      have hx_val : (S_u : ZMod p) * (x : ZMod p) = 2 * r1 - r2 := by
        dsimp only [x]
        rw [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul, IsUnit.unit_spec]
      let t : ZMod p := (x : ZMod p) - r1
      have hr2_eq : -(u 2 : ZMod p) * (x : ZMod p) - 2 * t = r2 := by
        dsimp only [t]; rw [hSu] at hx_val; linear_combination -hx_val
      refine ⟨(t, x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩, ?_⟩
      · have hr1_eq : (x : ZMod p) - t = r1 := sub_sub_cancel _ _
        rw [hr1_eq, hr2_eq]
        exact ⟨h1a, h1b, h2a⟩
      · exact Prod.ext (sub_sub_cancel _ _) hr2_eq
  obtain ⟨t_max, -, ht_max⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod p))
    (fun t => (A_of t).card) ⟨0, Finset.mem_univ 0⟩
  refine ⟨A_of t_max, ?_, hsf t_max⟩
  calc L * (p - 1 - 2 * L) = ∑ t : ZMod p, (A_of t).card := havg.symm
    _ ≤ ∑ _t : ZMod p, (A_of t_max).card := Finset.sum_le_sum fun t _ => ht_max t (Finset.mem_univ t)
    _ = p * (A_of t_max).card := by simp [ZMod.card]

private lemma exists_dilate_colouring_of_indep {k p s r : ℕ} (hp : p.Prime)
    (u : Fin k → (ZMod p)ˣ) (A : Finset (ZMod p)ˣ) (hAs : s ≤ A.card)
    (hsf : ∀ x : Fin k → (ZMod p)ˣ, (∀ i, x i ∈ A) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0)
    (hbound : (p - 1 - s) ^ r * (p - 1) < (p - 1) ^ r) :
    ∃ col : (ZMod p)ˣ → Fin r, ∀ x : Fin k → (ZMod p)ˣ,
      (∀ i j, col (x i) = col (x j)) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcardU : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  have hUpos : 0 < p - 1 := by have := hp.two_le; omega
  have hs_le : s ≤ p - 1 := by
    have : A.card ≤ Fintype.card (ZMod p)ˣ := Finset.card_le_univ A
    omega
  -- One greedy step: for any uncovered R ⊆ (ZMod p)ˣ, ∃ m, |(R \ m•A)| * (p-1) ≤ (p-1-s) * |R|
  have hstep : ∀ R : Finset (ZMod p)ˣ, ∃ m : (ZMod p)ˣ,
      (R \ A.image (m * ·)).card * (p - 1) ≤ (p - 1 - s) * R.card := by
    intro R
    -- Sum |(R ∩ m•A)| over m ∈ (ZMod p)ˣ equals R.card * A.card
    have hsum_inter : ∑ m : (ZMod p)ˣ, (R ∩ A.image (m * ·)).card = R.card * A.card := by
      have h1 : ∀ m : (ZMod p)ˣ, (R ∩ A.image (m * ·)).card =
          ∑ x ∈ R, if m⁻¹ * x ∈ A then 1 else 0 := fun m => by
        rw [show R ∩ A.image (m * ·) = R.filter (· ∈ A.image (m * ·)) by
          ext; simp [Finset.mem_inter, Finset.mem_filter], Finset.card_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hiff : x ∈ A.image (m * ·) ↔ m⁻¹ * x ∈ A := by
          constructor
          · intro hx
            obtain ⟨a, ha, hma⟩ := Finset.mem_image.mp hx
            have : m⁻¹ * x = a := by rw [← hma, inv_mul_cancel_left]
            rwa [this]
          · intro hx
            exact Finset.mem_image.mpr ⟨m⁻¹ * x, hx, mul_inv_cancel_left m x⟩
        rw [if_congr hiff rfl rfl]
      rw [Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_comm]
      have h2 : ∀ x ∈ R, (∑ m : (ZMod p)ˣ, if m⁻¹ * x ∈ A then 1 else 0) = A.card := fun x _ => by
        rw [← Finset.card_filter]
        refine Finset.card_bij (fun m _ => m⁻¹ * x) ?_ ?_ ?_
        · intro m hm; exact (Finset.mem_filter.mp hm).2
        · intro m1 _ m2 _ h
          have : m1⁻¹ = m2⁻¹ := mul_right_cancel h
          exact inv_injective this
        · intro a ha
          refine ⟨x * a⁻¹, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · simpa [mul_inv_rev, mul_assoc] using ha
          · simp [mul_inv_rev, mul_assoc]
      rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]
    obtain ⟨m, -, hm⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod p)ˣ)
      (fun m => (R ∩ A.image (m * ·)).card) ⟨1, Finset.mem_univ 1⟩
    have hge : R.card * s ≤ (p - 1) * (R ∩ A.image (m * ·)).card := by
      calc R.card * s ≤ R.card * A.card := Nat.mul_le_mul_left _ hAs
        _ = ∑ m' : (ZMod p)ˣ, (R ∩ A.image (m' * ·)).card := hsum_inter.symm
        _ ≤ ∑ _m' : (ZMod p)ˣ, (R ∩ A.image (m * ·)).card :=
            Finset.sum_le_sum fun m' _ => hm m' (Finset.mem_univ m')
        _ = (p - 1) * (R ∩ A.image (m * ·)).card := by simp [hcardU]
    refine ⟨m, ?_⟩
    have hpart : (R \ A.image (m * ·)).card + (R ∩ A.image (m * ·)).card = R.card :=
      Finset.card_sdiff_add_card_inter R (A.image (m * ·))
    have hsub : (p - 1 - s) * R.card + R.card * s = (p - 1) * R.card := by
      zify [hs_le]; ring
    nlinarith
  -- Induct on r to obtain r multipliers covering all of R whenever (p-1-s)^r * R.card < (p-1)^r
  have hcover : ∀ (t : ℕ) (R : Finset (ZMod p)ˣ),
      (p - 1 - s) ^ t * R.card < (p - 1) ^ t →
      ∃ ms : Fin t → (ZMod p)ˣ, ∀ x ∈ R, ∃ c : Fin t, x ∈ A.image (ms c * ·) := by
    intro t
    induction t with
    | zero =>
      intro R hlt
      simp only [pow_zero, one_mul] at hlt
      have hempty : R = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨Fin.elim0, fun x hx => absurd (hempty ▸ hx) (Finset.notMem_empty x)⟩
    | succ t ih =>
      intro R hlt
      obtain ⟨m0, hm0⟩ := hstep R
      let R' : Finset (ZMod p)ˣ := R \ A.image (m0 * ·)
      have hlt' : (p - 1 - s) ^ t * R'.card < (p - 1) ^ t := by
        have hmul : (p - 1 - s) ^ t * R'.card * (p - 1) < (p - 1) ^ t * (p - 1) := by
          calc (p - 1 - s) ^ t * R'.card * (p - 1)
              = (p - 1 - s) ^ t * (R'.card * (p - 1)) := by ring
            _ ≤ (p - 1 - s) ^ t * ((p - 1 - s) * R.card) := Nat.mul_le_mul_left _ hm0
            _ = (p - 1 - s) ^ (t + 1) * R.card := by rw [pow_succ]; ring
            _ < (p - 1) ^ (t + 1) := hlt
            _ = (p - 1) ^ t * (p - 1) := pow_succ (p - 1) t
        exact Nat.lt_of_mul_lt_mul_right hmul
      obtain ⟨ms', hms'⟩ := ih R' hlt'
      refine ⟨Fin.cons m0 ms', fun x hx => ?_⟩
      by_cases hx0 : x ∈ A.image (m0 * ·)
      · exact ⟨0, by simpa using hx0⟩
      · obtain ⟨c, hc⟩ := hms' x (Finset.mem_sdiff.mpr ⟨hx, hx0⟩)
        exact ⟨c.succ, by simpa using hc⟩
  have hbound_univ : (p - 1 - s) ^ r * (Finset.univ : Finset (ZMod p)ˣ).card < (p - 1) ^ r := by
    simpa [hcardU] using hbound
  obtain ⟨ms, hms⟩ := hcover r Finset.univ hbound_univ
  choose col hcol using fun x : (ZMod p)ˣ => hms x (Finset.mem_univ x)
  refine ⟨col, fun x hmon hsum => ?_⟩
  have hrpos : 0 < r := by
    by_contra hr0
    have hr' : r = 0 := by omega
    subst hr'
    simp at hbound
    omega
  by_cases hk0 : k = 0
  · subst hk0
    have : (∑ i : Fin 0, (u i : ZMod p) * (x i : ZMod p)) = 0 := rfl
    exact hsf Fin.elim0 (fun i => Fin.elim0 i) this
  · let i0 : Fin k := ⟨0, Nat.pos_of_ne_zero hk0⟩
    let c0 : Fin r := col (x i0)
    have hmem_dil : ∀ i : Fin k, x i ∈ A.image (ms c0 * ·) := fun i => by
      have := hcol (x i)
      rwa [hmon i i0] at this
    choose y hy hmy using fun i : Fin k => Finset.mem_image.mp (hmem_dil i)
    apply hsf y hy
    have hfac : (ms c0 : ZMod p) * ∑ i : Fin k, (u i : ZMod p) * (y i : ZMod p) = 0 := by
      rw [Finset.mul_sum]
      convert hsum using 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hmy i, Units.val_mul]; ring
    exact (mul_eq_zero.mp hfac).resolve_left (ms c0).ne_zero

/- ### Module 4: 3-Variable Fourier Bias Certificate on (ZMod p)ˣ -/

private lemma fourier_bias_of_solution_free_k3 {p : ℕ} (hp : p.Prime)
    (u : Fin 3 → (ZMod p)ˣ) (A : Finset (ZMod p)ˣ) (hAne : A.Nonempty)
    (hsf : ∀ x : Fin 3 → (ZMod p)ˣ, (∀ i, x i ∈ A) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0) :
    ∃ r : (ZMod p)ˣ,
      ((A.card : ℝ) ^ 2 / (p : ℝ)) ≤
        ‖∑ x ∈ A, Complex.exp (2 * Real.pi * Complex.I * (((r * x : (ZMod p)ˣ) : ZMod p).val : ℂ) / (p : ℂ))‖ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp_pos_R : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_ne_C : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (p : ℂ))
  let e : ZMod p → ℂ := fun a => Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / (p : ℂ))
  have he_pow : ∀ a : ZMod p, e a = ζ ^ a.val := fun a => by
    dsimp only [e, ζ]
    rw [← Complex.exp_nat_mul]
    congr 1; ring
  have hζp : ζ ^ p = 1 := by
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ hp_ne_C]
    exact Complex.exp_two_pi_mul_I
  have he_add : ∀ a b : ZMod p, e (a + b) = e a * e b := fun a b => by
    rw [he_pow, he_pow, he_pow, ← pow_add, ZMod.val_add]
    have hdiv := (Nat.div_add_mod (a.val + b.val) p).symm
    conv_rhs => rw [hdiv, pow_add, pow_mul, hζp, one_pow, one_mul]
  have he_zero : e 0 = 1 := by simp [e]
  have he_neg : ∀ a : ZMod p, e (-a) = starRingEnd ℂ (e a) := fun a => by
    have h1 : e (-a) * e a = 1 := by rw [← he_add, neg_add_cancel, he_zero]
    have h2 : starRingEnd ℂ (e a) * e a = 1 := by
      dsimp only [e]
      rw [← Complex.exp_conj, ← Complex.exp_add]
      have hconj : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (a.val : ℂ) / (p : ℂ)) =
          -(2 * Real.pi * Complex.I * (a.val : ℂ) / (p : ℂ)) := by
        simp only [map_div₀, map_mul, map_ofNat, map_natCast, Complex.conj_ofReal, Complex.conj_I]
        ring
      rw [hconj, neg_add_cancel, Complex.exp_zero]
    have he_ne : e a ≠ 0 := Complex.exp_ne_zero _
    exact mul_right_cancel₀ he_ne (h1.trans h2.symm)
  have hζ_ne_one : ∀ a : ZMod p, a ≠ 0 → e a ≠ 1 := by
    intro a ha h1
    dsimp only [e] at h1
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
    have hval_eq : (a.val : ℂ) = (n : ℂ) * (p : ℂ) := by
      have hmul : 2 * Real.pi * Complex.I * (a.val : ℂ) = (n : ℂ) * (2 * Real.pi * Complex.I) * (p : ℂ) := by
        have := congrArg (· * (p : ℂ)) hn
        rwa [div_mul_cancel₀ _ hp_ne_C] at this
      have hmul' : (2 * Real.pi * Complex.I) * (a.val : ℂ) = (2 * Real.pi * Complex.I) * ((n : ℂ) * (p : ℂ)) := by
        linear_combination hmul
      exact mul_left_cancel₀ hpi hmul'
    have hval_int : (a.val : ℤ) = n * (p : ℤ) := by exact_mod_cast hval_eq
    have hpdvd : p ∣ a.val := Int.ofNat_dvd.mp ⟨n, by linarith⟩
    have hlt := ZMod.val_lt a
    have hpos : 0 < a.val := Nat.pos_of_ne_zero fun h0 => ha ((ZMod.val_eq_zero a).mp h0)
    have := Nat.le_of_dvd hpos hpdvd
    omega
  have horth : ∀ a : ZMod p, ∑ r : ZMod p, e (r * a) = if a = 0 then (p : ℂ) else 0 := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp [he_zero, ZMod.card]
    · rw [if_neg ha]
      have hsum_range : ∑ r : ZMod p, e (r * a) = ∑ n ∈ Finset.range p, (e a) ^ n := by
        refine Finset.sum_bij (fun r _ => r.val) (fun r _ => Finset.mem_range.mpr (ZMod.val_lt r))
          (fun r1 _ r2 _ h => ZMod.val_injective p h)
          (fun n hn => ⟨(n : ZMod p), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)⟩)
          fun r _ => ?_
        rw [he_pow, he_pow, ← pow_mul, ZMod.val_mul]
        have hdiv := (Nat.div_add_mod (r.val * a.val) p).symm
        conv_rhs => rw [mul_comm, hdiv, pow_add, pow_mul, hζp, one_pow, one_mul]
      rw [hsum_range, geom_sum_eq (hζ_ne_one a ha), he_pow, ← pow_mul, mul_comm, pow_mul, hζp,
        one_pow, sub_self, zero_div]
  let fhat : ZMod p → ℂ := fun r => ∑ x ∈ A, e (r * (x : ZMod p))
  have hfhat0 : fhat 0 = (A.card : ℂ) := by simp [fhat, he_zero]
  -- Parseval: ∑ r : ZMod p, ‖fhat r‖ ^ 2 = p * A.card
  have hparseval : ∑ r : ZMod p, ‖fhat r‖ ^ 2 = (p : ℝ) * (A.card : ℝ) := by
    have hC : (∑ r : ZMod p, (‖fhat r‖ ^ 2 : ℂ)) = (p : ℂ) * (A.card : ℂ) := by
      have hterm : ∀ r : ZMod p, (‖fhat r‖ ^ 2 : ℂ) = fhat r * starRingEnd ℂ (fhat r) := fun r => by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast
      rw [Finset.sum_congr rfl fun r _ => hterm r]
      have hexp : ∀ r : ZMod p, fhat r * starRingEnd ℂ (fhat r) =
          ∑ x ∈ A, ∑ y ∈ A, e (r * ((x : ZMod p) - (y : ZMod p))) := fun r => by
        dsimp only [fhat]
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← he_neg, ← he_add]
        congr 1; ring
      rw [Finset.sum_congr rfl fun r _ => hexp r, Finset.sum_comm]
      trans ∑ x ∈ A, ∑ y ∈ A, ∑ r : ZMod p, e (r * ((x : ZMod p) - (y : ZMod p)))
      · exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
      · simp_rw [horth]
        have hinner : ∀ x ∈ A, (∑ y ∈ A, if (x : ZMod p) - (y : ZMod p) = 0 then (p : ℂ) else 0) = (p : ℂ) := by
          intro x hx
          have hiff : ∀ y ∈ A, ((x : ZMod p) - (y : ZMod p) = 0 ↔ x = y) := fun y _ => by
            rw [sub_eq_zero, Units.ext_iff]
          have hsum_eq : (∑ y ∈ A, if (x : ZMod p) - (y : ZMod p) = 0 then (p : ℂ) else 0) =
              ∑ y ∈ A, if x = y then (p : ℂ) else 0 :=
            Finset.sum_congr rfl fun y hy => by rw [if_congr (hiff y hy) rfl rfl]
          rw [hsum_eq, Finset.sum_ite_eq A x, if_pos hx]
        rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, mul_comm]
    exact_mod_cast hC
  -- Solution count identity: ∑ r : ZMod p, fhat (u 0 * r) * fhat (u 1 * r) * fhat (u 2 * r) = 0
  have hcount : ∑ r : ZMod p, fhat ((u 0 : ZMod p) * r) *
      fhat ((u 1 : ZMod p) * r) * fhat ((u 2 : ZMod p) * r) = 0 := by
    have hexp : ∀ r : ZMod p, fhat ((u 0 : ZMod p) * r) *
        fhat ((u 1 : ZMod p) * r) * fhat ((u 2 : ZMod p) * r) =
        ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A,
          e (r * ((u 0 : ZMod p) * (x : ZMod p) + (u 1 : ZMod p) * (y : ZMod p) + (u 2 : ZMod p) * (z : ZMod p))) := by
      intro r
      dsimp only [fhat]
      rw [mul_assoc, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← he_add, ← he_add]
      congr 1; ring
    rw [Finset.sum_congr rfl fun r _ => hexp r]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun y hy => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun z hz => ?_
    rw [horth]
    have hne : (u 0 : ZMod p) * (x : ZMod p) + (u 1 : ZMod p) * (y : ZMod p) +
        (u 2 : ZMod p) * (z : ZMod p) ≠ 0 := by
      have h := hsf ![x, y, z] (fun i => by fin_cases i <;> assumption)
      simpa [Fin.sum_univ_three] using h
    rw [if_neg hne]
  -- Isolate r = 0 and bound nonzero sum by max_{r ≠ 0} ‖fhat r‖ * (p * A.card)
  have hsplit : (A.card : ℂ) ^ 3 = -(∑ r : (ZMod p)ˣ,
      fhat ((u 0 : ZMod p) * (r : ZMod p)) * fhat ((u 1 : ZMod p) * (r : ZMod p)) *
      fhat ((u 2 : ZMod p) * (r : ZMod p))) := by
    have h0 : (Finset.univ : Finset (ZMod p)) = insert 0 (Finset.univ.erase 0) :=
      (Finset.insert_erase (Finset.mem_univ 0)).symm
    rw [h0, Finset.sum_insert (Finset.notMem_erase _ _)] at hcount
    simp only [mul_zero, hfhat0] at hcount
    have hbij : ∑ r ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        fhat ((u 0 : ZMod p) * r) * fhat ((u 1 : ZMod p) * r) * fhat ((u 2 : ZMod p) * r) =
        ∑ r : (ZMod p)ˣ, fhat ((u 0 : ZMod p) * (r : ZMod p)) *
          fhat ((u 1 : ZMod p) * (r : ZMod p)) * fhat ((u 2 : ZMod p) * (r : ZMod p)) := by
      refine Finset.sum_bij (fun r hr => (isUnit_iff_ne_zero.mpr (Finset.mem_erase.mp hr).1).unit)
        (fun _ _ => Finset.mem_univ _)
        (fun r1 hr1 r2 hr2 h => by
          have := congrArg Units.val h; simpa only [IsUnit.unit_spec] using this)
        (fun u' _ => ⟨(u' : ZMod p), Finset.mem_erase.mpr ⟨u'.ne_zero, Finset.mem_univ _⟩,
          Units.ext (by simp)⟩)
        (fun r hr => by simp)
    rw [hbij] at hcount
    linear_combination hcount
  obtain ⟨r_max, -, hr_max⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod p)ˣ)
    (fun r => ‖fhat (r : ZMod p)‖) ⟨1, Finset.mem_univ 1⟩
  refine ⟨r_max, ?_⟩
  have hM_bound : ∀ r : (ZMod p)ˣ, ‖fhat ((u 0 : ZMod p) * (r : ZMod p))‖ ≤ ‖fhat (r_max : ZMod p)‖ := by
    intro r
    have h := hr_max (u 0 * r) (Finset.mem_univ _)
    simpa [Units.val_mul] using h
  have hnorm_le : (A.card : ℝ) ^ 3 ≤
      ‖fhat (r_max : ZMod p)‖ * ∑ r : (ZMod p)ˣ,
        ‖fhat ((u 1 : ZMod p) * (r : ZMod p))‖ * ‖fhat ((u 2 : ZMod p) * (r : ZMod p))‖ := by
    have h1 : (A.card : ℝ) ^ 3 = ‖(A.card : ℂ) ^ 3‖ := by simp
    rw [h1, hsplit, norm_neg]
    calc ‖∑ r : (ZMod p)ˣ, fhat ((u 0 : ZMod p) * (r : ZMod p)) *
            fhat ((u 1 : ZMod p) * (r : ZMod p)) * fhat ((u 2 : ZMod p) * (r : ZMod p))‖
        ≤ ∑ r : (ZMod p)ˣ, ‖fhat ((u 0 : ZMod p) * (r : ZMod p)) *
            fhat ((u 1 : ZMod p) * (r : ZMod p)) * fhat ((u 2 : ZMod p) * (r : ZMod p))‖ :=
          norm_sum_le _ _
      _ = ∑ r : (ZMod p)ˣ, ‖fhat ((u 0 : ZMod p) * (r : ZMod p))‖ *
            (‖fhat ((u 1 : ZMod p) * (r : ZMod p))‖ * ‖fhat ((u 2 : ZMod p) * (r : ZMod p))‖) := by
          refine Finset.sum_congr rfl fun r _ => by rw [norm_mul, norm_mul, mul_assoc]
      _ ≤ ∑ r : (ZMod p)ˣ, ‖fhat (r_max : ZMod p)‖ *
            (‖fhat ((u 1 : ZMod p) * (r : ZMod p))‖ * ‖fhat ((u 2 : ZMod p) * (r : ZMod p))‖) :=
          Finset.sum_le_sum fun r _ =>
            mul_le_mul_of_nonneg_right (hM_bound r) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hcs : ∑ r : (ZMod p)ˣ,
      ‖fhat ((u 1 : ZMod p) * (r : ZMod p))‖ * ‖fhat ((u 2 : ZMod p) * (r : ZMod p))‖ ≤
      (p : ℝ) * (A.card : ℝ) := by
    have hsq_le : ∀ w : (ZMod p)ˣ,
        ∑ r : (ZMod p)ˣ, ‖fhat ((w : ZMod p) * (r : ZMod p))‖ ^ 2 ≤ (p : ℝ) * (A.card : ℝ) := fun w => by
      have hreidx : ∑ r : (ZMod p)ˣ, ‖fhat ((w : ZMod p) * (r : ZMod p))‖ ^ 2 =
          ∑ r : (ZMod p)ˣ, ‖fhat (r : ZMod p)‖ ^ 2 := by
        refine Finset.sum_bij (fun r _ => w * r) (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => mul_left_cancel h) (fun r _ => ⟨w⁻¹ * r, Finset.mem_univ _, by simp⟩)
          (fun r _ => by simp [Units.val_mul])
      rw [hreidx, ← hparseval]
      have hsub : ∑ r : (ZMod p)ˣ, ‖fhat (r : ZMod p)‖ ^ 2 =
          ∑ r ∈ (Finset.univ : Finset (ZMod p)).erase 0, ‖fhat r‖ ^ 2 := by
        refine Finset.sum_bij (fun r _ => (r : ZMod p))
          (fun r _ => Finset.mem_erase.mpr ⟨r.ne_zero, Finset.mem_univ _⟩)
          (fun _ _ _ _ h => Units.ext h)
          (fun r hr => ⟨(isUnit_iff_ne_zero.mpr (Finset.mem_erase.mp hr).1).unit, Finset.mem_univ _, by simp⟩)
          (fun _ _ => rfl)
      rw [hsub]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => sq_nonneg _)
    have h2ab : ∑ r : (ZMod p)ˣ,
        (2 * (‖fhat ((u 1 : ZMod p) * (r : ZMod p))‖ * ‖fhat ((u 2 : ZMod p) * (r : ZMod p))‖)) ≤
        ∑ r : (ZMod p)ˣ, (‖fhat ((u 1 : ZMod p) * (r : ZMod p))‖ ^ 2 +
          ‖fhat ((u 2 : ZMod p) * (r : ZMod p))‖ ^ 2) :=
      Finset.sum_le_sum fun r _ => by nlinarith [sq_nonneg (‖fhat ((u 1 : ZMod p) * (r : ZMod p))‖ -
        ‖fhat ((u 2 : ZMod p) * (r : ZMod p))‖)]
    rw [← Finset.mul_sum, Finset.sum_add_distrib] at h2ab
    linarith [hsq_le (u 1), hsq_le (u 2)]
  have hApos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hAne.card_pos
  have hfinal : (A.card : ℝ) ^ 3 ≤ ‖fhat (r_max : ZMod p)‖ * ((p : ℝ) * (A.card : ℝ)) :=
    le_trans hnorm_le (mul_le_mul_of_nonneg_left hcs (norm_nonneg _))
  have hdiv : (A.card : ℝ) ^ 2 / (p : ℝ) ≤ ‖fhat (r_max : ZMod p)‖ := by
    rw [div_le_iff₀ hp_pos_R]
    nlinarith
  simpa only [fhat, e, Units.val_mul] using hdiv

end ReductionProofs

theorem main : H1 → H2 → H3 → type_of% @Green21.green_21.variants.fox_kleitman_modular := by
  rintro ⟨C1, hH1⟩ ⟨C2, hH2⟩ ⟨f3, hH3⟩
  let B3 : ℕ := 27
  let M3 : ℕ := max (max 54 (4 * B3 ^ 2 + 4 * B3)) (max C1 C2)
  refine ⟨fun k => if k = 1 then 1 else if k = 2 then 3 else if k = 3 then M3
    else max (max (2 * k ^ 2) (4 * (k ^ 2) ^ 2 + 4 * k ^ 2)) (f3 k), ?_⟩
  intro k p hk hp a ha
  rcases eq_or_ne k 1 with rfl | hk1
  · simpa using solve_k_one hp a ha
  rcases eq_or_ne k 2 with rfl | hk2
  · simpa using solve_k_two hp a ha
  obtain ⟨c, u, hu0, hcu, hu_ne⟩ := normalize_units hk hp a ha
  have hcol_cast : ∀ {n m : ℕ} (hnm : n ≤ m),
      (∃ col : (ZMod p)ˣ → Fin n, ∀ x : Fin k → (ZMod p)ˣ,
        (∀ i j, col (x i) = col (x j)) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0) →
      ∃ col : (ZMod p)ˣ → Fin m, ∀ x : Fin k → (ZMod p)ˣ,
        (∀ i j, col (x i) = col (x j)) → ∑ i, (a i : ZMod p) * (x i : ZMod p) ≠ 0 := by
    intro n m hnm ⟨col, hcol⟩
    refine ⟨fun x => Fin.castLE hnm (col x), fun x hmon hsum => ?_⟩
    apply hcol x (fun i j => Fin.castLE_injective hnm (hmon i j))
    have hsum' : (c : ZMod p) * ∑ i, (u i : ZMod p) * (x i : ZMod p) = 0 := by
      rw [Finset.mul_sum]
      convert hsum using 1
      refine Finset.sum_congr rfl fun i _ => by rw [hcu i, mul_assoc]
    exact (c.isUnit.mul_right_eq_zero).mp hsum'
  rcases eq_or_ne k 3 with rfl | hk3
  · -- Arity k = 3
    have : Fact p.Prime := ⟨hp⟩
    by_cases hp54 : p ≤ 54
    · exact hcol_cast (show 54 ≤ _ from by simp [M3]) (solve_small_prime (by norm_num) hp hp54 u hu_ne)
    · have hp_gt : 54 < p := Nat.lt_of_not_le hp54
      by_cases hm : ∃ m : (ZMod p)ˣ,
          ∑ i : Fin 3, min (((m * u i : (ZMod p)ˣ) : ZMod p).val)
            (p - ((m * u i : (ZMod p)ˣ) : ZMod p).val) ≤ 27
      · obtain ⟨m, hm⟩ := hm
        exact hcol_cast (show 4 * B3 ^ 2 + 4 * B3 ≤ _ from by simp [M3, B3])
          (solve_signed_L1 (by norm_num) (by norm_num) hp (by omega) u hu_ne m hm)
      · push Not at hm
        -- Helper: permute & rescale u into v so that any equal pair lands at (0, 1) with v 0 = v 1 = 1
        have hperm_eq : ∀ (σ : Equiv.Perm (Fin 3)) (w : (ZMod p)ˣ),
            (∃ col : (ZMod p)ˣ → Fin C1, ∀ x : Fin 3 → (ZMod p)ˣ,
              (∀ i j, col (x i) = col (x j)) →
              ∑ i, ((w * u (σ i) : (ZMod p)ˣ) : ZMod p) * (x i : ZMod p) ≠ 0) →
            ∃ col : (ZMod p)ˣ → Fin C1, ∀ x : Fin 3 → (ZMod p)ˣ,
              (∀ i j, col (x i) = col (x j)) → ∑ i, (u i : ZMod p) * (x i : ZMod p) ≠ 0 := by
          intro σ w ⟨col, hcol⟩
          refine ⟨col, fun x hmon hsum => ?_⟩
          apply hcol (fun i => x (σ i)) (fun i j => hmon (σ i) (σ j))
          have h1 : (∑ i : Fin 3, ((w * u (σ i) : (ZMod p)ˣ) : ZMod p) * (x (σ i) : ZMod p)) =
              (w : ZMod p) * ∑ i : Fin 3, (u (σ i) : ZMod p) * (x (σ i) : ZMod p) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [Units.val_mul, mul_assoc]
          rw [h1, Equiv.sum_comp σ (fun i => (u i : ZMod p) * (x i : ZMod p)), hsum, mul_zero]
        -- Helper: transfer non-zero subset sums & signed L^1 > 27 under permutation + scaling
        have hperm_conds : ∀ (σ : Equiv.Perm (Fin 3)) (w : (ZMod p)ˣ),
            (∀ I : Finset (Fin 3), I.Nonempty → ∑ i ∈ I, ((w * u (σ i) : (ZMod p)ˣ) : ZMod p) ≠ 0) ∧
            (∀ m : (ZMod p)ˣ, 27 < ∑ i : Fin 3,
              min (((m * (w * u (σ i)) : (ZMod p)ˣ) : ZMod p).val)
                (p - ((m * (w * u (σ i)) : (ZMod p)ˣ) : ZMod p).val)) := by
          intro σ w
          refine ⟨fun I hIne hzero => ?_, fun m => ?_⟩
          · have h1 : (w : ZMod p) * ∑ i ∈ I, (u (σ i) : ZMod p) = 0 := by
              rw [Finset.mul_sum]
              simpa only [Units.val_mul] using hzero
            have h2 : ∑ i ∈ I.map σ.toEmbedding, (u i : ZMod p) = 0 := by
              rw [Finset.sum_map]
              exact (mul_eq_zero.mp h1).resolve_left w.ne_zero
            exact hu_ne (I.map σ.toEmbedding) (Finset.Nonempty.map hIne) h2
          · have hreidx : (∑ i : Fin 3, min (((m * (w * u (σ i)) : (ZMod p)ˣ) : ZMod p).val)
                (p - ((m * (w * u (σ i)) : (ZMod p)ˣ) : ZMod p).val)) =
                ∑ i : Fin 3, min ((((m * w) * u i : (ZMod p)ˣ) : ZMod p).val)
                  (p - (((m * w) * u i : (ZMod p)ˣ) : ZMod p).val) := by
              simp_rw [← mul_assoc]
              exact Equiv.sum_comp σ (fun i => min ((((m * w) * u i : (ZMod p)ˣ) : ZMod p).val)
                (p - (((m * w) * u i : (ZMod p)ˣ) : ZMod p).val))
            rw [hreidx]
            exact hm (m * w)
        have hu0' : u 0 = 1 := hu0
        -- All three equal is impossible because signed L^1 of (1,1,1) is 3 ≤ 27
        have hnot_all_eq : ¬ (u 0 = u 1 ∧ u 1 = u 2) := by
          rintro ⟨h01, h12⟩
          have h1 : ∑ i : Fin 3, min (((1 * u i : (ZMod p)ˣ) : ZMod p).val)
              (p - ((1 * u i : (ZMod p)ˣ) : ZMod p).val) = 3 := by
            have : Fact p.Prime := ⟨hp⟩
            rw [Fin.sum_univ_three, ← h12, ← h01, hu0']
            simp only [mul_one, Units.val_one, ZMod.val_one]
            omega
          have := hm 1
          omega
        by_cases h01 : u 0 = u 1
        · have h2ne : u 2 ≠ 1 := fun h => hnot_all_eq ⟨h01, by rw [← h01, hu0', h]⟩
          have hsol := hH1 p hp hp_gt u hu0' (h01.symm.trans hu0') h2ne hu_ne hm
          exact hcol_cast (show C1 ≤ _ from by simp [M3]) hsol
        · by_cases h02 : u 0 = u 2
          · let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
            obtain ⟨hsub, hL1⟩ := hperm_conds σ 1
            have hv0 : (1 : (ZMod p)ˣ) * u (σ 0) = 1 := by
              change (1 : (ZMod p)ˣ) * u 0 = 1; rw [one_mul, hu0']
            have hv1 : (1 : (ZMod p)ˣ) * u (σ 1) = 1 := by
              change (1 : (ZMod p)ˣ) * u 2 = 1; rw [one_mul, ← h02, hu0']
            have hv2 : (1 : (ZMod p)ˣ) * u (σ 2) ≠ 1 := by
              change (1 : (ZMod p)ˣ) * u 1 ≠ 1; rw [one_mul, ← hu0']; exact Ne.symm h01
            have hsol := hperm_eq σ 1 (hH1 p hp hp_gt _ hv0 hv1 hv2 hsub hL1)
            exact hcol_cast (show C1 ≤ _ from by simp [M3]) hsol
          · by_cases h12 : u 1 = u 2
            · let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
              let w : (ZMod p)ˣ := (u 1)⁻¹
              obtain ⟨hsub, hL1⟩ := hperm_conds σ w
              have hv0 : w * u (σ 0) = 1 := by
                change (u 1)⁻¹ * u 2 = 1; rw [← h12, inv_mul_cancel]
              have hv1 : w * u (σ 1) = 1 := by
                change (u 1)⁻¹ * u 1 = 1; exact inv_mul_cancel _
              have hv2 : w * u (σ 2) ≠ 1 := by
                change (u 1)⁻¹ * u 0 ≠ 1
                intro h
                have : u 0 = u 1 := by
                  have := congrArg (u 1 * ·) h
                  simpa [mul_inv_cancel_left] using this
                exact h01 this
              have hsol := hperm_eq σ w (hH1 p hp hp_gt _ hv0 hv1 hv2 hsub hL1)
              exact hcol_cast (show C1 ≤ _ from by simp [M3]) hsol
            · have hsol := hH2 p hp hp_gt u hu0' h01 h02 h12 hu_ne hm
              exact hcol_cast (show C2 ≤ _ from by simp [M3]) hsol
  · -- Arity k ≥ 4
    have hk4 : 4 ≤ k := by omega
    have hbranch : (if k = 1 then 1 else if k = 2 then 3 else if k = 3 then M3
        else max (max (2 * k ^ 2) (4 * (k ^ 2) ^ 2 + 4 * k ^ 2)) (f3 k)) =
        max (max (2 * k ^ 2) (4 * (k ^ 2) ^ 2 + 4 * k ^ 2)) (f3 k) := by
      rw [if_neg hk1, if_neg hk2, if_neg hk3]
    by_cases hp_le : p ≤ 2 * k ^ 2
    · exact hcol_cast (by dsimp only; rw [hbranch]; exact le_trans (le_max_left _ _) (le_max_left _ _))
        (solve_small_prime hk hp hp_le u hu_ne)
    · have hp_gt : 2 * k ^ 2 < p := Nat.lt_of_not_le hp_le
      by_cases hm : ∃ m : (ZMod p)ˣ,
          ∑ i : Fin k, min (((m * u i : (ZMod p)ˣ) : ZMod p).val)
            (p - ((m * u i : (ZMod p)ˣ) : ZMod p).val) ≤ k ^ 2
      · obtain ⟨m, hm⟩ := hm
        have hB1 : 1 ≤ k ^ 2 := by nlinarith
        exact hcol_cast (by dsimp only; rw [hbranch]; exact le_trans (le_max_right _ _) (le_max_left _ _))
          (solve_signed_L1 hk hB1 hp hp_gt u hu_ne m hm)
      · push Not at hm
        exact hcol_cast (by dsimp only; rw [hbranch]; exact le_max_right _ _)
          (hH3 k p hk4 hp hp_gt u hu0 hu_ne hm)

end OMA.R_Green21_green_21_variants_fox_kleitman_modular_R2
