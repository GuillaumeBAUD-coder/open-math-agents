import FormalConjectures.ErdosProblems.«1204»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
The finite Selberg sieve inequality and a lower bound for its denominator
give Elliott's asymptotic lower bound for admissible tuples.
-/

open Erdos1204 Filter Asymptotics
open scoped Classical BigOperators

namespace OMA.R_Erdos1204_erdos_1204_variants_A_lower_R1

/-- The finite upper-bound sieve with cutoff z, applied to admissible residues. -/
def H1 : Prop :=
  ∀ (S : Finset ℕ) (N z : ℕ), IsAdmissible S → S ⊆ Finset.range N → 1 ≤ z →
    (S.card : ℝ) ≤
      (N : ℝ) / (∑ d ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / d.totient) + (z : ℝ)^2

/-- The Selberg denominator dominates a harmonic sum through z. -/
def H2 : Prop :=
  ∀ z : ℕ, 1 ≤ z →
    Real.log ((z : ℝ) + 1) ≤
      ∑ d ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / d.totient

lemma admissible_large_primes {S : Finset ℕ} {k : ℕ} (hc : S.card = k)
    (hS : ∀ q ∈ S, k < q ∧ q.Prime) : IsAdmissible S := by
  intro p hp
  by_cases hpk : p ≤ k
  · refine ⟨0, fun q hq h0 => ?_⟩
    have hpq : p ∣ q := (ZMod.natCast_eq_zero_iff q p).mp h0
    have heq : p = q := (Nat.dvd_prime_two_le (hS q hq).2 hp.two_le).mp hpq
    have hnq := (hS q hq).1
    omega
  · let : NeZero p := ⟨hp.ne_zero⟩
    let T : Finset (ZMod p) := S.image Nat.cast
    have ht : T.card ≤ S.card := Finset.card_image_le
    have hu : T.card < (Finset.univ : Finset (ZMod p)).card := by
      rw [Finset.card_univ, ZMod.card]
      omega
    obtain ⟨r, _, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hu
    exact ⟨r, fun q hq heq => hr (Finset.mem_image.mpr ⟨q, hq, heq⟩)⟩

lemma minimum_attained (k : ℕ) :
    ∃ S : Finset ℕ, S.card = k ∧ IsAdmissible S ∧ S ⊆ Finset.range (A k + 1) := by
  let p : ℕ → ℕ := fun j => Nat.nth Nat.Prime (k + 1 + j)
  let e : ℕ ↪ ℕ := ⟨p, fun i j h =>
    Nat.add_left_cancel ((Nat.nth_injective Nat.infinite_setOfPred_prime) h)⟩
  let S := (Finset.range k).map e
  have hc : S.card = k := by simp [S]
  have hprime : ∀ q ∈ S, k < q ∧ q.Prime := by
    intro q hq
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hq
    change k < p j ∧ (p j).Prime
    have h : k + 1 + j ≤ p j :=
      Nat.le_nth fun hfin => (Nat.infinite_setOfPred_prime.not_finite hfin).elim
    exact ⟨by omega,
      Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _⟩
  have hex : {m : ℕ | ∃ T : Finset ℕ, T.card = k ∧ IsAdmissible T ∧
      ∀ a ∈ T, a ≤ m}.Nonempty :=
    ⟨S.sup id, S, hc, admissible_large_primes hc hprime, fun a ha => Finset.le_sup (f := id) ha⟩
  obtain ⟨T, hT, hadm, hmax⟩ := Nat.sInf_mem hex
  exact ⟨T, hT, hadm, fun a ha => Finset.mem_range.mpr (Nat.lt_succ_of_le (hmax a ha))⟩

theorem main : H1 → H2 → type_of% @Erdos1204.erdos_1204.variants.A_lower := by
  intro sieve denom ε hε
  by_cases hc : 0 < 1/2 - ε
  swap
  · exact Eventually.of_forall fun k =>
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hc) (Nat.cast_nonneg _))
        (Real.log_natCast_nonneg k)).trans (Nat.cast_nonneg _)
  let c : ℝ := 1/2 - ε
  let β : ℝ := 1/2 - ε/2
  have hcβ : c < β := by dsimp [c, β]; linarith
  have hβ : 0 < β := hc.trans hcβ
  have hδ : 0 < 1 - 2*β := by dsimp [β]; linarith
  let η : ℝ := (1/c - 1/β)/2
  have hη : 0 < η := by
    have h := one_div_lt_one_div_of_lt hc hcβ
    dsimp [η]
    linarith
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (isLittleO_iff.mp (isLittleO_log_rpow_atTop hδ) hη)
  obtain ⟨K, hK⟩ := exists_nat_gt (max 2 (max T (1/(c*η))))
  filter_upwards [eventually_ge_atTop K] with k hk
  let N := A k + 1
  let X : ℝ := N
  obtain ⟨S, hcard, hadm, hsub⟩ := minimum_attained k
  have hkN : k ≤ N := by
    rw [← hcard]
    simpa using Finset.card_le_card hsub
  have hkX : (k : ℝ) ≤ X := Nat.cast_le.mpr hkN
  have hKX : (K : ℝ) ≤ X := (Nat.cast_le.mpr hk).trans hkX
  have h2k : (2 : ℝ) < k := ((le_max_left _ _).trans_lt hK).trans_le (Nat.cast_le.mpr hk)
  have h2X : 2 < X := h2k.trans_le hkX
  have hXp : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  let z := ⌊X ^ β⌋₊
  have hX1 : 1 ≤ X := by linarith
  have hz : 1 ≤ z := Nat.le_floor (by simpa using Real.one_le_rpow hX1 hβ.le)
  have hzupper : (z : ℝ) ≤ X ^ β := Nat.floor_le (Real.rpow_nonneg hXp.le _)
  have hzlower : X ^ β < (z : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdenom := denom z hz
  have hdenom' : β * Real.log X ≤
      ∑ d ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / d.totient := by
    rw [← Real.log_rpow hXp]
    exact (Real.log_le_log (Real.rpow_pos_of_pos hXp _) hzlower.le).trans hdenom
  have hB := sieve S N z hadm hsub hz
  rw [hcard] at hB
  have hzsq : (z : ℝ)^2 ≤ X ^ (2*β) := by
    calc
      (z : ℝ)^2 ≤ (X ^ β)^2 := by gcongr
      _ = X ^ (2*β) := by
        rw [mul_comm 2 β]
        exact (Real.rpow_mul_natCast hXp.le β 2).symm
  have hbound : (k : ℝ) ≤ X / (β * Real.log X) + X ^ (2*β) :=
    hB.trans (add_le_add (div_le_div_of_nonneg_left hXp.le (mul_pos hβ hlogX) hdenom') hzsq)
  have hXT : T ≤ X := ((le_max_left _ _).trans ((le_max_right _ _).trans hK.le)).trans hKX
  have herror := hT X hXT
  rw [Real.norm_of_nonneg hlogX.le, Real.norm_of_nonneg (Real.rpow_nonneg hXp.le _)] at herror
  have herr : X ^ (2*β) * Real.log X ≤ η * X := by
    calc
      X ^ (2*β) * Real.log X ≤ X ^ (2*β) * (η * X ^ (1-2*β)) :=
        mul_le_mul_of_nonneg_left herror (Real.rpow_nonneg hXp.le _)
      _ = η * X := by
        rw [mul_left_comm, ← Real.rpow_add hXp, show 2*β+(1-2*β) = 1 by ring, Real.rpow_one]
  have hlogk := Real.log_le_log (by linarith : 0 < (k : ℝ)) hkX
  have hklog : (k : ℝ) * Real.log k ≤ X / β + η * X := by
    calc
      (k : ℝ) * Real.log k ≤ (k : ℝ) * Real.log X :=
        mul_le_mul_of_nonneg_left hlogk (Nat.cast_nonneg _)
      _ ≤ (X / (β * Real.log X) + X ^ (2*β)) * Real.log X :=
        mul_le_mul_of_nonneg_right hbound hlogX.le
      _ = X / β + X ^ (2*β) * Real.log X := by
        rw [add_mul]
        congr 1
        field_simp
      _ ≤ _ := add_le_add_right herr _
  have hcoef : c * (1/β + η) = 1 - c*η := by
    have hηeq : 2 * η = 1 / c - 1 / β := by dsimp [η]; ring
    have hm : c * (2 * η) = c * (1 / c - 1 / β) := congrArg (fun t => c * t) hηeq
    have hcc : c * (1 / c) = 1 := by rw [← div_eq_mul_one_div, div_self hc.ne']
    rw [mul_sub, hcc] at hm
    rw [mul_add]
    linarith only [hm]
  have hKeta : 1/(c*η) ≤ X :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans hK.le)).trans hKX
  have hret : 1 ≤ c*η*X := by
    have h := (div_le_iff₀ (mul_pos hc hη)).mp hKeta
    simpa only [mul_comm X] using h
  have hXeq : X = (A k : ℝ) + 1 := by simp [X, N]
  change c * (k : ℝ) * Real.log k ≤ _
  calc
    c * (k : ℝ) * Real.log k ≤ c * (X/β + η*X) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hklog hc.le
    _ = (1-c*η)*X := by rw [← hcoef]; ring
    _ ≤ (A k : ℝ) := by rw [sub_mul]; linarith

end OMA.R_Erdos1204_erdos_1204_variants_A_lower_R1
