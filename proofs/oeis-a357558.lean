import OMAStatements.S_oeis_a357558

-- Credit: @RiverMint78

/-!
The factor p - 1 follows from the elementary weighted binomial identity.
In the remaining congruence, divide the squared binomial by p^2 first.
Then a first-order expansion modulo p^2 reduces the sum to harmonic
sums, which vanish to the required orders by reflection and the
inverse-square sum in the prime field.
-/

namespace A357558Proof
open OMA.S_oeis_a357558
open scoped BigOperators

private abbrev R (p : ℕ) := ZMod (p ^ 2)

private def invAt (p i : ℕ) : R p := ((i + 1 : ℕ) : R p)⁻¹

private def harmonic (p n : ℕ) : R p :=
  ∑ i ∈ Finset.range n, invAt p i

private def squareSum (p n : ℕ) : R p :=
  ∑ i ∈ Finset.range n, invAt p i ^ 2

private theorem small_coprime (p i : ℕ) [Fact p.Prime] (h₁ : 0 < i) (h₂ : i < p) :
    i.Coprime p :=
  ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt h₁ h₂)).symm

private theorem small_isUnit (p i : ℕ) [Fact p.Prime] (h₁ : 0 < i) (h₂ : i < p) :
    IsUnit (i : R p) :=
  (ZMod.isUnit_iff_coprime i (p ^ 2)).mpr ((small_coprime p i h₁ h₂).pow_right 2)

private theorem small_inverse (p i : ℕ) [Fact p.Prime] (h₁ : 0 < i) (h₂ : i < p) :
    ((i : R p)⁻¹) * (i : R p) = 1 :=
  ZMod.inv_mul_of_unit _ (small_isUnit p i h₁ h₂)

private theorem p_square (p : ℕ) : (p : R p) ^ 2 = 0 := by
  rw [← Nat.cast_pow]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr dvd_rfl

private def reduce (p : ℕ) : R p →+* ZMod p :=
  ZMod.castHom (show p ∣ p ^ 2 by exact dvd_pow_self _ (by decide)) _

private theorem reduced_inverse (p i : ℕ) [Fact p.Prime] (h₁ : 0 < i) (h₂ : i < p) :
    reduce p ((i : R p)⁻¹) = ((i : ZMod p)⁻¹) := by
  have hi : (i : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt h₁ h₂
  have hm : reduce p ((i : R p)⁻¹) * (i : ZMod p) = 1 := by
    rw [← map_natCast (reduce p) i, ← map_mul, small_inverse p i h₁ h₂, map_one]
  calc
    reduce p ((i : R p)⁻¹) =
        (reduce p ((i : R p)⁻¹) * (i : ZMod p)) * ((i : ZMod p)⁻¹) := by
      rw [mul_assoc, mul_inv_cancel₀ hi, mul_one]
    _ = (i : ZMod p)⁻¹ := by simp [hm]

private theorem reduced_zero_mul (p : ℕ) [Fact p.Prime] (z : R p)
    (hz : reduce p z = 0) : (p : R p) * z = 0 := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hv : (z.val : ZMod p) = 0 := by
    rw [← map_natCast (reduce p), ZMod.natCast_zmod_val, hz]
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hv
  rw [← ZMod.natCast_zmod_val z, hq, Nat.cast_mul, ← mul_assoc, ← pow_two, p_square, zero_mul]

private theorem finEquiv_value (p : ℕ) [NeZero p] (i : Fin p) :
    ZMod.finEquiv p i = (i.val : ZMod p) := by
  cases p with
  | zero => exact i.elim0
  | succ p =>
      exact (ZMod.natCast_zmod_val (ZMod.finEquiv (p + 1) i)).symm

private theorem field_squares (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (∑ i ∈ Finset.range (p - 1), (((i + 1 : ℕ) : ZMod p)⁻¹) ^ 2) = 0 := by
  let f (i : ℕ) : ZMod p := ((i : ZMod p)⁻¹) ^ 2
  have hf : (∑ i : ZMod p, i ^ 2) = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 (by rw [ZMod.card]; omega)
  have hsum : (∑ i ∈ Finset.range p, f i) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    calc
      (∑ i : Fin p, f i.val) = ∑ i : ZMod p, i⁻¹ ^ 2 := by
        apply Fintype.sum_equiv (ZMod.finEquiv p).toEquiv
        intro i
        change f i.val = (ZMod.finEquiv p i)⁻¹ ^ 2
        rw [finEquiv_value]
      _ = ∑ i : ZMod p, i ^ 2 := by
        exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun _ => rfl)
      _ = 0 := hf
  calc
    (∑ i ∈ Finset.range (p - 1), f (i + 1)) =
        (∑ i ∈ Finset.range (p - 1), f (i + 1)) + f 0 := by simp [f]
    _ = ∑ i ∈ Finset.range (p - 1 + 1), f i := (Finset.sum_range_succ' f (p - 1)).symm
    _ = 0 := by rwa [Nat.sub_add_cancel (by omega : 1 ≤ p)]

private theorem squareSum_killed (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (p : R p) * squareSum p (p - 1) = 0 := by
  apply reduced_zero_mul
  unfold squareSum
  rw [map_sum]
  simp only [map_pow]
  convert field_squares p hp using 1
  apply Finset.sum_congr rfl
  intro i hi
  unfold invAt
  rw [reduced_inverse p (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)]

private theorem inverse_reflection (p i : ℕ) [Fact p.Prime] (h₁ : 0 < i) (h₂ : i < p) :
    (i : R p)⁻¹ + ((p - i : ℕ) : R p)⁻¹ = -(p : R p) * ((i : R p)⁻¹) ^ 2 := by
  let x : R p := i
  let y : R p := (p - i : ℕ)
  have hx : x⁻¹ * x = 1 := small_inverse p i h₁ h₂
  have hy : y⁻¹ * y = 1 := small_inverse p (p - i) (by omega) (by omega)
  have hxy : x + y = (p : R p) := by
    dsimp [x, y]
    rw [Nat.cast_sub (by omega)]
    ring
  have h : x⁻¹ + y⁻¹ = (p : R p) * (x⁻¹ * y⁻¹) := by
    rw [← hxy]
    linear_combination -y⁻¹ * hx - x⁻¹ * hy
  have hp0 : (p : R p) ^ 2 = 0 := p_square p
  have hz : (p : R p) * (x⁻¹ + y⁻¹) = 0 := by
    rw [h, ← mul_assoc, ← pow_two, hp0, zero_mul]
  change x⁻¹ + y⁻¹ = -(p : R p) * x⁻¹ ^ 2
  linear_combination h + x⁻¹ * hz

private theorem harmonic_zero (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    harmonic p (p - 1) = 0 := by
  have hr :
      (∑ i ∈ Finset.range (p - 1), invAt p (p - 1 - 1 - i)) = harmonic p (p - 1) :=
    Finset.sum_range_reflect (invAt p) (p - 1)
  have h : (2 : R p) * harmonic p (p - 1) = 0 := by
    calc
      (2 : R p) * harmonic p (p - 1) =
        ∑ i ∈ Finset.range (p - 1), (invAt p i + invAt p (p - 1 - 1 - i)) := by
          rw [Finset.sum_add_distrib, hr, two_mul]
          rfl
      _ = ∑ i ∈ Finset.range (p - 1), -(p : R p) * invAt p i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hr' : p - 1 - 1 - i + 1 = p - (i + 1) := by omega
        simpa [invAt, hr'] using inverse_reflection p (i + 1) (by omega) (by omega)
      _ = 0 := by
        rw [← Finset.mul_sum, neg_mul]
        exact neg_eq_zero.mpr (squareSum_killed p hp)
  have hi : (2 : R p)⁻¹ * 2 = 1 := by
    simpa only [Nat.cast_ofNat] using small_inverse p 2 (by decide) (by omega)
  calc
    harmonic p (p - 1) = (2 : R p)⁻¹ * ((2 : R p) * harmonic p (p - 1)) := by
      rw [← mul_assoc, hi, one_mul]
    _ = 0 := by rw [h, mul_zero]

private theorem square_of_harmonic (p n : ℕ) :
    2 * (∑ i ∈ Finset.range n, invAt p i * harmonic p i) =
      harmonic p n ^ 2 - squareSum p n := by
  induction n with
  | zero => simp [harmonic, squareSum]
  | succ n ih =>
      have h₁ : harmonic p (n + 1) = harmonic p n + invAt p n :=
        Finset.sum_range_succ _ _
      have h₂ : squareSum p (n + 1) = squareSum p n + invAt p n ^ 2 :=
        Finset.sum_range_succ _ _
      rw [Finset.sum_range_succ, h₁, h₂]
      linear_combination ih



private theorem cross_killed (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (p : R p) * (∑ i ∈ Finset.range (p - 1), invAt p i * harmonic p i) = 0 := by
  have hs := square_of_harmonic p (p - 1)
  rw [harmonic_zero p hp, zero_pow (by decide : 2 ≠ 0), zero_sub] at hs
  have hn := squareSum_killed p hp
  let x := (p : R p) * (∑ i ∈ Finset.range (p - 1), invAt p i * harmonic p i)
  have hx : 2 * x = 0 := by
    dsimp [x]
    linear_combination (p : R p) * hs - hn
  have hi : (2 : R p)⁻¹ * 2 = 1 := by
    simpa only [Nat.cast_ofNat] using small_inverse p 2 (by decide) (by omega)
  change x = 0
  calc
    x = (2 : R p)⁻¹ * (2 * x) := by rw [← mul_assoc, hi, one_mul]
    _ = 0 := by rw [hx, mul_zero]

private def signedChoose (p k : ℕ) : R p :=
  (-1 : R p) ^ k * ((p - 1).choose k : R p)

private theorem signed_expansion (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    signedChoose p k = 1 - (p : R p) * harmonic p k := by
  induction k with
  | zero => simp [signedChoose, harmonic]
  | succ k ih =>
      have hnat := Nat.choose_succ_right_eq (p - 1) k
      have hsub : (((p - 1 - k : ℕ) : R p)) = (p : R p) - ((k + 1 : ℕ) : R p) := by
        rw [show p - 1 - k = p - (k + 1) by omega, Nat.cast_sub (by omega)]
      have hrec : ((k + 1 : ℕ) : R p) * signedChoose p (k + 1) =
          (((k + 1 : ℕ) : R p) - (p : R p)) * signedChoose p k := by
        have he := congrArg (fun n : ℕ => (n : R p)) hnat
        simp only [Nat.cast_mul] at he
        rw [hsub] at he
        simp only [signedChoose, pow_succ]
        linear_combination -((-1 : R p) ^ k) * he
      have hu : invAt p k * ((k + 1 : ℕ) : R p) = 1 :=
        small_inverse p (k + 1) (by omega) hk
      have hx : signedChoose p (k + 1) =
          signedChoose p k * (1 - (p : R p) * invAt p k) := by
        calc
          signedChoose p (k + 1) =
              invAt p k * (((k + 1 : ℕ) : R p) * signedChoose p (k + 1)) := by
            rw [← mul_assoc, hu, one_mul]
          _ = signedChoose p k * (1 - (p : R p) * invAt p k) := by
            rw [hrec]
            linear_combination signedChoose p k * hu
      rw [hx, ih (by omega), show harmonic p (k + 1) = harmonic p k + invAt p k from
        Finset.sum_range_succ _ _]
      linear_combination (harmonic p k * invAt p k) * p_square p

private theorem upper_expansion (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    ((p + k).choose k : R p) = 1 + (p : R p) * harmonic p k := by
  induction k with
  | zero => simp [harmonic]
  | succ k ih =>
      have hnat : (k + 1) * (p + (k + 1)).choose (k + 1) =
          (p + (k + 1)) * (p + k).choose k := by
        simpa only [Nat.add_assoc, Nat.mul_comm _ (k + 1)] using
          (Nat.add_one_mul_choose_eq (p + k) k).symm
      have hrec := congrArg (fun n : ℕ => (n : R p)) hnat
      simp only [Nat.cast_mul] at hrec
      have hu : invAt p k * ((k + 1 : ℕ) : R p) = 1 :=
        small_inverse p (k + 1) (by omega) hk
      have hx : ((p + (k + 1)).choose (k + 1) : R p) =
          ((p + k).choose k : R p) * (1 + (p : R p) * invAt p k) := by
        calc
          ((p + (k + 1)).choose (k + 1) : R p) =
              invAt p k * (((k + 1 : ℕ) : R p) * ((p + (k + 1)).choose (k + 1) : R p)) := by
            rw [← mul_assoc, hu, one_mul]
          _ = ((p + k).choose k : R p) * (1 + (p : R p) * invAt p k) := by
            rw [hrec, Nat.cast_add p (k + 1)]
            linear_combination ((p + k).choose k : R p) * hu
      rw [hx, ih (by omega), show harmonic p (k + 1) = harmonic p k + invAt p k from
        Finset.sum_range_succ _ _]
      linear_combination (harmonic p k * invAt p k) * p_square p

private def normalizedChoose (p k : ℕ) : ℕ := (p + k).choose (k + 1) / p

private theorem normalized_identity (p k : ℕ) [Fact p.Prime] (hk : k + 1 < p) :
    p * normalizedChoose p k = (p + k).choose (k + 1) ∧
      (k + 1) * normalizedChoose p k = (p + k).choose k := by
  have hp : p.Prime := Fact.out
  have h := Nat.choose_succ_right_eq (p + k) k
  rw [Nat.add_sub_cancel_right] at h
  have hd : p ∣ (p + k).choose (k + 1) := by
    have hd' : p ∣ (p + k).choose (k + 1) * (k + 1) := by rw [h]; exact dvd_mul_left _ _
    exact (hp.dvd_mul.mp hd').resolve_right (Nat.not_dvd_of_pos_of_lt (by omega) hk)
  have eq₁ : p * normalizedChoose p k = (p + k).choose (k + 1) := Nat.mul_div_cancel' hd
  refine ⟨eq₁, Nat.eq_of_mul_eq_mul_left hp.pos ?_⟩
  calc
    p * ((k + 1) * normalizedChoose p k) = (p * normalizedChoose p k) * (k + 1) := by ac_rfl
    _ = (p + k).choose k * p := by rw [eq₁, h]
    _ = p * (p + k).choose k := mul_comm _ _

private theorem normalized_summand (p k : ℕ) [Fact p.Prime] (hk : k + 1 < p) :
    ((k + 1 : ℕ) : R p) * signedChoose p (k + 1) * (normalizedChoose p k : R p) ^ 2 =
      invAt p k + (p : R p) * (invAt p k * harmonic p k - invAt p k ^ 2) := by
  have hu : invAt p k * ((k + 1 : ℕ) : R p) = 1 :=
    small_inverse p (k + 1) (by omega) hk
  have hb : (normalizedChoose p k : R p) = invAt p k * ((p + k).choose k : R p) := by
    have h := congrArg (fun x : ℕ => (x : R p)) (normalized_identity p k hk).2
    simp only [Nat.cast_mul] at h
    rw [← h, ← mul_assoc, hu, one_mul]
  have hf : ((1 + (p : R p) * harmonic p k) : R p) ^ 2 =
      1 + 2 * (p : R p) * harmonic p k := by
    linear_combination harmonic p k ^ 2 * p_square p
  calc
    _ = invAt p k * signedChoose p (k + 1) * ((p + k).choose k : R p) ^ 2 := by
      rw [hb]
      linear_combination
        (invAt p k * signedChoose p (k + 1) * ((p + k).choose k : R p) ^ 2) * hu
    _ = _ := by
      rw [signed_expansion p (k + 1) hk, upper_expansion p k (by omega), hf,
        show harmonic p (k + 1) = harmonic p k + invAt p k from Finset.sum_range_succ _ _]
      linear_combination (-2 * invAt p k * harmonic p k * (harmonic p k + invAt p k)) * p_square p

private def weightedSum (p : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (p - 1),
    (-1 : ℤ) ^ (k + 1) * (k + 1 : ℕ) * ((p - 1).choose (k + 1) : ℕ) *
      (normalizedChoose p k : ℤ) ^ 2

private theorem weighted_zero (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (weightedSum p : R p) = 0 := by
  have hcast :
      (weightedSum p : R p) =
        ∑ i ∈ Finset.range (p - 1),
          ((i + 1 : ℕ) : R p) * signedChoose p (i + 1) * (normalizedChoose p i : R p) ^ 2 := by
    unfold weightedSum
    push_cast
    congr 1
    ext i
    simp only [signedChoose]
    ring
  rw [hcast]
  calc
    _ = ∑ i ∈ Finset.range (p - 1),
        (invAt p i + (p : R p) * (invAt p i * harmonic p i - invAt p i ^ 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact normalized_summand p i (by omega)
    _ = harmonic p (p - 1) +
        ((p : R p) * (∑ i ∈ Finset.range (p - 1), invAt p i * harmonic p i) -
          (p : R p) * squareSum p (p - 1)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
      rfl
    _ = 0 := by rw [harmonic_zero p hp, cross_killed p hp, squareSum_killed p hp]; ring

private theorem a_factor (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    a (p - 1) = (p : ℤ) ^ 2 * weightedSum p := by
  let summand (k : ℕ) : ℤ :=
    (-1 : ℤ) ^ (p - 1 + k) * (k : ℤ) * ((p - 1).choose k : ℕ) *
      ((p - 1 + k).choose k : ℤ) ^ 2
  change (∑ k ∈ Finset.range (p - 1 + 1), summand k) = (p : ℤ) ^ 2 * weightedSum p
  rw [Finset.sum_range_succ', show summand 0 = 0 by simp [summand], add_zero,
    weightedSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hi := Finset.mem_range.mp hk
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have heven : Even (p - 1) := by obtain ⟨j, hj⟩ := hodd; exact ⟨j, by omega⟩
  simp only [summand, pow_add (-1 : ℤ) (p - 1) (k + 1), heven.neg_one_pow, one_mul]
  rw [show p - 1 + (k + 1) = p + k by omega, ← (normalized_identity p k (by omega)).1,
      Nat.cast_mul]
  ring

private theorem index_dvd (n : ℕ) (hn : 0 < n) : (n : ℤ) ∣ a n := by
  unfold a
  apply Finset.dvd_sum
  intro k _
  cases k with
  | zero => simp
  | succ k =>
      have h := Nat.add_one_mul_choose_eq (n - 1) k
      rw [Nat.sub_add_cancel hn] at h
      have hcast := congrArg (fun j : ℕ => (j : ℤ)) h
      simp only [Nat.cast_mul] at hcast
      refine ⟨(-1 : ℤ) ^ (n + (k + 1)) * ((n - 1).choose k : ℤ) *
        ((n + (k + 1)).choose (k + 1) : ℤ) ^ 2, ?_⟩
      linear_combination (-((-1 : ℤ) ^ (n + (k + 1))) *
        ((n + (k + 1)).choose (k + 1) : ℤ) ^ 2) * hcast

end A357558Proof

open A357558Proof OMA.S_oeis_a357558 in
theorem OMA.solution : type_of% @OMA.S_oeis_a357558.main := by
  intro p hp hp5
  let : Fact p.Prime := ⟨hp⟩
  have hnorm : ((p ^ 2 : ℕ) : ℤ) ∣ weightedSum p :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (weighted_zero p hp5)
  have hp4 : ((p ^ 4 : ℕ) : ℤ) ∣ a (p - 1) := by
    obtain ⟨z, hz⟩ := hnorm
    refine ⟨z, ?_⟩
    rw [a_factor p hp5, hz, Nat.cast_pow, Nat.cast_pow]
    ring
  have hcNat : (p - 1).Coprime (p ^ 4) := (small_coprime p (p - 1) (by omega) (by omega)).pow_right 4
  have hc : IsCoprime ((p - 1 : ℕ) : ℤ) ((p ^ 4 : ℕ) : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact hcNat
  simpa only [Nat.cast_mul] using hc.mul_dvd (index_dvd (p - 1) (by omega)) hp4
