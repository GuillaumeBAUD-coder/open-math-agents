import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H1_R1
import Mathlib.NumberTheory.Bernoulli
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
Proof of step RegularPrimes.isRegularPrime_iff_Bernoulli.R3.H1.R1.H2:
Kummer-Faulhaber congruence modulo p^2 relating the power sum of exponent 1 + p*(k-1)
to B_k / k modulo p for even k in [2, p - 3].
-/

namespace OMA.StepR3H1R1H2

private lemma p_sq_zero (p : ℕ) : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
  norm_cast
  exact ZMod.natCast_self (p ^ 2)

private lemma mul_p_pow_eq_zero (p : ℕ) (t : ZMod (p ^ 2)) {m : ℕ} (hm : 2 ≤ m) :
    ((p : ZMod (p ^ 2)) * t) ^ m = 0 := by
  have hm' : m = 2 + (m - 2) := by omega
  rw [hm', mul_pow, pow_add, p_sq_zero, zero_mul, zero_mul]

private lemma add_mul_p_pow_p {p : ℕ} (hp5 : 5 ≤ p) (x t : ZMod (p ^ 2)) :
    ((p : ZMod (p ^ 2)) * t + x) ^ p = x ^ p := by
  rw [add_pow]
  have hp_split : p + 1 = (p - 1) + 1 + 1 := by omega
  rw [hp_split, Finset.sum_range_succ', Finset.sum_range_succ']
  have htail : ∑ j ∈ Finset.range (p - 1),
      ((p : ZMod (p ^ 2)) * t) ^ (j + 1 + 1) * x ^ (p - (j + 1 + 1)) *
        ↑(p.choose (j + 1 + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [mul_p_pow_eq_zero p t (by omega : 2 ≤ j + 1 + 1), zero_mul, zero_mul]
  have hmid : ((p : ZMod (p ^ 2)) * t) ^ (0 + 1) * x ^ (p - (0 + 1)) *
      ↑(p.choose (0 + 1)) = 0 := by
    simp only [zero_add, pow_one, Nat.choose_one_right]
    calc (p : ZMod (p ^ 2)) * t * x ^ (p - 1) * (p : ZMod (p ^ 2))
        = (p : ZMod (p ^ 2)) ^ 2 * (t * x ^ (p - 1)) := by ring
      _ = 0 := by rw [p_sq_zero, zero_mul]
  rw [htail, zero_add, hmid, zero_add]
  simp

private lemma nat_pow_k_expand {p : ℕ} [Fact p.Prime] {k : ℕ} (hk2 : 2 ≤ k) (a : ℕ) :
    (a : ZMod (p ^ 2)) ^ k =
      (1 - (k : ZMod (p ^ 2))) * ((a : ZMod (p ^ 2)) ^ p) ^ k +
        (k : ZMod (p ^ 2)) * (a : ZMod (p ^ 2)) ^ (1 + p * (k - 1)) := by
  have hfermat : (((a : ℤ) - (a : ℤ) ^ p : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.pow_card, sub_self]
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ) - (a : ℤ) ^ p) p).mp hfermat
  let u : ZMod (p ^ 2) := (a : ZMod (p ^ 2)) ^ p
  let δ : ZMod (p ^ 2) := (p : ZMod (p ^ 2)) * (c : ZMod (p ^ 2))
  have hδ : (a : ZMod (p ^ 2)) - u = δ := by
    have hc' : (((a : ℤ) - (a : ℤ) ^ p : ℤ) : ZMod (p ^ 2)) =
        (((p : ℤ) * c : ℤ) : ZMod (p ^ 2)) := congrArg Int.cast hc
    push_cast at hc'
    exact hc'
  have ha_eq : (a : ZMod (p ^ 2)) = δ + u := by
    rw [← hδ]
    ring
  have hexpand : (δ + u) ^ k =
      u ^ k + δ * u ^ (k - 1) * (k : ZMod (p ^ 2)) := by
    rw [add_pow]
    have hk_split : k + 1 = (k - 1) + 1 + 1 := by omega
    rw [hk_split, Finset.sum_range_succ', Finset.sum_range_succ']
    have htail : ∑ j ∈ Finset.range (k - 1),
        δ ^ (j + 1 + 1) * u ^ (k - (j + 1 + 1)) * ↑(k.choose (j + 1 + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have h0 : δ ^ (j + 1 + 1) = 0 := mul_p_pow_eq_zero p (c : ZMod (p ^ 2)) (by omega)
      rw [h0, zero_mul, zero_mul]
    rw [htail, zero_add]
    simp only [zero_add, pow_one, Nat.choose_one_right, pow_zero, one_mul, Nat.sub_zero,
      Nat.choose_zero_right, Nat.cast_one, mul_one]
    ring
  have hau : (a : ZMod (p ^ 2)) * u ^ (k - 1) = (a : ZMod (p ^ 2)) ^ (1 + p * (k - 1)) := by
    dsimp only [u]
    rw [pow_add, pow_one, pow_mul]
  have huu : u * u ^ (k - 1) = u ^ k := by
    conv_rhs => rw [show k = 1 + (k - 1) by omega, pow_add, pow_one]
  calc (a : ZMod (p ^ 2)) ^ k
      = (δ + u) ^ k := by rw [← ha_eq]
    _ = u ^ k + ((a : ZMod (p ^ 2)) - u) * u ^ (k - 1) * (k : ZMod (p ^ 2)) := by
        rw [hexpand, ← hδ]
    _ = u ^ k + (k : ZMod (p ^ 2)) * ((a : ZMod (p ^ 2)) * u ^ (k - 1)) -
          (k : ZMod (p ^ 2)) * (u * u ^ (k - 1)) := by ring
    _ = (1 - (k : ZMod (p ^ 2))) * u ^ k +
          (k : ZMod (p ^ 2)) * (a : ZMod (p ^ 2)) ^ (1 + p * (k - 1)) := by
        rw [hau, huu]
        ring

private lemma sum_teichmuller_eq_zero {p : ℕ} [hp : Fact p.Prime] {k : ℕ}
    (hk2 : 2 ≤ k) (hkp : k ≤ p - 3) :
    ∑ a ∈ Finset.Ico 1 p, ((a : ZMod (p ^ 2)) ^ p) ^ k = 0 := by
  have hp5 : 5 ≤ p := by omega
  have : NeZero p := ⟨by omega⟩
  have : NeZero (p ^ 2) := ⟨by positivity⟩
  let τ : ZMod p → ZMod (p ^ 2) := fun x => (x.val : ZMod (p ^ 2)) ^ p
  have hτ_mul : ∀ x y : ZMod p, τ (x * y) = τ x * τ y := by
    intro x y
    dsimp only [τ]
    let qv : ℕ := x.val * y.val / p
    have hdiv : p * qv + (x * y).val = x.val * y.val := by
      dsimp only [qv]
      rw [ZMod.val_mul]
      exact Nat.div_add_mod (x.val * y.val) p
    have hcast : (p : ZMod (p ^ 2)) * (qv : ZMod (p ^ 2)) +
        ((x * y).val : ZMod (p ^ 2)) = (x.val : ZMod (p ^ 2)) * (y.val : ZMod (p ^ 2)) := by
      have h1 := congrArg (Nat.cast (R := ZMod (p ^ 2))) hdiv
      push_cast at h1
      exact h1
    rw [← mul_pow, ← hcast, add_mul_p_pow_p hp5]
  have hsum_eq : ∑ a ∈ Finset.Ico 1 p, ((a : ZMod (p ^ 2)) ^ p) ^ k =
      ∑ x : ZMod p, (τ x) ^ k := by
    have hbij : ∑ x : ZMod p, (τ x) ^ k =
        ∑ a ∈ Finset.range p, ((a : ZMod (p ^ 2)) ^ p) ^ k := by
      refine Finset.sum_bij (fun (x : ZMod p) _ => x.val) ?_ ?_ ?_ ?_
      · intro x _
        exact Finset.mem_range.mpr (ZMod.val_lt x)
      · intro x₁ _ x₂ _ hval
        exact ZMod.val_injective p hval
      · intro a ha
        exact ⟨(a : ZMod p), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)⟩
      · intro x _
        rfl
    have hrange : Finset.range p = insert 0 (Finset.Ico 1 p) := by
      ext a
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hbij, hrange, Finset.sum_insert (by simp)]
    have hz : (((0 : ℕ) : ZMod (p ^ 2)) ^ p) ^ k = 0 := by
      rw [Nat.cast_zero, zero_pow (by omega), zero_pow (by omega)]
    rw [hz, zero_add]
  rw [hsum_eq]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hbij_g : Function.Bijective (fun x : ZMod p => (g : ZMod p) * x) := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨(↑g⁻¹ : ZMod p) * y, ?_⟩⟩
    · have h1 := congrArg ((↑g⁻¹ : ZMod p) * ·) hxy
      dsimp only at h1
      rw [← mul_assoc, Units.inv_mul, one_mul, ← mul_assoc, Units.inv_mul, one_mul] at h1
      exact h1
    · dsimp only
      rw [← mul_assoc, Units.mul_inv, one_mul]
  have hshift : ∑ x : ZMod p, (τ x) ^ k =
      (τ (g : ZMod p)) ^ k * ∑ x : ZMod p, (τ x) ^ k := by
    conv_lhs =>
      rw [← Fintype.sum_bijective (fun x : ZMod p => (g : ZMod p) * x) hbij_g
        (fun x => (τ ((g : ZMod p) * x)) ^ k) (fun x => (τ x) ^ k) (fun _ => rfl)]
    simp_rw [hτ_mul, mul_pow]
    rw [← Finset.mul_sum]
  let z : ZMod (p ^ 2) := (τ (g : ZMod p)) ^ k - 1
  have hann : z * ∑ x : ZMod p, (τ x) ^ k = 0 := by
    dsimp only [z]
    linear_combination -hshift
  let φ : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)
  have hφz : φ z = (g : ZMod p) ^ k - 1 := by
    dsimp only [z, τ]
    rw [map_sub, map_one, map_pow, map_pow, map_natCast, ZMod.natCast_zmod_val, ZMod.pow_card]
  have hg_ne_one : (g : ZMod p) ^ k ≠ 1 := by
    intro h1
    have h1u : g ^ k = 1 := Units.ext (by simpa using h1)
    have hdvd : orderOf g ∣ k := orderOf_dvd_iff_pow_eq_one.mpr h1u
    have hord : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
        ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
    rw [hord] at hdvd
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hdvd
  have hφz_ne : φ z ≠ 0 := by
    rw [hφz]
    exact sub_ne_zero.mpr hg_ne_one
  have hz_unit : IsUnit z := by
    have hz_val : (z.val : ZMod (p ^ 2)) = z := ZMod.natCast_zmod_val z
    rw [← hz_val]
    have hnotdvd : ¬ p ∣ z.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      intro h0
      apply hφz_ne
      rw [← hz_val, map_natCast, h0]
    have hcop : z.val.Coprime (p ^ 2) :=
      ((hp.out.coprime_iff_not_dvd.mpr hnotdvd).symm).pow_right 2
    exact (ZMod.isUnit_iff_coprime z.val (p ^ 2)).mpr hcop
  exact hz_unit.mul_left_cancel (by rw [hann, mul_zero])

private lemma bernoulli_den_coprime {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {i : ℕ} (hi : i ≤ p - 3) : ((bernoulli i).den).Coprime p := by
  apply Nat.Coprime.symm
  rw [hp.out.coprime_iff_not_dvd]
  rcases eq_or_ne i 0 with rfl | hi0
  · simp
    omega
  rcases eq_or_ne i 1 with rfl | hi1
  · have hden1 : (bernoulli 1).den = 2 := by norm_num [bernoulli]
    rw [hden1]
    intro hdvd
    have := Nat.le_of_dvd (by decide) hdvd
    omega
  rcases i.even_or_odd with heven | hodd
  · rw [bernoulli_eq_bernoulli'_of_ne_one hi1]
    exact OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3.denominator_coprime p i
      (Finset.mem_Icc.mpr ⟨by omega, hi⟩) heven
  · rw [bernoulli_eq_zero_of_odd hodd (by omega)]
    simp
    omega

private lemma faulhaber_mod_p_sq {p : ℕ} [hp : Fact p.Prime] {k : ℕ}
    (hk2 : 2 ≤ k) (hkp : k ≤ p - 3) :
    (((bernoulli' k).den : ℕ) : ZMod (p ^ 2)) *
        (∑ a ∈ Finset.Ico 1 p, (a : ZMod (p ^ 2)) ^ k) =
      (p : ZMod (p ^ 2)) * ((bernoulli' k).num : ZMod (p ^ 2)) := by
  have hp5 : 5 ≤ p := by omega
  let D : ℕ := ∏ i ∈ Finset.range (k + 1), (bernoulli i).den
  let qd : ℕ → ℕ := fun i => D / (bernoulli i).den
  have hfaul := sum_range_pow p k
  have hk1_ne : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hfaul_mul : ((D : ℚ) * ((k : ℚ) + 1) * ∑ a ∈ Finset.range p, (a : ℚ) ^ k) =
      ∑ i ∈ Finset.range (k + 1),
        (bernoulli i * (D : ℚ)) * ((k + 1).choose i : ℚ) * (p : ℚ) ^ (k + 1 - i) := by
    rw [hfaul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hk1_ne]
  have hterm_int : ∀ i ∈ Finset.range (k + 1),
      bernoulli i * (D : ℚ) = ((bernoulli i).num : ℚ) * (qd i : ℚ) := by
    intro i hi
    have hdvd : (bernoulli i).den ∣ D := Finset.dvd_prod_of_mem _ hi
    have hD_eq : D = (bernoulli i).den * qd i := (Nat.mul_div_cancel' hdvd).symm
    calc bernoulli i * (D : ℚ)
        = bernoulli i * ((bernoulli i).den : ℚ) * (qd i : ℚ) := by
            conv_lhs => rw [hD_eq]
            push_cast
            ring
      _ = ((bernoulli i).num : ℚ) * (qd i : ℚ) := by
            rw [Rat.mul_den_eq_num]
  have hint_eq : ((D : ℤ) * ((k : ℤ) + 1) * ∑ a ∈ Finset.range p, (a : ℤ) ^ k) =
      ∑ i ∈ Finset.range (k + 1),
        (bernoulli i).num * (qd i : ℤ) *
          ((k + 1).choose i : ℤ) * (p : ℤ) ^ (k + 1 - i) := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hfaul_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hterm_int i hi]
  have hzmod : (((D : ℤ) * ((k : ℤ) + 1) * ∑ a ∈ Finset.range p, (a : ℤ) ^ k : ℤ) : ZMod (p ^ 2)) =
      ((∑ i ∈ Finset.range (k + 1),
        (bernoulli i).num * (qd i : ℤ) *
          ((k + 1).choose i : ℤ) * (p : ℤ) ^ (k + 1 - i) : ℤ) : ZMod (p ^ 2)) :=
    congrArg Int.cast hint_eq
  push_cast at hzmod
  rw [Finset.sum_range_succ] at hzmod
  have hlow_zero : ∑ x ∈ Finset.range k,
      ((bernoulli x).num : ZMod (p ^ 2)) * (qd x : ZMod (p ^ 2)) *
        ↑((k + 1).choose x) * (p : ZMod (p ^ 2)) ^ (k + 1 - x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxlt : x < k := Finset.mem_range.mp hx
    have hexp : k + 1 - x = 2 + (k - 1 - x) := by omega
    rw [hexp, pow_add, p_sq_zero, zero_mul, mul_zero]
  rw [hlow_zero, zero_add] at hzmod
  have hbk : bernoulli k = bernoulli' k := bernoulli_eq_bernoulli'_of_ne_one (by omega)
  have hqdk : qd k = D / (bernoulli' k).den := by
    dsimp only [qd]
    rw [hbk]
  have hck : (k + 1).choose k = k + 1 := by
    have haux : ∀ m : ℕ, (m + 1).choose m = m + 1 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [Nat.choose_succ_succ, ih, Nat.choose_self]
    exact haux k
  rw [hqdk, hbk, show k + 1 - k = 1 by omega, pow_one, hck] at hzmod
  have hrange_ico : ∑ a ∈ Finset.range p, (a : ZMod (p ^ 2)) ^ k =
      ∑ a ∈ Finset.Ico 1 p, (a : ZMod (p ^ 2)) ^ k := by
    have hrange : Finset.range p = insert 0 (Finset.Ico 1 p) := by
      ext a
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hrange, Finset.sum_insert (by simp), Nat.cast_zero, zero_pow (by omega), zero_add]
  rw [hrange_ico] at hzmod
  let Q : ℕ := D / (bernoulli' k).den
  have hD_fact : D = (bernoulli' k).den * Q := by
    have hdvd : (bernoulli k).den ∣ D :=
      Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega : k < k + 1))
    rw [hbk] at hdvd
    exact (Nat.mul_div_cancel' hdvd).symm
  have hD_cop : D.Coprime p :=
    Nat.Coprime.prod_left fun i hi =>
      bernoulli_den_coprime hp5 (by have := Finset.mem_range.mp hi; omega)
  have hQ_cop : Q.Coprime (p ^ 2) := by
    have hQ_p : Q.Coprime p := Nat.Coprime.of_dvd_left ⟨(bernoulli' k).den, by rw [hD_fact, mul_comm]⟩ hD_cop
    exact hQ_p.pow_right 2
  have hk1_cop : (k + 1).Coprime (p ^ 2) := by
    have hk1_p : (k + 1).Coprime p :=
      (hp.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
    exact hk1_p.pow_right 2
  have hQ_unit : IsUnit (Q : ZMod (p ^ 2)) := (ZMod.isUnit_iff_coprime Q (p ^ 2)).mpr hQ_cop
  have hk1_unit : IsUnit ((k + 1 : ℕ) : ZMod (p ^ 2)) :=
    (ZMod.isUnit_iff_coprime (k + 1) (p ^ 2)).mpr hk1_cop
  have hD_cast : (D : ZMod (p ^ 2)) = (((bernoulli' k).den : ℕ) : ZMod (p ^ 2)) * (Q : ZMod (p ^ 2)) := by
    have h1 := congrArg (Nat.cast (R := ZMod (p ^ 2))) hD_fact
    push_cast at h1
    exact h1
  have hk1_cast : ((k : ZMod (p ^ 2)) + 1) = ((k + 1 : ℕ) : ZMod (p ^ 2)) := by push_cast; ring
  have hcancel : ((Q : ZMod (p ^ 2)) * ((k + 1 : ℕ) : ZMod (p ^ 2))) *
      ((((bernoulli' k).den : ℕ) : ZMod (p ^ 2)) * ∑ a ∈ Finset.Ico 1 p, (a : ZMod (p ^ 2)) ^ k) =
      ((Q : ZMod (p ^ 2)) * ((k + 1 : ℕ) : ZMod (p ^ 2))) *
      ((p : ZMod (p ^ 2)) * ((bernoulli' k).num : ZMod (p ^ 2))) := by
    calc ((Q : ZMod (p ^ 2)) * ((k + 1 : ℕ) : ZMod (p ^ 2))) *
          ((((bernoulli' k).den : ℕ) : ZMod (p ^ 2)) * ∑ a ∈ Finset.Ico 1 p, (a : ZMod (p ^ 2)) ^ k)
        = (D : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2)) + 1) *
            ∑ a ∈ Finset.Ico 1 p, (a : ZMod (p ^ 2)) ^ k := by
            rw [hD_cast, hk1_cast]
            ring
      _ = ((bernoulli' k).num : ZMod (p ^ 2)) * (Q : ZMod (p ^ 2)) *
            ((k + 1 : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) := hzmod
      _ = ((Q : ZMod (p ^ 2)) * ((k + 1 : ℕ) : ZMod (p ^ 2))) *
            ((p : ZMod (p ^ 2)) * ((bernoulli' k).num : ZMod (p ^ 2))) := by ring
  exact (hQ_unit.mul hk1_unit).mul_left_cancel hcancel

end OMA.StepR3H1R1H2

theorem OMA.solution : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H1_R1.H2 := by
  intro p hp k hk2 hkp hkeven
  have hp5 : 5 ≤ p := by omega
  let S : ℕ := ∑ a ∈ Finset.Ico 1 p, a ^ (1 + p * (k - 1))
  have hsum_rel : (∑ a ∈ Finset.Ico 1 p, (a : ZMod (p ^ 2)) ^ k) =
      (k : ZMod (p ^ 2)) * (S : ZMod (p ^ 2)) := by
    have hexp : (∑ a ∈ Finset.Ico 1 p, (a : ZMod (p ^ 2)) ^ k) =
        ∑ a ∈ Finset.Ico 1 p,
          ((1 - (k : ZMod (p ^ 2))) * ((a : ZMod (p ^ 2)) ^ p) ^ k +
            (k : ZMod (p ^ 2)) * (a : ZMod (p ^ 2)) ^ (1 + p * (k - 1))) := by
      apply Finset.sum_congr rfl
      intro a _
      exact OMA.StepR3H1R1H2.nat_pow_k_expand hk2 a
    rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      OMA.StepR3H1R1H2.sum_teichmuller_eq_zero hk2 hkp, mul_zero, zero_add]
    dsimp only [S]
    push_cast
    rfl
  have hmod_p2 : (S : ZMod (p ^ 2)) * (k : ZMod (p ^ 2)) * (((bernoulli' k).den : ℕ) : ZMod (p ^ 2)) =
      (p : ZMod (p ^ 2)) * ((bernoulli' k).num : ZMod (p ^ 2)) := by
    have hf := OMA.StepR3H1R1H2.faulhaber_mod_p_sq hk2 hkp
    rw [hsum_rel] at hf
    linear_combination hf
  let φ : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)
  have hmod_p : (S : ZMod p) * (k : ZMod p) * (((bernoulli' k).den : ℕ) : ZMod p) = 0 := by
    have h := congrArg φ hmod_p2
    simpa [map_mul, map_natCast, CharP.cast_eq_zero] using h
  have hk_ne : (k : ZMod p) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff k p).not.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hden_ne : (((bernoulli' k).den : ℕ) : ZMod p) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff _ p).not.mpr
      (OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3.denominator_coprime p k
        (Finset.mem_Icc.mpr ⟨hk2, hkp⟩) hkeven)
  have hS_zero : (S : ZMod p) = 0 := by
    have h1 : (S : ZMod p) * (k : ZMod p) = 0 := (mul_eq_zero.mp hmod_p).resolve_right hden_ne
    exact (mul_eq_zero.mp h1).resolve_right hk_ne
  have hp_dvd_S : p ∣ S := (ZMod.natCast_eq_zero_iff S p).mp hS_zero
  let Q : ℕ := S / p
  have hSQ : p * Q = S := Nat.mul_div_cancel' hp_dvd_S
  have hint_zmod : ((((p : ℤ) * (Q : ℤ) * (k : ℤ) * ((bernoulli' k).den : ℤ) : ℤ)) : ZMod (p ^ 2)) =
      (((p : ℤ) * (bernoulli' k).num : ℤ) : ZMod (p ^ 2)) := by
    have hSQ_z : (p : ℤ) * (Q : ℤ) = (S : ℤ) := by exact_mod_cast hSQ
    rw [hSQ_z]
    simpa using hmod_p2
  have hdvd_p2 : ((p ^ 2 : ℕ) : ℤ) ∣
      (p : ℤ) * (bernoulli' k).num - (p : ℤ) * (Q : ℤ) * (k : ℤ) * ((bernoulli' k).den : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (p ^ 2)).mp hint_zmod
  have hdvd_mul : (p : ℤ) * (p : ℤ) ∣
      (p : ℤ) * ((bernoulli' k).num - (Q : ℤ) * (k : ℤ) * ((bernoulli' k).den : ℤ)) := by
    have h1 : ((p ^ 2 : ℕ) : ℤ) = (p : ℤ) * (p : ℤ) := by push_cast; ring
    have h2 : (p : ℤ) * (bernoulli' k).num - (p : ℤ) * (Q : ℤ) * (k : ℤ) * ((bernoulli' k).den : ℤ) =
        (p : ℤ) * ((bernoulli' k).num - (Q : ℤ) * (k : ℤ) * ((bernoulli' k).den : ℤ)) := by ring
    rwa [← h1, ← h2]
  have hp_ne_z : (p : ℤ) ≠ 0 := by omega
  have hdvd_p : ((p : ℕ) : ℤ) ∣
      (bernoulli' k).num - (Q : ℤ) * (k : ℤ) * ((bernoulli' k).den : ℤ) :=
    (mul_dvd_mul_iff_left hp_ne_z).mp hdvd_mul
  have hz_zero : (((bernoulli' k).num - (Q : ℤ) * (k : ℤ) * ((bernoulli' k).den : ℤ) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd_p
  push_cast at hz_zero
  change (Q : ZMod p) * ((k : ZMod p) * (((bernoulli' k).den : ℕ) : ZMod p)) =
      ((bernoulli' k).num : ZMod p)
  linear_combination -hz_zero
