import FormalConjectures.ErdosProblems.«325»

/-! The counting transfer for Wooley, Sums of three cubes II, Theorems 1.1
and 1.2. The second moment is expressed as a finite sum of squares of
representation counts. Fourier orthogonality identifies it with the
mixed sixth moment of the classical and smooth cubic Weyl sums. -/

namespace OMA.R_Erdos325_erdos_325_variants_wooley_R1

open Finset Filter Asymptotics
open scoped BigOperators Topology

private noncomputable def smooth (P R : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 P).filter fun m ↦ ∀ p : ℕ, p.Prime → p ∣ m → p ≤ R

private noncomputable def triples (P R : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Icc 1 P) ×ˢ (smooth P R ×ˢ smooth P R)

private def cubeSum (t : ℕ × ℕ × ℕ) : ℕ :=
  t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3

private noncomputable def moment (P R : ℕ) : ℝ :=
  ∑ y ∈ (triples P R).image cubeSum,
    (((triples P R).filter fun t ↦ cubeSum t = y).card : ℝ) ^ 2

theorem smooth_mem {P R m : ℕ} :
    m ∈ smooth P R ↔ 1 ≤ m ∧ m ≤ P ∧ (∀ p : ℕ, p.Prime → p ∣ m → p ≤ R) := by
  classical
  simp [smooth, and_assoc]

theorem moment_eq (P R : ℕ) :
    moment P R = ∑ y ∈ (triples P R).image cubeSum,
      (((triples P R).filter fun t ↦ cubeSum t = y).card : ℝ) ^ 2 := rfl

private theorem finite_count_transfer {P R x : ℕ} (hP : 1 ≤ P) (hfit : 3 * P ^ 3 ≤ x)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hdense : c * P ≤ ((smooth P R).card : ℝ))
    (henergy : moment P R ≤ C * (P : ℝ) ^ (3.24871567 : ℝ)) :
    (P : ℝ) ^ (2.75128433 : ℝ) ≤ (C / c ^ 4) * (Erdos325.cardIsSumThreePowerBelow 3 x : ℝ) := by
  classical
  have hp : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  let T := triples P R
  let S := T.image cubeSum
  let v (y : ℕ) : ℝ := ((T.filter fun t ↦ cubeSum t = y).card : ℝ)
  have hm : (T.card : ℝ) = ∑ y ∈ S, v y := by
    simpa only [S, v, Nat.cast_sum] using
      congrArg (fun k : ℕ ↦ (k : ℝ)) (Finset.card_eq_sum_card_image cubeSum T)
  have hcauchy : (T.card : ℝ) ^ 2 ≤ (S.card : ℝ) * moment P R := by
    rw [hm]
    simpa [moment, T, S, v, mul_comm] using
      (Finset.sum_mul_sq_le_sq_mul_sq S (fun _ ↦ (1 : ℝ)) v)
  let Q : Set ℕ := {n ∈ Set.Iic x | Erdos325.IsSumThreePower 3 n}
  have Qfinite : Q.Finite := (Set.finite_Iic x).subset fun _ h ↦ h.1
  have hsub : (↑S : Set ℕ) ⊆ Q := by
    intro y hy
    obtain ⟨⟨a,b,d⟩, ht, rfl⟩ := Finset.mem_image.mp hy
    rcases Finset.mem_product.mp ht with ⟨ha, hbd⟩
    rcases Finset.mem_product.mp hbd with ⟨hb, hd⟩
    have ha' := (Finset.mem_Icc.mp ha).2
    have hb' := (smooth_mem.mp hb).2.1
    have hd' := (smooth_mem.mp hd).2.1
    have bound : a ^ 3 + b ^ 3 + d ^ 3 ≤ 3 * P ^ 3 := by
      have h₁ : a ^ 3 ≤ P ^ 3 := Nat.pow_le_pow_left ha' _
      have h₂ : b ^ 3 ≤ P ^ 3 := Nat.pow_le_pow_left hb' _
      have h₃ : d ^ 3 ≤ P ^ 3 := Nat.pow_le_pow_left hd' _
      omega
    exact ⟨bound.trans hfit, a,b,d,rfl⟩
  have hcard : S.card ≤ Erdos325.cardIsSumThreePowerBelow 3 x := by
    simpa [Q, Erdos325.cardIsSumThreePowerBelow] using Set.ncard_le_ncard hsub Qfinite
  have tmass : c ^ 2 * (P : ℝ) ^ 3 ≤ (T.card : ℝ) := by
    have hT : T.card = P * (smooth P R).card ^ 2 := by
      simp [T, triples, Nat.card_Icc, pow_two]
    rw [hT, Nat.cast_mul, Nat.cast_pow]
    calc c ^ 2 * (P : ℝ) ^ 3 = (P : ℝ) * (c * P) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hc.le hp.le) hdense _) hp.le
  have combined : c ^ 4 * (P : ℝ) ^ (6 : ℕ) ≤
      (Erdos325.cardIsSumThreePowerBelow 3 x : ℝ) * (C * (P : ℝ) ^ (3.24871567 : ℝ)) := by
    calc c ^ 4 * (P : ℝ) ^ (6 : ℕ) = (c ^ 2 * (P : ℝ) ^ 3) ^ 2 := by ring
      _ ≤ (T.card : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) tmass _
      _ ≤ (S.card : ℝ) * moment P R := hcauchy
      _ ≤ _ := mul_le_mul (by exact_mod_cast hcard) henergy
        (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (by positivity)
  have hpow : (P : ℝ) ^ (2.75128433 : ℝ) * (P : ℝ) ^ (3.24871567 : ℝ) =
      (P : ℝ) ^ (6 : ℕ) := by
    rw [← Real.rpow_add hp, ← Real.rpow_natCast]
    norm_num
  have hc4 : 0 < c ^ 4 := pow_pos hc _
  have estimate : (P : ℝ) ^ (6 : ℕ) ≤
      ((C / c ^ 4) * (Erdos325.cardIsSumThreePowerBelow 3 x : ℝ)) *
        (P : ℝ) ^ (3.24871567 : ℝ) := by
    apply (le_of_mul_le_mul_left ?_ hc4)
    calc c ^ 4 * (P : ℝ) ^ (6 : ℕ) ≤ _ := combined
      _ = _ := by field_simp [hc4.ne']
  apply (le_of_mul_le_mul_right ?_ (Real.rpow_pos_of_pos hp (3.24871567 : ℝ)))
  rwa [hpow]

private theorem cube_scale (x Q : ℕ) (hx : 3 * (Q + 1) ^ 3 ≤ x) :
    ∃ P ≥ Q + 1, 3 * P ^ 3 ≤ x ∧ x < 3 * (P + 1) ^ 3 := by
  have h : ∃ n : ℕ, x < 3 * (n + 1) ^ 3 := by
    refine ⟨x, ?_⟩
    have hpow : x + 1 ≤ (x + 1) ^ 3 := Nat.le_self_pow (by decide) _
    omega
  let P := Nat.find h
  have pup : x < 3 * (P + 1) ^ 3 := Nat.find_spec h
  have plarge : Q + 1 ≤ P := by
    apply Nat.succ_le_of_lt
    apply lt_of_not_ge
    intro hlt
    have hpow : (P + 1) ^ 3 ≤ (Q + 1) ^ 3 := Nat.pow_le_pow_left (by omega) _
    omega
  obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero (show P ≠ 0 by omega)
  have hmin : ¬ x < 3 * (u + 1) ^ 3 := Nat.find_min h (by omega)
  have fit : 3 * P ^ 3 ≤ x := by
    rw [hu]
    exact le_of_not_gt hmin
  exact ⟨P, plarge, fit, pup⟩

/-- A fixed positive fraction of the integers up to P are P^η-smooth,
for each fixed positive η. -/
def H1 : Prop :=
  ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ P : ℕ in atTop, ∃ R : ℕ,
      (R : ℝ) ≤ (P : ℝ) ^ η ∧ c * P ≤ ((smooth P R).card : ℝ)

/-- The discrete mixed sixth-moment estimate of Wooley, Theorem 1.2. -/
def H2 : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
    ∀ᶠ P : ℕ in atTop, ∀ R : ℕ, (R : ℝ) ≤ (P : ℝ) ^ η →
      moment P R ≤ C * (P : ℝ) ^ (3.24871567 : ℝ)

theorem main : H1 → H2 → type_of% @Erdos325.erdos_325.variants.wooley := by
  intro density energy
  obtain ⟨η, hη, C, hC, hmoment⟩ := energy
  obtain ⟨c, hc, hdense⟩ := density η hη
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 (hdense.and hmoment)
  rw [isBigO_iff]
  let β : ℝ := 0.91709477
  have hβ : 0 ≤ β := by dsimp [β]; norm_num
  have h24 : (0 : ℝ) ≤ 24 := by norm_num
  have hfactor : 0 ≤ (24 : ℝ) ^ β := Real.rpow_nonneg h24 β
  refine ⟨(24 : ℝ) ^ β * (C / c ^ 4), ?_⟩
  filter_upwards [eventually_ge_atTop (3 * (Q + 1) ^ 3)] with x hx
  obtain ⟨P, hP, hfit, hbig⟩ := cube_scale x Q hx
  obtain ⟨hcP, hCP⟩ := hQ P (by omega)
  obtain ⟨R, hR, hdR⟩ := hcP
  have estimate := finite_count_transfer (by omega : 1 ≤ P) hfit hc hC hdR (hCP R hR)
  have hp : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
  have hbigR : (x : ℝ) < 3 * ((P : ℝ) + 1) ^ 3 := by exact_mod_cast hbig
  have hpow : ((P : ℝ) + 1) ^ (3 : ℕ) ≤ (2 * (P : ℝ)) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hx' : (x : ℝ) ≤ 24 * (P : ℝ) ^ (3 : ℕ) := by
    rw [mul_pow] at hpow
    nlinarith only [hbigR, hpow]
  change ‖(x : ℝ) ^ β‖ ≤ _ * ‖(Erdos325.cardIsSumThreePowerBelow 3 x : ℝ)‖
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) β),
    Real.norm_of_nonneg (Nat.cast_nonneg _)]
  calc (x : ℝ) ^ β ≤ (24 * (P : ℝ) ^ (3 : ℕ)) ^ β :=
        Real.rpow_le_rpow (by positivity) hx' hβ
    _ = (24 : ℝ) ^ β * (P : ℝ) ^ ((3 : ℝ) * β) := by
      have hP₀ : (0 : ℝ) ≤ P := Nat.cast_nonneg P
      calc (24 * (P : ℝ) ^ (3 : ℕ)) ^ β =
          (24 : ℝ) ^ β * ((P : ℝ) ^ (3 : ℕ)) ^ β :=
            Real.mul_rpow h24 (pow_nonneg hP₀ 3)
        _ = _ := congrArg (fun z : ℝ ↦ (24 : ℝ) ^ β * z)
              (Real.rpow_natCast_mul hP₀ 3 β).symm
    _ ≤ (24 : ℝ) ^ β * (P : ℝ) ^ (2.75128433 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp (by dsimp [β]; norm_num))
        hfactor
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left estimate hfactor

end OMA.R_Erdos325_erdos_325_variants_wooley_R1
