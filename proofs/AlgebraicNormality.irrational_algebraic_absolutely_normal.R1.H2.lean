import OMAReductions.R_AlgebraicNormality_irrational_algebraic_absolutely_normal_R1
import Mathlib.Tactic

/-!
# Normality in power bases

Proves `OMA.R_AlgebraicNormality_irrational_algebraic_absolutely_normal_R1.H2`:
if `x : ℝ` is normal in base `b ≥ 2`, then `x` is normal in base `b ^ k` for every `k ≥ 1`.
-/

open NormalNumber Filter

namespace OMA.NormalBasePow

private lemma natFloor_mul_div (b : ℕ) (hb : 0 < b) {z : ℝ} (hz : 0 ≤ z) :
    ⌊(b : ℝ) * z⌋₊ / b = ⌊z⌋₊ := by
  have hbR : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  apply Nat.div_eq_of_lt_le
  · apply Nat.le_floor
    rw [Nat.cast_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le hz) hbR.le
  · rw [Nat.floor_lt (mul_nonneg hbR.le hz), Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm]
    exact mul_lt_mul_of_pos_right (Nat.lt_floor_add_one z) hbR

private lemma natFloor_pow_div (b : ℕ) (hb : 0 < b) {y : ℝ} (hy : 0 ≤ y) (n t : ℕ) :
    ⌊(b : ℝ) ^ (n + t) * y⌋₊ / b ^ t = ⌊(b : ℝ) ^ n * y⌋₊ := by
  have h1 : (b : ℝ) ^ (n + t) * y = ((b ^ t : ℕ) : ℝ) * ((b : ℝ) ^ n * y) := by
    rw [Nat.cast_pow, pow_add, mul_comm ((b : ℝ) ^ n), mul_assoc]
  rw [h1]
  exact natFloor_mul_div (b ^ t) (pow_pos hb t) (mul_nonneg (pow_nonneg (Nat.cast_nonneg b) n) hy)

private lemma mod_pow_div_mod (b k N t : ℕ) (hb : 0 < b) (ht : t < k) :
    ((N % b ^ k) / b ^ t) % b = (N / b ^ t) % b := by
  have hsplit : N = N % b ^ k + b ^ k * (N / b ^ k) := (Nat.mod_add_div N (b ^ k)).symm
  have hk : k = t + 1 + (k - 1 - t) := by omega
  have hbk : b ^ k = b ^ t * (b * b ^ (k - 1 - t)) := by
    conv_lhs => rw [hk]
    rw [pow_add, pow_add, pow_one, mul_assoc]
  conv_rhs => rw [hsplit, hbk, mul_assoc]
  rw [Nat.add_mul_div_left _ _ (pow_pos hb t), mul_assoc, Nat.add_mul_mod_self_left, ← hbk]

private lemma eq_of_forall_div_mod_eq {b : ℕ} (hb : 0 < b) :
    ∀ {k a d : ℕ}, a < b ^ k → d < b ^ k →
      (∀ t < k, (a / b ^ t) % b = (d / b ^ t) % b) → a = d
  | 0, a, d, ha, hd, _ => by
      simp only [pow_zero] at ha hd
      omega
  | k + 1, a, d, ha, hd, h => by
      have hmod : a % b = d % b := by
        simpa using h 0 (Nat.zero_lt_succ k)
      have ha' : a / b < b ^ k := by
        rw [Nat.div_lt_iff_lt_mul hb, mul_comm, ← pow_succ']
        exact ha
      have hd' : d / b < b ^ k := by
        rw [Nat.div_lt_iff_lt_mul hb, mul_comm, ← pow_succ']
        exact hd
      have hdiv : a / b = d / b := by
        apply eq_of_forall_div_mod_eq hb ha' hd'
        intro t ht
        have hstep := h (t + 1) (Nat.add_lt_add_right ht 1)
        simpa [Nat.div_div_eq_div_mul, pow_succ'] using hstep
      have ha_eq : a = b * (a / b) + a % b := (Nat.div_add_mod a b).symm
      have hd_eq : d = b * (d / b) + d % b := (Nat.div_add_mod d b).symm
      rw [ha_eq, hd_eq, hdiv, hmod]

private lemma digitSeq_pow_eq_iff {b k : ℕ} (hb : 0 < b) (x : ℝ) (r d : ℕ) (hd : d < b ^ k) :
    digitSeq (b ^ k) x r = d ↔
      ∀ s : Fin k, digitSeq b x (k * r + s.1) = (d / b ^ (k - 1 - s.1)) % b := by
  set y := Int.fract x
  have hy : 0 ≤ y := Int.fract_nonneg x
  set N := ⌊(b : ℝ) ^ (k * r + k) * y⌋₊
  have hdigPow : digitSeq (b ^ k) x r = N % b ^ k := by
    unfold digitSeq
    have hpow : ((b ^ k : ℕ) : ℝ) ^ (r + 1) = (b : ℝ) ^ (k * r + k) := by
      rw [Nat.cast_pow, ← pow_mul, mul_add, mul_one]
    rw [hpow]
  have hdigB : ∀ s : Fin k, digitSeq b x (k * r + s.1) = (N / b ^ (k - 1 - s.1)) % b := by
    intro s
    unfold digitSeq
    have hidx : k * r + k = (k * r + s.1 + 1) + (k - 1 - s.1) := by omega
    have hN : N / b ^ (k - 1 - s.1) = ⌊(b : ℝ) ^ (k * r + s.1 + 1) * y⌋₊ := by
      dsimp only [N]
      rw [hidx]
      exact natFloor_pow_div b hb hy (k * r + s.1 + 1) (k - 1 - s.1)
    rw [hN]
  rw [hdigPow]
  constructor
  · intro h s
    rw [hdigB s, ← h]
    exact (mod_pow_div_mod b k N (k - 1 - s.1) hb (by omega)).symm
  · intro h
    apply eq_of_forall_div_mod_eq hb (Nat.mod_lt N (pow_pos hb k)) hd
    intro t ht
    rw [mod_pow_div_mod b k N t hb ht]
    have hs := h ⟨k - 1 - t, by omega⟩
    rw [hdigB ⟨k - 1 - t, by omega⟩] at hs
    have ht_eq : k - 1 - (k - 1 - t) = t := by omega
    simpa [ht_eq] using hs

private lemma word_pow_iff {b k m : ℕ} (hb : 0 < b) (hk : 1 ≤ k) (x : ℝ)
    (w : Fin m → ℕ) (hw : ∀ j, w j < b ^ k) :
    ∃ u : Fin (m * k) → ℕ, (∀ t, u t < b) ∧
      ∀ i : ℕ, (∀ j : Fin m, digitSeq (b ^ k) x (i + j.1) = w j) ↔
        (∀ t : Fin (m * k), digitSeq b x (k * i + t.1) = u t) := by
  have hk0 : 0 < k := by omega
  let u : Fin (m * k) → ℕ := fun t =>
    (w ⟨t.1 / k, Nat.div_lt_of_lt_mul (mul_comm m k ▸ t.2)⟩ / b ^ (k - 1 - t.1 % k)) % b
  refine ⟨u, fun t => Nat.mod_lt _ hb, fun i => ?_⟩
  constructor
  · intro h t
    set j : Fin m := ⟨t.1 / k, Nat.div_lt_of_lt_mul (mul_comm m k ▸ t.2)⟩
    set s : Fin k := ⟨t.1 % k, Nat.mod_lt t.1 hk0⟩
    have hj := (digitSeq_pow_eq_iff hb x (i + j.1) (w j) (hw j)).mp (h j) s
    have hidx : k * (i + j.1) + s.1 = k * i + t.1 := by
      have hdm : k * (t.1 / k) + t.1 % k = t.1 := Nat.div_add_mod t.1 k
      dsimp only [j, s]
      linarith
    rw [← hidx]
    exact hj
  · intro h j
    rw [digitSeq_pow_eq_iff hb x (i + j.1) (w j) (hw j)]
    intro s
    have ht_lt : j.1 * k + s.1 < m * k := by
      calc j.1 * k + s.1 < j.1 * k + k := Nat.add_lt_add_left s.2 _
        _ = (j.1 + 1) * k := by ring
        _ ≤ m * k := Nat.mul_le_mul_right k j.2
    have ht := h ⟨j.1 * k + s.1, ht_lt⟩
    have hdiv : (j.1 * k + s.1) / k = j.1 := by
      rw [mul_comm j.1 k, Nat.mul_add_div hk0, Nat.div_eq_of_lt s.2, add_zero]
    have hmod : (j.1 * k + s.1) % k = s.1 := by
      rw [mul_comm j.1 k, Nat.mul_add_mod, Nat.mod_eq_of_lt s.2]
    have hidx : k * i + (j.1 * k + s.1) = k * (i + j.1) + s.1 := by ring
    rw [← hidx]
    simpa [u, hdiv, hmod] using ht

private lemma sum_g_eq_zero {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 0 < Fintype.card α) (u : α) :
    ∑ a : α, ((if a = u then (1 : ℝ) else 0) - 1 / (Fintype.card α : ℝ)) = 0 := by
  have hD : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcard.ne'
  simp [Finset.sum_sub_distrib, hD]

private lemma sum_g_sq {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 0 < Fintype.card α) (u : α) :
    ∑ a : α, ((if a = u then (1 : ℝ) else 0) - 1 / (Fintype.card α : ℝ)) ^ 2 =
      1 - 1 / (Fintype.card α : ℝ) := by
  have hD : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcard.ne'
  have hexp : ∀ a : α,
      ((if a = u then (1 : ℝ) else 0) - 1 / (Fintype.card α : ℝ)) ^ 2 =
        (if a = u then (1 : ℝ) else 0) - 2 / (Fintype.card α : ℝ) * (if a = u then (1 : ℝ) else 0) +
          (1 / (Fintype.card α : ℝ)) ^ 2 := by
    intro a
    split_ifs <;> ring
  simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp [hD]
  ring

private lemma variance_bernoulli_sum {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 0 < Fintype.card α) (u : α) (q : ℕ) (hq : 0 < q) :
    ∑ S : Fin q → α,
        (((Finset.univ.filter (fun j : Fin q => S j = u)).card : ℝ) / (q : ℝ) -
          1 / (Fintype.card α : ℝ)) ^ 2 =
      ((Fintype.card α : ℝ) ^ q) * ((1 / (Fintype.card α : ℝ)) * (1 - 1 / (Fintype.card α : ℝ)) / (q : ℝ)) := by
  set D : ℝ := (Fintype.card α : ℝ)
  set p : ℝ := 1 / D
  have hD0 : D ≠ 0 := Nat.cast_ne_zero.mpr hcard.ne'
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  let g : α → ℝ := fun a => (if a = u then 1 else 0) - p
  have hg0 : ∑ a : α, g a = 0 := sum_g_eq_zero hcard u
  have hg2 : ∑ a : α, (g a) ^ 2 = 1 - p := sum_g_sq hcard u
  have hdiff : ∀ S : Fin q → α,
      ((Finset.univ.filter (fun j : Fin q => S j = u)).card : ℝ) / (q : ℝ) - p =
        (∑ j : Fin q, g (S j)) / (q : ℝ) := by
    intro S
    have hcnt : ((Finset.univ.filter (fun j : Fin q => S j = u)).card : ℝ) =
        ∑ j : Fin q, (if S j = u then (1 : ℝ) else 0) := by
      simp [Finset.sum_boole]
    have hsum : ∑ j : Fin q, g (S j) =
        ((Finset.univ.filter (fun j : Fin q => S j = u)).card : ℝ) - (q : ℝ) * p := by
      simp only [g, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hcnt]
    rw [hsum, sub_div, mul_div_cancel_left₀ p hq0]
  simp_rw [hdiff, div_pow, ← Finset.sum_div]
  have hmain : ∑ S : Fin q → α, (∑ j : Fin q, g (S j)) ^ 2 =
      D ^ q * (q * p * (1 - p)) := by
    have hsq : ∀ S : Fin q → α,
        (∑ j : Fin q, g (S j)) ^ 2 = ∑ j₁ : Fin q, ∑ j₂ : Fin q, g (S j₁) * g (S j₂) := by
      intro S
      rw [sq, Finset.sum_mul_sum]
    simp_rw [hsq]
    rw [Finset.sum_comm]
    have hinner : ∀ j₁ : Fin q,
        ∑ S : Fin q → α, ∑ j₂ : Fin q, g (S j₁) * g (S j₂) = D ^ (q - 1) * (1 - p) := by
      intro j₁
      rw [Finset.sum_comm]
      have hterm : ∀ j₂ : Fin q,
          ∑ S : Fin q → α, g (S j₁) * g (S j₂) =
            if j₂ = j₁ then D ^ (q - 1) * (1 - p) else 0 := by
        intro j₂
        let e := (Equiv.piSplitAt j₁ (fun _ : Fin q => α)).symm
        rw [← Equiv.sum_comp e]
        rw [Fintype.sum_prod_type]
        by_cases hjeq : j₂ = j₁
        · subst hjeq
          simp only [↓reduceIte]
          have hval : ∀ (a : α) (f : {i : Fin q // i ≠ j₂} → α),
              g (e (a, f) j₂) * g (e (a, f) j₂) = (g a) ^ 2 := by
            intro a f
            have he : e (a, f) j₂ = a := by
              change (Equiv.piSplitAt j₂ (fun _ : Fin q => α) (e (a, f))).1 = a
              simp [e]
            rw [he, sq]
          simp_rw [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hg2]
          have hcard_rest : (Fintype.card ({i : Fin q // i ≠ j₂} → α) : ℝ) = D ^ (q - 1) := by
            rw [Fintype.card_fun, Fintype.card_subtype_compl, Fintype.card_fin,
              Fintype.card_subtype_eq, Nat.cast_pow]
          rw [hcard_rest]
        · simp only [hjeq, ↓reduceIte]
          have hval : ∀ (a : α) (f : {i : Fin q // i ≠ j₁} → α),
              g (e (a, f) j₁) * g (e (a, f) j₂) = g a * g (f ⟨j₂, hjeq⟩) := by
            intro a f
            have he1 : e (a, f) j₁ = a := by
              change (Equiv.piSplitAt j₁ (fun _ : Fin q => α) (e (a, f))).1 = a
              simp [e]
            have he2 : e (a, f) j₂ = f ⟨j₂, hjeq⟩ := by
              change (Equiv.piSplitAt j₁ (fun _ : Fin q => α) (e (a, f))).2 ⟨j₂, hjeq⟩ = f ⟨j₂, hjeq⟩
              simp [e]
            rw [he1, he2]
          simp_rw [hval, ← Finset.mul_sum, ← Finset.sum_mul, hg0, zero_mul]
      simp_rw [hterm]
      simp
    simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hDq : D ^ (q - 1) = D ^ q * p := by
      have hq1 : q = (q - 1) + 1 := by omega
      conv_rhs => rw [hq1, pow_succ]
      dsimp only [p]
      field_simp [hD0]
    rw [hDq]
    ring
  rw [hmain]
  field_simp [hq0]

private lemma avg_abs_sub_mean_le {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 0 < Fintype.card α) (u : α) (q : ℕ) (hq : 0 < q) :
    ((1 / ((Fintype.card α : ℝ) ^ q)) *
      ∑ S : Fin q → α,
        |((Finset.univ.filter (fun j : Fin q => S j = u)).card : ℝ) / (q : ℝ) -
          1 / (Fintype.card α : ℝ)|) ^ 2 ≤ 1 / (q : ℝ) := by
  set D : ℝ := (Fintype.card α : ℝ)
  set p : ℝ := 1 / D
  have hDpos : 0 < D := Nat.cast_pos.mpr hcard
  have hDqpos : 0 < D ^ q := pow_pos hDpos q
  have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  let f : (Fin q → α) → ℝ :=
    fun S => |((Finset.univ.filter (fun j : Fin q => S j = u)).card : ℝ) / (q : ℝ) - p|
  have hcard_fn : (Fintype.card (Fin q → α) : ℝ) = D ^ q := by
    rw [Fintype.card_fun, Fintype.card_fin]
    simp [D]
  have hcs : (∑ S : Fin q → α, f S) ^ 2 ≤ D ^ q * ∑ S : Fin q → α, (f S) ^ 2 := by
    have h0 : 0 ≤ ∑ S₁ : Fin q → α, ∑ S₂ : Fin q → α, (f S₁ - f S₂) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hexp : ∑ S₁ : Fin q → α, ∑ S₂ : Fin q → α, (f S₁ - f S₂) ^ 2 =
        2 * D ^ q * (∑ S : Fin q → α, (f S) ^ 2) - 2 * (∑ S : Fin q → α, f S) ^ 2 := by
      have hsub : ∀ S₁ S₂ : Fin q → α,
          (f S₁ - f S₂) ^ 2 = (f S₁) ^ 2 - 2 * (f S₁ * f S₂) + (f S₂) ^ 2 := by
        intro S₁ S₂; ring
      simp_rw [hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard_fn]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring
    linarith
  have hcs' : (∑ S : Fin q → α, f S) ^ 2 ≤
      D ^ q * (D ^ q * (p * (1 - p) / (q : ℝ))) := by
    have hsq : ∑ S : Fin q → α, (f S) ^ 2 = D ^ q * (p * (1 - p) / (q : ℝ)) := by
      simp_rw [f, sq_abs]
      exact variance_bernoulli_sum hcard u q hq
    rwa [hsq] at hcs
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    rw [div_le_one hDpos]
    show (1 : ℝ) ≤ (Fintype.card α : ℝ)
    exact_mod_cast (show (1 : ℕ) ≤ Fintype.card α by omega)
  have hvar : p * (1 - p) ≤ 1 := by nlinarith
  have hle : (∑ S : Fin q → α, f S) ^ 2 ≤ (D ^ q) ^ 2 * (1 / (q : ℝ)) := by
    calc (∑ S : Fin q → α, f S) ^ 2
        ≤ D ^ q * (D ^ q * (p * (1 - p) / (q : ℝ))) := hcs'
      _ = (D ^ q) ^ 2 * (p * (1 - p) / (q : ℝ)) := by ring
      _ ≤ (D ^ q) ^ 2 * (1 / (q : ℝ)) := by gcongr
  rw [mul_pow, one_div, inv_pow]
  calc ((D ^ q) ^ 2)⁻¹ * (∑ S : Fin q → α, f S) ^ 2
      ≤ ((D ^ q) ^ 2)⁻¹ * ((D ^ q) ^ 2 * (1 / (q : ℝ))) := by gcongr
    _ = 1 / (q : ℝ) := by field_simp [hDqpos.ne']

private lemma isNormalInBase_pow_aux {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) {x : ℝ}
    (hx : IsNormalInBase b x) (m : ℕ) (w : Fin m → ℕ) (hw : ∀ j, w j < b ^ k) :
    Tendsto
      (fun n : ℕ =>
        (((Finset.range n).filter (fun i => ∀ j : Fin m, digitSeq (b ^ k) x (i + j.1) = w j)).card : ℝ) / n)
      atTop
      (nhds (1 / ((b ^ k : ℕ) : ℝ) ^ m)) := by
  have hb0 : 0 < b := by omega
  have hk0 : 0 < k := by omega
  by_cases hm0 : m = 0
  · subst hm0
    have hEq : ∀ n : ℕ, 0 < n →
        (((Finset.range n).filter (fun i => ∀ j : Fin 0, digitSeq (b ^ k) x (i + j.1) = w j)).card : ℝ) / n = 1 := by
      intro n hn
      have hfil : (Finset.range n).filter (fun i => ∀ j : Fin 0, digitSeq (b ^ k) x (i + j.1) = w j) =
          Finset.range n := by
        ext i
        simp
      rw [hfil, Finset.card_range]
      exact div_self (Nat.cast_ne_zero.mpr hn.ne')
    simp only [pow_zero, div_one]
    exact tendsto_const_nhds.congr' (Filter.eventually_atTop.mpr ⟨1, fun n hn => (hEq n hn).symm⟩)
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  set L := m * k
  obtain ⟨u, hu_lt, hu_iff⟩ := word_pow_iff hb0 hk x w hw
  have hLpos : 0 < L := Nat.mul_pos hmpos hk0
  set p : ℝ := 1 / (b : ℝ) ^ L
  have hp_eq : 1 / ((b ^ k : ℕ) : ℝ) ^ m = p := by
    dsimp only [p, L]
    rw [Nat.cast_pow, ← pow_mul, mul_comm]
  rw [hp_eq]
  -- Define occurrence predicate for u at position t
  let occ : ℕ → Prop := fun t => ∀ a : Fin L, digitSeq b x (t + a.1) = u a
  classical
  have hcount0 : ∀ n : ℕ,
      ((Finset.range n).filter (fun i => ∀ j : Fin m, digitSeq (b ^ k) x (i + j.1) = w j)).card =
      ((Finset.range n).filter (fun i => occ (k * i))).card := by
    intro n
    congr 1
    ext i
    simp only [Finset.mem_filter, occ]
    exact and_congr_right (fun _ => hu_iff i)
  simp_rw [hcount0]
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose q large enough that k / sqrt(q) < ε / 2, i.e., (2 * k / ε)^2 < q
  obtain ⟨q, hq_gt⟩ := exists_nat_gt ((2 * (k : ℝ) / ε) ^ 2)
  have hqpos : 0 < q := by
    by_contra hq0
    have hqeq : q = 0 := by omega
    rw [hqeq, Nat.cast_zero] at hq_gt
    linarith [sq_nonneg (2 * (k : ℝ) / ε)]
  have hq_real : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hqpos
  have hk_real : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk0
  set M := q * L
  let uFin : Fin L → Fin b := fun a => ⟨u a, hu_lt a⟩
  -- Window of length M starting at position t, viewed as Fin q → Fin L → Fin b
  let W : ℕ → (Fin q → Fin L → Fin b) := fun t j a =>
    ⟨digitSeq b x (t + (j.1 * L + a.1)), Nat.mod_lt _ hb0⟩
  let cnt : (Fin q → Fin L → Fin b) → ℕ := fun S =>
    (Finset.univ.filter (fun j : Fin q => S j = uFin)).card
  have hcnt_eq : ∀ t : ℕ, cnt (W t) =
      (Finset.univ.filter (fun j : Fin q => occ (t + j.1 * L))).card := by
    intro t
    dsimp only [cnt]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, W, uFin, occ]
    constructor
    · intro h a
      have := congr_fun h a
      simpa [add_assoc] using congr_arg Fin.val this
    · intro h
      funext a
      apply Fin.ext
      simpa [add_assoc] using h a
  -- Step 1: bound E_q := (1 / (b^L)^q) * ∑ S, |cnt S / q - p| < ε / (2 * k)
  let α := Fin L → Fin b
  have hcardα : Fintype.card α = b ^ L := by
    simp [α]
  have hcardα_pos : 0 < Fintype.card α := by
    rw [hcardα]
    exact pow_pos hb0 L
  set Eq : ℝ := (1 / ((Fintype.card α : ℝ) ^ q)) *
    ∑ S : Fin q → α, |((cnt S : ℝ) / (q : ℝ)) - p|
  have hEq_nonneg : 0 ≤ Eq := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hEq_sq : Eq ^ 2 ≤ 1 / (q : ℝ) := by
    have h := avg_abs_sub_mean_le hcardα_pos uFin q hqpos
    have hpα : 1 / (Fintype.card α : ℝ) = p := by
      rw [hcardα, Nat.cast_pow]
    simpa only [Eq, cnt, hpα] using h
  have hEq_lt : (k : ℝ) * Eq < ε / 2 := by
    have hlt_sq : (k : ℝ) ^ 2 * Eq ^ 2 < (ε / 2) ^ 2 := by
      have h1 : 1 / (q : ℝ) < (ε / (2 * (k : ℝ))) ^ 2 := by
        rw [div_lt_iff₀ hq_real]
        have hpos2 : 0 < (ε / (2 * (k : ℝ))) ^ 2 := by positivity
        have hinv : (2 * (k : ℝ) / ε) ^ 2 = ((ε / (2 * (k : ℝ))) ^ 2)⁻¹ := by
          field_simp [hε.ne', hk_real.ne']
        rw [hinv] at hq_gt
        have := mul_lt_mul_of_pos_left hq_gt hpos2
        rwa [mul_inv_cancel₀ hpos2.ne'] at this
      calc (k : ℝ) ^ 2 * Eq ^ 2 ≤ (k : ℝ) ^ 2 * (1 / (q : ℝ)) := by gcongr
        _ < (k : ℝ) ^ 2 * (ε / (2 * (k : ℝ))) ^ 2 := by gcongr
        _ = (ε / 2) ^ 2 := by field_simp [hk_real.ne']
    have hmul_sq : ((k : ℝ) * Eq) ^ 2 < (ε / 2) ^ 2 := by
      rw [mul_pow]; exact hlt_sq
    nlinarith [mul_nonneg hk_real.le hEq_nonneg, hε]
  -- Step 2: as n → ∞, (1 / (k * n)) * ∑ t ∈ range (k * n), |cnt (W t) / q - p| → Eq
  -- Rewrite sum over t as sum over S : Fin q → α of |cnt S / q - p| * (#{t < k*n | W t = S} / (k*n))
  have hfreq : ∀ S : Fin q → α,
      Tendsto (fun n : ℕ =>
        (((Finset.range (k * n)).filter (fun t => W t = S)).card : ℝ) / ((k * n : ℕ) : ℝ))
        atTop (nhds (1 / ((Fintype.card α : ℝ) ^ q))) := by
    intro S
    -- Express W t = S as a length-M word match
    let wS : Fin M → ℕ := fun idx =>
      (S ⟨idx.1 / L, Nat.div_lt_of_lt_mul (mul_comm q L ▸ idx.2)⟩
        ⟨idx.1 % L, Nat.mod_lt idx.1 hLpos⟩).1
    have hwS_lt : ∀ idx : Fin M, wS idx < b := fun idx => (S _ _).2
    have hmatch : ∀ t : ℕ, W t = S ↔ ∀ idx : Fin M, digitSeq b x (t + idx.1) = wS idx := by
      intro t
      constructor
      · intro h idx
        set j : Fin q := ⟨idx.1 / L, Nat.div_lt_of_lt_mul (mul_comm q L ▸ idx.2)⟩
        set a : Fin L := ⟨idx.1 % L, Nat.mod_lt idx.1 hLpos⟩
        have hja := congr_arg Fin.val (congr_fun (congr_fun h j) a)
        have hdm : j.1 * L + a.1 = idx.1 := by
          dsimp only [j, a]
          rw [mul_comm]
          exact Nat.div_add_mod idx.1 L
        simpa [W, wS, hdm] using hja
      · intro h
        funext j a
        apply Fin.ext
        have hidx_lt : j.1 * L + a.1 < M := by
          calc j.1 * L + a.1 < j.1 * L + L := Nat.add_lt_add_left a.2 _
            _ = (j.1 + 1) * L := by ring
            _ ≤ q * L := Nat.mul_le_mul_right L j.2
        have hdiv : (j.1 * L + a.1) / L = j.1 := by
          rw [mul_comm j.1 L, Nat.mul_add_div hLpos, Nat.div_eq_of_lt a.2, add_zero]
        have hmod : (j.1 * L + a.1) % L = a.1 := by
          rw [mul_comm j.1 L, Nat.mul_add_mod, Nat.mod_eq_of_lt a.2]
        have hja := h ⟨j.1 * L + a.1, hidx_lt⟩
        simpa [W, wS, hdiv, hmod] using hja
    have hnorm := hx M wS hwS_lt
    have hcomp : Tendsto (fun n : ℕ =>
        (((Finset.range (k * n)).filter (fun t => ∀ idx : Fin M, digitSeq b x (t + idx.1) = wS idx)).card : ℝ) /
          ((k * n : ℕ) : ℝ))
        atTop (nhds (1 / (b : ℝ) ^ M)) := by
      exact hnorm.comp (tendsto_atTop_atTop_of_monotone (fun a c hac => Nat.mul_le_mul_left k hac)
        (fun N => ⟨N, Nat.le_mul_of_pos_left N hk0⟩))
    have hcard_eq : (1 / (b : ℝ) ^ M) = 1 / ((Fintype.card α : ℝ) ^ q) := by
      rw [hcardα, Nat.cast_pow, ← pow_mul, mul_comm]
    rw [hcard_eq] at hcomp
    refine hcomp.congr (fun n => ?_)
    have hfil_eq : (Finset.range (k * n)).filter (fun t => ∀ idx : Fin M, digitSeq b x (t + idx.1) = wS idx) =
        (Finset.range (k * n)).filter (fun t => W t = S) := by
      ext t
      simp only [Finset.mem_filter]
      exact and_congr_right (fun _ => (hmatch t).symm)
    rw [hfil_eq]
  have hsum_tendsto :
      Tendsto (fun n : ℕ =>
        (k : ℝ) * (∑ S : Fin q → α,
          |((cnt S : ℝ) / (q : ℝ)) - p| *
            ((((Finset.range (k * n)).filter (fun t => W t = S)).card : ℝ) / ((k * n : ℕ) : ℝ))) +
        ((k * q * m : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds ((k : ℝ) * Eq + 0)) := by
    have h1 : Tendsto (fun n : ℕ =>
        ∑ S : Fin q → α,
          |((cnt S : ℝ) / (q : ℝ)) - p| *
            ((((Finset.range (k * n)).filter (fun t => W t = S)).card : ℝ) / ((k * n : ℕ) : ℝ)))
        atTop (nhds (∑ S : Fin q → α, |((cnt S : ℝ) / (q : ℝ)) - p| * (1 / ((Fintype.card α : ℝ) ^ q)))) := by
      exact tendsto_finsetSum _ (fun S _ => tendsto_const_nhds.mul (hfreq S))
    have hEq_rw : ∑ S : Fin q → α, |((cnt S : ℝ) / (q : ℝ)) - p| * (1 / ((Fintype.card α : ℝ) ^ q)) = Eq := by
      rw [← Finset.sum_mul, mul_comm]
    rw [hEq_rw] at h1
    have h2 : Tendsto (fun n : ℕ => ((k * q * m : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    exact (tendsto_const_nhds.mul h1).add h2
  rw [add_zero] at hsum_tendsto
  -- Since k * Eq < ε / 2, eventually the RHS is < ε
  have hδ : 0 < ε - (k : ℝ) * Eq := by linarith
  rw [Metric.tendsto_atTop] at hsum_tendsto
  obtain ⟨N₀, hN₀⟩ := hsum_tendsto (ε - (k : ℝ) * Eq) hδ
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hbound_n :
      (k : ℝ) * (∑ S : Fin q → α,
        |((cnt S : ℝ) / (q : ℝ)) - p| *
          ((((Finset.range (k * n)).filter (fun t => W t = S)).card : ℝ) / ((k * n : ℕ) : ℝ))) +
      ((k * q * m : ℕ) : ℝ) / (n : ℝ) < ε := by
    have hdist := hN₀ n (le_trans (le_max_left _ _) hn)
    rw [Real.dist_eq, abs_lt] at hdist
    linarith
  -- Step 3: show |A(0, n) / n - p| ≤ RHS
  -- First, for any r : ℕ, relate ∑ s < n, cnt (W (r + k * s)) to q * A(r, n)
  let A : ℕ → ℕ := fun r => ((Finset.range n).filter (fun i => occ (r + k * i))).card
  have hAr_bound : ∀ r : ℕ,
      |(A r : ℝ) / (n : ℝ) - p| ≤
        (1 / (n : ℝ)) * (∑ s ∈ Finset.range n, |((cnt (W (r + k * s)) : ℝ) / (q : ℝ)) - p|) +
        ((q * m : ℕ) : ℝ) / (n : ℝ) := by
    intro r
    have hshift : ∀ j : Fin q,
        |(((Finset.range n).filter (fun s => occ (r + k * s + j.1 * L))).card : ℝ) - (A r : ℝ)| ≤
          (q * m : ℝ) := by
      intro j
      -- occ (r + k * s + j * L) = occ (r + k * (s + j * m))
      have hrew : (Finset.range n).filter (fun s => occ (r + k * s + j.1 * L)) =
          (Finset.range n).filter (fun s => occ (r + k * (s + j.1 * m))) := by
        congr 1; ext s
        have : r + k * s + j.1 * L = r + k * (s + j.1 * m) := by dsimp only [L]; ring
        rw [this]
      rw [hrew]
      set d := j.1 * m
      have hd_le : d ≤ q * m := Nat.mul_le_mul_right m (le_of_lt j.2)
      -- Compare card of {s < n | P (s + d)} and {i < n | P i}
      set S1 := (Finset.range n).filter (fun s => occ (r + k * (s + d)))
      set S2 := (Finset.range n).filter (fun i => occ (r + k * i))
      have h12 : S1.card ≤ S2.card + d := by
        let T := S1.image (fun s => s + d)
        have hTcard : T.card = S1.card := Finset.card_image_of_injective _ (add_left_injective d)
        rw [← hTcard]
        have hsub : T ⊆ S2 ∪ Finset.Ico n (n + d) := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
          rcases Finset.mem_filter.mp hs with ⟨hsr, hso⟩
          rw [Finset.mem_range] at hsr
          rw [Finset.mem_union]
          by_cases hlt : s + d < n
          · left; exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hso⟩
          · right; exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        calc T.card ≤ (S2 ∪ Finset.Ico n (n + d)).card := Finset.card_le_card hsub
          _ ≤ S2.card + (Finset.Ico n (n + d)).card := Finset.card_union_le _ _
          _ = S2.card + d := by simp
      have h21 : S2.card ≤ S1.card + d := by
        have hsub : S2 ⊆ Finset.range d ∪ S1.image (fun s => s + d) := by
          intro i hi
          rcases Finset.mem_filter.mp hi with ⟨hir, hio⟩
          rw [Finset.mem_range] at hir
          rw [Finset.mem_union]
          by_cases hlt : i < d
          · left; exact Finset.mem_range.mpr hlt
          · right
            refine Finset.mem_image.mpr ⟨i - d, ?_, by omega⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
            have : i - d + d = i := by omega
            rwa [this]
        have hTcard : (S1.image (fun s => s + d)).card = S1.card :=
          Finset.card_image_of_injective _ (add_left_injective d)
        calc S2.card ≤ (Finset.range d ∪ S1.image (fun s => s + d)).card := Finset.card_le_card hsub
          _ ≤ (Finset.range d).card + (S1.image (fun s => s + d)).card := Finset.card_union_le _ _
          _ = S1.card + d := by rw [Finset.card_range, hTcard, add_comm]
      have hdR : (d : ℝ) ≤ (q * m : ℝ) := by exact_mod_cast hd_le
      have h12R : (S1.card : ℝ) ≤ (S2.card : ℝ) + (d : ℝ) := by exact_mod_cast h12
      have h21R : (S2.card : ℝ) ≤ (S1.card : ℝ) + (d : ℝ) := by exact_mod_cast h21
      rw [abs_le]
      constructor <;> linarith
    -- Sum over s < n of cnt (W (r + k * s)) equals ∑ j : Fin q, #{s < n | occ (r + k * s + j * L)}
    have hsum_cnt : (∑ s ∈ Finset.range n, (cnt (W (r + k * s)) : ℝ)) =
        ∑ j : Fin q, (((Finset.range n).filter (fun s => occ (r + k * s + j.1 * L))).card : ℝ) := by
      simp_rw [hcnt_eq, Finset.card_filter, Nat.cast_sum]
      rw [Finset.sum_comm]
    have hdiff_avg :
        |(A r : ℝ) / (n : ℝ) - (1 / (n : ℝ)) * (∑ s ∈ Finset.range n, (cnt (W (r + k * s)) : ℝ) / (q : ℝ))| ≤
          ((q * m : ℕ) : ℝ) / (n : ℝ) := by
      have hrew : (A r : ℝ) / (n : ℝ) - (1 / (n : ℝ)) * (∑ s ∈ Finset.range n, (cnt (W (r + k * s)) : ℝ) / (q : ℝ)) =
          ((q : ℝ) * (A r : ℝ) - ∑ s ∈ Finset.range n, (cnt (W (r + k * s)) : ℝ)) / ((q : ℝ) * (n : ℝ)) := by
        rw [← Finset.sum_div]
        field_simp [hq_real.ne', hnR.ne']
      rw [hrew, abs_div, abs_of_pos (mul_pos hq_real hnR)]
      have hnum : |(q : ℝ) * (A r : ℝ) - ∑ s ∈ Finset.range n, (cnt (W (r + k * s)) : ℝ)| ≤
          (q : ℝ) * ((q * m : ℕ) : ℝ) := by
        rw [hsum_cnt, abs_sub_comm]
        have hqA : (q : ℝ) * (A r : ℝ) = ∑ _j : Fin q, (A r : ℝ) := by simp
        rw [hqA, ← Finset.sum_sub_distrib]
        calc |∑ j : Fin q, ((((Finset.range n).filter (fun s => occ (r + k * s + j.1 * L))).card : ℝ) - (A r : ℝ))|
            ≤ ∑ j : Fin q, |(((Finset.range n).filter (fun s => occ (r + k * s + j.1 * L))).card : ℝ) - (A r : ℝ)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j : Fin q, (q * m : ℝ) := Finset.sum_le_sum (fun j _ => hshift j)
          _ = (q : ℝ) * ((q * m : ℕ) : ℝ) := by simp [Nat.cast_mul]
      calc |(q : ℝ) * (A r : ℝ) - ∑ s ∈ Finset.range n, (cnt (W (r + k * s)) : ℝ)| / ((q : ℝ) * (n : ℝ))
          ≤ ((q : ℝ) * ((q * m : ℕ) : ℝ)) / ((q : ℝ) * (n : ℝ)) := by gcongr
        _ = ((q * m : ℕ) : ℝ) / (n : ℝ) := by field_simp [hq_real.ne']
    have htri : |(A r : ℝ) / (n : ℝ) - p| ≤
        |(A r : ℝ) / (n : ℝ) - (1 / (n : ℝ)) * (∑ s ∈ Finset.range n, (cnt (W (r + k * s)) : ℝ) / (q : ℝ))| +
        |(1 / (n : ℝ)) * (∑ s ∈ Finset.range n, (cnt (W (r + k * s)) : ℝ) / (q : ℝ)) - p| := by
      simpa [sub_add_sub_cancel] using abs_add_le
        ((A r : ℝ) / (n : ℝ) - (1 / (n : ℝ)) * (∑ s ∈ Finset.range n, (cnt (W (r + k * s)) : ℝ) / (q : ℝ)))
        ((1 / (n : ℝ)) * (∑ s ∈ Finset.range n, (cnt (W (r + k * s)) : ℝ) / (q : ℝ)) - p)
    have havg_p : |(1 / (n : ℝ)) * (∑ s ∈ Finset.range n, (cnt (W (r + k * s)) : ℝ) / (q : ℝ)) - p| ≤
        (1 / (n : ℝ)) * (∑ s ∈ Finset.range n, |((cnt (W (r + k * s)) : ℝ) / (q : ℝ)) - p|) := by
      have hp_sum : p = (1 / (n : ℝ)) * (∑ _s ∈ Finset.range n, p) := by
        simp [hnR.ne']
      conv_lhs => rw [hp_sum, ← mul_sub, ← Finset.sum_sub_distrib]
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hnR)]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    linarith
  -- Sum over r ∈ range k and note A 0 = count for r = 0
  have hA0_le : |(A 0 : ℝ) / (n : ℝ) - p| ≤ ∑ r ∈ Finset.range k, |(A r : ℝ) / (n : ℝ) - p| := by
    exact Finset.single_le_sum (f := fun r => |(A r : ℝ) / (n : ℝ) - p|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hk0)
  -- Bijection (r, s) ↦ r + k * s from range k × range n to range (k * n)
  have hsum_kn :
      ∑ r ∈ Finset.range k, ∑ s ∈ Finset.range n, |((cnt (W (r + k * s)) : ℝ) / (q : ℝ)) - p| =
        ∑ t ∈ Finset.range (k * n), |((cnt (W t) : ℝ) / (q : ℝ)) - p| := by
    rw [← Finset.sum_product']
    refine Finset.sum_nbij' (fun p => p.1 + k * p.2) (fun t => (t % k, t / k)) ?_ ?_ ?_ ?_ ?_
    · intro ⟨r, s⟩ hp
      rcases Finset.mem_product.mp hp with ⟨hr, hs⟩
      rw [Finset.mem_range] at hr hs ⊢
      calc r + k * s < k + k * s := Nat.add_lt_add_right hr _
        _ = k * (s + 1) := by ring
        _ ≤ k * n := Nat.mul_le_mul_left k hs
    · intro t ht
      rw [Finset.mem_range] at ht
      refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt t hk0),
        Finset.mem_range.mpr (Nat.div_lt_of_lt_mul ht)⟩
    · intro ⟨r, s⟩ hp
      rcases Finset.mem_product.mp hp with ⟨hr, _⟩
      rw [Finset.mem_range] at hr
      ext
      · dsimp only
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
      · dsimp only
        rw [Nat.add_mul_div_left _ _ hk0, Nat.div_eq_of_lt hr, zero_add]
    · intro t _
      exact Nat.mod_add_div t k
    · intro _ _
      rfl
  -- Group ∑ t < k*n by S = W t
  have hgroup :
      ∑ t ∈ Finset.range (k * n), |((cnt (W t) : ℝ) / (q : ℝ)) - p| =
        ∑ S : Fin q → α,
          |((cnt S : ℝ) / (q : ℝ)) - p| *
            (((Finset.range (k * n)).filter (fun t => W t = S)).card : ℝ) := by
    symm
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range (k * n)) (t := (Finset.univ : Finset (Fin q → α)))
      (g := W) (fun _ _ => Finset.mem_univ _) (fun t => |((cnt (W t) : ℝ) / (q : ℝ)) - p|)]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    have hcongr : ∑ t ∈ (Finset.range (k * n)).filter (fun t => W t = S), |((cnt (W t) : ℝ) / (q : ℝ)) - p| =
        ∑ _t ∈ (Finset.range (k * n)).filter (fun t => W t = S), |((cnt S : ℝ) / (q : ℝ)) - p| :=
      Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2])
    rw [hcongr, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Combine everything!
  have htotal : |(A 0 : ℝ) / (n : ℝ) - p| ≤
      (k : ℝ) * (∑ S : Fin q → α,
        |((cnt S : ℝ) / (q : ℝ)) - p| *
          ((((Finset.range (k * n)).filter (fun t => W t = S)).card : ℝ) / ((k * n : ℕ) : ℝ))) +
      ((k * q * m : ℕ) : ℝ) / (n : ℝ) := by
    calc |(A 0 : ℝ) / (n : ℝ) - p|
        ≤ ∑ r ∈ Finset.range k, |(A r : ℝ) / (n : ℝ) - p| := hA0_le
      _ ≤ ∑ r ∈ Finset.range k,
            ((1 / (n : ℝ)) * (∑ s ∈ Finset.range n, |((cnt (W (r + k * s)) : ℝ) / (q : ℝ)) - p|) +
              ((q * m : ℕ) : ℝ) / (n : ℝ)) := Finset.sum_le_sum (fun r _ => hAr_bound r)
      _ = (1 / (n : ℝ)) * (∑ r ∈ Finset.range k, ∑ s ∈ Finset.range n, |((cnt (W (r + k * s)) : ℝ) / (q : ℝ)) - p|) +
            ((k * q * m : ℕ) : ℝ) / (n : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ = (k : ℝ) * (∑ S : Fin q → α,
            |((cnt S : ℝ) / (q : ℝ)) - p| *
              ((((Finset.range (k * n)).filter (fun t => W t = S)).card : ℝ) / ((k * n : ℕ) : ℝ))) +
            ((k * q * m : ℕ) : ℝ) / (n : ℝ) := by
          rw [hsum_kn, hgroup]
          congr 1
          simp_rw [← mul_div_assoc, ← Finset.sum_div, Nat.cast_mul]
          field_simp [hk_real.ne', hnR.ne']
  rw [Real.dist_eq]
  have hA0_eq : A 0 = ((Finset.range n).filter (fun i => occ (k * i))).card := by
    dsimp only [A]
    congr 1
    ext i
    simp
  rw [← hA0_eq]
  linarith

end OMA.NormalBasePow

theorem OMA.solution : OMA.R_AlgebraicNormality_irrational_algebraic_absolutely_normal_R1.H2 := by
  intro b k hb hk x hx m w hw
  exact OMA.NormalBasePow.isNormalInBase_pow_aux hb hk hx m w hw
