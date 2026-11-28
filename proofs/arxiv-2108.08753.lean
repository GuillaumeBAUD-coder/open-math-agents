import OMAStatements.S_arxiv_2108_08753
import Mathlib

namespace OMA.P_arxiv_2108_08753

open OMA.S_arxiv_2108_08753

/-- Tait's `X`-set: `{0, 1, ..., m - 1} ⊆ ZMod p` where `m = ⌊√(p / 8)⌋`, so
`(x + z)^2 < 4 m^2 ≤ p / 2` for all `x, z < m`. -/
private def Xset (p : ℕ) : Finset (ZMod p) :=
  (Finset.range (Nat.sqrt (p / 8))).image (fun k : ℕ => (k : ZMod p))

/-- Tait's `Y`-set: `{y : ZMod p | p / 4 < y < p / 2}`, so `p / 2 < y + w < p`
for all `y, w ∈ Yset p`. -/
private def Yset (p : ℕ) : Finset (ZMod p) :=
  (Finset.Ioo (p / 4) (p / 2)).image (fun k : ℕ => (k : ZMod p))

/-- Explicit independent set `I = X × Y` of size `Ω(p^{3/2})` in `Π_p`. -/
private def taitIndep (p : ℕ) : Finset (ZMod p × ZMod p) :=
  Xset p ×ˢ Yset p

private lemma natCast_inj_on_lt {p : ℕ} [NeZero p] {a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have h1 : ((a : ZMod p)).val = ((b : ZMod p)).val := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at h1

private lemma taitIndep_isIndep {p : ℕ} (hp : 100 ≤ p) :
    IsParabolaIndep p (taitIndep p) := by
  have : NeZero p := ⟨by omega⟩
  intro u hu v hv hadj
  rcases Finset.mem_product.mp hu with ⟨huX, huY⟩
  rcases Finset.mem_product.mp hv with ⟨hvX, hvY⟩
  obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp huX
  obtain ⟨z, hz, hzv⟩ := Finset.mem_image.mp hvX
  obtain ⟨y, hy, hyu⟩ := Finset.mem_image.mp huY
  obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hvY
  rw [Finset.mem_range] at hx hz
  rw [Finset.mem_Ioo] at hy hw
  have hsq_le : (Nat.sqrt (p / 8)) ^ 2 ≤ p / 8 := by
    rw [sq]; exact Nat.sqrt_le (p / 8)
  have hxz_sq_lt : (x + z) ^ 2 < p / 2 := by
    have h1 : x + z + 1 ≤ 2 * Nat.sqrt (p / 8) := by omega
    have h2 : (x + z) ^ 2 < (2 * Nat.sqrt (p / 8)) ^ 2 := by nlinarith
    have h3 : (2 * Nat.sqrt (p / 8)) ^ 2 ≤ p / 2 := by
      have : (2 * Nat.sqrt (p / 8)) ^ 2 = 4 * (Nat.sqrt (p / 8)) ^ 2 := by ring
      omega
    omega
  have hyw_gt : p / 2 < y + w := by omega
  have hyw_lt : y + w < p := by omega
  have hxz_lt_p : (x + z) ^ 2 < p := by omega
  have heq : (((x + z) ^ 2 : ℕ) : ZMod p) = ((y + w : ℕ) : ZMod p) := by
    have h2 := hadj.2
    rw [← hxu, ← hzv, ← hyu, ← hwv] at h2
    push_cast
    exact h2
  have hnat : (x + z) ^ 2 = y + w := natCast_inj_on_lt hxz_lt_p hyw_lt heq
  omega

private lemma card_Xset {p : ℕ} (hp : 100 ≤ p) :
    (Xset p).card = Nat.sqrt (p / 8) := by
  have : NeZero p := ⟨by omega⟩
  have hm_le : Nat.sqrt (p / 8) ≤ p :=
    le_trans (Nat.sqrt_le_self _) (Nat.div_le_self _ _)
  rw [Xset, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_range] at ha hb
  exact natCast_inj_on_lt (lt_of_lt_of_le ha hm_le) (lt_of_lt_of_le hb hm_le) hab

private lemma card_Yset {p : ℕ} (hp : 100 ≤ p) :
    (Yset p).card = p / 2 - p / 4 - 1 := by
  have : NeZero p := ⟨by omega⟩
  rw [Yset, Finset.card_image_of_injOn, Nat.card_Ioo]
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_Ioo] at ha hb
  exact natCast_inj_on_lt (by omega) (by omega) hab

private lemma card_taitIndep_lb {p : ℕ} (hp : 1000 ≤ p) :
    (p : ℝ) ^ 6 ≤ (20 * ((taitIndep p).card : ℝ)) ^ 4 := by
  have hcard : (taitIndep p).card = Nat.sqrt (p / 8) * (p / 2 - p / 4 - 1) := by
    rw [taitIndep, Finset.card_product, card_Xset (by omega), card_Yset (by omega)]
  have hm_lb : p / 8 < (Nat.sqrt (p / 8) + 1) ^ 2 := by
    rw [sq]; exact Nat.lt_succ_sqrt (p / 8)
  have hm_ge : p ≤ 10 * (Nat.sqrt (p / 8)) ^ 2 := by
    have hdiv : p ≤ 8 * (p / 8) + 7 := by omega
    have h1 : 10 ≤ Nat.sqrt (p / 8) := by
      rw [Nat.le_sqrt]; omega
    nlinarith
  have hy_ge : p ≤ 5 * (p / 2 - p / 4 - 1) := by omega
  have hnat : p ^ 3 ≤ 250 * (taitIndep p).card ^ 2 := by
    rw [hcard, mul_pow]
    have h1 : p * p ^ 2 ≤ (10 * (Nat.sqrt (p / 8)) ^ 2) * (5 * (p / 2 - p / 4 - 1)) ^ 2 :=
      Nat.mul_le_mul hm_ge (Nat.pow_le_pow_left hy_ge 2)
    have h2 : (10 * (Nat.sqrt (p / 8)) ^ 2) * (5 * (p / 2 - p / 4 - 1)) ^ 2 =
        250 * ((Nat.sqrt (p / 8)) ^ 2 * (p / 2 - p / 4 - 1) ^ 2) := by ring
    linarith
  have hnat2 : p ^ 6 ≤ (20 * (taitIndep p).card) ^ 4 := by
    have hsq : (p ^ 3) ^ 2 ≤ (250 * (taitIndep p).card ^ 2) ^ 2 := Nat.pow_le_pow_left hnat 2
    have h3 : (p ^ 3) ^ 2 = p ^ 6 := by ring
    have h4 : (250 * (taitIndep p).card ^ 2) ^ 2 ≤ (20 * (taitIndep p).card) ^ 4 := by
      have ha : (250 * (taitIndep p).card ^ 2) ^ 2 = 62500 * (taitIndep p).card ^ 4 := by ring
      have hb : (20 * (taitIndep p).card) ^ 4 = 160000 * (taitIndep p).card ^ 4 := by ring
      rw [ha, hb]
      omega
    omega
  exact_mod_cast hnat2

private lemma rpow_five_eighths_pow_four {p : ℕ} :
    (((p * p : ℝ) ^ ((1 / 2 : ℝ) + (1 / 8 : ℝ))) ^ 4) = (p : ℝ) ^ 5 := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hpp0 : (0 : ℝ) ≤ (p : ℝ) * (p : ℝ) := mul_nonneg hp0 hp0
  rw [← Real.rpow_natCast (((p * p : ℝ) ^ ((1 / 2 : ℝ) + (1 / 8 : ℝ)))) 4,
    ← Real.rpow_mul hpp0]
  have hexp : ((1 / 2 : ℝ) + 1 / 8) * (4 : ℕ) = (5 / 2 : ℝ) := by norm_num
  rw [hexp, ← sq (p : ℝ), ← Real.rpow_natCast (p : ℝ) 2, ← Real.rpow_mul hp0]
  have hexp2 : ((2 : ℕ) : ℝ) * (5 / 2 : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
  rw [hexp2, Real.rpow_natCast]

end OMA.P_arxiv_2108_08753

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2108_08753.main) := by
  intro h
  obtain ⟨C, hC⟩ := h (1 / 8 : ℝ) (by norm_num)
  let B : ℕ := max 1000 (Nat.ceil ((20 * max C 1) ^ 4) + 1)
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes B
  have hp1000 : 1000 ≤ p := le_trans (le_max_left _ _) hp_ge
  have hp2 : 2 < p := by omega
  have hbound := hC p hp_prime hp2 (OMA.P_arxiv_2108_08753.taitIndep p)
    (OMA.P_arxiv_2108_08753.taitIndep_isIndep (by omega))
  have hCmax : C ≤ max C 1 := le_max_left C 1
  have hbase_nn : 0 ≤ (p * p : ℝ) ^ ((1 / 2 : ℝ) + (1 / 8 : ℝ)) :=
    Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg p)) _
  have hbound' : (OMA.P_arxiv_2108_08753.taitIndep p).card ≤
      (max C 1) * ((p * p : ℝ) ^ ((1 / 2 : ℝ) + (1 / 8 : ℝ))) :=
    le_trans hbound (mul_le_mul_of_nonneg_right hCmax hbase_nn)
  have h20 : 20 * ((OMA.P_arxiv_2108_08753.taitIndep p).card : ℝ) ≤
      (20 * max C 1) * ((p * p : ℝ) ^ ((1 / 2 : ℝ) + (1 / 8 : ℝ))) := by linarith
  have hpow4 : (20 * ((OMA.P_arxiv_2108_08753.taitIndep p).card : ℝ)) ^ 4 ≤
      ((20 * max C 1) * ((p * p : ℝ) ^ ((1 / 2 : ℝ) + (1 / 8 : ℝ)))) ^ 4 :=
    pow_le_pow_left₀ (by positivity) h20 4
  rw [mul_pow (20 * max C 1), OMA.P_arxiv_2108_08753.rpow_five_eighths_pow_four] at hpow4
  have hlb := OMA.P_arxiv_2108_08753.card_taitIndep_lb hp1000
  have hp6_le : (p : ℝ) ^ 6 ≤ (20 * max C 1) ^ 4 * (p : ℝ) ^ 5 := le_trans hlb hpow4
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (by omega)
  have hp5_pos : (0 : ℝ) < (p : ℝ) ^ 5 := pow_pos hp_pos 5
  have hp_gt : (20 * max C 1) ^ 4 < (p : ℝ) := by
    have h1 : (Nat.ceil ((20 * max C 1) ^ 4) + 1 : ℕ) ≤ p := le_trans (le_max_right _ _) hp_ge
    have h2 : ((Nat.ceil ((20 * max C 1) ^ 4) : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast h1
    have h3 : (20 * max C 1) ^ 4 ≤ (Nat.ceil ((20 * max C 1) ^ 4) : ℝ) := Nat.le_ceil _
    linarith
  have hlt : (20 * max C 1) ^ 4 * (p : ℝ) ^ 5 < (p : ℝ) ^ 6 := by
    have : (p : ℝ) ^ 6 = (p : ℝ) * (p : ℝ) ^ 5 := by ring
    rw [this]
    exact mul_lt_mul_of_pos_right hp_gt hp5_pos
  linarith
