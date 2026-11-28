import FormalConjectures.ErdosProblems.«542»
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Proof of Erdos Problem 542 (Chen 1996). -/

namespace Erdos542Chen

def bands : List (ℕ × ℕ × ℕ) :=
  [(1, 2, 10000), (2, 3, 5000), (3, 5, 1667), (6, 7, 1334), (10, 11, 739),
   (15, 17, 449), (22, 23, 307), (28, 29, 222), (35, 36, 118), (36, 37, 174),
   (58, 59, 57)]

noncomputable def bandSum (m p q : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc (m / q) (m / p), (1 : ℝ) / k

noncomputable def S (m : ℕ) : ℝ :=
  (bands.map fun t => (t.2.2 : ℝ) / 10000 * bandSum m t.1 t.2.1).sum

noncomputable def uncoveredBandSum (n : ℕ) (A : Finset ℕ) (p q : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Ioc (n / q) (n / p)).filter (fun k => ∀ a ∈ A, ¬ a ∣ k), (1 : ℝ) / k

noncomputable def Sa (n : ℕ) (A : Finset ℕ) : ℝ :=
  (bands.map fun t => (t.2.2 : ℝ) / 10000 * uncoveredBandSum n A t.1 t.2.1).sum

private lemma nat_div_antitone {m p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) : m / q ≤ m / p := by
  rw [Nat.le_div_iff_mul_le hp]
  calc
    m / q * p ≤ m / q * q := Nat.mul_le_mul_left _ hpq
    _ = q * (m / q) := mul_comm _ _
    _ ≤ m := Nat.mul_div_le m q

lemma band_identity (n : ℕ) (A : Finset ℕ) (hA : Erdos542.IsLcmFree n A)
    {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    ∑ a ∈ A, (1 : ℝ) / a * bandSum (n / a) p q = bandSum n p q - uncoveredBandSum n A p q := by
  have hq : 0 < q := lt_trans hp hpq
  let s := Finset.Ioc (n / q) (n / p)
  have h_split :
      (∑ k ∈ s.filter (fun k => ¬ ∀ a ∈ A, ¬ a ∣ k), (1 : ℝ) / k) + uncoveredBandSum n A p q =
        bandSum n p q := by
    simpa [uncoveredBandSum, bandSum, s, add_comm] using
      (Finset.sum_filter_add_sum_filter_not s (fun k => ∀ a ∈ A, ¬ a ∣ k) (fun k => (1 : ℝ) / k))
  have h_biUnion :
      s.filter (fun k => ¬ ∀ a ∈ A, ¬ a ∣ k) = A.biUnion (fun a => s.filter (fun k => a ∣ k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_biUnion, not_forall, not_not]
    tauto
  have h_disj : (A : Set ℕ).PairwiseDisjoint (fun a => s.filter (fun k => a ∣ k)) := by
    intro a ha b hb hab
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro k hka hkb
    simp only [Finset.mem_filter, s, Finset.mem_Ioc] at hka hkb
    have hk_pos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hka.1.1
    have hk_le : k ≤ n := le_trans hka.1.2 (Nat.div_le_self n p)
    have hlcm_dvd : Nat.lcm a b ∣ k := Nat.lcm_dvd hka.2 hkb.2
    have hlcm_le : Nat.lcm a b ≤ n := le_trans (Nat.le_of_dvd hk_pos hlcm_dvd) hk_le
    exact absurd (hA.2 ha hb hab) (not_lt.mpr hlcm_le)
  have h_sum_biUnion :
      ∑ k ∈ s.filter (fun k => ¬ ∀ a ∈ A, ¬ a ∣ k), (1 : ℝ) / k =
        ∑ a ∈ A, ∑ k ∈ s.filter (fun k => a ∣ k), (1 : ℝ) / k := by
    rw [h_biUnion, Finset.sum_biUnion h_disj]
  have h_term : ∀ a ∈ A,
      (1 : ℝ) / a * bandSum (n / a) p q = ∑ k ∈ s.filter (fun k => a ∣ k), (1 : ℝ) / k := by
    intro a ha
    have ha_mem : a ∈ Finset.Icc 1 n := hA.1 ha
    have ha_pos : 0 < a := (Finset.mem_Icc.mp ha_mem).1
    rw [bandSum, Finset.mul_sum]
    refine Finset.sum_bij (fun k _ => a * k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Ioc] at hk
      simp only [Finset.mem_filter, s, Finset.mem_Ioc, dvd_mul_right, and_true]
      rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (mul_pos ha_pos hq)] at hk
      rw [Nat.div_div_eq_div_mul, Nat.le_div_iff_mul_le (mul_pos ha_pos hp)] at hk
      constructor
      · rw [Nat.div_lt_iff_lt_mul hq]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hk.1
      · rw [Nat.le_div_iff_mul_le hp]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hk.2
    · intro k₁ _ k₂ _ hk
      exact Nat.mul_left_cancel ha_pos hk
    · intro m hm
      simp only [Finset.mem_filter, s, Finset.mem_Ioc] at hm
      rcases hm.2 with ⟨k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      simp only [Finset.mem_Ioc]
      rw [Nat.div_lt_iff_lt_mul hq, Nat.le_div_iff_mul_le hp] at hm
      rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (mul_pos ha_pos hq),
          Nat.div_div_eq_div_mul, Nat.le_div_iff_mul_le (mul_pos ha_pos hp)]
      constructor
      · simpa [mul_assoc, mul_left_comm, mul_comm] using hm.1.1
      · simpa [mul_assoc, mul_left_comm, mul_comm] using hm.1.2
    · intro k _
      push_cast
      ring
  calc
    ∑ a ∈ A, (1 : ℝ) / a * bandSum (n / a) p q
        = ∑ a ∈ A, ∑ k ∈ s.filter (fun k => a ∣ k), (1 : ℝ) / k := Finset.sum_congr rfl h_term
    _ = ∑ k ∈ s.filter (fun k => ¬ ∀ a ∈ A, ¬ a ∣ k), (1 : ℝ) / k := h_sum_biUnion.symm
    _ = bandSum n p q - uncoveredBandSum n A p q := eq_sub_of_add_eq h_split

private lemma band_list_identity (n : ℕ) (A : Finset ℕ) (hA : Erdos542.IsLcmFree n A)
    (L : List (ℕ × ℕ × ℕ)) (hL : ∀ t ∈ L, 0 < t.1 ∧ t.1 < t.2.1) :
    ∑ a ∈ A, (1 : ℝ) / a * (L.map fun t => (t.2.2 : ℝ) / 10000 * bandSum (n / a) t.1 t.2.1).sum =
      (L.map fun t => (t.2.2 : ℝ) / 10000 * bandSum n t.1 t.2.1).sum -
        (L.map fun t => (t.2.2 : ℝ) / 10000 * uncoveredBandSum n A t.1 t.2.1).sum := by
  induction L with
  | nil => simp
  | cons t ts ih =>
    have ht : 0 < t.1 ∧ t.1 < t.2.1 := hL t (by simp)
    have hts : ∀ s ∈ ts, 0 < s.1 ∧ s.1 < s.2.1 := fun s hs => hL s (by simp [hs])
    simp only [List.map_cons, List.sum_cons]
    have h_dist :
        ∑ a ∈ A, (1 : ℝ) / a *
          ((t.2.2 : ℝ) / 10000 * bandSum (n / a) t.1 t.2.1 +
            (ts.map fun x => (x.2.2 : ℝ) / 10000 * bandSum (n / a) x.1 x.2.1).sum) =
          (t.2.2 : ℝ) / 10000 * (∑ a ∈ A, (1 : ℝ) / a * bandSum (n / a) t.1 t.2.1) +
            ∑ a ∈ A, (1 : ℝ) / a *
              (ts.map fun x => (x.2.2 : ℝ) / 10000 * bandSum (n / a) x.1 x.2.1).sum := by
      have h1 : ∀ a ∈ A,
          (1 : ℝ) / a *
            ((t.2.2 : ℝ) / 10000 * bandSum (n / a) t.1 t.2.1 +
              (ts.map fun x => (x.2.2 : ℝ) / 10000 * bandSum (n / a) x.1 x.2.1).sum) =
          (t.2.2 : ℝ) / 10000 * ((1 : ℝ) / a * bandSum (n / a) t.1 t.2.1) +
            (1 : ℝ) / a * (ts.map fun x => (x.2.2 : ℝ) / 10000 * bandSum (n / a) x.1 x.2.1).sum := by
        intro a _
        ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h_dist, band_identity n A hA ht.1 ht.2, ih hts]
    ring

lemma chen_lemma1 (n : ℕ) (A : Finset ℕ) (hA : Erdos542.IsLcmFree n A) :
    ∑ a ∈ A, (1 : ℝ) / a * S (n / a) = S n - Sa n A :=
  band_list_identity n A hA bands (by decide)

lemma bandSum_75_84_le_one (m : ℕ) : bandSum m 75 84 ≤ 1 := by
  let B := m / 84
  let A' := m / 75
  have h1 : 75 * A' ≤ m := Nat.mul_div_le m 75
  have h2 : m < 84 * (B + 1) := by
    have hdm := Nat.div_add_mod m 84
    have hml := Nat.mod_lt m (by decide : 0 < 84)
    change 84 * B + m % 84 = m at hdm
    omega
  have hA' : A' ≤ 2 * B + 1 := by omega
  have hcard : (Finset.Ioc B A').card ≤ B + 1 := by
    rw [Nat.card_Ioc]
    omega
  have hB_pos : (0 : ℝ) < (B : ℝ) + 1 := by positivity
  have hle : ∀ k ∈ Finset.Ioc B A', (1 : ℝ) / k ≤ 1 / ((B : ℝ) + 1) := by
    intro k hk
    have hk' : B + 1 ≤ k := (Finset.mem_Ioc.mp hk).1
    have hkr : (B : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk'
    exact one_div_le_one_div_of_le hB_pos hkr
  calc
    bandSum m 75 84
        = ∑ k ∈ Finset.Ioc B A', (1 : ℝ) / k := rfl
    _ ≤ ∑ _k ∈ Finset.Ioc B A', (1 : ℝ) / ((B : ℝ) + 1) := Finset.sum_le_sum hle
    _ = ((Finset.Ioc B A').card : ℝ) * (1 / ((B : ℝ) + 1)) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((B : ℝ) + 1) * (1 / ((B : ℝ) + 1)) := by
      gcongr
      exact_mod_cast hcard
    _ = 1 := mul_one_div_cancel (ne_of_gt hB_pos)

lemma chen_lemma4 {n u v k : ℕ} {A : Finset ℕ} (hA : Erdos542.IsLcmFree n A)
    (hu : 0 < u) (hv : 0 < v) (huv : Nat.Coprime u v) (hk : 0 < k)
    (huvk : u * v * k ≤ n) (hunc : ∀ a ∈ A, ¬ a ∣ k) :
    (∀ a ∈ A, ¬ a ∣ u * k) ∨ (∀ a ∈ A, ¬ a ∣ v * k) := by
  by_contra h
  push Not at h
  rcases h with ⟨⟨a, ha, ha_dvd⟩, ⟨b, hb, hb_dvd⟩⟩
  have hlcm_dvd : Nat.lcm a b ∣ Nat.lcm (u * k) (v * k) :=
    Nat.lcm_dvd (ha_dvd.trans (Nat.dvd_lcm_left _ _)) (hb_dvd.trans (Nat.dvd_lcm_right _ _))
  have hlcm_eq : Nat.lcm (u * k) (v * k) = u * v * k := by
    rw [mul_comm u k, mul_comm v k, Nat.lcm_mul_left, huv.lcm_eq_mul]
    ring
  have hpos : 0 < u * v * k := mul_pos (mul_pos hu hv) hk
  have hlcm_le : Nat.lcm a b ≤ n := by
    rw [hlcm_eq] at hlcm_dvd
    exact le_trans (Nat.le_of_dvd hpos hlcm_dvd) huvk
  have hab : a = b := by
    by_contra hne
    exact absurd (hA.2 ha hb hne) (not_lt.mpr hlcm_le)
  subst hab
  have hgcd_eq : Nat.gcd (u * k) (v * k) = k := by
    rw [mul_comm u k, mul_comm v k, Nat.gcd_mul_left, huv.gcd_eq_one, mul_one]
  have ha_dvd_k : a ∣ k := by
    rw [← hgcd_eq]
    exact Nat.dvd_gcd ha_dvd hb_dvd
  exact hunc a ha ha_dvd_k

private lemma uncoveredBandSum_nonneg (n : ℕ) (A : Finset ℕ) (p q : ℕ) :
    0 ≤ uncoveredBandSum n A p q := by
  unfold uncoveredBandSum
  positivity

lemma Sa_lower_bound (n : ℕ) (A : Finset ℕ) (hA : Erdos542.IsLcmFree n A) :
    (3 : ℝ) / 500 * uncoveredBandSum n A 75 84 ≤ Sa n A := by
  have hSa_ge :
      (449 : ℝ) / 10000 * uncoveredBandSum n A 15 17 +
          (1334 : ℝ) / 10000 * uncoveredBandSum n A 6 7 ≤ Sa n A := by
    simp only [Sa, bands, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have h0 := uncoveredBandSum_nonneg n A 1 2
    have h1 := uncoveredBandSum_nonneg n A 2 3
    have h2 := uncoveredBandSum_nonneg n A 3 5
    have h4 := uncoveredBandSum_nonneg n A 10 11
    have h6 := uncoveredBandSum_nonneg n A 22 23
    have h7 := uncoveredBandSum_nonneg n A 28 29
    have h8 := uncoveredBandSum_nonneg n A 35 36
    have h9 := uncoveredBandSum_nonneg n A 36 37
    have h10 := uncoveredBandSum_nonneg n A 58 59
    linarith
  let U := (Finset.Ioc (n / 84) (n / 75)).filter (fun k => ∀ a ∈ A, ¬ a ∣ k)
  let U1 := U.filter (fun k => ∀ a ∈ A, ¬ a ∣ 5 * k)
  let U2 := U.filter (fun k => ¬ ∀ a ∈ A, ¬ a ∣ 5 * k)
  have hU_split :
      uncoveredBandSum n A 75 84 =
        (∑ k ∈ U1, (1 : ℝ) / k) + (∑ k ∈ U2, (1 : ℝ) / k) := by
    simpa [uncoveredBandSum, U, U1, U2] using
      (Finset.sum_filter_add_sum_filter_not U (fun k => ∀ a ∈ A, ¬ a ∣ 5 * k) (fun k => (1 : ℝ) / k)).symm
  have hU1_le : ∑ k ∈ U1, (1 : ℝ) / k ≤ 5 * uncoveredBandSum n A 15 17 := by
    have h_sub :
        U1.image (fun k => 5 * k) ⊆
          (Finset.Ioc (n / 17) (n / 15)).filter (fun m => ∀ a ∈ A, ¬ a ∣ m) := by
      intro m hm
      rw [Finset.mem_image] at hm
      rcases hm with ⟨k, hk, rfl⟩
      simp only [U1, U, Finset.mem_filter, Finset.mem_Ioc] at hk
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, hk.2⟩
      · rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 17)]
        have hk1 := (Nat.div_lt_iff_lt_mul (by decide : 0 < 84)).mp hk.1.1.1
        omega
      · rw [Nat.le_div_iff_mul_le (by decide : 0 < 15)]
        have hk2 := (Nat.le_div_iff_mul_le (by decide : 0 < 75)).mp hk.1.1.2
        omega
    have h_img :
        ∑ m ∈ U1.image (fun k : ℕ => 5 * k), (1 : ℝ) / (m : ℝ) =
          ∑ k ∈ U1, (1 : ℝ) / ((5 * k : ℕ) : ℝ) := by
      refine Finset.sum_image ?_
      intro k₁ _ k₂ _ hk
      dsimp only at hk
      omega
    have h_le : ∑ k ∈ U1, (1 : ℝ) / ((5 * k : ℕ) : ℝ) ≤ uncoveredBandSum n A 15 17 := by
      rw [← h_img]
      exact Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun m _ _ => by positivity)
    have h_eq : ∑ k ∈ U1, (1 : ℝ) / k = 5 * ∑ k ∈ U1, (1 : ℝ) / ((5 * k : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    rw [h_eq]
    linarith
  have hU2_le : ∑ k ∈ U2, (1 : ℝ) / k ≤ 12 * uncoveredBandSum n A 6 7 := by
    have h_sub :
        U2.image (fun k => 12 * k) ⊆
          (Finset.Ioc (n / 7) (n / 6)).filter (fun m => ∀ a ∈ A, ¬ a ∣ m) := by
      intro m hm
      rw [Finset.mem_image] at hm
      rcases hm with ⟨k, hk, rfl⟩
      simp only [U2, U, Finset.mem_filter, Finset.mem_Ioc] at hk
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      have hk_pos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hk.1.1.1
      have hk2 : k * 75 ≤ n := (Nat.le_div_iff_mul_le (by decide : 0 < 75)).mp hk.1.1.2
      have h_not12 : ∀ a ∈ A, ¬ a ∣ 12 * k := by
        have h4 := chen_lemma4 hA (by decide : 0 < 5) (by decide : 0 < 12) (by decide : Nat.Coprime 5 12)
          hk_pos (by omega : 5 * 12 * k ≤ n) hk.1.2
        exact h4.resolve_left hk.2
      refine ⟨⟨?_, ?_⟩, h_not12⟩
      · rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 7)]
        have hk1 := (Nat.div_lt_iff_lt_mul (by decide : 0 < 84)).mp hk.1.1.1
        omega
      · rw [Nat.le_div_iff_mul_le (by decide : 0 < 6)]
        omega
    have h_img :
        ∑ m ∈ U2.image (fun k : ℕ => 12 * k), (1 : ℝ) / (m : ℝ) =
          ∑ k ∈ U2, (1 : ℝ) / ((12 * k : ℕ) : ℝ) := by
      refine Finset.sum_image ?_
      intro k₁ _ k₂ _ hk
      dsimp only at hk
      omega
    have h_le : ∑ k ∈ U2, (1 : ℝ) / ((12 * k : ℕ) : ℝ) ≤ uncoveredBandSum n A 6 7 := by
      rw [← h_img]
      exact Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun m _ _ => by positivity)
    have h_eq : ∑ k ∈ U2, (1 : ℝ) / k = 12 * ∑ k ∈ U2, (1 : ℝ) / ((12 * k : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    rw [h_eq]
    linarith
  have hv1 : 0 ≤ uncoveredBandSum n A 15 17 := uncoveredBandSum_nonneg n A 15 17
  have hv2 : 0 ≤ uncoveredBandSum n A 6 7 := uncoveredBandSum_nonneg n A 6 7
  linarith

lemma main_reduction (n : ℕ) (A : Finset ℕ) (hA : Erdos542.IsLcmFree n A)
    (hS1 : ∀ m, 1 ≤ m → (1 : ℝ) ≤ S m) (hS75 : ∀ m, 75 ≤ m → (1 : ℝ) + 3 / 500 ≤ S m) :
    ∑ a ∈ A, (1 : ℝ) / a ≤ S n - (3 : ℝ) / 500 * bandSum n 75 84 := by
  have h_pt : ∀ a ∈ A,
      (1 : ℝ) / a + (3 : ℝ) / 500 * ((1 : ℝ) / a * bandSum (n / a) 75 84) ≤ (1 : ℝ) / a * S (n / a) := by
    intro a ha
    have ha_mem := Finset.mem_Icc.mp (hA.1 ha)
    have ha_pos : 0 < a := ha_mem.1
    have hdiv_pos : 1 ≤ n / a := Nat.div_pos ha_mem.2 ha_pos
    have ha_inv_nonneg : (0 : ℝ) ≤ (1 : ℝ) / a := by positivity
    by_cases h75 : 75 ≤ n / a
    · have hS := hS75 (n / a) h75
      have hb := bandSum_75_84_le_one (n / a)
      have h1 : (1 : ℝ) + 3 / 500 * bandSum (n / a) 75 84 ≤ S (n / a) := by linarith
      calc
        (1 : ℝ) / a + (3 : ℝ) / 500 * ((1 : ℝ) / a * bandSum (n / a) 75 84)
            = (1 : ℝ) / a * (1 + 3 / 500 * bandSum (n / a) 75 84) := by ring
        _ ≤ (1 : ℝ) / a * S (n / a) := mul_le_mul_of_nonneg_left h1 ha_inv_nonneg
    · have hlt : n / a < 75 := not_le.mp h75
      have hb0 : bandSum (n / a) 75 84 = 0 := by
        simp [bandSum, Nat.div_eq_of_lt hlt]
      have hS := hS1 (n / a) hdiv_pos
      have h1 : (1 : ℝ) / a * 1 ≤ (1 : ℝ) / a * S (n / a) :=
        mul_le_mul_of_nonneg_left hS ha_inv_nonneg
      rw [hb0]
      linarith
  have h_sum := Finset.sum_le_sum h_pt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h_sum
  have hid := band_identity n A hA (by decide : 0 < 75) (by decide : 75 < 84)
  have hcl1 := chen_lemma1 n A hA
  have hlb := Sa_lower_bound n A hA
  linarith

lemma harmonic_ge_log {B A : ℕ} (hBA : B ≤ A) :
    Real.log (((A : ℝ) + 1) / ((B : ℝ) + 1)) ≤ ∑ k ∈ Finset.Ioc B A, (1 : ℝ) / k := by
  induction A, hBA using Nat.le_induction with
  | base =>
    have hpos : (0 : ℝ) < (B : ℝ) + 1 := by positivity
    rw [div_self hpos.ne', Real.log_one, Finset.Ioc_self, Finset.sum_empty]
  | succ A hBA ih =>
    have hIoc : Finset.Ioc B (A + 1) = insert (A + 1) (Finset.Ioc B A) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    rw [hIoc, Finset.sum_insert (by simp)]
    have hstep : Real.log (((A : ℝ) + 2) / ((A : ℝ) + 1)) ≤ 1 / ((A : ℝ) + 1) := by
      have hle := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < ((A : ℝ) + 2) / ((A : ℝ) + 1))
      have heq : ((A : ℝ) + 2) / ((A : ℝ) + 1) - 1 = 1 / ((A : ℝ) + 1) := by
        field_simp
        ring
      linarith
    have hlog : Real.log ((((A + 1 : ℕ) : ℝ) + 1) / ((B : ℝ) + 1)) =
        Real.log (((A : ℝ) + 2) / ((A : ℝ) + 1)) + Real.log (((A : ℝ) + 1) / ((B : ℝ) + 1)) := by
      push_cast
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    push_cast at hlog ⊢
    linarith

lemma harmonic_le_log {B A : ℕ} (hB : 1 ≤ B) (hBA : B ≤ A) :
    ∑ k ∈ Finset.Ioc B A, (1 : ℝ) / k ≤ Real.log ((A : ℝ) / (B : ℝ)) := by
  induction A, hBA using Nat.le_induction with
  | base =>
    have hpos : (0 : ℝ) < (B : ℝ) := by positivity
    rw [div_self hpos.ne', Real.log_one, Finset.Ioc_self, Finset.sum_empty]
  | succ A hBA ih =>
    have hA : (0 : ℝ) < (A : ℝ) := by
      have : 1 ≤ A := le_trans hB hBA
      positivity
    have hIoc : Finset.Ioc B (A + 1) = insert (A + 1) (Finset.Ioc B A) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    rw [hIoc, Finset.sum_insert (by simp)]
    have hstep : 1 / ((A : ℝ) + 1) ≤ Real.log (((A : ℝ) + 1) / (A : ℝ)) := by
      have hle := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (A : ℝ) / ((A : ℝ) + 1))
      have hinv : Real.log ((A : ℝ) / ((A : ℝ) + 1)) = -Real.log (((A : ℝ) + 1) / (A : ℝ)) := by
        rw [← Real.log_inv]
        congr 1
        field_simp
      have heq : (A : ℝ) / ((A : ℝ) + 1) - 1 = -(1 / ((A : ℝ) + 1)) := by
        field_simp
        ring
      linarith
    have hlog : Real.log (((A + 1 : ℕ) : ℝ) / (B : ℝ)) =
        Real.log (((A : ℝ) + 1) / (A : ℝ)) + Real.log ((A : ℝ) / (B : ℝ)) := by
      push_cast
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    push_cast at hlog ⊢
    linarith

lemma bandSum_ge_log (m : ℕ) {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    Real.log ((q : ℝ) / p) - ((q : ℝ) - 1) / ((m : ℝ) + 1) ≤ bandSum m p q := by
  have hq0 : 0 < q := lt_trans hp hpq
  have hBA : m / q ≤ m / p := nat_div_antitone hp hpq.le
  have hharm := harmonic_ge_log hBA
  change Real.log ((((m / p : ℕ) : ℝ) + 1) / (((m / q : ℕ) : ℝ) + 1)) ≤ bandSum m p q at hharm
  have hpR : (0 : ℝ) < p := by positivity
  have hqR : (0 : ℝ) < q := by positivity
  have hm_p_nat : m + 1 ≤ (m / p + 1) * p := by
    have h1 := Nat.div_add_mod m p
    have h2 := Nat.mod_lt m hp
    nlinarith
  have hm_p : ((m : ℝ) + 1) / (p : ℝ) ≤ ((m / p : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ hpR]
    exact_mod_cast hm_p_nat
  have hm_q_nat : (m / q + 1) * q ≤ m + q := by
    have h1 := Nat.mul_div_le m q
    nlinarith
  have hm_q : ((m / q : ℕ) : ℝ) + 1 ≤ ((m : ℝ) + (q : ℝ)) / (q : ℝ) := by
    rw [le_div_iff₀ hqR]
    exact_mod_cast hm_q_nat
  have hratio : ((q : ℝ) / p) * (((m : ℝ) + 1) / ((m : ℝ) + q)) ≤
      (((m / p : ℕ) : ℝ) + 1) / (((m / q : ℕ) : ℝ) + 1) := by
    have heq : ((q : ℝ) / p) * (((m : ℝ) + 1) / ((m : ℝ) + q)) =
        (((m : ℝ) + 1) / (p : ℝ)) / (((m : ℝ) + (q : ℝ)) / (q : ℝ)) := by
      field_simp
    rw [heq]
    gcongr
  have hlog_le := Real.log_le_log (by positivity) hratio
  have hlog_mul : Real.log (((q : ℝ) / p) * (((m : ℝ) + 1) / ((m : ℝ) + q))) =
      Real.log ((q : ℝ) / p) - Real.log (((m : ℝ) + q) / ((m : ℝ) + 1)) := by
    rw [Real.log_mul (by positivity) (by positivity), sub_eq_add_neg]
    congr 1
    rw [← Real.log_inv]
    congr 1
    field_simp
  have hlog_err : Real.log (((m : ℝ) + q) / ((m : ℝ) + 1)) ≤ ((q : ℝ) - 1) / ((m : ℝ) + 1) := by
    have hle := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < ((m : ℝ) + q) / ((m : ℝ) + 1))
    have heq : ((m : ℝ) + q) / ((m : ℝ) + 1) - 1 = ((q : ℝ) - 1) / ((m : ℝ) + 1) := by
      field_simp
      ring
    linarith
  linarith

lemma bandSum_le_log {m p q : ℕ} (hp : 0 < p) (hpq : p < q) (hqm : q ≤ m) :
    bandSum m p q ≤ Real.log ((q : ℝ) / p) + ((q : ℝ) - 1) / ((m : ℝ) - ((q : ℝ) - 1)) := by
  have hq0 : 0 < q := lt_trans hp hpq
  have hB : 1 ≤ m / q := Nat.div_pos hqm hq0
  have hBA : m / q ≤ m / p := nat_div_antitone hp hpq.le
  have hharm := harmonic_le_log hB hBA
  change bandSum m p q ≤ Real.log (((m / p : ℕ) : ℝ) / ((m / q : ℕ) : ℝ)) at hharm
  have hpR : (0 : ℝ) < p := by positivity
  have hqR : (0 : ℝ) < q := by positivity
  have hm0 : 0 < m := lt_of_lt_of_le hq0 hqm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmqR : (0 : ℝ) < ((m / q : ℕ) : ℝ) := by exact_mod_cast hB
  have hmpR : (0 : ℝ) < ((m / p : ℕ) : ℝ) := by exact_mod_cast le_trans hB hBA
  have hsubR : (0 : ℝ) < (m : ℝ) - ((q : ℝ) - 1) := by
    have : (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hqm
    linarith
  have hm_p_nat : (m / p) * p ≤ m := by
    rw [mul_comm]
    exact Nat.mul_div_le m p
  have hm_p : ((m / p : ℕ) : ℝ) ≤ (m : ℝ) / (p : ℝ) := by
    rw [le_div_iff₀ hpR]
    exact_mod_cast hm_p_nat
  have hm_q_nat : m + 1 ≤ (m / q) * q + q := by
    have h1 := Nat.div_add_mod m q
    have h2 := Nat.mod_lt m hq0
    nlinarith
  have hm_q : ((m : ℝ) - ((q : ℝ) - 1)) / (q : ℝ) ≤ ((m / q : ℕ) : ℝ) := by
    rw [div_le_iff₀ hqR]
    have hcast : (m : ℝ) + 1 ≤ ((m / q : ℕ) : ℝ) * (q : ℝ) + (q : ℝ) := by exact_mod_cast hm_q_nat
    linarith
  have hratio : ((m / p : ℕ) : ℝ) / ((m / q : ℕ) : ℝ) ≤
      ((q : ℝ) / p) * ((m : ℝ) / ((m : ℝ) - ((q : ℝ) - 1))) := by
    have heq : ((q : ℝ) / p) * ((m : ℝ) / ((m : ℝ) - ((q : ℝ) - 1))) =
        ((m : ℝ) / (p : ℝ)) / (((m : ℝ) - ((q : ℝ) - 1)) / (q : ℝ)) := by
      field_simp [hsubR.ne']
    rw [heq]
    gcongr
  have hlog_le := Real.log_le_log (div_pos hmpR hmqR) hratio
  have hlog_mul : Real.log (((q : ℝ) / p) * ((m : ℝ) / ((m : ℝ) - ((q : ℝ) - 1)))) =
      Real.log ((q : ℝ) / p) + Real.log ((m : ℝ) / ((m : ℝ) - ((q : ℝ) - 1))) := by
    rw [Real.log_mul (div_pos hqR hpR).ne' (div_pos hmR hsubR).ne']
  have hlog_err : Real.log ((m : ℝ) / ((m : ℝ) - ((q : ℝ) - 1))) ≤
      ((q : ℝ) - 1) / ((m : ℝ) - ((q : ℝ) - 1)) := by
    have hle := Real.log_le_sub_one_of_pos (div_pos hmR hsubR)
    have heq : (m : ℝ) / ((m : ℝ) - ((q : ℝ) - 1)) - 1 =
        ((q : ℝ) - 1) / ((m : ℝ) - ((q : ℝ) - 1)) := by
      field_simp [hsubR.ne']
      ring
    linarith
  linarith

lemma log_div_bounds {p q : ℝ} (hp : 0 < p) (hpq : p < q) (m : ℕ) :
    (∑ i ∈ Finset.range m, ((q - p) / q) ^ (i + 1) / (i + 1)) -
      ((q - p) / q) ^ (m + 1) / (1 - (q - p) / q) ≤ Real.log (q / p) ∧
    Real.log (q / p) ≤
      (∑ i ∈ Finset.range m, ((q - p) / q) ^ (i + 1) / (i + 1)) +
      ((q - p) / q) ^ (m + 1) / (1 - (q - p) / q) := by
  have hq : 0 < q := lt_trans hp hpq
  have hx0 : 0 ≤ (q - p) / q := by
    apply div_nonneg (by linarith) hq.le
  have hx1 : (q - p) / q < 1 := by
    rw [div_lt_one hq]
    linarith
  have hax : |(q - p) / q| = (q - p) / q := abs_of_nonneg hx0
  have z := Real.abs_log_sub_add_sum_range_le (x := (q - p) / q) (by rw [hax]; exact hx1) m
  rw [hax] at z
  have h1mx : 1 - (q - p) / q = (q / p)⁻¹ := by
    field_simp
    ring
  rw [h1mx, Real.log_inv, ← sub_eq_add_neg] at z
  rw [← h1mx] at z
  have hbounds := abs_le.mp z
  constructor <;> linarith

private lemma log_div_sandwich3 {p q lo hi : ℝ} (hp : 0 < p) (hpq : p < q)
    (hlo : lo ≤ ((q - p) / q) + ((q - p) / q) ^ 2 / 2 + ((q - p) / q) ^ 3 / 3 -
      ((q - p) / q) ^ 4 / (1 - (q - p) / q))
    (hhi : ((q - p) / q) + ((q - p) / q) ^ 2 / 2 + ((q - p) / q) ^ 3 / 3 +
      ((q - p) / q) ^ 4 / (1 - (q - p) / q) ≤ hi) :
    lo ≤ Real.log (q / p) ∧ Real.log (q / p) ≤ hi := by
  have h := log_div_bounds hp hpq 3
  have hsum : (∑ i ∈ Finset.range 3, ((q - p) / q) ^ (i + 1) / (i + 1)) =
      ((q - p) / q) + ((q - p) / q) ^ 2 / 2 + ((q - p) / q) ^ 3 / 3 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, pow_one]
    ring
  have hexp : (3 : ℕ) + 1 = 4 := rfl
  rw [hsum, hexp] at h
  exact ⟨le_trans hlo h.1, le_trans h.2 hhi⟩

lemma C_const_bounds :
    (10172 : ℝ) / 10000 ≤ (bands.map fun t => (t.2.2 : ℝ) / 10000 * Real.log ((t.2.1 : ℝ) / t.1)).sum ∧
    (bands.map fun t => (t.2.2 : ℝ) / 10000 * Real.log ((t.2.1 : ℝ) / t.1)).sum ≤ (10174 : ℝ) / 10000 := by
  simp only [bands, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  norm_num
  have h2_gt := Real.log_two_gt_d9
  have h2_lt := Real.log_two_lt_d9
  have h3_gt := Real.log_three_gt_d9
  have h3_lt := Real.log_three_lt_d9
  have h5_gt := Real.log_five_gt_d9
  have h5_lt := Real.log_five_lt_d9
  have h32 : Real.log ((3 : ℝ) / 2) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  have h53 : Real.log ((5 : ℝ) / 3) = Real.log 5 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  have hb1_lo : (693147 : ℝ) / 1000000 ≤ Real.log 2 := by linarith only [h2_gt]
  have hb1_hi : Real.log 2 ≤ (693148 : ℝ) / 1000000 := by linarith only [h2_lt]
  have hb2_lo : (405465 : ℝ) / 1000000 ≤ Real.log ((3 : ℝ) / 2) := by
    linarith only [h32, h3_gt, h2_lt]
  have hb2_hi : Real.log ((3 : ℝ) / 2) ≤ (405466 : ℝ) / 1000000 := by
    linarith only [h32, h3_lt, h2_gt]
  have hb3_lo : (510825 : ℝ) / 1000000 ≤ Real.log ((5 : ℝ) / 3) := by
    linarith only [h53, h5_gt, h3_lt]
  have hb3_hi : Real.log ((5 : ℝ) / 3) ≤ (510826 : ℝ) / 1000000 := by
    linarith only [h53, h5_lt, h3_gt]
  have hb6 := log_div_sandwich3 (p := 6) (q := 7) (lo := 153547 / 1000000) (hi := 154519 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb10 := log_div_sandwich3 (p := 10) (q := 11) (lo := 95216 / 1000000) (hi := 95367 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb15 := log_div_sandwich3 (p := 15) (q := 17) (lo := 124893 / 1000000) (hi := 125328 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb22 := log_div_sandwich3 (p := 22) (q := 23) (lo := 44447 / 1000000) (hi := 44455 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb28 := log_div_sandwich3 (p := 28) (q := 29) (lo := 35089 / 1000000) (hi := 35093 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb35 := log_div_sandwich3 (p := 35) (q := 36) (lo := 28170 / 1000000) (hi := 28172 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb36 := log_div_sandwich3 (p := 36) (q := 37) (lo := 27398 / 1000000) (hi := 27400 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb58 := log_div_sandwich3 (p := 58) (q := 59) (lo := 17094 / 1000000) (hi := 17095 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · linarith only [hb1_lo, hb2_lo, hb3_lo, hb6.1, hb10.1, hb15.1, hb22.1, hb28.1, hb35.1, hb36.1, hb58.1]
  · linarith only [hb1_hi, hb2_hi, hb3_hi, hb6.2, hb10.2, hb15.2, hb22.2, hb28.2, hb35.2, hb36.2, hb58.2]

private lemma list_sum_le_sum {α : Type*} (l : List α) (f g : α → ℝ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem a hx))

private lemma list_sum_sub {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map fun t => f t - g t).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

private lemma list_sum_add {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map fun t => f t + g t).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

private lemma list_sum_div {α : Type*} (l : List α) (f : α → ℝ) (c : ℝ) :
    (l.map fun t => f t / c).sum = (l.map f).sum / c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

private lemma bands_prop : ∀ t ∈ bands, 0 < t.1 ∧ t.1 < t.2.1 ∧ t.2.1 ≤ 59 := by decide

lemma S_ge_large {m : ℕ} (hm : 678 ≤ m) : (1 : ℝ) + 3 / 500 ≤ S m := by
  have hC := C_const_bounds.1
  have hS_lb : (bands.map fun t => (t.2.2 : ℝ) / 10000 * Real.log ((t.2.1 : ℝ) / t.1) -
      ((t.2.2 : ℝ) / 10000 * ((t.2.1 : ℝ) - 1)) / ((m : ℝ) + 1)).sum ≤ S m := by
    unfold S
    refine list_sum_le_sum bands _ _ fun t ht => ?_
    obtain ⟨hp, hpq, _⟩ := bands_prop t ht
    have hband := bandSum_ge_log m hp hpq
    have hw : (0 : ℝ) ≤ (t.2.2 : ℝ) / 10000 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hband hw
    have heq : (t.2.2 : ℝ) / 10000 * (Real.log ((t.2.1 : ℝ) / t.1) - ((t.2.1 : ℝ) - 1) / (m + 1)) =
        (t.2.2 : ℝ) / 10000 * Real.log ((t.2.1 : ℝ) / t.1) -
          ((t.2.2 : ℝ) / 10000 * ((t.2.1 : ℝ) - 1)) / ((m : ℝ) + 1) := by ring
    linarith only [hmul, heq]
  rw [list_sum_sub, list_sum_div] at hS_lb
  have herr_sum : (bands.map fun t => (t.2.2 : ℝ) / 10000 * ((t.2.1 : ℝ) - 1)).sum = 18979 / 2500 := by
    simp only [bands, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    norm_num
  rw [herr_sum] at hS_lb
  have hmR : (679 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (678 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hdiv : (18979 : ℝ) / 2500 / ((m : ℝ) + 1) ≤ 18979 / 2500 / 679 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmR
  linarith only [hC, hS_lb, hdiv]

lemma final_bound {n : ℕ} (hn : 172509 < n) :
    S n - (3 : ℝ) / 500 * bandSum n 75 84 < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11 := by
  have hn1 : 172510 ≤ n := hn
  have hnR : (172510 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hC := C_const_bounds.2
  have hS_ub : S n ≤ (bands.map fun t => (t.2.2 : ℝ) / 10000 * Real.log ((t.2.1 : ℝ) / t.1) +
      ((t.2.2 : ℝ) / 10000 * ((t.2.1 : ℝ) - 1)) / (172510 - 58)).sum := by
    unfold S
    refine list_sum_le_sum bands _ _ fun t ht => ?_
    obtain ⟨hp, hpq, hq59⟩ := bands_prop t ht
    have hband := bandSum_le_log hp hpq (le_trans hq59 (by omega : 59 ≤ n))
    have hq1 : (0 : ℝ) ≤ (t.2.1 : ℝ) - 1 := by
      have : 1 ≤ t.2.1 := by omega
      have : (1 : ℝ) ≤ t.2.1 := by exact_mod_cast this
      linarith
    have hq59R : (t.2.1 : ℝ) ≤ 59 := by exact_mod_cast hq59
    have hdiv : ((t.2.1 : ℝ) - 1) / ((n : ℝ) - ((t.2.1 : ℝ) - 1)) ≤ ((t.2.1 : ℝ) - 1) / (172510 - 58) :=
      div_le_div_of_nonneg_left hq1 (by norm_num) (by linarith only [hnR, hq59R])
    have hw : (0 : ℝ) ≤ (t.2.2 : ℝ) / 10000 := by positivity
    have hband' : bandSum n t.1 t.2.1 ≤
        Real.log ((t.2.1 : ℝ) / t.1) + ((t.2.1 : ℝ) - 1) / (172510 - 58) := by
      linarith only [hband, hdiv]
    have hmul := mul_le_mul_of_nonneg_left hband' hw
    have heq : (t.2.2 : ℝ) / 10000 * (Real.log ((t.2.1 : ℝ) / t.1) + ((t.2.1 : ℝ) - 1) / (172510 - 58)) =
        (t.2.2 : ℝ) / 10000 * Real.log ((t.2.1 : ℝ) / t.1) +
          ((t.2.2 : ℝ) / 10000 * ((t.2.1 : ℝ) - 1)) / (172510 - 58) := by ring
    linarith only [hmul, heq]
  rw [list_sum_add, list_sum_div] at hS_ub
  have herr_sum : (bands.map fun t => (t.2.2 : ℝ) / 10000 * ((t.2.1 : ℝ) - 1)).sum = 18979 / 2500 := by
    simp only [bands, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    norm_num
  rw [herr_sum] at hS_ub
  have h75 : Real.log ((28 : ℝ) / 25) - 83 / 172511 ≤ bandSum n 75 84 := by
    have h := bandSum_ge_log n (p := 75) (q := 84) (by norm_num) (by norm_num)
    have hdiv : ((84 : ℝ) - 1) / ((n : ℝ) + 1) ≤ ((84 : ℝ) - 1) / 172511 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hnR])
    norm_num at h hdiv
    linarith only [h, hdiv]
  have hlog75 := (log_div_bounds (p := 25) (q := 28) (by norm_num) (by norm_num) 2).1
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at hlog75
  norm_num at hlog75
  have hlog75_round : (1115 : ℝ) / 10000 ≤ Real.log ((28 : ℝ) / 25) := by linarith only [hlog75]
  have h75_lb : (1115 : ℝ) / 10000 - 83 / 172511 ≤ bandSum n 75 84 := by
    linarith only [h75, hlog75_round]
  linarith only [hC, hS_ub, h75_lb]

inductive T10
  | leaf (v : ℕ)
  | node (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : T10)

def T10.pick : T10 → ℕ → T10
  | .leaf v, _ => .leaf v
  | .node c0 c1 c2 c3 c4 c5 c6 c7 c8 c9, d =>
    match d with
    | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3 | 4 => c4
    | 5 => c5 | 6 => c6 | 7 => c7 | 8 => c8 | _ => c9

def T10.val : T10 → ℕ
  | .leaf v => v
  | .node c0 _ _ _ _ _ _ _ _ _ => c0.val

private def pZero : T10 :=
  let z1 := T10.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0)
  .node z1 z1 z1 z1 z1 z1 z1 z1 z1 z1

def pTable : T10 := .node
  (.node
    (.node (.leaf 0) (.leaf 1000000) (.leaf 1500000) (.leaf 1833333) (.leaf 2083333) (.leaf 2283333) (.leaf 2449999) (.leaf 2592856) (.leaf 2717856) (.leaf 2828967))
    (.node (.leaf 2928967) (.leaf 3019876) (.leaf 3103209) (.leaf 3180132) (.leaf 3251560) (.leaf 3318226) (.leaf 3380726) (.leaf 3439549) (.leaf 3495104) (.leaf 3547735))
    (.node (.leaf 3597735) (.leaf 3645354) (.leaf 3690808) (.leaf 3734286) (.leaf 3775952) (.leaf 3815952) (.leaf 3854413) (.leaf 3891450) (.leaf 3927164) (.leaf 3961646))
    (.node (.leaf 3994979) (.leaf 4027237) (.leaf 4058487) (.leaf 4088790) (.leaf 4118201) (.leaf 4146772) (.leaf 4174549) (.leaf 4201576) (.leaf 4227891) (.leaf 4253532))
    (.node (.leaf 4278532) (.leaf 4302922) (.leaf 4326731) (.leaf 4349986) (.leaf 4372713) (.leaf 4394935) (.leaf 4416674) (.leaf 4437950) (.leaf 4458783) (.leaf 4479191))
    (.node (.leaf 4499191) (.leaf 4518798) (.leaf 4538028) (.leaf 4556895) (.leaf 4575413) (.leaf 4593594) (.leaf 4611451) (.leaf 4628994) (.leaf 4646235) (.leaf 4663184))
    (.node (.leaf 4679850) (.leaf 4696243) (.leaf 4712372) (.leaf 4728245) (.leaf 4743870) (.leaf 4759254) (.leaf 4774405) (.leaf 4789330) (.leaf 4804035) (.leaf 4818527))
    (.node (.leaf 4832812) (.leaf 4846896) (.leaf 4860784) (.leaf 4874482) (.leaf 4887995) (.leaf 4901328) (.leaf 4914485) (.leaf 4927472) (.leaf 4940292) (.leaf 4952950))
    (.node (.leaf 4965450) (.leaf 4977795) (.leaf 4989990) (.leaf 5002038) (.leaf 5013942) (.leaf 5025706) (.leaf 5037333) (.leaf 5048827) (.leaf 5060190) (.leaf 5071425))
    (.node (.leaf 5082536) (.leaf 5093525) (.leaf 5104394) (.leaf 5115146) (.leaf 5125784) (.leaf 5136310) (.leaf 5146726) (.leaf 5157035) (.leaf 5167239) (.leaf 5177340))
  )
  (.node
    (.node (.leaf 5187340) (.leaf 5197240) (.leaf 5207043) (.leaf 5216751) (.leaf 5226366) (.leaf 5235889) (.leaf 5245322) (.leaf 5254667) (.leaf 5263926) (.leaf 5273100))
    (.node (.leaf 5282190) (.leaf 5291199) (.leaf 5300127) (.leaf 5308976) (.leaf 5317747) (.leaf 5326442) (.leaf 5335062) (.leaf 5343609) (.leaf 5352083) (.leaf 5360486))
    (.node (.leaf 5368819) (.leaf 5377083) (.leaf 5385279) (.leaf 5393409) (.leaf 5401473) (.leaf 5409473) (.leaf 5417409) (.leaf 5425283) (.leaf 5433095) (.leaf 5440846))
    (.node (.leaf 5448538) (.leaf 5456171) (.leaf 5463746) (.leaf 5471264) (.leaf 5478726) (.leaf 5486133) (.leaf 5493485) (.leaf 5500784) (.leaf 5508030) (.leaf 5515224))
    (.node (.leaf 5522366) (.leaf 5529458) (.leaf 5536500) (.leaf 5543493) (.leaf 5550437) (.leaf 5557333) (.leaf 5564182) (.leaf 5570984) (.leaf 5577740) (.leaf 5584451))
    (.node (.leaf 5591117) (.leaf 5597739) (.leaf 5604317) (.leaf 5610852) (.leaf 5617345) (.leaf 5623796) (.leaf 5630206) (.leaf 5636575) (.leaf 5642904) (.leaf 5649193))
    (.node (.leaf 5655443) (.leaf 5661654) (.leaf 5667826) (.leaf 5673960) (.leaf 5680057) (.leaf 5686117) (.leaf 5692141) (.leaf 5698129) (.leaf 5704081) (.leaf 5709998))
    (.node (.leaf 5715880) (.leaf 5721727) (.leaf 5727540) (.leaf 5733320) (.leaf 5739067) (.leaf 5744781) (.leaf 5750462) (.leaf 5756111) (.leaf 5761728) (.leaf 5767314))
    (.node (.leaf 5772869) (.leaf 5778393) (.leaf 5783887) (.leaf 5789351) (.leaf 5794785) (.leaf 5800190) (.leaf 5805566) (.leaf 5810913) (.leaf 5816232) (.leaf 5821523))
    (.node (.leaf 5826786) (.leaf 5832021) (.leaf 5837229) (.leaf 5842410) (.leaf 5847564) (.leaf 5852692) (.leaf 5857794) (.leaf 5862870) (.leaf 5867920) (.leaf 5872945))
  )
  (.node
    (.node (.leaf 5877945) (.leaf 5882920) (.leaf 5887870) (.leaf 5892796) (.leaf 5897697) (.leaf 5902575) (.leaf 5907429) (.leaf 5912259) (.leaf 5917066) (.leaf 5921850))
    (.node (.leaf 5926611) (.leaf 5931350) (.leaf 5936066) (.leaf 5940760) (.leaf 5945432) (.leaf 5950083) (.leaf 5954712) (.leaf 5959320) (.leaf 5963907) (.leaf 5968473))
    (.node (.leaf 5973018) (.leaf 5977542) (.leaf 5982046) (.leaf 5986530) (.leaf 5990994) (.leaf 5995438) (.leaf 5999862) (.leaf 6004267) (.leaf 6008652) (.leaf 6013018))
    (.node (.leaf 6017365) (.leaf 6021694) (.leaf 6026004) (.leaf 6030295) (.leaf 6034568) (.leaf 6038823) (.leaf 6043060) (.leaf 6047279) (.leaf 6051480) (.leaf 6055664))
    (.node (.leaf 6059830) (.leaf 6063979) (.leaf 6068111) (.leaf 6072226) (.leaf 6076324) (.leaf 6080405) (.leaf 6084470) (.leaf 6088518) (.leaf 6092550) (.leaf 6096566))
    (.node (.leaf 6100566) (.leaf 6104550) (.leaf 6108518) (.leaf 6112470) (.leaf 6116407) (.leaf 6120328) (.leaf 6124234) (.leaf 6128125) (.leaf 6132000) (.leaf 6135861))
    (.node (.leaf 6139707) (.leaf 6143538) (.leaf 6147354) (.leaf 6151156) (.leaf 6154943) (.leaf 6158716) (.leaf 6162475) (.leaf 6166220) (.leaf 6169951) (.leaf 6173668))
    (.node (.leaf 6177371) (.leaf 6181061) (.leaf 6184737) (.leaf 6188400) (.leaf 6192049) (.leaf 6195685) (.leaf 6199308) (.leaf 6202918) (.leaf 6206515) (.leaf 6210099))
    (.node (.leaf 6213670) (.leaf 6217228) (.leaf 6220774) (.leaf 6224307) (.leaf 6227828) (.leaf 6231336) (.leaf 6234832) (.leaf 6238316) (.leaf 6241788) (.leaf 6245248))
    (.node (.leaf 6248696) (.leaf 6252132) (.leaf 6255556) (.leaf 6258968) (.leaf 6262369) (.leaf 6265758) (.leaf 6269136) (.leaf 6272503) (.leaf 6275858) (.leaf 6279202))
  )
  (.node
    (.node (.leaf 6282535) (.leaf 6285857) (.leaf 6289168) (.leaf 6292468) (.leaf 6295757) (.leaf 6299035) (.leaf 6302302) (.leaf 6305559) (.leaf 6308805) (.leaf 6312041))
    (.node (.leaf 6315266) (.leaf 6318481) (.leaf 6321686) (.leaf 6324880) (.leaf 6328064) (.leaf 6331238) (.leaf 6334402) (.leaf 6337556) (.leaf 6340700) (.leaf 6343834))
    (.node (.leaf 6346959) (.leaf 6350074) (.leaf 6353179) (.leaf 6356274) (.leaf 6359360) (.leaf 6362436) (.leaf 6365503) (.leaf 6368561) (.leaf 6371609) (.leaf 6374648))
    (.node (.leaf 6377678) (.leaf 6380699) (.leaf 6383711) (.leaf 6386714) (.leaf 6389708) (.leaf 6392693) (.leaf 6395669) (.leaf 6398636) (.leaf 6401594) (.leaf 6404543))
    (.node (.leaf 6407484) (.leaf 6410416) (.leaf 6413339) (.leaf 6416254) (.leaf 6419160) (.leaf 6422058) (.leaf 6424948) (.leaf 6427829) (.leaf 6430702) (.leaf 6433567))
    (.node (.leaf 6436424) (.leaf 6439273) (.leaf 6442113) (.leaf 6444945) (.leaf 6447769) (.leaf 6450585) (.leaf 6453393) (.leaf 6456194) (.leaf 6458987) (.leaf 6461772))
    (.node (.leaf 6464549) (.leaf 6467319) (.leaf 6470081) (.leaf 6472835) (.leaf 6475582) (.leaf 6478321) (.leaf 6481053) (.leaf 6483777) (.leaf 6486494) (.leaf 6489204))
    (.node (.leaf 6491906) (.leaf 6494601) (.leaf 6497289) (.leaf 6499969) (.leaf 6502642) (.leaf 6505308) (.leaf 6507967) (.leaf 6510619) (.leaf 6513264) (.leaf 6515902))
    (.node (.leaf 6518533) (.leaf 6521157) (.leaf 6523774) (.leaf 6526384) (.leaf 6528988) (.leaf 6531585) (.leaf 6534175) (.leaf 6536758) (.leaf 6539335) (.leaf 6541905))
    (.node (.leaf 6544469) (.leaf 6547026) (.leaf 6549577) (.leaf 6552121) (.leaf 6554659) (.leaf 6557190) (.leaf 6559715) (.leaf 6562233) (.leaf 6564745) (.leaf 6567251))
  )
  (.node
    (.node (.leaf 6569751) (.leaf 6572244) (.leaf 6574731) (.leaf 6577212) (.leaf 6579687) (.leaf 6582156) (.leaf 6584619) (.leaf 6587076) (.leaf 6589526) (.leaf 6591970))
    (.node (.leaf 6594409) (.leaf 6596842) (.leaf 6599269) (.leaf 6601690) (.leaf 6604105) (.leaf 6606514) (.leaf 6608917) (.leaf 6611315) (.leaf 6613707) (.leaf 6616093))
    (.node (.leaf 6618473) (.leaf 6620848) (.leaf 6623217) (.leaf 6625581) (.leaf 6627939) (.leaf 6630291) (.leaf 6632638) (.leaf 6634979) (.leaf 6637315) (.leaf 6639646))
    (.node (.leaf 6641971) (.leaf 6644291) (.leaf 6646605) (.leaf 6648914) (.leaf 6651218) (.leaf 6653516) (.leaf 6655809) (.leaf 6658097) (.leaf 6660380) (.leaf 6662657))
    (.node (.leaf 6664929) (.leaf 6667196) (.leaf 6669458) (.leaf 6671715) (.leaf 6673967) (.leaf 6676214) (.leaf 6678456) (.leaf 6680693) (.leaf 6682925) (.leaf 6685152))
    (.node (.leaf 6687374) (.leaf 6689591) (.leaf 6691803) (.leaf 6694010) (.leaf 6696212) (.leaf 6698409) (.leaf 6700601) (.leaf 6702789) (.leaf 6704972) (.leaf 6707150))
    (.node (.leaf 6709323) (.leaf 6711492) (.leaf 6713656) (.leaf 6715815) (.leaf 6717970) (.leaf 6720120) (.leaf 6722265) (.leaf 6724406) (.leaf 6726542) (.leaf 6728674))
    (.node (.leaf 6730801) (.leaf 6732924) (.leaf 6735042) (.leaf 6737156) (.leaf 6739265) (.leaf 6741370) (.leaf 6743470) (.leaf 6745566) (.leaf 6747658) (.leaf 6749745))
    (.node (.leaf 6751828) (.leaf 6753907) (.leaf 6755981) (.leaf 6758051) (.leaf 6760117) (.leaf 6762178) (.leaf 6764235) (.leaf 6766288) (.leaf 6768337) (.leaf 6770381))
    (.node (.leaf 6772421) (.leaf 6774457) (.leaf 6776489) (.leaf 6778517) (.leaf 6780541) (.leaf 6782561) (.leaf 6784577) (.leaf 6786589) (.leaf 6788597) (.leaf 6790601))
  )
  (.node
    (.node (.leaf 6792601) (.leaf 6794597) (.leaf 6796589) (.leaf 6798577) (.leaf 6800561) (.leaf 6802541) (.leaf 6804517) (.leaf 6806489) (.leaf 6808457) (.leaf 6810421))
    (.node (.leaf 6812381) (.leaf 6814337) (.leaf 6816290) (.leaf 6818239) (.leaf 6820184) (.leaf 6822125) (.leaf 6824062) (.leaf 6825996) (.leaf 6827926) (.leaf 6829852))
    (.node (.leaf 6831775) (.leaf 6833694) (.leaf 6835609) (.leaf 6837521) (.leaf 6839429) (.leaf 6841333) (.leaf 6843234) (.leaf 6845131) (.leaf 6847024) (.leaf 6848914))
    (.node (.leaf 6850800) (.leaf 6852683) (.leaf 6854562) (.leaf 6856438) (.leaf 6858310) (.leaf 6860179) (.leaf 6862044) (.leaf 6863906) (.leaf 6865764) (.leaf 6867619))
    (.node (.leaf 6869470) (.leaf 6871318) (.leaf 6873163) (.leaf 6875004) (.leaf 6876842) (.leaf 6878676) (.leaf 6880507) (.leaf 6882335) (.leaf 6884159) (.leaf 6885980))
    (.node (.leaf 6887798) (.leaf 6889612) (.leaf 6891423) (.leaf 6893231) (.leaf 6895036) (.leaf 6896837) (.leaf 6898635) (.leaf 6900430) (.leaf 6902222) (.leaf 6904010))
    (.node (.leaf 6905795) (.leaf 6907577) (.leaf 6909356) (.leaf 6911132) (.leaf 6912905) (.leaf 6914674) (.leaf 6916440) (.leaf 6918203) (.leaf 6919963) (.leaf 6921720))
    (.node (.leaf 6923474) (.leaf 6925225) (.leaf 6926973) (.leaf 6928718) (.leaf 6930460) (.leaf 6932199) (.leaf 6933935) (.leaf 6935668) (.leaf 6937398) (.leaf 6939125))
    (.node (.leaf 6940849) (.leaf 6942570) (.leaf 6944288) (.leaf 6946003) (.leaf 6947715) (.leaf 6949424) (.leaf 6951130) (.leaf 6952833) (.leaf 6954533) (.leaf 6956230))
    (.node (.leaf 6957924) (.leaf 6959616) (.leaf 6961305) (.leaf 6962991) (.leaf 6964674) (.leaf 6966354) (.leaf 6968031) (.leaf 6969706) (.leaf 6971378) (.leaf 6973047))
  )
  (.node
    (.node (.leaf 6974713) (.leaf 6976376) (.leaf 6978037) (.leaf 6979695) (.leaf 6981350) (.leaf 6983002) (.leaf 6984652) (.leaf 6986299) (.leaf 6987943) (.leaf 6989585))
    (.node (.leaf 6991224) (.leaf 6992860) (.leaf 6994493) (.leaf 6996124) (.leaf 6997752) (.leaf 6999378) (.leaf 7001001) (.leaf 7002621) (.leaf 7004239) (.leaf 7005854))
    (.node (.leaf 7007466) (.leaf 7009076) (.leaf 7010683) (.leaf 7012288) (.leaf 7013890) (.leaf 7015490) (.leaf 7017087) (.leaf 7018681) (.leaf 7020273) (.leaf 7021862))
    (.node (.leaf 7023449) (.leaf 7025033) (.leaf 7026615) (.leaf 7028194) (.leaf 7029771) (.leaf 7031345) (.leaf 7032917) (.leaf 7034486) (.leaf 7036053) (.leaf 7037617))
    (.node (.leaf 7039179) (.leaf 7040739) (.leaf 7042296) (.leaf 7043851) (.leaf 7045403) (.leaf 7046953) (.leaf 7048500) (.leaf 7050045) (.leaf 7051588) (.leaf 7053128))
    (.node (.leaf 7054666) (.leaf 7056202) (.leaf 7057735) (.leaf 7059266) (.leaf 7060795) (.leaf 7062321) (.leaf 7063845) (.leaf 7065367) (.leaf 7066886) (.leaf 7068403))
    (.node (.leaf 7069918) (.leaf 7071430) (.leaf 7072940) (.leaf 7074448) (.leaf 7075954) (.leaf 7077457) (.leaf 7078958) (.leaf 7080457) (.leaf 7081954) (.leaf 7083448))
    (.node (.leaf 7084940) (.leaf 7086430) (.leaf 7087918) (.leaf 7089403) (.leaf 7090886) (.leaf 7092367) (.leaf 7093846) (.leaf 7095323) (.leaf 7096797) (.leaf 0))
    (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))
    (.node (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0) (.leaf 0))
  )
  pZero
  pZero
  pZero

def pFn (k : ℕ) : ℕ :=
  (((pTable.pick (k / 100)).pick ((k / 10) % 10)).pick (k % 10)).val

def checkStepRange : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, count + 1 =>
    Nat.ble (pFn lo) (pFn (lo + 1)) &&
    Nat.ble ((lo + 1) * (pFn (lo + 1) - pFn lo)) 1000000 &&
    checkStepRange (lo + 1) count

def bandScore (m : ℕ) : ℕ :=
  10000 * (pFn (m / 1) - pFn (m / 2)) +
  5000 * (pFn (m / 2) - pFn (m / 3)) +
  1667 * (pFn (m / 3) - pFn (m / 5)) +
  1334 * (pFn (m / 6) - pFn (m / 7)) +
  739 * (pFn (m / 10) - pFn (m / 11)) +
  449 * (pFn (m / 15) - pFn (m / 17)) +
  307 * (pFn (m / 22) - pFn (m / 23)) +
  222 * (pFn (m / 28) - pFn (m / 29)) +
  118 * (pFn (m / 35) - pFn (m / 36)) +
  174 * (pFn (m / 36) - pFn (m / 37)) +
  57 * (pFn (m / 58) - pFn (m / 59))

def checkRange : ℕ → ℕ → ℕ → Bool
  | _, 0, _ => true
  | lo, count + 1, thresh =>
    Nat.ble thresh (bandScore lo) && checkRange (lo + 1) count thresh

lemma checkStepRange_1 : checkStepRange 0 170 = true := by decide
lemma checkStepRange_2 : checkStepRange 170 170 = true := by decide
lemma checkStepRange_3 : checkStepRange 340 170 = true := by decide
lemma checkStepRange_4 : checkStepRange 510 168 = true := by decide

lemma checkRange_small_true : checkRange 1 74 10000000000 = true := by decide

lemma checkRange_gamma_1 : checkRange 75 150 10060000000 = true := by decide
lemma checkRange_gamma_2 : checkRange 225 150 10060000000 = true := by decide
lemma checkRange_gamma_3 : checkRange 375 150 10060000000 = true := by decide
lemma checkRange_gamma_4 : checkRange 525 153 10060000000 = true := by decide

lemma checkStepRange_sound (lo count : ℕ) (h : checkStepRange lo count = true) :
    ∀ k, lo ≤ k → k < lo + count →
      pFn k ≤ pFn (k + 1) ∧ (k + 1) * (pFn (k + 1) - pFn k) ≤ 1000000 := by
  induction count generalizing lo with
  | zero => intro k h1 h2; omega
  | succ c ih =>
    simp only [checkStepRange, Bool.and_eq_true] at h
    intro k h1 h2
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · exact ⟨Nat.ble_eq.mp h.1.1, Nat.ble_eq.mp h.1.2⟩
    · exact ih (lo + 1) h.2 k hlt (by omega)

lemma checkRange_sound (lo count thresh : ℕ)
    (h : checkRange lo count thresh = true) :
    ∀ m, lo ≤ m → m < lo + count → thresh ≤ bandScore m := by
  induction count generalizing lo with
  | zero => intro m h1 h2; omega
  | succ c ih =>
    simp only [checkRange, Bool.and_eq_true] at h
    intro m h1 h2
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · exact Nat.ble_eq.mp h.1
    · exact ih (lo + 1) h.2 m hlt (by omega)

lemma pFn_steps : ∀ k < 678, pFn k ≤ pFn (k + 1) ∧
    (k + 1) * (pFn (k + 1) - pFn k) ≤ 1000000 := by
  intro k hk
  by_cases h1 : k < 170
  · exact checkStepRange_sound 0 170 checkStepRange_1 k (Nat.zero_le k) h1
  · by_cases h2 : k < 340
    · exact checkStepRange_sound 170 170 checkStepRange_2 k (by omega) h2
    · by_cases h3 : k < 510
      · exact checkStepRange_sound 340 170 checkStepRange_3 k (by omega) h3
      · exact checkStepRange_sound 510 168 checkStepRange_4 k (by omega) (by omega)

lemma f_mono (f : ℕ → ℕ) (M : ℕ) (h : ∀ k < M, f k ≤ f (k + 1))
    {B A : ℕ} (hBA : B ≤ A) (hAM : A ≤ M) : f B ≤ f A := by
  induction A, hBA using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact le_trans (ih (Nat.le_of_succ_le hAM)) (h n (Nat.lt_of_succ_le hAM))

lemma harmonic_ge_of_steps (f : ℕ → ℕ) (M : ℕ)
    (hsteps : ∀ k < M, f k ≤ f (k + 1) ∧ (k + 1) * (f (k + 1) - f k) ≤ 1000000)
    {B A : ℕ} (hBA : B ≤ A) (hAM : A ≤ M) :
    ((f A - f B : ℕ) : ℝ) / 1000000 ≤ ∑ k ∈ Finset.Ioc B A, (1 : ℝ) / k := by
  induction A, hBA using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hnM : n ≤ M := Nat.le_of_succ_le hAM
    have hnlt : n < M := Nat.lt_of_succ_le hAM
    have ih' := ih hnM
    have hIoc : Finset.Ioc B (n + 1) = insert (n + 1) (Finset.Ioc B n) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have hnotmem : n + 1 ∉ Finset.Ioc B n := by
      simp only [Finset.mem_Ioc]
      omega
    rw [hIoc, Finset.sum_insert hnotmem]
    have hmono : f B ≤ f n := f_mono f M (fun k hk => (hsteps k hk).1) hn hnM
    have hstep := hsteps n hnlt
    have hdiff : f (n + 1) - f B = (f n - f B) + (f (n + 1) - f n) := by omega
    rw [hdiff, Nat.cast_add, add_div]
    have hstep_real : ((f (n + 1) - f n : ℕ) : ℝ) / 1000000 ≤ (1 : ℝ) / (n + 1 : ℕ) := by
      have hpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
      rw [div_le_div_iff₀ (by norm_num) hpos]
      have hnat : (f (n + 1) - f n) * (n + 1) ≤ 1 * 1000000 := by
        rw [Nat.mul_comm, one_mul]
        exact hstep.2
      exact_mod_cast hnat
    linarith

private lemma bandScore_eq_list (m : ℕ) :
    bandScore m = (bands.map fun b => b.2.2 * (pFn (m / b.1) - pFn (m / b.2.1))).sum := by
  simp only [bandScore, bands, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, add_assoc]

lemma bandScore_le_S_aux (m : ℕ) (hm : m ≤ 678)
    (hsteps : ∀ k < 678, pFn k ≤ pFn (k + 1) ∧
      (k + 1) * (pFn (k + 1) - pFn k) ≤ 1000000)
    (L : List (ℕ × ℕ × ℕ))
    (hL : ∀ b ∈ L, 0 < b.1 ∧ b.1 ≤ b.2.1) :
    (((L.map fun b => b.2.2 * (pFn (m / b.1) - pFn (m / b.2.1))).sum : ℕ) : ℝ) / 10000000000 ≤
      (L.map fun t => (t.2.2 : ℝ) / 10000 * bandSum m t.1 t.2.1).sum := by
  induction L with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul]
    have hb := hL b List.mem_cons_self
    have hbs := fun x hx => hL x (List.mem_cons_of_mem b hx)
    have hdiv_le : m / b.2.1 ≤ m / b.1 := nat_div_antitone hb.1 hb.2
    have hdiv_M : m / b.1 ≤ 678 := le_trans (Nat.div_le_self m b.1) hm
    have hharm := harmonic_ge_of_steps pFn 678 hsteps hdiv_le hdiv_M
    have hterm : ((b.2.2 : ℝ) * ((pFn (m / b.1) - pFn (m / b.2.1) : ℕ) : ℝ)) / 10000000000 ≤
        (b.2.2 : ℝ) / 10000 * bandSum m b.1 b.2.1 := by
      have heq : ((b.2.2 : ℝ) * ((pFn (m / b.1) - pFn (m / b.2.1) : ℕ) : ℝ)) / 10000000000 =
          (b.2.2 : ℝ) / 10000 * (((pFn (m / b.1) - pFn (m / b.2.1) : ℕ) : ℝ) / 1000000) := by
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hharm (by positivity)
    rw [add_div]
    exact add_le_add hterm (ih hbs)

lemma bandScore_le_S {m : ℕ} (hm : m ≤ 678) :
    ((bandScore m : ℕ) : ℝ) / 10000000000 ≤ S m := by
  rw [bandScore_eq_list m]
  exact bandScore_le_S_aux m hm pFn_steps bands (by decide)

lemma pFn_gamma {m : ℕ} (hm1 : 75 ≤ m) (hm2 : m < 678) : 10060000000 ≤ bandScore m := by
  by_cases h1 : m < 225
  · exact checkRange_sound 75 150 10060000000 checkRange_gamma_1 m hm1 h1
  · by_cases h2 : m < 375
    · exact checkRange_sound 225 150 10060000000 checkRange_gamma_2 m (by omega) h2
    · by_cases h3 : m < 525
      · exact checkRange_sound 375 150 10060000000 checkRange_gamma_3 m (by omega) h3
      · exact checkRange_sound 525 153 10060000000 checkRange_gamma_4 m (by omega) (by omega)

lemma S_ge_one_small {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m < 678) : (1 : ℝ) ≤ S m := by
  have hle : ((bandScore m : ℕ) : ℝ) / 10000000000 ≤ S m := bandScore_le_S (Nat.le_of_lt hm2)
  have hscore : 10000000000 ≤ bandScore m := by
    by_cases h75 : m < 75
    · exact checkRange_sound 1 74 10000000000 checkRange_small_true m hm1 h75
    · have h1 := pFn_gamma (by omega) hm2
      omega
  have h1 : (1 : ℝ) ≤ ((bandScore m : ℕ) : ℝ) / 10000000000 := by
    have hcast : (10000000000 : ℝ) ≤ (bandScore m : ℝ) := by exact_mod_cast hscore
    linarith
  exact le_trans h1 hle

lemma S_ge_gamma_small {m : ℕ} (hm1 : 75 ≤ m) (hm2 : m < 678) : (1 : ℝ) + 3 / 500 ≤ S m := by
  have hle : ((bandScore m : ℕ) : ℝ) / 10000000000 ≤ S m := bandScore_le_S (Nat.le_of_lt hm2)
  have hscore : 10060000000 ≤ bandScore m := pFn_gamma hm1 hm2
  have h1 : (1 : ℝ) + 3 / 500 ≤ ((bandScore m : ℕ) : ℝ) / 10000000000 := by
    have hcast : (10060000000 : ℝ) ≤ (bandScore m : ℝ) := by exact_mod_cast hscore
    linarith
  exact le_trans h1 hle

end Erdos542Chen

theorem OMA.solution : type_of% @Erdos542.erdos_542.variants.chen := by
  intro n hn A hA
  have hS1 : ∀ m, 1 ≤ m → (1 : ℝ) ≤ Erdos542Chen.S m := by
    intro m hm
    by_cases h : m < 678
    · exact Erdos542Chen.S_ge_one_small hm h
    · linarith [Erdos542Chen.S_ge_large (Nat.not_lt.mp h)]
  have hS75 : ∀ m, 75 ≤ m → (1 : ℝ) + 3 / 500 ≤ Erdos542Chen.S m := by
    intro m hm
    by_cases h : m < 678
    · exact Erdos542Chen.S_ge_gamma_small hm h
    · exact Erdos542Chen.S_ge_large (Nat.not_lt.mp h)
  exact lt_of_le_of_lt (Erdos542Chen.main_reduction n A hA hS1 hS75)
    (Erdos542Chen.final_bound hn)
