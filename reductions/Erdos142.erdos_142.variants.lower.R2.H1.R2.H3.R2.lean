import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R2
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.ZMod.Basic

/-!
# Prime-cyclic polylogarithmic reduction for 4-adic multicolor progressions (k >= 4)

Reduces the polylogarithmic-color Ramsey step on 4-adic intervals `[1, 4 ^ j]` for all `k >= 4`
to prime-cyclic `k`-AP-free density bounds `|E| ≤ C * p / (log p) ^ 5` in `ZMod p`, split into
`k = 4` (`H1`) and `k >= 5` (`H2`), via:
1. Bertrand's postulate (`2 * N < p ≤ 4 * N`) and wraparound-free Freiman embedding `[1, N] ↪ ZMod p`.
2. Color-class pigeonhole extracting a monochromatic `k`-AP once `r k N < N / q`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2_H3_R2

open Erdos142 Filter Real

/-- Prime-cyclic 4-AP-free bound at the `(log p) ^ 5` threshold. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop, p.Prime →
    ∀ E : Finset (ZMod p),
      (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < 4 → a + (i : ZMod p) * d ∈ E) →
      (E.card : ℝ) ≤ C * (p : ℝ) / Real.log (p : ℝ) ^ 5

/-- Prime-cyclic k-AP-free bound at the `(log p) ^ 5` threshold for all `k >= 5`. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop, p.Prime →
    ∀ E : Finset (ZMod p),
      (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ E) →
      (E.card : ℝ) ≤ C * (p : ℝ) / Real.log (p : ℝ) ^ 5

lemma apFree_iff {A : Set ℕ} {k : ℕ} (hk : 1 < k) :
    A.IsAPOfLengthFree k ↔ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  constructor
  · rintro hA ⟨a, d, hd, hterms⟩
    let f (i : ℕ) := a + i * d
    let T := (Finset.range k).image f
    have hf : Function.Injective f := fun i j hij =>
      Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
    have hT : ((T : Finset ℕ) : Set ℕ) = {a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} := by
      ext x; simp [T, f]
    have hcard : T.card = k := by simp [T, Finset.card_image_of_injective _ hf]
    have hsub : (T : Set ℕ) ⊆ A := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hterms i (Finset.mem_range.mp hi)
    exact hk'.not_ge (hA _ hsub ⟨a, d, by simp [hcard], hT⟩)
  · intro hno T hsub hT
    obtain ⟨a, d, hcard, hterms⟩ := hT
    have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
      rw [hterms]; exact ⟨i, by exact_mod_cast hi, by simp⟩
    have hd : 0 < d := by
      by_contra! h
      have he : d = 0 := Nat.eq_zero_of_le_zero h
      have hs : T = {a} := by
        apply Set.Subset.antisymm
        · rw [hterms, he]; rintro _ ⟨i, -, rfl⟩; simp
        · apply Set.singleton_subset_iff.mpr; simpa using hmem 0 (by omega)
      rw [hs] at hcard; exact hk'.ne (by simpa using hcard)
    exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

lemma exists_maximizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧
      r k N = S.card := by
  let C : Set ℕ := {m | ∃ S : Finset ℕ, ∃ _ : S ⊆ Finset.Icc 1 N,
    ∃ _ : (S : Set ℕ).IsAPOfLengthFree k, S.card = m}
  have hz : 0 ∈ C := by
    refine ⟨∅, Finset.empty_subset _, (apFree_iff hk).mpr ?_, rfl⟩
    rintro ⟨a, d, -, h⟩; simpa using h 0 (by omega)
  have hb : BddAbove C := by
    refine ⟨N, ?_⟩; rintro _ ⟨S, hS, -, rfl⟩; simpa using Finset.card_le_card hS
  obtain ⟨S, hS, hf, he⟩ := Nat.sSup_mem ⟨0, hz⟩ hb
  exact ⟨S, hS, hf, he.symm⟩

lemma cyclic_embed_no_wrap {k N p : ℕ} (hk : 2 ≤ k) (hp : p.Prime)
    (hpN : 2 * N < p) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hfree : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) :
    ∃ E : Finset (ZMod p), E.card = S.card ∧
      ¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ E := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let E : Finset (ZMod p) := S.image (fun x : ℕ => (x : ZMod p))
  have hinj : Set.InjOn (fun x : ℕ => (x : ZMod p)) (S : Set ℕ) := by
    intro x hx y hy hxy
    have hxN := (Finset.mem_Icc.mp (hS hx)).2
    have hyN := (Finset.mem_Icc.mp (hS hy)).2
    have hval := congrArg ZMod.val hxy
    rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
  refine ⟨E, Finset.card_image_of_injOn hinj, ?_⟩
  rintro ⟨a, d, hd, hmem⟩
  have hmem_nat : ∀ i < k, ∃ x ∈ S, (x : ZMod p) = a + (i : ZMod p) * d := fun i hi =>
    Finset.mem_image.mp (hmem i hi)
  choose xs hxsS hxseq using hmem_nat
  have hxs_bd : ∀ i (hi : i < k), 1 ≤ xs i hi ∧ xs i hi ≤ N := fun i hi =>
    Finset.mem_Icc.mp (hS (hxsS i hi))
  have hx01_ne : xs 0 (by omega) ≠ xs 1 (by omega) := by
    intro h
    have h0 := hxseq 0 (by omega); have h1 := hxseq 1 (by omega); rw [h] at h0
    have hd0 : d = 0 := by
      have : a + 0 = a + d := by simpa using h0.symm.trans h1
      exact (add_left_cancel this).symm
    exact hd hd0
  rcases lt_or_gt_of_ne hx01_ne with hlt | hgt
  · set δ : ℕ := xs 1 (by omega) - xs 0 (by omega)
    have hδ_pos : 0 < δ := by omega
    have hδ_lt : δ < N := by
      have h0 := hxs_bd 0 (by omega); have h1 := hxs_bd 1 (by omega); omega
    have hd_eq : (δ : ZMod p) = d := by
      have hsum : (xs 0 (by omega) : ZMod p) + (δ : ZMod p) = (xs 1 (by omega) : ZMod p) := by
        rw [← Nat.cast_add, Nat.add_sub_of_le hlt.le]
      have h0 : (xs 0 (by omega) : ZMod p) = a := by simpa using hxseq 0 (by omega)
      have h1 : (xs 1 (by omega) : ZMod p) = a + d := by simpa using hxseq 1 (by omega)
      calc (δ : ZMod p) = ((xs 0 (by omega) : ZMod p) + (δ : ZMod p)) - (xs 0 (by omega) : ZMod p) := by ring
        _ = (xs 1 (by omega) : ZMod p) - (xs 0 (by omega) : ZMod p) := by rw [hsum]
        _ = (a + d) - a := by rw [h0, h1]
        _ = d := by ring
    have hstep : ∀ i (hi : i + 1 < k), xs (i + 1) hi = xs i (by omega) + δ := by
      intro i hi
      have hcast : ((xs (i + 1) hi : ℕ) : ZMod p) = ((xs i (by omega) + δ : ℕ) : ZMod p) := by
        rw [Nat.cast_add, hd_eq, hxseq (i + 1) hi, hxseq i (by omega), Nat.cast_add, Nat.cast_one]
        ring
      have hbi := hxs_bd i (by omega); have hbi1 := hxs_bd (i + 1) hi
      have hval := congrArg ZMod.val hcast
      rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
    have hformula : ∀ i (hi : i < k), xs i hi = xs 0 (by omega) + i * δ := by
      intro i
      induction i with
      | zero => intro hi; simp
      | succ i ih => intro hi; rw [hstep i hi, ih (by omega)]; ring
    refine hfree ⟨xs 0 (by omega), δ, hδ_pos, fun i hi => ?_⟩
    rw [← hformula i hi]; exact hxsS i hi
  · set δ : ℕ := xs 0 (by omega) - xs 1 (by omega)
    have hδ_pos : 0 < δ := by omega
    have hδ_lt : δ < N := by
      have h0 := hxs_bd 0 (by omega); have h1 := hxs_bd 1 (by omega); omega
    have hd_eq : (δ : ZMod p) = -d := by
      have hsum : (xs 1 (by omega) : ZMod p) + (δ : ZMod p) = (xs 0 (by omega) : ZMod p) := by
        rw [← Nat.cast_add, Nat.add_sub_of_le hgt.le]
      have h0 : (xs 0 (by omega) : ZMod p) = a := by simpa using hxseq 0 (by omega)
      have h1 : (xs 1 (by omega) : ZMod p) = a + d := by simpa using hxseq 1 (by omega)
      calc (δ : ZMod p) = ((xs 1 (by omega) : ZMod p) + (δ : ZMod p)) - (xs 1 (by omega) : ZMod p) := by ring
        _ = (xs 0 (by omega) : ZMod p) - (xs 1 (by omega) : ZMod p) := by rw [hsum]
        _ = a - (a + d) := by rw [h0, h1]
        _ = -d := by ring
    have hstep : ∀ i (hi : i + 1 < k), xs (i + 1) hi + δ = xs i (by omega) := by
      intro i hi
      have hcast : ((xs (i + 1) hi + δ : ℕ) : ZMod p) = ((xs i (by omega) : ℕ) : ZMod p) := by
        rw [Nat.cast_add, hd_eq, hxseq (i + 1) hi, hxseq i (by omega), Nat.cast_add, Nat.cast_one]
        ring
      have hbi := hxs_bd i (by omega); have hbi1 := hxs_bd (i + 1) hi
      have hval := congrArg ZMod.val hcast
      rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
    have hrev : ∀ i (hi : i < k), xs (k - 1 - i) (by omega) = xs (k - 1) (by omega) + i * δ := by
      intro i
      induction i with
      | zero => intro hi; simp
      | succ i ih =>
        intro hi
        have hs := hstep (k - 1 - (i + 1)) (by omega)
        have hprev := ih (by omega)
        have hEq : xs (k - 1 - (i + 1) + 1) (by omega) = xs (k - 1 - i) (by omega) := by
          congr 1; omega
        rw [hEq] at hs
        have : xs (k - 1 - (i + 1)) (by omega) = xs (k - 1 - i) (by omega) + δ := by omega
        rw [this, hprev]; ring
    refine hfree ⟨xs (k - 1) (by omega), δ, hδ_pos, fun i hi => ?_⟩
    rw [← hrev i hi]; exact hxsS (k - 1 - i) (by omega)

lemma monochromatic_of_r_lt {N M k : ℕ} (hk : 1 < k) (hM : 0 < M)
    (bound : (r k N : ℝ) < (N : ℝ) / (M : ℝ)) (c : ℕ → Fin M) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k,
      a + i * d ∈ Finset.Icc 1 N ∧ c (a + i * d) = c a := by
  classical
  have hmass : r k N * M < N := by
    exact_mod_cast (lt_div_iff₀ (Nat.cast_pos.mpr hM : 0 < (M : ℝ))).mp bound
  obtain ⟨color, _, hlarge⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.Icc 1 N) (t := Finset.univ) (f := c) (n := r k N)
    (fun _ _ => Finset.mem_univ _) (by simpa [Nat.mul_comm] using hmass)
  let S := (Finset.Icc 1 N).filter fun x => c x = color
  have hnotfree : ¬ (S : Set ℕ).IsAPOfLengthFree k := by
    intro hfree
    apply hlarge.not_ge
    change S.card ≤ r k N
    unfold r Set.IsAPOfLengthFree.maxCard
    refine le_csSup ?_ ⟨S, Finset.filter_subset _ _, hfree, rfl⟩
    refine ⟨N, ?_⟩
    rintro _ ⟨U, hU, _, rfl⟩
    simpa using Finset.card_le_card hU
  rw [apFree_iff hk] at hnotfree
  push Not at hnotfree
  obtain ⟨a, d, hd, hmem⟩ := hnotfree
  refine ⟨a, d, hd, fun i hi => ?_⟩
  have hsi := Finset.mem_filter.mp (hmem i hi)
  have hs0 : a ∈ Finset.Icc 1 N ∧ c a = color := by simpa using Finset.mem_filter.mp (hmem 0 (by omega))
  exact ⟨hsi.1, hsi.2.trans hs0.2.symm⟩

lemma ramsey_of_cyclic {k : ℕ} (hk : 2 ≤ k)
    (hcyc : ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop, p.Prime →
      ∀ E : Finset (ZMod p),
        (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ E) →
        (E.card : ℝ) ≤ C * (p : ℝ) / Real.log (p : ℝ) ^ 5) :
    ∀ᶠ j : ℕ in Filter.atTop,
      ∀ c : ℕ → Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4),
        ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ Finset.Icc 1 (4 ^ j) ∧ c (a + i * d) = c a := by
  obtain ⟨C, hC, hP⟩ := hcyc
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp hP
  have h4top : Tendsto (fun j : ℕ => 4 ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < 4)
  have hlog_top : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hNbound : ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) < (N : ℝ) / (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop (max P₀ 3),
      hlog_top.eventually (eventually_gt_atTop (max 2 (64 * C)))] with N hN hlogN
    have hNP : P₀ ≤ N := (le_max_left _ _).trans hN
    have hN3 : 3 ≤ N := (le_max_right _ _).trans hN
    have hlog2 : 2 < Real.log (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hlogN
    have hlogC : 64 * C < Real.log (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hlogN
    obtain ⟨S, hSsub, hSfree, hScard⟩ := exists_maximizer (by omega : 1 < k) N
    obtain ⟨p, hp, hp2N, hp4N⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
    obtain ⟨E, hEcard, hEfree⟩ := cyclic_embed_no_wrap hk hp hp2N hSsub
      ((apFree_iff (by omega : 1 < k)).mp hSfree)
    have hEb := hP₀ p (by omega) hp E hEfree
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hNp : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show N ≤ p by omega)
    have hp_le : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast (show p ≤ 4 * N by omega)
    have hlog_le : Real.log (N : ℝ) ≤ Real.log (p : ℝ) := Real.log_le_log hN_pos hNp
    have hlog_pos : 0 < Real.log (N : ℝ) := by linarith
    have hpow5_le : Real.log (N : ℝ) ^ 5 ≤ Real.log (p : ℝ) ^ 5 :=
      pow_le_pow_left₀ hlog_pos.le hlog_le 5
    have hceil_le : ((⌈Real.log (N : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      have hlt : (⌈Real.log (N : ℝ)⌉₊ : ℝ) < Real.log (N : ℝ) + 1 :=
        Nat.ceil_lt_add_one hlog_pos.le
      push_cast; linarith
    have hceil4_le : (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) ≤ 16 * Real.log (N : ℝ) ^ 4 := by
      have h1 : (((⌈Real.log (N : ℝ)⌉₊ + 1 : ℕ) : ℝ)) ^ 4 ≤ (2 * Real.log (N : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hceil_le 4
      have h2 : (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) =
          (((⌈Real.log (N : ℝ)⌉₊ + 1 : ℕ) : ℝ)) ^ 4 := by push_cast; rfl
      rw [h2]
      linarith [show (2 * Real.log (N : ℝ)) ^ 4 = 16 * Real.log (N : ℝ) ^ 4 by ring]
    have hEcard' : (E.card : ℝ) = (r k N : ℝ) := by exact_mod_cast (hEcard.trans hScard.symm)
    rw [hEcard'] at hEb
    have hceil4_pos : (0 : ℝ) < (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) := by positivity
    have hden5_pos : (0 : ℝ) < Real.log (N : ℝ) ^ 5 := pow_pos hlog_pos 5
    calc
      (r k N : ℝ) ≤ C * (p : ℝ) / Real.log (p : ℝ) ^ 5 := hEb
      _ ≤ C * (4 * (N : ℝ)) / Real.log (N : ℝ) ^ 5 :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hp_le hC.le) hden5_pos hpow5_le
      _ < (N : ℝ) / (16 * Real.log (N : ℝ) ^ 4) := by
          rw [div_lt_div_iff₀ hden5_pos (by positivity)]
          have hmul : 64 * C * Real.log (N : ℝ) ^ 4 < Real.log (N : ℝ) ^ 5 := by
            have : Real.log (N : ℝ) ^ 5 = Real.log (N : ℝ) * Real.log (N : ℝ) ^ 4 := by ring
            rw [this]
            exact mul_lt_mul_of_pos_right hlogC (pow_pos hlog_pos 4)
          nlinarith
      _ ≤ (N : ℝ) / (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_left hN_pos.le hceil4_pos hceil4_le
  filter_upwards [h4top.eventually hNbound] with j hj c
  exact monochromatic_of_r_lt (by omega) (by positivity) hj c

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2.H3 := by
  intro h4 h5 k hk
  rcases eq_or_lt_of_le hk with rfl | hk5
  · exact ramsey_of_cyclic (by decide) h4
  · exact ramsey_of_cyclic (by omega) (h5 k hk5)

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2_H3_R2
