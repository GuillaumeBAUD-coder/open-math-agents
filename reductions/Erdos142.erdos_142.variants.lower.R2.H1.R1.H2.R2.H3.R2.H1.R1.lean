import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.ZMod.Basic

/-!
# Prime-cyclic stretched-exponential reduction for k >= 5 via Bertrand Freiman embedding

Reduces the integer stretched-exponential bound `r k N / N ≤ C * exp (-c * (log N) ^ e)`
for all `k >= 5` to its prime-cyclic counterpart in `ZMod p`, split into `k = 5` (`H1`)
and `k >= 6` (`H2`), via Bertrand's postulate (`2 * N < p ≤ 4 * N`) and Freiman embedding
`[1, N] ↪ ZMod p` preserving `k`-AP-freeness without wraparound.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2_H1_R1

open Erdos142 Filter Real

/-- Prime-cyclic stretched-exponential 5-AP-free bound in `ZMod p`. -/
def H1 : Prop :=
  ∃ C c e : ℝ, 0 < C ∧ 0 < c ∧ 0 < e ∧ ∀ᶠ p : ℕ in atTop, p.Prime →
    ∀ E : Finset (ZMod p),
      (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < 5 → a + (i : ZMod p) * d ∈ E) →
      (E.card : ℝ) / (p : ℝ) ≤ C * Real.exp (-c * Real.log (p : ℝ) ^ e)

/-- Prime-cyclic stretched-exponential k-AP-free bound in `ZMod p` for all `k >= 6`. -/
def H2 : Prop :=
  ∀ k : ℕ, 6 ≤ k → ∃ C c e : ℝ, 0 < C ∧ 0 < c ∧ 0 < e ∧ ∀ᶠ p : ℕ in atTop, p.Prime →
    ∀ E : Finset (ZMod p),
      (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ E) →
      (E.card : ℝ) / (p : ℝ) ≤ C * Real.exp (-c * Real.log (p : ℝ) ^ e)

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
      ext x
      simp [T, f]
    have hcard : T.card = k := by simp [T, Finset.card_image_of_injective _ hf]
    have hsub : (T : Set ℕ) ⊆ A := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hterms i (Finset.mem_range.mp hi)
    exact hk'.not_ge (hA _ hsub ⟨a, d, by simp [hcard], hT⟩)
  · intro hno T hsub hT
    obtain ⟨a, d, hcard, hterms⟩ := hT
    have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
      rw [hterms]
      exact ⟨i, by exact_mod_cast hi, by simp⟩
    have hd : 0 < d := by
      by_contra! h
      have he : d = 0 := Nat.eq_zero_of_le_zero h
      have hs : T = {a} := by
        apply Set.Subset.antisymm
        · rw [hterms, he]
          rintro _ ⟨i, -, rfl⟩
          simp
        · apply Set.singleton_subset_iff.mpr
          simpa using hmem 0 (by omega)
      rw [hs] at hcard
      exact hk'.ne (by simpa using hcard)
    exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

lemma exists_maximizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧
      r k N = S.card := by
  let C : Set ℕ := {m | ∃ S : Finset ℕ, ∃ _ : S ⊆ Finset.Icc 1 N,
    ∃ _ : (S : Set ℕ).IsAPOfLengthFree k, S.card = m}
  have hz : 0 ∈ C := by
    refine ⟨∅, Finset.empty_subset _, (apFree_iff hk).mpr ?_, rfl⟩
    rintro ⟨a, d, -, h⟩
    simpa using h 0 (by omega)
  have hb : BddAbove C := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, -, rfl⟩
    simpa using Finset.card_le_card hS
  obtain ⟨S, hS, hf, he⟩ := Nat.sSup_mem ⟨0, hz⟩ hb
  exact ⟨S, hS, hf, he.symm⟩

/-- Freiman embedding of a `k`-AP-free subset of `[1, N]` into `ZMod p` for prime `p > 2 * N`. -/
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
  have hmem_nat : ∀ i < k, ∃ x ∈ S, (x : ZMod p) = a + (i : ZMod p) * d := by
    intro i hi
    exact Finset.mem_image.mp (hmem i hi)
  choose xs hxsS hxseq using hmem_nat
  have hxs_bd : ∀ i (hi : i < k), 1 ≤ xs i hi ∧ xs i hi ≤ N := fun i hi =>
    Finset.mem_Icc.mp (hS (hxsS i hi))
  have hx01_ne : xs 0 (by omega) ≠ xs 1 (by omega) := by
    intro h
    have h0 := hxseq 0 (by omega)
    have h1 := hxseq 1 (by omega)
    rw [h] at h0
    have hd0 : d = 0 := by
      have : a + 0 = a + d := by simpa using h0.symm.trans h1
      exact (add_left_cancel this).symm
    exact hd hd0
  rcases lt_or_gt_of_ne hx01_ne with hlt | hgt
  · set δ : ℕ := xs 1 (by omega) - xs 0 (by omega)
    have hδ_pos : 0 < δ := by omega
    have hδ_lt : δ < N := by
      have h0 := hxs_bd 0 (by omega)
      have h1 := hxs_bd 1 (by omega)
      omega
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
      have hbi := hxs_bd i (by omega)
      have hbi1 := hxs_bd (i + 1) hi
      have hval := congrArg ZMod.val hcast
      rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
    have hformula : ∀ i (hi : i < k), xs i hi = xs 0 (by omega) + i * δ := by
      intro i
      induction i with
      | zero => intro hi; simp
      | succ i ih =>
        intro hi
        rw [hstep i hi, ih (by omega)]
        ring
    refine hfree ⟨xs 0 (by omega), δ, hδ_pos, fun i hi => ?_⟩
    rw [← hformula i hi]
    exact hxsS i hi
  · set δ : ℕ := xs 0 (by omega) - xs 1 (by omega)
    have hδ_pos : 0 < δ := by omega
    have hδ_lt : δ < N := by
      have h0 := hxs_bd 0 (by omega)
      have h1 := hxs_bd 1 (by omega)
      omega
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
      have hbi := hxs_bd i (by omega)
      have hbi1 := hxs_bd (i + 1) hi
      have hval := congrArg ZMod.val hcast
      rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
    have hrev : ∀ i (hi : i < k), xs (k - 1 - i) (by omega) = xs (k - 1) (by omega) + i * δ := by
      intro i
      induction i with
      | zero => intro hi; simp
      | succ i ih =>
        intro hi
        have hidx : k - 1 - i = (k - 1 - (i + 1)) + 1 := by omega
        have hs := hstep (k - 1 - (i + 1)) (by omega)
        have hprev := ih (by omega)
        have hEq : xs (k - 1 - (i + 1) + 1) (by omega) = xs (k - 1 - i) (by omega) := by
          congr 1; omega
        rw [hEq] at hs
        have : xs (k - 1 - (i + 1)) (by omega) = xs (k - 1 - i) (by omega) + δ := by
          -- Wait: hs is xs (k - 1 - (i + 1) + 1) + δ = xs (k - 1 - (i + 1))!
          omega
        rw [this, hprev]
        ring
    refine hfree ⟨xs (k - 1) (by omega), δ, hδ_pos, fun i hi => ?_⟩
    rw [← hrev i hi]
    exact hxsS (k - 1 - i) (by omega)

/-- Transfer a prime-cyclic stretched-exponential bound to integers `[1, N]` via Bertrand. -/
lemma integer_of_cyclic {k : ℕ} (hk : 2 ≤ k)
    (hcyc : ∃ C c e : ℝ, 0 < C ∧ 0 < c ∧ 0 < e ∧ ∀ᶠ p : ℕ in atTop, p.Prime →
      ∀ E : Finset (ZMod p),
        (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ E) →
        (E.card : ℝ) / (p : ℝ) ≤ C * Real.exp (-c * Real.log (p : ℝ) ^ e)) :
    ∃ C c e : ℝ, 0 < C ∧ 0 < c ∧ 0 < e ∧ ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) / (N : ℝ) ≤ C * Real.exp (-c * Real.log (N : ℝ) ^ e) := by
  obtain ⟨C, c, e, hC, hc, he, hP⟩ := hcyc
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp hP
  refine ⟨4 * C, c, e, by positivity, hc, he, ?_⟩
  filter_upwards [eventually_ge_atTop (max P₀ 2)] with N hN
  have hNP : P₀ ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨S, hSsub, hSfree, hScard⟩ := exists_maximizer (by omega : 1 < k) N
  obtain ⟨p, hp, hp2N, hp4N⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  obtain ⟨E, hEcard, hEfree⟩ := cyclic_embed_no_wrap hk hp hp2N hSsub
    ((apFree_iff (by omega : 1 < k)).mp hSfree)
  have hEb := hP₀ p (by omega) hp E hEfree
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hp_le : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast (show p ≤ 4 * N by omega)
  have hNp : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show N ≤ p by omega)
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog_le : Real.log (N : ℝ) ≤ Real.log (p : ℝ) := Real.log_le_log hN_pos hNp
  have hpow_le : Real.log (N : ℝ) ^ e ≤ Real.log (p : ℝ) ^ e :=
    Real.rpow_le_rpow hlogN_pos.le hlog_le he.le
  have hexp_le : Real.exp (-c * Real.log (p : ℝ) ^ e) ≤ Real.exp (-c * Real.log (N : ℝ) ^ e) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hEcard' : (E.card : ℝ) = (r k N : ℝ) := by exact_mod_cast (hEcard.trans hScard.symm)
  rw [hEcard'] at hEb
  have hr_le : (r k N : ℝ) ≤ C * (p : ℝ) * Real.exp (-c * Real.log (p : ℝ) ^ e) := by
    have := (div_le_iff₀ hp_pos).mp hEb
    linarith
  rw [div_le_iff₀ hN_pos]
  calc
    (r k N : ℝ) ≤ C * (p : ℝ) * Real.exp (-c * Real.log (p : ℝ) ^ e) := hr_le
    _ ≤ C * (4 * (N : ℝ)) * Real.exp (-c * Real.log (N : ℝ) ^ e) := by
        have h1 : C * (p : ℝ) ≤ C * (4 * (N : ℝ)) := mul_le_mul_of_nonneg_left hp_le hC.le
        exact mul_le_mul h1 hexp_le (Real.exp_pos _).le (by positivity)
    _ = 4 * C * Real.exp (-c * Real.log (N : ℝ) ^ e) * (N : ℝ) := by ring

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2.H1 := by
  intro h5 h6 k hk
  rcases eq_or_lt_of_le hk with rfl | hk6
  · exact integer_of_cyclic (by decide) h5
  · exact integer_of_cyclic (by omega) (h6 k hk6)

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2_H1_R1
