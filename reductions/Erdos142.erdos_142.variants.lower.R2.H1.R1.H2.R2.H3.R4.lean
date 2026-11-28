import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2
import Mathlib

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R4 of step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3
-- Credit: @yhay81

/-!
# General Gowers U^{k-1} reduction for k ≥ 5 summable densities

Reduces `H3` (`∀ k ≥ 5, Summable (fun j ↦ r k (4 ^ j) / 4 ^ j)`) via Bertrand prime
embedding (`2 * 4^j < p ≤ 4 * 4^j`) into `ZMod p` to:
- `H1`: a summable density threshold for subsets of `ZMod p` with large `U^{k-1}` cube sum
  to contain a nontrivial `k`-term arithmetic progression;
- `H2`: the general Gowers `U^s` generalized von Neumann inequality on `ZMod p` for all `s ≥ 1`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R4

open Erdos142 Filter

/-- For each k ≥ 5 there is a summable threshold B(j) such that every subset of ZMod p
    (with prime 2 * 4^j < p ≤ 4 * 4^j) above density B(j) and with large Gowers U^{k-1}
    cube sum contains a nontrivial k-term arithmetic progression in ZMod p. -/
def H1 : Prop :=
  ∀ k : ℕ, 5 ≤ k →
    ∃ B : ℕ → ℝ, Summable B ∧
      ∀ᶠ j : ℕ in Filter.atTop,
        ∀ (p : ℕ) [Fact p.Prime], 2 * 4 ^ j < p → p ≤ 4 * 4 ^ j →
          ∀ S : Finset (ZMod p),
            let α : ℝ := (S.card : ℝ) / (p : ℝ)
            let f : ZMod p → ℝ := fun x => (if x ∈ S then (1 : ℝ) else 0) - α
            B j < α →
            (p : ℝ) ^ k * (α ^ k / (2 * (k : ℝ))) ^ (2 ^ (k - 1)) ≤
              ∑ x : ZMod p, ∑ h : Fin (k - 1) → ZMod p,
                ∏ ω : Fin (k - 1) → Bool,
                  f (x + ∑ r : Fin (k - 1), if ω r then h r else 0) →
            ∃ x d : ZMod p, d ≠ 0 ∧ ∀ i : Fin k, x + (i.1 : ZMod p) * d ∈ S

/-- General Gowers U^s generalized von Neumann inequality on ZMod p: for every s ≥ 1 and
    s + 1 pairwise distinct shifts c : Fin (s + 1) → ZMod p, the (s + 1)-AP linear form
    of real functions bounded by 1 in slots 0..s-1 is controlled by the Gowers U^s cube sum
    of the last function. -/
def H2 : Prop :=
  ∀ (s : ℕ), 1 ≤ s → ∀ (p : ℕ) [Fact p.Prime],
    ∀ (c : Fin (s + 1) → ZMod p), Function.Injective c →
    ∀ (f : Fin (s + 1) → ZMod p → ℝ),
      (∀ (i : Fin (s + 1)), i.1 < s → ∀ x, |f i x| ≤ 1) →
      (∑ x : ZMod p, ∑ d : ZMod p,
        ∏ i : Fin (s + 1), f i (x + c i * d)) ^ (2 ^ s) ≤
      (p : ℝ) ^ (2 ^ (s + 1) - (s + 1)) *
        ∑ x : ZMod p, ∑ h : Fin s → ZMod p,
          ∏ ω : Fin s → Bool,
            f (Fin.last s) (x + ∑ j : Fin s, if ω j then h j else 0)

lemma exists_max_apFree (k N : ℕ) (hk : 2 ≤ k) :
    ∃ S₀ : Finset ℕ, S₀ ⊆ Finset.Icc 1 N ∧ (S₀ : Set ℕ).IsAPOfLengthFree k ∧
      S₀.card = Erdos142.r k N := by
  let E : Set ℕ :=
    {Finset.card S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k)}
  have h0 : 0 ∈ E := by
    refine ⟨∅, Finset.empty_subset _, ?_, Finset.card_empty⟩
    intro t ht hAP
    rw [Finset.coe_empty, Set.subset_empty_iff] at ht
    subst ht
    exact False.elim (Set.not_isAPOfLength_empty (by exact_mod_cast (by omega : 0 < k)) hAP)
  have hbdd : BddAbove E := by
    refine ⟨N, ?_⟩
    rintro m ⟨S, hS, -, rfl⟩
    exact (Finset.card_le_card hS).trans (by simp [Nat.card_Icc])
  have hmem : sSup E ∈ E := Nat.sSup_mem ⟨0, h0⟩ hbdd
  rcases hmem with ⟨S₀, hsub, hfree, hcard⟩
  exact ⟨S₀, hsub, hfree, hcard⟩

lemma not_ap_free_of_strict_ap {S₀ : Finset ℕ} {k a₀ δ : ℕ}
    (hk : 2 ≤ k) (hδ : 0 < δ)
    (hmem : ∀ m < k, a₀ + m * δ ∈ S₀)
    (hfree : (S₀ : Set ℕ).IsAPOfLengthFree k) : False := by
  let T : Set ℕ := {a₀ + n • δ | (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞))}
  have hTsub : T ⊆ (S₀ : Set ℕ) := by
    rintro y ⟨n, hn, rfl⟩
    have hnk : n < k := Nat.cast_lt.mp hn
    simpa [smul_eq_mul] using hmem n hnk
  have hTeq : T = Set.range (fun i : Fin k => a₀ + i.1 * δ) := by
    ext y
    simp only [T, Set.mem_ofPred_eq, Set.mem_range, smul_eq_mul, Nat.cast_lt]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
    · rintro ⟨⟨n, hn⟩, rfl⟩
      exact ⟨n, hn, rfl⟩
  have hinj : Function.Injective (fun i : Fin k => a₀ + i.1 * δ) := by
    intro i j hij
    ext
    exact Nat.eq_of_mul_eq_mul_right hδ (Nat.add_left_cancel hij)
  have hcard : ENat.card T = (k : ℕ∞) := by
    rw [hTeq, ← ENat.card_congr (Equiv.ofInjective _ hinj), ENat.card_eq_coe_fintype_card,
      Fintype.card_fin]
  have hAP : T.IsAPOfLength k := ⟨a₀, δ, hcard, rfl⟩
  have hk1 : (k : ℕ∞) ≤ 1 := hfree T hTsub hAP
  have hk1' : k ≤ 1 := by exact_mod_cast hk1
  omega

lemma embed_ap_free {k N p : ℕ} [hp : Fact p.Prime] (hk : 3 ≤ k) (hNp : 2 * N < p)
    {S₀ : Finset ℕ} (hsub : S₀ ⊆ Finset.Icc 1 N)
    (hfree : (S₀ : Set ℕ).IsAPOfLengthFree k) :
    (S₀.image (Nat.cast : ℕ → ZMod p)).card = S₀.card ∧
    ¬ ∃ x d : ZMod p, d ≠ 0 ∧ ∀ i : Fin k,
        x + (i.1 : ZMod p) * d ∈ S₀.image (Nat.cast : ℕ → ZMod p) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  constructor
  · refine Finset.card_image_of_injOn fun a ha b hb hab => ?_
    have haN : a ≤ N := (Finset.mem_Icc.mp (hsub ha)).2
    have hbN : b ≤ N := (Finset.mem_Icc.mp (hsub hb)).2
    have hval := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
  · rintro ⟨x, d, hd, hmem⟩
    choose a haS haZ using fun i : Fin k => Finset.mem_image.mp (hmem i)
    have haN : ∀ i : Fin k, a i ≤ N := fun i => (Finset.mem_Icc.mp (hsub (haS i))).2
    have hmid : ∀ (m : ℕ) (hm : m + 2 < k),
        a ⟨m, by omega⟩ + a ⟨m + 2, hm⟩ = 2 * a ⟨m + 1, by omega⟩ := by
      intro m hm
      have hZ : ((a ⟨m, by omega⟩ + a ⟨m + 2, hm⟩ : ℕ) : ZMod p) =
          ((2 * a ⟨m + 1, by omega⟩ : ℕ) : ZMod p) := by
        push_cast
        rw [haZ, haZ, haZ]
        push_cast
        ring
      have h1 : a ⟨m, by omega⟩ + a ⟨m + 2, hm⟩ < p := by
        have := haN ⟨m, by omega⟩
        have := haN ⟨m + 2, hm⟩
        omega
      have h2 : 2 * a ⟨m + 1, by omega⟩ < p := by
        have := haN ⟨m + 1, by omega⟩
        omega
      have hval := congrArg ZMod.val hZ
      rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hval
    have ha01 : a ⟨0, by omega⟩ ≠ a ⟨1, by omega⟩ := by
      intro heq
      have hZ : (a ⟨0, by omega⟩ : ZMod p) = (a ⟨1, by omega⟩ : ZMod p) := congrArg Nat.cast heq
      rw [haZ, haZ] at hZ
      apply hd
      have hZ' : x + 0 * d = x + 1 * d := by simpa using hZ
      linear_combination -hZ'
    rcases lt_or_gt_of_ne ha01 with hlt | hgt
    · set δ : ℕ := a ⟨1, by omega⟩ - a ⟨0, by omega⟩
      have hprog : ∀ m (hm : m < k), a ⟨m, hm⟩ = a ⟨0, by omega⟩ + m * δ := by
        intro m
        induction m using Nat.strong_induction_on with
        | h m ih =>
          intro hm
          match m with
          | 0 => simp
          | 1 => omega
          | m' + 2 =>
            have h0 := ih m' (by omega) (by omega)
            have h1 := ih (m' + 1) (by omega) (by omega)
            have h2 := hmid m' hm
            have hm1 : (m' + 1) * δ = m' * δ + δ := by ring
            have hm2 : (m' + 2) * δ = m' * δ + 2 * δ := by ring
            omega
      have hδpos : 0 < δ := by dsimp only [δ]; omega
      exact not_ap_free_of_strict_ap (a₀ := a ⟨0, by omega⟩) (by omega) hδpos
        (fun m hm => by rw [← hprog m hm]; exact haS _) hfree
    · set δ : ℕ := a ⟨0, by omega⟩ - a ⟨1, by omega⟩
      have hprog : ∀ m (hm : m < k), a ⟨m, hm⟩ + m * δ = a ⟨0, by omega⟩ := by
        intro m
        induction m using Nat.strong_induction_on with
        | h m ih =>
          intro hm
          match m with
          | 0 => simp
          | 1 => omega
          | m' + 2 =>
            have h0 := ih m' (by omega) (by omega)
            have h1 := ih (m' + 1) (by omega) (by omega)
            have h2 := hmid m' hm
            have hm1 : (m' + 1) * δ = m' * δ + δ := by ring
            have hm2 : (m' + 2) * δ = m' * δ + 2 * δ := by ring
            omega
      have hrev : ∀ n < k, a ⟨k - 1, by omega⟩ + n * δ ∈ S₀ := by
        intro n hn
        have hlast := hprog (k - 1) (by omega)
        have hcur := hprog (k - 1 - n) (by omega)
        have hlin : (k - 1 - n) * δ + n * δ = (k - 1) * δ := by
          rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
        have heq : a ⟨k - 1, by omega⟩ + n * δ = a ⟨k - 1 - n, by omega⟩ := by omega
        rw [heq]
        exact haS _
      have hδpos : 0 < δ := by dsimp only [δ]; omega
      exact not_ap_free_of_strict_ap (by omega) hδpos hrev hfree

lemma prod_sub_prod_fin {k : ℕ} (u v : Fin k → ℝ) :
    (∏ i : Fin k, u i) - (∏ i : Fin k, v i) =
      ∑ r : Fin k, ∏ i : Fin k,
        if i.1 < r.1 then u i else if i = r then u i - v i else v i := by
  let P : ℕ → ℝ := fun m => ∏ i : Fin k, if i.1 < m then u i else v i
  have hP0 : P 0 = ∏ i : Fin k, v i := by simp [P]
  have hPk : P k = ∏ i : Fin k, u i := Finset.prod_congr rfl fun i _ => if_pos i.2
  have hdiff : ∀ r : Fin k, P (r.1 + 1) - P r.1 =
      ∏ i : Fin k, if i.1 < r.1 then u i else if i = r then u i - v i else v i := by
    intro r
    have h1 : P (r.1 + 1) = u r * ∏ i ∈ Finset.univ.erase r,
        (if i.1 < r.1 then u i else v i) := by
      dsimp only [P]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
      rw [if_pos (Nat.lt_succ_self r.1)]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i.1 ≠ r.1 := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
      have hiff : i.1 < r.1 + 1 ↔ i.1 < r.1 := by omega
      simp only [hiff]
    have h2 : P r.1 = v r * ∏ i ∈ Finset.univ.erase r,
        (if i.1 < r.1 then u i else v i) := by
      dsimp only [P]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
      rw [if_neg (lt_irrefl r.1)]
    have h3 : (∏ i : Fin k, if i.1 < r.1 then u i else if i = r then u i - v i else v i) =
        (u r - v r) * ∏ i ∈ Finset.univ.erase r, (if i.1 < r.1 then u i else v i) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
      rw [if_neg (lt_irrefl r.1), if_pos rfl]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ r := (Finset.mem_erase.mp hi).1
      simp only [if_neg hne]
    rw [h1, h2, h3]
    ring
  calc (∏ i : Fin k, u i) - (∏ i : Fin k, v i)
      = P k - P 0 := by rw [hPk, hP0]
    _ = ∑ m ∈ Finset.range k, (P (m + 1) - P m) := (Finset.sum_range_sub P k).symm
    _ = ∑ r : Fin k, (P (r.1 + 1) - P r.1) := (Fin.sum_univ_eq_sum_range _ k).symm
    _ = ∑ r : Fin k, ∏ i : Fin k,
          if i.1 < r.1 then u i else if i = r then u i - v i else v i :=
        Finset.sum_congr rfl fun r _ => hdiff r

lemma gvn_cube_lower_bound (h2 : H2) {k p : ℕ} [hp : Fact p.Prime]
    (hk : 5 ≤ k) (hkp : k < p) (S : Finset (ZMod p))
    (hnoAP : ¬ ∃ x d : ZMod p, d ≠ 0 ∧ ∀ i : Fin k, x + (i.1 : ZMod p) * d ∈ S)
    (hbig : 2 ≤ (p : ℝ) * ((S.card : ℝ) / (p : ℝ)) ^ (k - 1)) :
    let α : ℝ := (S.card : ℝ) / (p : ℝ)
    let f : ZMod p → ℝ := fun x => (if x ∈ S then (1 : ℝ) else 0) - α
    (p : ℝ) ^ k * (α ^ k / (2 * (k : ℝ))) ^ (2 ^ (k - 1)) ≤
      ∑ x : ZMod p, ∑ h : Fin (k - 1) → ZMod p,
        ∏ ω : Fin (k - 1) → Bool,
          f (x + ∑ r : Fin (k - 1), if ω r then h r else 0) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  let α : ℝ := (S.card : ℝ) / (p : ℝ)
  let g : ZMod p → ℝ := fun x => if x ∈ S then (1 : ℝ) else 0
  let f : ZMod p → ℝ := fun x => g x - α
  let U : ℝ := ∑ x : ZMod p, ∑ h : Fin (k - 1) → ZMod p,
    ∏ ω : Fin (k - 1) → Bool, f (x + ∑ r : Fin (k - 1), if ω r then h r else 0)
  change (p : ℝ) ^ k * (α ^ k / (2 * (k : ℝ))) ^ (2 ^ (k - 1)) ≤ U
  have hα_nonneg : 0 ≤ α := by positivity
  have hα_le_one : α ≤ 1 := by
    rw [div_le_one hp_pos]
    have hcard : S.card ≤ Fintype.card (ZMod p) := Finset.card_le_univ S
    rw [ZMod.card] at hcard
    exact_mod_cast hcard
  have hg_bdd : ∀ x, |g x| ≤ 1 := fun x => by
    dsimp only [g]
    split_ifs <;> norm_num
  have hα_bdd : |α| ≤ 1 := abs_le.mpr ⟨by linarith, hα_le_one⟩
  -- Count k-APs in S: only d = 0 contributes
  have hcount : ∑ x : ZMod p, ∑ d : ZMod p, ∏ i : Fin k, g (x + (i.1 : ZMod p) * d) =
      (p : ℝ) * α := by
    have hinner : ∀ x : ZMod p,
        ∑ d : ZMod p, ∏ i : Fin k, g (x + (i.1 : ZMod p) * d) = g x := by
      intro x
      rw [Finset.sum_eq_single (0 : ZMod p)]
      · simp only [mul_zero, add_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        dsimp only [g]
        split_ifs
        · simp
        · exact zero_pow (by omega)
      · intro d _ hd0
        have hnot : ¬ ∀ i : Fin k, x + (i.1 : ZMod p) * d ∈ S :=
          fun hall => hnoAP ⟨x, d, hd0, hall⟩
        push Not at hnot
        rcases hnot with ⟨i₀, hi₀⟩
        refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
        simp [g, hi₀]
      · intro h0
        exact absurd (Finset.mem_univ 0) h0
    simp_rw [hinner]
    have hsumg : ∑ x : ZMod p, g x = (S.card : ℝ) := by
      simp [g]
    rw [hsumg]
    dsimp only [α]
    field_simp
  -- Constant term sum
  have hconst : ∑ _x : ZMod p, ∑ _d : ZMod p, ∏ _i : Fin k, α = (p : ℝ) ^ 2 * α ^ k := by
    simp [ZMod.card]
    ring
  -- Define the k telescoping terms
  let Fslot : Fin k → Fin k → ZMod p → ℝ := fun r i =>
    if i.1 < r.1 then g else if i = r then f else fun _ => α
  let T : Fin k → ℝ := fun r =>
    ∑ x : ZMod p, ∑ d : ZMod p, ∏ i : Fin k, Fslot r i (x + (i.1 : ZMod p) * d)
  have htelescope : (p : ℝ) * α - (p : ℝ) ^ 2 * α ^ k = ∑ r : Fin k, T r := by
    rw [← hcount, ← hconst, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    have hpt : ∀ x d : ZMod p,
        (∏ i : Fin k, g (x + (i.1 : ZMod p) * d)) - (∏ _i : Fin k, α) =
        ∑ r : Fin k, ∏ i : Fin k, Fslot r i (x + (i.1 : ZMod p) * d) := by
      intro x d
      have h := prod_sub_prod_fin (fun i : Fin k => g (x + (i.1 : ZMod p) * d)) (fun _ => α)
      refine h.trans (Finset.sum_congr rfl fun r _ => Finset.prod_congr rfl fun i _ => ?_)
      dsimp only [Fslot, f]
      split_ifs <;> rfl
    simp_rw [hpt]
    calc ∑ x : ZMod p, ∑ d : ZMod p, ∑ r : Fin k, ∏ i : Fin k, Fslot r i (x + (i.1 : ZMod p) * d)
        = ∑ x : ZMod p, ∑ r : Fin k, ∑ d : ZMod p,
            ∏ i : Fin k, Fslot r i (x + (i.1 : ZMod p) * d) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ r : Fin k, ∑ x : ZMod p, ∑ d : ZMod p,
            ∏ i : Fin k, Fslot r i (x + (i.1 : ZMod p) * d) := Finset.sum_comm
  -- Bound each T r via H2
  have hT_bound : ∀ r : Fin k, (T r) ^ (2 ^ (k - 1)) ≤ (p : ℝ) ^ (2 ^ k - k) * U := by
    intro r
    let s : ℕ := k - 1
    have hs1 : 1 ≤ s := by omega
    have hsk : s + 1 = k := by omega
    let eCast : Fin (s + 1) ≃ Fin k := finCongr hsk
    let r' : Fin (s + 1) := eCast.symm r
    let σ : Fin (s + 1) ≃ Fin (s + 1) := Equiv.swap r' (Fin.last s)
    let e : Fin (s + 1) ≃ Fin k := σ.trans eCast
    let c' : Fin (s + 1) → ZMod p := fun j => ((e j).1 : ZMod p)
    let f' : Fin (s + 1) → ZMod p → ℝ := fun j => Fslot r (e j)
    have hc'_inj : Function.Injective c' := by
      intro j₁ j₂ hj
      have hval := congrArg ZMod.val hj
      have hlt1 : (e j₁).1 < p := lt_trans (e j₁).2 hkp
      have hlt2 : (e j₂).1 < p := lt_trans (e j₂).2 hkp
      rw [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at hval
      exact e.injective (Fin.ext hval)
    have he_last : e (Fin.last s) = r := by
      change eCast (Equiv.swap r' (Fin.last s) (Fin.last s)) = r
      rw [Equiv.swap_apply_right]
      exact eCast.apply_symm_apply r
    have hf'_bdd : ∀ (j : Fin (s + 1)), j.1 < s → ∀ x, |f' j x| ≤ 1 := by
      intro j hj x
      have hjne : j ≠ Fin.last s := fun h => by
        have := congrArg Fin.val h
        simp at this
        omega
      have hene : e j ≠ r := by
        rw [← he_last]
        exact fun h => hjne (e.injective h)
      simp only [f', Fslot, if_neg hene]
      split_ifs
      · exact hg_bdd x
      · exact hα_bdd
    have hf'_last : f' (Fin.last s) = f := by
      dsimp only [f']
      rw [he_last]
      dsimp only [Fslot]
      rw [if_neg (lt_irrefl r.1), if_pos rfl]
    have hsum_eq : ∑ x : ZMod p, ∑ d : ZMod p, ∏ j : Fin (s + 1), f' j (x + c' j * d) = T r := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => ?_
      exact Fintype.prod_equiv e _ _ fun _ => rfl
    have hgv := h2 s hs1 p c' hc'_inj f' hf'_bdd
    rw [hsum_eq, hf'_last] at hgv
    have hexp : 2 ^ (s + 1) - (s + 1) = 2 ^ k - k := by rw [hsk]
    simpa only [hexp] using hgv
  -- Combine the k bounds using the maximum |T r|
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨r₀, -, hr₀max⟩ := Finset.exists_max_image Finset.univ (fun r : Fin k => |T r|) hne
  have heven : Even (2 ^ (k - 1)) := by
    refine ⟨2 ^ (k - 2), ?_⟩
    have h1 : k - 1 = (k - 2) + 1 := by omega
    rw [h1, pow_succ]
    ring
  have habs_D : (p : ℝ) ^ 2 * α ^ k / 2 ≤ |∑ r : Fin k, T r| := by
    have hneg : -(∑ r : Fin k, T r) = (p : ℝ) ^ 2 * α ^ k - (p : ℝ) * α := by
      linarith [htelescope]
    have hle : (p : ℝ) ^ 2 * α ^ k / 2 ≤ (p : ℝ) ^ 2 * α ^ k - (p : ℝ) * α := by
      have hmul : 2 * ((p : ℝ) * α) ≤ (p : ℝ) * α ^ (k - 1) * ((p : ℝ) * α) :=
        mul_le_mul_of_nonneg_right hbig (by positivity)
      have hpow : (p : ℝ) * α ^ (k - 1) * ((p : ℝ) * α) = (p : ℝ) ^ 2 * α ^ k := by
        have hk1 : k - 1 + 1 = k := by omega
        calc (p : ℝ) * α ^ (k - 1) * ((p : ℝ) * α)
            = (p : ℝ) ^ 2 * (α ^ (k - 1) * α) := by ring
          _ = (p : ℝ) ^ 2 * α ^ (k - 1 + 1) := by rw [← pow_succ α (k - 1)]
          _ = (p : ℝ) ^ 2 * α ^ k := by rw [hk1]
      linarith
    calc (p : ℝ) ^ 2 * α ^ k / 2
        ≤ -(∑ r : Fin k, T r) := by linarith
      _ ≤ |∑ r : Fin k, T r| := neg_le_abs _
  have hsum_le : |∑ r : Fin k, T r| ≤ (k : ℝ) * |T r₀| := by
    calc |∑ r : Fin k, T r|
        ≤ ∑ r : Fin k, |T r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : Fin k, |T r₀| := Finset.sum_le_sum fun r _ => hr₀max r (Finset.mem_univ r)
      _ = (k : ℝ) * |T r₀| := by simp
  have hpow_bound : ((p : ℝ) ^ 2 * α ^ k / 2) ^ (2 ^ (k - 1)) ≤
      (k : ℝ) ^ (2 ^ (k - 1)) * ((p : ℝ) ^ (2 ^ k - k) * U) := by
    have hstep := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 2 * α ^ k / 2)
      (habs_D.trans hsum_le) (2 ^ (k - 1))
    calc ((p : ℝ) ^ 2 * α ^ k / 2) ^ (2 ^ (k - 1))
        ≤ ((k : ℝ) * |T r₀|) ^ (2 ^ (k - 1)) := hstep
      _ = (k : ℝ) ^ (2 ^ (k - 1)) * |T r₀| ^ (2 ^ (k - 1)) := mul_pow _ _ _
      _ = (k : ℝ) ^ (2 ^ (k - 1)) * (T r₀) ^ (2 ^ (k - 1)) := by rw [heven.pow_abs]
      _ ≤ (k : ℝ) ^ (2 ^ (k - 1)) * ((p : ℝ) ^ (2 ^ k - k) * U) :=
          mul_le_mul_of_nonneg_left (hT_bound r₀) (by positivity)
  -- Divide out (k : ℝ) ^ (2^(k-1)) * (p : ℝ) ^ (2^k - k)
  have hfac_pos : (0 : ℝ) < (k : ℝ) ^ (2 ^ (k - 1)) * (p : ℝ) ^ (2 ^ k - k) := by positivity
  have hp_pow : (p : ℝ) ^ (2 ^ k - k) * (p : ℝ) ^ k = ((p : ℝ) ^ 2) ^ (2 ^ (k - 1)) := by
    rw [← pow_add, ← pow_mul]
    congr 1
    have hle : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    have h2k : 2 * 2 ^ (k - 1) = 2 ^ k := by
      have hk1 : k = (k - 1) + 1 := by omega
      conv_rhs => rw [hk1, pow_succ']
    omega
  have hlhs_eq : (k : ℝ) ^ (2 ^ (k - 1)) * (p : ℝ) ^ (2 ^ k - k) *
      ((p : ℝ) ^ k * (α ^ k / (2 * (k : ℝ))) ^ (2 ^ (k - 1))) =
      ((p : ℝ) ^ 2 * α ^ k / 2) ^ (2 ^ (k - 1)) := by
    calc (k : ℝ) ^ (2 ^ (k - 1)) * (p : ℝ) ^ (2 ^ k - k) *
            ((p : ℝ) ^ k * (α ^ k / (2 * (k : ℝ))) ^ (2 ^ (k - 1)))
        = ((p : ℝ) ^ (2 ^ k - k) * (p : ℝ) ^ k) *
            ((k : ℝ) ^ (2 ^ (k - 1)) * (α ^ k / (2 * (k : ℝ))) ^ (2 ^ (k - 1))) := by ring
      _ = ((p : ℝ) ^ 2) ^ (2 ^ (k - 1)) *
            ((k : ℝ) * (α ^ k / (2 * (k : ℝ)))) ^ (2 ^ (k - 1)) := by
          rw [hp_pow, ← mul_pow]
      _ = ((p : ℝ) ^ 2 * ((k : ℝ) * (α ^ k / (2 * (k : ℝ))))) ^ (2 ^ (k - 1)) := by
          rw [← mul_pow]
      _ = ((p : ℝ) ^ 2 * α ^ k / 2) ^ (2 ^ (k - 1)) := by
          congr 1
          field_simp
  refine le_of_mul_le_mul_left ?_ hfac_pos
  rw [hlhs_eq]
  linarith [hpow_bound]

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2.H3 := by
  intro h1 h2 k hk
  obtain ⟨B, hB, hEv⟩ := h1 k hk
  have hBnorm : Summable (fun j : ℕ => ‖B j‖) := summable_norm_iff.mpr hB
  let q : ℝ := ((4 : ℝ)⁻¹) ^ (1 / ((k - 1 : ℕ) : ℝ))
  have hkm1_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one (by positivity) (by norm_num) (by positivity)
  have hqpow : q ^ (k - 1) = (4 : ℝ)⁻¹ := by
    dsimp only [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have hmul : 1 / ((k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) = 1 := by field_simp
    rw [hmul, Real.rpow_one]
  have hDom : Summable (fun j : ℕ => 4 * (‖B j‖ + q ^ j)) :=
    (hBnorm.add (summable_geometric_of_lt_one hq0 hq1)).mul_left 4
  refine Summable.of_norm_bounded_eventually_nat hDom ?_
  filter_upwards [hEv, eventually_ge_atTop k] with j hj hjk
  have hkj : k ≤ 2 * 4 ^ j := by
    have h1 : j < 2 ^ j := Nat.lt_two_pow_self
    have h2 : 2 ^ j ≤ 4 ^ j := Nat.pow_le_pow_left (by norm_num) j
    omega
  rw [Real.norm_of_nonneg (by positivity)]
  obtain ⟨p, hpPrime, hpLo, hpHi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * 4 ^ j) (by positivity)
  have hpHi' : p ≤ 4 * 4 ^ j := by omega
  have : Fact p.Prime := ⟨hpPrime⟩
  have hkp : k < p := by omega
  obtain ⟨S₀, hS₀sub, hS₀free, hS₀card⟩ := exists_max_apFree k (4 ^ j) (by omega)
  let S : Finset (ZMod p) := S₀.image (Nat.cast : ℕ → ZMod p)
  have ⟨hScard, hnoAP⟩ := embed_ap_free (p := p) (by omega) hpLo hS₀sub hS₀free
  let α : ℝ := (S.card : ℝ) / (p : ℝ)
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
  have hα_nonneg : 0 ≤ α := by positivity
  have hα_bound : α ≤ ‖B j‖ + q ^ j := by
    by_cases hbig : 2 ≤ (p : ℝ) * α ^ (k - 1)
    · have hcube := gvn_cube_lower_bound h2 hk hkp S hnoAP hbig
      have hα_le_B : α ≤ B j := by
        by_contra hlt
        push Not at hlt
        exact hnoAP (hj p hpLo hpHi' S hlt hcube)
      have hB_le : B j ≤ ‖B j‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
      linarith [pow_nonneg hq0 j]
    · push Not at hbig
      have hpLoR : 2 * (4 : ℝ) ^ j ≤ (p : ℝ) := by exact_mod_cast hpLo.le
      have hpow_le : α ^ (k - 1) ≤ (q ^ j) ^ (k - 1) := by
        have h1 : (2 * (4 : ℝ) ^ j) * α ^ (k - 1) ≤ 2 :=
          (mul_le_mul_of_nonneg_right hpLoR (by positivity)).trans hbig.le
        have h2' : α ^ (k - 1) ≤ ((4 : ℝ)⁻¹) ^ j := by
          rw [inv_pow, ← one_div, le_div_iff₀ (by positivity)]
          linarith
        calc α ^ (k - 1) ≤ ((4 : ℝ)⁻¹) ^ j := h2'
          _ = (q ^ (k - 1)) ^ j := by rw [hqpow]
          _ = (q ^ j) ^ (k - 1) := by rw [← pow_mul, mul_comm, pow_mul]
      have hαq : α ≤ q ^ j := le_of_pow_le_pow_left₀ (by omega) (by positivity) hpow_le
      linarith [norm_nonneg (B j)]
  have h4j_pos : (0 : ℝ) < (4 : ℝ) ^ j := by positivity
  have hpHiR : (p : ℝ) ≤ 4 * (4 : ℝ) ^ j := by exact_mod_cast hpHi'
  have hr_eq : (Erdos142.r k (4 ^ j) : ℝ) = (p : ℝ) * α := by
    dsimp only [α]
    rw [hScard, hS₀card]
    field_simp
  calc (Erdos142.r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j
      = ((p : ℝ) / (4 : ℝ) ^ j) * α := by rw [hr_eq]; ring
    _ ≤ 4 * α := by
        refine mul_le_mul_of_nonneg_right ?_ hα_nonneg
        rw [div_le_iff₀ h4j_pos]
        exact hpHiR
    _ ≤ 4 * (‖B j‖ + q ^ j) := mul_le_mul_of_nonneg_left hα_bound (by norm_num)

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R4
