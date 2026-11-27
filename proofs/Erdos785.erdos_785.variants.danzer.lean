import FormalConjectures.ErdosProblems.«785»

-- Problem: Erdős Problem 785 — danzer
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/785.lean:93 (declaration Erdos785.erdos_785.variants.danzer)
-- Credit: @OrangeHeadz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Sketch.  Put `a i = i + (i ^ 2)!`, `X k = k * a k`, `Y k = (k + 1) * a k` and `m k = k - ⌊√k⌋`.
Take `A = {a i : i ≥ 1}` and let `B` be the union over `k ≥ 4` of the multiples of `m k` in
`[X k, Y (k + 1))`.

* If `√k < i ≤ k` then `m k ≤ k < i ^ 2`, so `m k ∣ (i ^ 2)!` and `a i ≡ i (mod m k)`.  The
  `m k` consecutive indices `√k < i ≤ k` therefore give every residue modulo `m k`, and every
  `n ∈ [Y k, Y (k + 1))` is `a i + b` with `b` a multiple of `m k` in `[X k, Y (k + 1))`.
* For `X (j + 1) ≤ x < X (j + 2)` the set `A` has `j + 1` or `j + 2` elements up to `x`, while `B`
  has between `(x - X j) / m (j + 1) - 2` and `Y j + (x + a (j + 1)) / m j + 2`.  Because
  `(j + 1) ^ 3 * a j ≤ a (j + 1)`, the product of the two counts is `x (1 + o(1))`.
-/

namespace OMA785

open Finset
open scoped Pointwise

/-- The modulus used at stage `k`. -/
def md (k : ℕ) : ℕ := k - Nat.sqrt k

/-- The elements of the sparse set. -/
def av (i : ℕ) : ℕ := i + (i ^ 2).factorial

def X (k : ℕ) : ℕ := k * av k

def Y (k : ℕ) : ℕ := (k + 1) * av k

def Bset : Set ℕ := {b | ∃ k, 4 ≤ k ∧ md k ∣ b ∧ X k ≤ b ∧ b < Y (k + 1)}

def Aset : Set ℕ := Set.range fun i : ℕ => av (i + 1)

/- Basic facts about the sequences. -/

lemma av_lt_succ (i : ℕ) : av i < av (i + 1) := by
  unfold av
  have h : (i ^ 2).factorial ≤ ((i + 1) ^ 2).factorial :=
    Nat.factorial_le (Nat.pow_le_pow_left (Nat.le_succ i) 2)
  omega

lemma av_strictMono : StrictMono av := strictMono_nat_of_lt_succ av_lt_succ

lemma le_av (i : ℕ) : i ≤ av i := Nat.le_add_right _ _

lemma av_pos (i : ℕ) : 0 < av i := by
  unfold av
  have := Nat.factorial_pos (i ^ 2)
  omega

lemma av_growth (j : ℕ) (hj : 1 ≤ j) : (j + 1) ^ 3 * av j ≤ av (j + 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
  obtain ⟨F, hF⟩ : ∃ F, F = ((t + 1) ^ 2).factorial := ⟨_, rfl⟩
  have h1 : av (t + 1) ≤ 2 * F := by
    unfold av
    have h : t + 1 ≤ ((t + 1) ^ 2).factorial :=
      (Nat.le_self_pow (by norm_num) _).trans (Nat.self_le_factorial _)
    rw [← hF] at h ⊢
    omega
  have e : (t + 1) ^ 2 = t ^ 2 + 2 * t + 1 := by ring
  have e' : (t + 1 + 1) ^ 2 = t ^ 2 + 4 * t + 4 := by ring
  have h2 : ((t + 1) ^ 2 + 3).factorial ≤ ((t + 1 + 1) ^ 2).factorial :=
    Nat.factorial_le (by omega)
  have h3 : ((t + 1) ^ 2 + 3).factorial =
      ((t + 1) ^ 2 + 3) * (((t + 1) ^ 2 + 2) * (((t + 1) ^ 2 + 1) * F)) := by
    rw [hF, show (t + 1) ^ 2 + 3 = ((t + 1) ^ 2 + 2) + 1 from rfl, Nat.factorial_succ,
      show (t + 1) ^ 2 + 2 = ((t + 1) ^ 2 + 1) + 1 from rfl, Nat.factorial_succ,
      Nat.factorial_succ]
  have a1 : 2 * (t + 2) ≤ (t + 1) ^ 2 + 3 := by omega
  have a2 : t + 2 ≤ (t + 1) ^ 2 + 2 := by omega
  have a3 : t + 2 ≤ (t + 1) ^ 2 + 1 := by omega
  have h4 : 2 * (t + 2) * ((t + 2) * (t + 2)) ≤
      ((t + 1) ^ 2 + 3) * (((t + 1) ^ 2 + 2) * ((t + 1) ^ 2 + 1)) :=
    Nat.mul_le_mul a1 (Nat.mul_le_mul a2 a3)
  have h5 : av (t + 1 + 1) ≥ ((t + 1 + 1) ^ 2).factorial := by
    unfold av; omega
  calc (t + 1 + 1) ^ 3 * av (t + 1) ≤ (t + 1 + 1) ^ 3 * (2 * F) := Nat.mul_le_mul_left _ h1
    _ = 2 * (t + 2) * ((t + 2) * (t + 2)) * F := by ring
    _ ≤ ((t + 1) ^ 2 + 3) * (((t + 1) ^ 2 + 2) * ((t + 1) ^ 2 + 1)) * F :=
        Nat.mul_le_mul_right _ h4
    _ = ((t + 1) ^ 2 + 3).factorial := by rw [h3]; ring
    _ ≤ ((t + 1 + 1) ^ 2).factorial := h2
    _ ≤ av (t + 1 + 1) := h5

lemma Y_eq (k : ℕ) : Y k = X k + av k := by unfold X Y; ring

lemma X_lt_succ (k : ℕ) : X k < X (k + 1) := by
  unfold X
  have h1 := (av_lt_succ k).le
  have h2 := av_pos (k + 1)
  calc k * av k ≤ k * av (k + 1) := Nat.mul_le_mul_left _ h1
    _ < k * av (k + 1) + av (k + 1) := by omega
    _ = (k + 1) * av (k + 1) := by ring

lemma X_strictMono : StrictMono X := strictMono_nat_of_lt_succ X_lt_succ

lemma Y_le_X_succ (k : ℕ) : Y k ≤ X (k + 1) := by
  unfold X Y
  exact Nat.mul_le_mul_left _ (av_lt_succ k).le

lemma Y_lt_succ (k : ℕ) : Y k < Y (k + 1) := by
  have h1 := Y_le_X_succ k
  have h2 := Y_eq (k + 1)
  have h3 := av_pos (k + 1)
  omega

lemma Y_strictMono : StrictMono Y := strictMono_nat_of_lt_succ Y_lt_succ

lemma le_X (k : ℕ) : k ≤ X k := by
  unfold X
  exact Nat.le_mul_of_pos_right _ (av_pos k)

lemma md_pos {k : ℕ} (hk : 2 ≤ k) : 0 < md k := by
  unfold md
  have := Nat.sqrt_lt_self (show 1 < k by omega)
  omega

lemma md_le (k : ℕ) : md k ≤ k := Nat.sub_le _ _

lemma md_le_succ (k : ℕ) : md k ≤ md (k + 1) := by
  unfold md
  have h1 : Nat.sqrt (k + 1) ≤ Nat.sqrt k + 1 := Nat.sqrt_succ_le_succ_sqrt k
  have h2 := Nat.sqrt_le_self k
  have h3 := Nat.sqrt_le_self (k + 1)
  omega

/-- Locating `x` between consecutive values of a strictly increasing sequence. -/
lemma stage (f : ℕ → ℕ) (hf : StrictMono f) {K x : ℕ} (hx : f K ≤ x) :
    ∃ k, K ≤ k ∧ f k ≤ x ∧ x < f (k + 1) := by
  have hid : ∀ n, n ≤ f n := hf.id_le
  have hKx : K ≤ x := (hid K).trans hx
  refine ⟨Nat.findGreatest (fun j => f j ≤ x) x, Nat.le_findGreatest hKx hx,
    Nat.findGreatest_spec (P := fun j => f j ≤ x) hKx hx, ?_⟩
  by_contra hcon
  have h1 : f (Nat.findGreatest (fun j => f j ≤ x) x + 1) ≤ x := Nat.le_of_not_lt hcon
  have h2 : Nat.findGreatest (fun j => f j ≤ x) x + 1 ≤ x := (hid _).trans h1
  have h3 := Nat.le_findGreatest (P := fun j => f j ≤ x) h2 h1
  omega

/-- Counting multiples of `m` in `(L, U]`. -/
lemma card_mul (m L U : ℕ) (hLU : L ≤ U) :
    ((Finset.Ioc L U).filter (fun b => m ∣ b)).card + L / m = U / m := by
  have h1 := Nat.Ioc_filter_dvd_card_eq_div U m
  have h2 := Nat.Ioc_filter_dvd_card_eq_div L m
  have hunion : (Finset.Ioc 0 U).filter (fun b => m ∣ b) =
      (Finset.Ioc 0 L).filter (fun b => m ∣ b) ∪ (Finset.Ioc L U).filter (fun b => m ∣ b) := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le L) hLU]
  have hdisj : Disjoint ((Finset.Ioc 0 L).filter (fun b => m ∣ b))
      ((Finset.Ioc L U).filter (fun b => m ∣ b)) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rw [Finset.mem_filter, Finset.mem_Ioc] at hb1 hb2
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj, h2] at h1
  omega

/- The sum set. -/

lemma mem_add_of_large {n : ℕ} (hn : Y 4 ≤ n) : n ∈ Aset + Bset := by
  obtain ⟨k, hk, hYk, hnk⟩ := stage Y Y_strictMono hn
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt k := ⟨_, rfl⟩
  have hmpos : 0 < md k := md_pos (by omega)
  have hsk : s < k := by rw [hs]; exact Nat.sqrt_lt_self (by omega)
  have hmd : md k + s = k := by unfold md; rw [← hs]; omega
  obtain ⟨r, hr⟩ : ∃ r, r = (n - (s + 1)) % md k := ⟨_, rfl⟩
  have hrlt : r < md k := by rw [hr]; exact Nat.mod_lt _ hmpos
  obtain ⟨i, hi⟩ : ∃ i, i = s + 1 + r := ⟨_, rfl⟩
  have hik : i ≤ k := by omega
  have hksq : k < (s + 1) ^ 2 := by rw [hs]; exact Nat.lt_succ_sqrt' k
  have hisq : (s + 1) ^ 2 ≤ i ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hdvd1 : md k ∣ (i ^ 2).factorial :=
    Nat.dvd_factorial hmpos (by have := md_le k; omega)
  have havi : av i ≤ av k := av_strictMono.monotone hik
  have hYeq := Y_eq k
  have hkav := le_av k
  have hdvd2 : md k ∣ (n - (s + 1)) - r := by rw [hr]; exact Nat.dvd_sub_mod _
  have hbeq : n - av i = ((n - (s + 1)) - r) - (i ^ 2).factorial := by
    unfold av
    omega
  have hdvd : md k ∣ n - av i := by rw [hbeq]; exact Nat.dvd_sub hdvd2 hdvd1
  refine Set.mem_add.2 ⟨av i, ⟨i - 1, ?_⟩, n - av i, ⟨k, hk, hdvd, by omega, by omega⟩, by omega⟩
  show av (i - 1 + 1) = av i
  rw [Nat.sub_add_cancel (by omega)]

/- Counting the sparse set. -/

lemma countA_bounds {k x : ℕ} (hk : 1 ≤ k) (h1 : X k ≤ x) (h2 : x < X (k + 1)) :
    k ≤ (Aset ∩ Set.Icc 1 x).ncard ∧ (Aset ∩ Set.Icc 1 x).ncard ≤ k + 1 := by
  constructor
  · have hsub : (((Finset.Icc 1 k).image av : Finset ℕ) : Set ℕ) ⊆ Aset ∩ Set.Icc 1 x := by
      intro b hb
      rw [Finset.mem_coe, Finset.mem_image] at hb
      obtain ⟨i, hi, rfl⟩ := hb
      rw [Finset.mem_Icc] at hi
      refine ⟨⟨i - 1, ?_⟩, av_pos i, ?_⟩
      · show av (i - 1 + 1) = av i
        rw [Nat.sub_add_cancel hi.1]
      · have h3 : av i ≤ av k := av_strictMono.monotone hi.2
        have h4 : av k ≤ X k := by
          unfold X
          exact Nat.le_mul_of_pos_left _ (by omega)
        omega
    have hfin : (Aset ∩ Set.Icc 1 x).Finite := (Set.finite_Icc 1 x).inter_of_right _
    have h := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ av_strictMono.injective,
      Nat.card_Icc] at h
    omega
  · have hsub : Aset ∩ Set.Icc 1 x ⊆ (((Finset.Icc 1 (k + 1)).image av : Finset ℕ) : Set ℕ) := by
      rintro b ⟨⟨i, rfl⟩, -, hbx⟩
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨i + 1, ?_, rfl⟩
      rw [Finset.mem_Icc]
      refine ⟨by omega, ?_⟩
      by_contra hcon
      have h3 : av (k + 1 + 1) ≤ av (i + 1) := av_strictMono.monotone (by omega)
      have h4 := av_growth (k + 1) (by omega)
      have h5 : (k + 1) * av (k + 1) < (k + 1 + 1) ^ 3 * av (k + 1) := by
        apply Nat.mul_lt_mul_of_pos_right _ (av_pos _)
        calc k + 1 < k + 1 + 1 := by omega
          _ ≤ (k + 1 + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      have h6 : X (k + 1) = (k + 1) * av (k + 1) := rfl
      simp only [] at hbx
      omega
    have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h
    have h' := Finset.card_image_le (s := Finset.Icc 1 (k + 1)) (f := av)
    rw [Nat.card_Icc] at h'
    omega

/- Counting the dense set. -/

lemma countB_upper {j x : ℕ} (hj : 4 ≤ j) (h1 : X (j + 1) ≤ x) (h2 : x < X (j + 2)) :
    md j * (Bset ∩ Set.Icc 1 x).ncard ≤ md j * Y j + x + av (j + 1) + md (j + 1) := by
  obtain ⟨F1, hF1⟩ : ∃ F : Finset ℕ, F = Finset.Ioc 0 (Y j) := ⟨_, rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F : Finset ℕ, F = (Finset.Ioc 0 (Y (j + 1))).filter (fun b => md j ∣ b) :=
    ⟨_, rfl⟩
  obtain ⟨F3, hF3⟩ : ∃ F : Finset ℕ,
      F = (Finset.Ioc (X (j + 1) - 1) x).filter (fun b => md (j + 1) ∣ b) := ⟨_, rfl⟩
  have hXpos : 0 < X (j + 1) := lt_of_lt_of_le (by omega) (le_X (j + 1))
  have hsub : Bset ∩ Set.Icc 1 x ⊆ ((F1 ∪ F2 ∪ F3 : Finset ℕ) : Set ℕ) := by
    rintro b ⟨⟨i, hi4, hdvd, hXi, hYi⟩, hb1, hbx⟩
    have hilt : i < j + 2 := X_strictMono.lt_iff_lt.1 (by omega)
    rw [Finset.mem_coe, Finset.mem_union, Finset.mem_union]
    rcases Nat.lt_or_ge i j with hij | hij
    · left; left
      rw [hF1, Finset.mem_Ioc]
      have h3 : Y (i + 1) ≤ Y j := Y_strictMono.monotone (by omega)
      exact ⟨hb1, by omega⟩
    · rcases Nat.eq_or_lt_of_le hij with rfl | hij'
      · left; right
        rw [hF2, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hb1, hYi.le⟩, hdvd⟩
      · have hi : i = j + 1 := by omega
        subst hi
        right
        rw [hF3, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨by omega, hbx⟩, hdvd⟩
  have hc := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hc
  have hc1 : (F1 ∪ F2 ∪ F3).card ≤ F1.card + F2.card + F3.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hcard1 : F1.card = Y j := by rw [hF1, Nat.card_Ioc]; omega
  have hcard2 : F2.card = Y (j + 1) / md j := by
    rw [hF2]; exact Nat.Ioc_filter_dvd_card_eq_div _ _
  have hcard3 : F3.card + (X (j + 1) - 1) / md (j + 1) = x / md (j + 1) := by
    rw [hF3]; exact card_mul _ _ _ (by omega)
  have hm' : 0 < md j := md_pos (by omega)
  have hm : 0 < md (j + 1) := md_pos (by omega)
  have hmm : md j ≤ md (j + 1) := md_le_succ j
  obtain ⟨c, hcdef⟩ : ∃ c, c = (Bset ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
  rw [← hcdef] at hc ⊢
  obtain ⟨q1, hq1⟩ : ∃ q, q = Y (j + 1) / md j := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q, q = x / md (j + 1) := ⟨_, rfl⟩
  obtain ⟨q3, hq3⟩ : ∃ q, q = (X (j + 1) - 1) / md (j + 1) := ⟨_, rfl⟩
  rw [← hq1] at hcard2
  rw [← hq2, ← hq3] at hcard3
  have b1 : md j * q1 ≤ Y (j + 1) := by rw [hq1]; exact Nat.mul_div_le _ _
  have b2 : md (j + 1) * q2 ≤ x := by rw [hq2]; exact Nat.mul_div_le _ _
  have b3 : X (j + 1) - 1 < md (j + 1) * q3 + md (j + 1) := by
    have := Nat.lt_mul_div_succ (X (j + 1) - 1) hm
    rw [← hq3] at this
    calc X (j + 1) - 1 < md (j + 1) * (q3 + 1) := this
      _ = md (j + 1) * q3 + md (j + 1) := by ring
  have e1 : md (j + 1) * F3.card + md (j + 1) * q3 = md (j + 1) * q2 := by
    rw [← Nat.mul_add, hcard3]
  have e2 : md j * F3.card ≤ md (j + 1) * F3.card := Nat.mul_le_mul_right _ hmm
  have e3 : md j * c ≤ md j * Y j + md j * q1 + md j * F3.card := by
    calc md j * c ≤ md j * (Y j + q1 + F3.card) := Nat.mul_le_mul_left _ (by omega)
      _ = md j * Y j + md j * q1 + md j * F3.card := by ring
  have hYeq := Y_eq (j + 1)
  omega

lemma countB_lower {j x : ℕ} (hj : 4 ≤ j) (h1 : X (j + 1) ≤ x) (h2 : x < X (j + 2)) :
    x ≤ md (j + 1) * (Bset ∩ Set.Icc 1 x).ncard + X j + 2 * md (j + 1) := by
  obtain ⟨G1, hG1⟩ : ∃ F : Finset ℕ,
      F = (Finset.Ioc (X j - 1) (X (j + 1) - 1)).filter (fun b => md j ∣ b) := ⟨_, rfl⟩
  obtain ⟨F3, hF3⟩ : ∃ F : Finset ℕ,
      F = (Finset.Ioc (X (j + 1) - 1) x).filter (fun b => md (j + 1) ∣ b) := ⟨_, rfl⟩
  have hXj : j ≤ X j := le_X j
  have hXlt : X j < X (j + 1) := X_lt_succ j
  have hYeq1 := Y_eq (j + 1)
  have hYeq2 := Y_eq (j + 2)
  have hsub : ((G1 ∪ F3 : Finset ℕ) : Set ℕ) ⊆ Bset ∩ Set.Icc 1 x := by
    intro b hb
    rw [Finset.mem_coe, Finset.mem_union] at hb
    rcases hb with hb | hb
    · rw [hG1, Finset.mem_filter, Finset.mem_Ioc] at hb
      exact ⟨⟨j, hj, hb.2, by omega, by omega⟩, by omega, by omega⟩
    · rw [hF3, Finset.mem_filter, Finset.mem_Ioc] at hb
      exact ⟨⟨j + 1, by omega, hb.2, by omega, (show b < Y (j + 2) by omega)⟩, by omega, hb.1.2⟩
  have hdisj : Disjoint G1 F3 := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rw [hG1, Finset.mem_filter, Finset.mem_Ioc] at hb1
    rw [hF3, Finset.mem_filter, Finset.mem_Ioc] at hb2
    omega
  have hfin : (Bset ∩ Set.Icc 1 x).Finite := (Set.finite_Icc 1 x).inter_of_right _
  have hc := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj] at hc
  have hm' : 0 < md j := md_pos (by omega)
  have hm : 0 < md (j + 1) := md_pos (by omega)
  have hmm : md j ≤ md (j + 1) := md_le_succ j
  obtain ⟨c, hcdef⟩ : ∃ c, c = (Bset ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
  rw [← hcdef] at hc ⊢
  obtain ⟨q2, hq2⟩ : ∃ q, q = x / md (j + 1) := ⟨_, rfl⟩
  obtain ⟨q3, hq3⟩ : ∃ q, q = (X (j + 1) - 1) / md (j + 1) := ⟨_, rfl⟩
  obtain ⟨q4, hq4⟩ : ∃ q, q = (X (j + 1) - 1) / md j := ⟨_, rfl⟩
  obtain ⟨q5, hq5⟩ : ∃ q, q = (X j - 1) / md j := ⟨_, rfl⟩
  have hcard3 : F3.card + q3 = q2 := by
    rw [hF3, hq3, hq2]; exact card_mul _ _ _ (by omega)
  have hcard1 : G1.card + q5 = q4 := by
    rw [hG1, hq5, hq4]; exact card_mul _ _ _ (by omega)
  have b2 : x < md (j + 1) * q2 + md (j + 1) := by
    have := Nat.lt_mul_div_succ x hm
    rw [← hq2] at this
    calc x < md (j + 1) * (q2 + 1) := this
      _ = md (j + 1) * q2 + md (j + 1) := by ring
  have b3 : md (j + 1) * q3 ≤ X (j + 1) - 1 := by rw [hq3]; exact Nat.mul_div_le _ _
  have b4 : X (j + 1) - 1 < md j * q4 + md j := by
    have := Nat.lt_mul_div_succ (X (j + 1) - 1) hm'
    rw [← hq4] at this
    calc X (j + 1) - 1 < md j * (q4 + 1) := this
      _ = md j * q4 + md j := by ring
  have b5 : md j * q5 ≤ X j - 1 := by rw [hq5]; exact Nat.mul_div_le _ _
  have e1 : md (j + 1) * F3.card + md (j + 1) * q3 = md (j + 1) * q2 := by
    rw [← Nat.mul_add, hcard3]
  have e2 : md j * G1.card + md j * q5 = md j * q4 := by
    rw [← Nat.mul_add, hcard1]
  have e3 : md j * G1.card ≤ md (j + 1) * G1.card := Nat.mul_le_mul_right _ hmm
  have e4 : md (j + 1) * G1.card + md (j + 1) * F3.card ≤ md (j + 1) * c := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hc
  omega

/- The product of the two counts. -/

lemma ratio_bounds {j x T : ℕ} (hj : 4 ≤ j) (hT : (9 * T + 10) ^ 2 ≤ j)
    (h1 : X (j + 1) ≤ x) (h2 : x < X (j + 2)) :
    T * x ≤ (T + 1) * ((Aset ∩ Set.Icc 1 x).ncard * (Bset ∩ Set.Icc 1 x).ncard) ∧
      (T + 1) * ((Aset ∩ Set.Icc 1 x).ncard * (Bset ∩ Set.Icc 1 x).ncard) ≤ (T + 2) * x := by
  obtain ⟨hA1, hA2⟩ := countA_bounds (k := j + 1) (by omega) h1 h2
  have hU := countB_upper hj h1 h2
  have hL := countB_lower hj h1 h2
  obtain ⟨cA, hcA⟩ : ∃ c, c = (Aset ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (Bset ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
  rw [← hcA] at hA1 hA2 ⊢
  rw [← hc] at hU hL ⊢
  obtain ⟨α, hα⟩ : ∃ α, α = av (j + 1) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = Y j := ⟨_, rfl⟩
  obtain ⟨m', hm'⟩ : ∃ m, m = md j := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = md (j + 1) := ⟨_, rfl⟩
  rw [← hα, ← hP, ← hm', ← hm] at hU
  rw [← hm] at hL
  have hm'pos : 0 < m' := by rw [hm']; exact md_pos (by omega)
  have hm'j : m' ≤ j := by rw [hm']; exact md_le j
  have hmj : m ≤ j + 1 := by rw [hm]; exact md_le (j + 1)
  have hαj : j + 1 ≤ α := by rw [hα]; exact le_av (j + 1)
  have hxα : (j + 1) * α ≤ x := by rw [hα]; exact h1
  have hPα : (j + 1) ^ 2 * P ≤ α := by
    have := av_growth j (by omega)
    rw [hP, hα]
    calc (j + 1) ^ 2 * Y j = (j + 1) ^ 3 * av j := by unfold Y; ring
      _ ≤ av (j + 1) := this
  have hXP : X j ≤ P := by
    rw [hP]; unfold X Y
    exact Nat.mul_le_mul_right _ (by omega)
  -- auxiliary products
  have p1 : (j + 1) * P ≤ α := by
    calc (j + 1) * P ≤ (j + 1) * ((j + 1) * P) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
      _ = (j + 1) ^ 2 * P := by ring
      _ ≤ α := hPα
  have p2 : m' * P ≤ α := (Nat.mul_le_mul_right _ (by omega)).trans p1
  have p3 : α ≤ (j + 1) * α := Nat.le_mul_of_pos_left _ (by omega)
  -- upper bound
  have hUp : m' * (cA * c) ≤ (j + 8) * x := by
    have s1 : m' * (cA * c) ≤ (j + 2) * (m' * P + x + α + m) := by
      calc m' * (cA * c) = cA * (m' * c) := by ring
        _ ≤ (j + 2) * (m' * P + x + α + m) := Nat.mul_le_mul hA2 hU
    have s2 : (j + 2) * (m' * P + α + m) ≤ 6 * x := by
      calc (j + 2) * (m' * P + α + m) ≤ (2 * (j + 1)) * (3 * α) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = 6 * ((j + 1) * α) := by ring
        _ ≤ 6 * x := Nat.mul_le_mul_left _ hxα
    calc m' * (cA * c) ≤ (j + 2) * (m' * P + x + α + m) := s1
      _ = (j + 2) * x + (j + 2) * (m' * P + α + m) := by ring
      _ ≤ (j + 2) * x + 6 * x := Nat.add_le_add_left s2 _
      _ = (j + 8) * x := by ring
  -- lower bound
  have hLo : (j + 1) * x ≤ (j + 1) * (cA * c) + 3 * x := by
    have s1 : (j + 1) * x ≤ (j + 1) * (m * c + X j + 2 * m) := Nat.mul_le_mul_left _ hL
    have s2 : (j + 1) * (X j + 2 * m) ≤ 3 * x := by
      have t1 : (j + 1) * X j ≤ α := (Nat.mul_le_mul_left _ hXP).trans p1
      have t2 : (j + 1) * (2 * m) ≤ 2 * ((j + 1) * α) := by
        calc (j + 1) * (2 * m) ≤ (j + 1) * (2 * α) := Nat.mul_le_mul_left _ (by omega)
          _ = 2 * ((j + 1) * α) := by ring
      have t3 : (j + 1) * (X j + 2 * m) = (j + 1) * X j + (j + 1) * (2 * m) := by ring
      omega
    have s3 : (j + 1) * (m * c) ≤ (j + 1) * (cA * c) := by
      calc (j + 1) * (m * c) = m * ((j + 1) * c) := by ring
        _ ≤ (j + 1) * (cA * c) := by
            calc m * ((j + 1) * c) ≤ (j + 1) * ((j + 1) * c) := Nat.mul_le_mul_right _ hmj
              _ ≤ (j + 1) * (cA * c) :=
                  Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hA1)
    have s4 : (j + 1) * (m * c + X j + 2 * m) = (j + 1) * (m * c) + (j + 1) * (X j + 2 * m) := by
      ring
    omega
  -- the size of `j`
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt j := ⟨_, rfl⟩
  have hs1 : 9 * T + 10 ≤ s := by
    rw [hs, Nat.le_sqrt']
    exact hT
  have hs2 : s * s ≤ j := by rw [hs]; exact Nat.sqrt_le j
  have hms : m' + s = j := by
    rw [hm']; unfold md; rw [← hs]
    have := Nat.sqrt_le_self j
    rw [← hs] at this
    omega
  have hTs : T ≤ T * s := Nat.le_mul_of_pos_right _ (by omega)
  have hss : s * (9 * T + 10) ≤ s * s := Nat.mul_le_mul_left _ hs1
  have hss' : s * (9 * T + 10) = 9 * (T * s) + 10 * s := by ring
  have hbig : (s + 8) * (T + 1) ≤ m' := by
    have e : (s + 8) * (T + 1) = T * s + s + 8 * T + 8 := by ring
    omega
  have hjT : (j + 8) * (T + 1) ≤ m' * (T + 2) := by
    have e1 : (j + 8) * (T + 1) = m' * (T + 1) + (s + 8) * (T + 1) := by rw [← hms]; ring
    have e2 : m' * (T + 2) = m' * (T + 1) + m' := by ring
    omega
  have hj3 : 3 * (T + 1) ≤ j + 1 := by
    have : 9 * T + 10 ≤ s * s := (Nat.le_mul_self _).trans (Nat.mul_le_mul hs1 hs1)
    omega
  constructor
  · -- lower
    have t1 : (j + 1) * (T * x) ≤ (j + 1) * ((T + 1) * (cA * c)) := by
      have u1 : (T + 1) * ((j + 1) * x) ≤ (T + 1) * ((j + 1) * (cA * c) + 3 * x) :=
        Nat.mul_le_mul_left _ hLo
      have u2 : 3 * (T + 1) * x ≤ (j + 1) * x := Nat.mul_le_mul_right _ hj3
      have u3 : (T + 1) * ((j + 1) * x) = (j + 1) * (T * x) + (j + 1) * x := by ring
      have u4 : (T + 1) * ((j + 1) * (cA * c) + 3 * x) =
          (j + 1) * ((T + 1) * (cA * c)) + 3 * (T + 1) * x := by ring
      omega
    exact Nat.le_of_mul_le_mul_left t1 (by omega)
  · -- upper
    have t1 : m' * ((T + 1) * (cA * c)) ≤ m' * ((T + 2) * x) := by
      calc m' * ((T + 1) * (cA * c)) = (T + 1) * (m' * (cA * c)) := by ring
        _ ≤ (T + 1) * ((j + 8) * x) := Nat.mul_le_mul_left _ hUp
        _ = (j + 8) * (T + 1) * x := by ring
        _ ≤ m' * (T + 2) * x := Nat.mul_le_mul_right _ hjT
        _ = m' * ((T + 2) * x) := by ring
    exact Nat.le_of_mul_le_mul_left t1 hm'pos

end OMA785

theorem OMA.solution : type_of% @Erdos785.erdos_785.variants.danzer := by
  refine ⟨OMA785.Aset, OMA785.Bset, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `A` is infinite
    apply Set.infinite_range_of_injective
    intro a b h
    have := OMA785.av_strictMono.injective h
    omega
  · -- `B` is infinite
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨k, hk⟩ : ∃ k, k = N + 4 := ⟨_, rfl⟩
    have hm : 0 < OMA785.md k := OMA785.md_pos (by omega)
    refine ⟨OMA785.md k * (OMA785.X k / OMA785.md k + 1),
      ⟨k, by omega, dvd_mul_right _ _, (Nat.lt_mul_div_succ _ hm).le, ?_⟩, ?_⟩
    · have h1 : OMA785.md k * (OMA785.X k / OMA785.md k + 1) =
          OMA785.md k * (OMA785.X k / OMA785.md k) + OMA785.md k := by ring
      have h2 := Nat.mul_div_le (OMA785.X k) (OMA785.md k)
      have h3 := OMA785.md_le k
      have h4 := OMA785.X_lt_succ k
      have h5 := OMA785.Y_eq (k + 1)
      have h6 := OMA785.le_av (k + 1)
      omega
    · have h1 := Nat.lt_mul_div_succ (OMA785.X k) hm
      have h2 := OMA785.le_X k
      omega
  · -- `0 ∉ A`
    rintro ⟨i, hi⟩
    have := OMA785.av_pos (i + 1)
    simp only [] at hi
    omega
  · -- `0 ∉ B`
    rintro ⟨k, hk, -, hX, -⟩
    have := OMA785.le_X k
    omega
  · -- `A + B` contains all large integers
    exact Filter.eventually_atTop.2 ⟨OMA785.Y 4, fun n hn => OMA785.mem_add_of_large hn⟩
  · -- the counting functions
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T, hT⟩ := exists_nat_one_div_lt hε
    refine ⟨OMA785.X ((9 * T + 10) ^ 2 + 5), fun x hx => ?_⟩
    obtain ⟨k, hk, hXk, hxk⟩ := OMA785.stage OMA785.X OMA785.X_strictMono hx
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨hlo, hhi⟩ := OMA785.ratio_bounds (j := j) (x := x) (T := T) (by omega) (by omega)
      hXk hxk
    unfold Erdos785.counting
    obtain ⟨N, hN⟩ : ∃ N : ℕ,
        N = (OMA785.Aset ∩ Set.Icc 1 x).ncard * (OMA785.Bset ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
    rw [← hN] at hlo hhi
    have hxpos : (0 : ℝ) < x := by
      have h1 := OMA785.le_X (j + 1)
      have h2 : 0 < x := by omega
      exact_mod_cast h2
    have hNr : ((OMA785.Aset ∩ Set.Icc 1 x).ncard : ℝ) * ((OMA785.Bset ∩ Set.Icc 1 x).ncard : ℝ)
        = (N : ℝ) := by
      rw [hN]; push_cast; ring
    rw [hNr, Real.dist_eq, div_sub_one hxpos.ne', abs_div, abs_of_pos hxpos, div_lt_iff₀ hxpos]
    have h1 : (T : ℝ) * x ≤ ((T : ℝ) + 1) * N := by exact_mod_cast hlo
    have h2 : ((T : ℝ) + 1) * N ≤ ((T : ℝ) + 2) * x := by exact_mod_cast hhi
    have hTpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    have h3 : (1 : ℝ) < ε * ((T : ℝ) + 1) := by
      rw [div_lt_iff₀ hTpos] at hT
      exact hT
    have h4 : (x : ℝ) < ε * ((T : ℝ) + 1) * x := by nlinarith
    rw [abs_lt]
    constructor
    · have h5 : ((T : ℝ) + 1) * (-(ε * x)) < ((T : ℝ) + 1) * ((N : ℝ) - x) := by nlinarith
      exact lt_of_mul_lt_mul_left h5 hTpos.le
    · have h5 : ((T : ℝ) + 1) * ((N : ℝ) - x) < ((T : ℝ) + 1) * (ε * x) := by nlinarith
      exact lt_of_mul_lt_mul_left h5 hTpos.le
