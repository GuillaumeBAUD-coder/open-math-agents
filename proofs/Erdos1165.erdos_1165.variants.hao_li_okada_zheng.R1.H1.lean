import OMAReductions.R_Erdos1165_erdos_1165_variants_hao_li_okada_zheng_R1
import Mathlib
-- Credit: @LordMike

/-!
Polya's recurrence theorem for the simple random walk on Z^2 (Polya 1921), in the form of
hypothesis H1 of the reduction Erdos1165.erdos_1165.variants.hao_li_okada_zheng.R1:
almost surely the local time at the origin is unbounded.

Route (all finite combinatorics plus one cylinder-measure lemma, no Markov property):
* cylinder events of the first L steps have measure (count of good step words) / 4^L;
* last-exit decomposition: sum over j of Z(j) N(L-j) is at most 4^L, where Z(j) counts closed
  walks of length j and N(t) counts walks of length t that avoid the origin at times 1..t;
* N(t)/4^t is antitone and Z(2n) >= centralBinom(n)^2 >= 16^n/(4n), so the sum of Z(j)/4^j
  diverges and N(t)/4^t tends to 0;
* the event that no return happens after time j has measure at most N(t)/4^t for every t;
* a path with bounded local time at the origin has a last visit j, so it lies in that event.
-/

namespace OMA.Polya

open MeasureTheory Filter Finset
open scoped ENNReal Topology

abbrev Path := ℕ → ℤ × ℤ

/-- The canonical simple random walk law of H1. -/
noncomputable def μ : Measure Path :=
  Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond Measure.count Erdos1165.steps)

/-- The coordinate process used in H1. -/
def coord : ℕ → Path → ℤ × ℤ := fun k s => s k

/-- The four unit steps, as a finset. -/
def stepsF : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

/-- Step words of length L. -/
def walks (L : ℕ) : Finset (Fin L → ℤ × ℤ) := Fintype.piFinset fun _ => stepsF

/-- Position after k steps of a finite word (all steps if k is at least L). -/
def pos {L : ℕ} (w : Fin L → ℤ × ℤ) (k : ℕ) : ℤ × ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin L => (i : ℕ) < k), w i

/-- The first L steps of a path. -/
def restr (L : ℕ) (s : Path) : Fin L → ℤ × ℤ := fun i => s i

/-- Number of closed step words of length L. -/
def Z (L : ℕ) : ℕ := ((walks L).filter fun w => pos w L = 0).card

/-- Number of step words of length t that avoid the origin at times 1, ..., t. -/
def N (t : ℕ) : ℕ := ((walks t).filter fun w : Fin t → ℤ × ℤ => ∀ k ∈ Finset.Icc (1 : ℕ) t, pos w k ≠ (0 : ℤ × ℤ)).card

/-- Words of length L whose last visit to the origin (in times 0..L) is at time j. -/
def E (L j : ℕ) : Finset (Fin L → ℤ × ℤ) :=
  (walks L).filter fun w : Fin L → ℤ × ℤ => pos w j = 0 ∧ ∀ k ∈ Finset.Ioc j L, pos w k ≠ (0 : ℤ × ℤ)

/-- Paths that never come back, after time j, to the site occupied at time j. -/
def G (j : ℕ) : Set Path :=
  {s | ∀ k, j < k → Erdos1165.position coord k s ≠ Erdos1165.position coord j s}

/-- The first j letters of a word of length j + t. -/
def first (j t : ℕ) (w : Fin (j + t) → ℤ × ℤ) : Fin j → ℤ × ℤ := fun i => w (Fin.castAdd t i)

/-- The last t letters of a word of length j + t. -/
def last (j t : ℕ) (w : Fin (j + t) → ℤ × ℤ) : Fin t → ℤ × ℤ := fun i => w (Fin.natAdd j i)

/- Measure of cylinder events -/

theorem steps_eq : Erdos1165.steps = (stepsF : Set (ℤ × ℤ)) := by
  ext x
  simp [Erdos1165.steps, stepsF]

theorem cond_singleton (x : ℤ × ℤ) :
    ProbabilityTheory.cond Measure.count Erdos1165.steps {x} =
      if x ∈ stepsF then (4 : ℝ≥0∞)⁻¹ else 0 := by
  rw [ProbabilityTheory.cond_apply (MeasurableSet.of_discrete) Measure.count, steps_eq,
    Measure.count_apply_finset]
  have h4 : stepsF.card = 4 := by rfl
  rw [h4]
  split_ifs with hx
  · have : (stepsF : Set (ℤ × ℤ)) ∩ {x} = {x} := Set.inter_eq_right.mpr (by simpa using hx)
    rw [this, Measure.count_singleton]
    simp
  · have : (stepsF : Set (ℤ × ℤ)) ∩ {x} = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro hy rfl
      exact hx hy
    rw [this]
    simp

theorem map_restr_aux1 :
    IsProbabilityMeasure (ProbabilityTheory.cond Measure.count Erdos1165.steps) := by
  have h4 : Measure.count Erdos1165.steps = 4 := by
    rw [steps_eq, Measure.count_apply_finset]
    rfl
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite (by rw [h4]; norm_num)
    (by rw [h4]; exact ENNReal.ofNat_ne_top)

theorem map_restr_aux2 (L : ℕ) (w : Fin L → ℤ × ℤ) :
    restr L ⁻¹' {w} =
      Set.pi ((Finset.range L : Finset ℕ) : Set ℕ)
        (fun k => {if h : k < L then w ⟨k, h⟩ else 0}) := by
  ext s
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Finset.coe_range, Set.mem_Iio]
  constructor
  · rintro rfl k hk
    simp [restr, hk]
  · intro h
    funext i
    have := h i i.isLt
    simpa [restr, i.isLt] using this

theorem map_restr (L : ℕ) :
    μ.map (restr L) =
      (4 ^ L : ℝ≥0∞)⁻¹ • Measure.count.restrict (walks L : Set (Fin L → ℤ × ℤ)) := by
  have hmeas : Measurable (restr L) := measurable_pi_lambda _ fun i => measurable_pi_apply _
  have := map_restr_aux1
  refine Measure.ext_of_singleton fun w => ?_
  rw [Measure.map_apply hmeas (measurableSet_singleton w), map_restr_aux2, μ,
    Measure.infinitePi_pi _ (fun _ _ => MeasurableSet.of_discrete)]
  rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton w), smul_eq_mul]
  rw [← Fin.prod_univ_eq_prod_range (fun k => ProbabilityTheory.cond Measure.count Erdos1165.steps
    {if h : k < L then w ⟨k, h⟩ else 0}) L]
  have hterm : ∀ i : Fin L, ProbabilityTheory.cond Measure.count Erdos1165.steps
      {if h : (i : ℕ) < L then w ⟨i, h⟩ else 0} = if w i ∈ stepsF then (4 : ℝ≥0∞)⁻¹ else 0 := by
    intro i
    rw [dif_pos i.isLt, cond_singleton]
  rw [Finset.prod_congr rfl (fun i _ => hterm i)]
  by_cases hw : w ∈ walks L
  · have hall : ∀ i : Fin L, w i ∈ stepsF := Fintype.mem_piFinset.mp hw
    rw [Finset.prod_congr rfl (fun i _ => if_pos (hall i)), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ENNReal.inv_pow]
    have : ({w} : Set (Fin L → ℤ × ℤ)) ∩ (walks L : Set _) = {w} :=
      Set.inter_eq_left.mpr (by simpa using hw)
    rw [this, Measure.count_singleton, mul_one]
  · have hex : ∃ i : Fin L, w i ∉ stepsF := by
      by_contra hc
      push Not at hc
      exact hw (Fintype.mem_piFinset.mpr hc)
    obtain ⟨i, hi⟩ := hex
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)]
    have : ({w} : Set (Fin L → ℤ × ℤ)) ∩ (walks L : Set _) = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Finset.mem_coe, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro rfl
      exact hw
    rw [this]
    simp

theorem measure_cyl (L : ℕ) (P : (Fin L → ℤ × ℤ) → Prop) [DecidablePred P] :
    μ {s | P (restr L s)} = (((walks L).filter P).card : ℝ≥0∞) / 4 ^ L := by
  have hmeas : Measurable (restr L) := measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hset : {s | P (restr L s)} = restr L ⁻¹' {w | P w} := rfl
  rw [hset, ← Measure.map_apply hmeas MeasurableSet.of_discrete, map_restr, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.of_discrete, smul_eq_mul]
  have : {w | P w} ∩ (walks L : Set (Fin L → ℤ × ℤ)) = (((walks L).filter P : Finset _) : Set _) := by
    ext w
    simp [and_comm]
  rw [this, Measure.count_apply_finset, div_eq_mul_inv, mul_comm]

/- Finite combinatorics of step words -/

theorem card_walks (L : ℕ) : (walks L).card = 4 ^ L := by
  rw [walks, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

theorem card_split (j t : ℕ) (P : (Fin j → ℤ × ℤ) → Prop) (Q : (Fin t → ℤ × ℤ) → Prop)
    [DecidablePred P] [DecidablePred Q] :
    ((walks (j + t)).filter fun w => P (first j t w) ∧ Q (last j t w)).card =
      ((walks j).filter P).card * ((walks t).filter Q).card := by
  rw [← Finset.card_product]
  symm
  refine Finset.card_nbij' (fun p => Fin.append p.1 p.2) (fun w => (first j t w, last j t w))
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Set.mem_ofPred_eq] at hp
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
    have hf : first j t (Fin.append p.1 p.2) = p.1 := by
      funext i
      simp [first]
    have hl : last j t (Fin.append p.1 p.2) = p.2 := by
      funext i
      simp [last]
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, hf, hl]
    refine ⟨?_, h2, h4⟩
    rw [walks, Fintype.mem_piFinset] at h1 h3 ⊢
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa using h1 a
    · simpa using h3 b
  · intro w hw
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hw
    obtain ⟨h1, h2, h3⟩ := hw
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Set.mem_ofPred_eq]
    rw [walks, Fintype.mem_piFinset] at h1
    refine ⟨⟨?_, h2⟩, ?_, h3⟩
    · rw [walks, Fintype.mem_piFinset]
      intro i
      exact h1 _
    · rw [walks, Fintype.mem_piFinset]
      intro i
      exact h1 _
  · intro p _
    exact Prod.ext (funext fun i => by simp [first]) (funext fun i => by simp [last])
  · intro w _
    exact Fin.append_castAdd_natAdd

theorem pos_first (j t : ℕ) (w : Fin (j + t) → ℤ × ℤ) (k : ℕ) (hk : k ≤ j) :
    pos w k = pos (first j t w) k := by
  unfold pos first
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_add]
  have h0 : ∑ i : Fin t, (if ((Fin.natAdd j i : Fin (j + t)) : ℕ) < k then w (Fin.natAdd j i) else 0)
      = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    simp only [Fin.val_natAdd]
    omega
  rw [h0, add_zero]
  rfl

theorem pos_last (j t : ℕ) (w : Fin (j + t) → ℤ × ℤ) (k : ℕ) :
    pos w (j + k) = pos (first j t w) j + pos (last j t w) k := by
  unfold pos first last
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos, if_pos i.isLt]
    simp only [Fin.val_castAdd]
    omega
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.val_natAdd]
    by_cases h : (i : ℕ) < k
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

theorem pos_restr (L k : ℕ) (hk : k ≤ L) (s : Path) :
    Erdos1165.position coord k s = pos (restr L s) k := by
  unfold Erdos1165.position pos restr coord
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun i => if i < k then s i else 0) L,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

theorem card_E (L j : ℕ) (hj : j ≤ L) : (E L j).card = Z j * N (L - j) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_sub_cancel_left]
  have hE : E (j + t) j = (walks (j + t)).filter fun w : Fin (j + t) → ℤ × ℤ =>
      pos (first j t w) j = 0 ∧
        ∀ k ∈ Finset.Icc (1 : ℕ) t, pos (last j t w) k ≠ (0 : ℤ × ℤ) := by
    unfold E
    refine Finset.filter_congr fun w _ => ?_
    rw [pos_first j t w j le_rfl]
    constructor
    · rintro ⟨h0, h⟩
      refine ⟨h0, fun k hk => ?_⟩
      have hk' := Finset.mem_Icc.mp hk
      have := h (j + k) (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
      rwa [pos_last, h0, zero_add] at this
    · rintro ⟨h0, h⟩
      refine ⟨h0, fun k hk => ?_⟩
      have hk' := Finset.mem_Ioc.mp hk
      obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_lt hk'.1
      have := h (k' + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [show j + k' + 1 = j + (k' + 1) by omega, pos_last, h0, zero_add]
      exact this
  rw [hE, card_split j t (fun u => pos u j = 0)
    (fun v => ∀ k ∈ Finset.Icc (1 : ℕ) t, pos v k ≠ (0 : ℤ × ℤ))]
  rfl

theorem E_disj (L : ℕ) : ((Finset.range (L + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint (E L) := by
  have key : ∀ j j', j < j' → j' ≤ L → Disjoint (E L j) (E L j') := by
    intro j j' hjj' hj'
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [E, Finset.mem_filter] at hw hw'
    exact hw.2.2 j' (Finset.mem_Ioc.mpr ⟨hjj', hj'⟩) hw'.2.1
  intro j hj j' hj' hne
  simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key j j' h (by omega)
  · exact (key j' j h (by omega)).symm

theorem sum_ZN_le (L : ℕ) : ∑ j ∈ Finset.range (L + 1), Z j * N (L - j) ≤ 4 ^ L := by
  have h1 : ∑ j ∈ Finset.range (L + 1), Z j * N (L - j) =
      ∑ j ∈ Finset.range (L + 1), (E L j).card := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [card_E L j (by simpa [Nat.lt_succ_iff] using hj)]
  rw [h1, ← Finset.card_biUnion (E_disj L), ← card_walks L]
  refine Finset.card_le_card ?_
  intro w hw
  simp only [Finset.mem_biUnion] at hw
  obtain ⟨j, _, hj⟩ := hw
  exact (Finset.mem_filter.mp hj).1

theorem N_succ_le (t : ℕ) : N (t + 1) ≤ 4 * N t := by
  have h := card_split t 1 (fun u => ∀ k ∈ Finset.Icc (1 : ℕ) t, pos u k ≠ (0 : ℤ × ℤ))
    (fun _ => True)
  rw [Finset.filter_true_of_mem (fun _ _ => trivial), card_walks] at h
  have h4 : N t * 4 ^ 1 = 4 * N t := by ring
  rw [← h4]
  refine le_trans ?_ (le_of_eq h)
  unfold N
  refine Finset.card_le_card fun w hw => ?_
  simp only [Finset.mem_filter] at hw ⊢
  refine ⟨hw.1, fun k hk => ?_, trivial⟩
  have hk' := Finset.mem_Icc.mp hk
  rw [← pos_first t 1 w k hk'.2]
  exact hw.2 k (Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩)

def Z_even_ge_phi (n : ℕ) (p : Finset (Fin (2 * n)) × Finset (Fin (2 * n))) : Fin (2 * n) → ℤ × ℤ :=
  fun i => if i ∈ p.1 then (if i ∈ p.2 then (1, 0) else (0, 1))
    else (if i ∈ p.2 then (0, -1) else (-1, 0))

theorem Z_even_ge_aux1 (n : ℕ) (A : Finset (Fin (2 * n))) (hA : A.card = n) :
    ∑ i : Fin (2 * n), (if i ∈ A then (1 : ℤ) else -1) = 0 := by
  have h1 : ∀ i : Fin (2 * n), (if i ∈ A then (1 : ℤ) else -1) = 2 * (if i ∈ A then (1 : ℤ) else 0) - 1 := by
    intro i; split_ifs <;> norm_num
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp [hA]

theorem Z_even_ge_aux2 (n : ℕ) (p : Finset (Fin (2 * n)) × Finset (Fin (2 * n)))
    (hA : p.1.card = n) (hB : p.2.card = n) : Z_even_ge_phi n p ∈ (walks (2 * n)).filter fun w => pos w (2 * n) = 0 := by
  rw [Finset.mem_filter, walks, Fintype.mem_piFinset]
  refine ⟨?_, ?_⟩
  · intro i
    unfold Z_even_ge_phi
    simp only [stepsF, Finset.mem_insert, Finset.mem_singleton]
    split_ifs <;> simp
  · have hp : pos (Z_even_ge_phi n p) (2 * n) = ∑ i, Z_even_ge_phi n p i := by
      unfold pos
      congr 1
      rw [Finset.filter_true_of_mem]
      intro i _
      exact i.2
    rw [hp]
    have e1 := Z_even_ge_aux1 n p.1 hA
    have e2 := Z_even_ge_aux1 n p.2 hB
    have f1 : ∑ i, (Z_even_ge_phi n p i).1 + ∑ i, (Z_even_ge_phi n p i).2 = 0 := by
      rw [← e1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold Z_even_ge_phi
      split_ifs <;> simp
    have f2 : ∑ i, (Z_even_ge_phi n p i).1 - ∑ i, (Z_even_ge_phi n p i).2 = 0 := by
      rw [← e2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold Z_even_ge_phi
      split_ifs <;> simp
    apply Prod.ext
    · simp only [Prod.fst_sum, Prod.fst_zero]; omega
    · simp only [Prod.snd_sum, Prod.snd_zero]; omega

theorem Z_even_ge_aux3 (n : ℕ) (p q : Finset (Fin (2 * n)) × Finset (Fin (2 * n)))
    (h : Z_even_ge_phi n p = Z_even_ge_phi n q) : p = q := by
  have key : ∀ i, (i ∈ p.1 ↔ i ∈ q.1) ∧ (i ∈ p.2 ↔ i ∈ q.2) := by
    intro i
    have := congrFun h i
    unfold Z_even_ge_phi at this
    by_cases a : i ∈ p.1 <;> by_cases b : i ∈ p.2 <;> by_cases c : i ∈ q.1 <;> by_cases d : i ∈ q.2 <;>
      simp_all
  exact Prod.ext (Finset.ext fun i => (key i).1) (Finset.ext fun i => (key i).2)

theorem Z_even_ge (n : ℕ) : n.centralBinom ^ 2 ≤ Z (2 * n) := by
  set S : Finset (Finset (Fin (2 * n))) := (Finset.univ : Finset (Fin (2 * n))).powersetCard n with hS
  have hSc : S.card = n.centralBinom := by
    rw [hS, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      Nat.centralBinom_eq_two_mul_choose]
  have hc : (S ×ˢ S).card = n.centralBinom ^ 2 := by
    rw [Finset.card_product, hSc, sq]
  rw [← hc]
  unfold Z
  refine Finset.card_le_card_of_injOn (Z_even_ge_phi n) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_product, hS, Finset.mem_powersetCard, Finset.mem_powersetCard] at hp
    exact Z_even_ge_aux2 n p hp.1.2 hp.2.2
  · intro p _ q _ h
    exact Z_even_ge_aux3 n p q h

theorem central_ge (n : ℕ) (hn : 1 ≤ n) : 16 ^ n ≤ 4 * n * n.centralBinom ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hrec := Nat.succ_mul_centralBinom_succ n
    have key : (n + 1) * 16 ^ (n + 1) ≤ (n + 1) * (4 * (n + 1) * (n + 1).centralBinom ^ 2) := by
      have e : (n + 1) * (4 * (n + 1) * (n + 1).centralBinom ^ 2) =
          4 * ((n + 1) * (n + 1).centralBinom) ^ 2 := by ring
      rw [e, hrec, pow_succ]
      nlinarith [ih, Nat.zero_le (n.centralBinom ^ 2)]
    exact Nat.le_of_mul_le_mul_left key (Nat.succ_pos n)

/- Real-number estimates -/

theorem partial_ge_aux1 (n : ℕ) :
    (1 : ℝ) / (4 * ((n : ℝ) + 1)) ≤ (Z (2 * (n + 1)) : ℝ) / 4 ^ (2 * (n + 1)) := by
  have h1 : (16 : ℝ) ^ (n + 1) ≤ 4 * ((n + 1 : ℕ) : ℝ) * ((n + 1).centralBinom : ℝ) ^ 2 := by
    exact_mod_cast central_ge (n + 1) (by omega)
  have h2 : ((n + 1).centralBinom : ℝ) ^ 2 ≤ (Z (2 * (n + 1)) : ℝ) := by
    exact_mod_cast Z_even_ge (n + 1)
  have h4 : (4 : ℝ) ^ (2 * (n + 1)) = 16 ^ (n + 1) := by
    rw [pow_mul]; norm_num
  rw [h4, div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast at h1
  have h5 : (0 : ℝ) ≤ 4 * ((n : ℝ) + 1) := by positivity
  calc (1 : ℝ) * 16 ^ (n + 1) ≤ 4 * ((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ) ^ 2 := by
        linarith
    _ ≤ 4 * ((n : ℝ) + 1) * (Z (2 * (n + 1)) : ℝ) := mul_le_mul_of_nonneg_left h2 h5
    _ = (Z (2 * (n + 1)) : ℝ) * (4 * ((n : ℝ) + 1)) := by ring

theorem partial_ge (m : ℕ) :
    ∑ n ∈ Finset.range m, (1 : ℝ) / (4 * ((n : ℝ) + 1)) ≤
      ∑ j ∈ Finset.range (2 * m + 1), (Z j : ℝ) / 4 ^ j := by
  calc ∑ n ∈ Finset.range m, (1 : ℝ) / (4 * ((n : ℝ) + 1))
      ≤ ∑ n ∈ Finset.range m, (Z (2 * (n + 1)) : ℝ) / 4 ^ (2 * (n + 1)) :=
        Finset.sum_le_sum fun n _ => partial_ge_aux1 n
    _ = ∑ j ∈ (Finset.range m).image (fun n : ℕ => 2 * (n + 1)), (Z j : ℝ) / 4 ^ j := by
        rw [Finset.sum_image]
        intro a _ b _ h
        simp only at h
        omega
    _ ≤ ∑ j ∈ Finset.range (2 * m + 1), (Z j : ℝ) / 4 ^ j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_image, Finset.mem_range] at hj ⊢
          obtain ⟨n, hn, rfl⟩ := hj
          omega
        · intro j _ _
          positivity

theorem sum_tendsto :
    Tendsto (fun L : ℕ => ∑ j ∈ Finset.range (L + 1), (Z j : ℝ) / 4 ^ j) atTop atTop := by
  have hH := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hq : Tendsto (fun m : ℕ => ∑ n ∈ Finset.range m, (1 : ℝ) / (4 * ((n : ℝ) + 1))) atTop atTop := by
    have h2 := hH.const_mul_atTop (show (0 : ℝ) < 1 / 4 by norm_num)
    refine h2.congr (fun m => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨m, hm⟩ := (tendsto_atTop_atTop.1 hq) b
  refine ⟨2 * m, fun L hL => ?_⟩
  calc b ≤ ∑ n ∈ Finset.range m, (1 : ℝ) / (4 * ((n : ℝ) + 1)) := hm m le_rfl
    _ ≤ ∑ j ∈ Finset.range (2 * m + 1), (Z j : ℝ) / 4 ^ j := partial_ge m
    _ ≤ ∑ j ∈ Finset.range (L + 1), (Z j : ℝ) / 4 ^ j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega
      · intro i _ _
        positivity

theorem r_anti (L j : ℕ) (hj : j ≤ L) :
    (N L : ℝ) / 4 ^ L ≤ (N (L - j) : ℝ) / 4 ^ (L - j) := by
  have hanti : Antitone fun m : ℕ => (N m : ℝ) / 4 ^ m := by
    refine antitone_nat_of_succ_le fun m => ?_
    have h := N_succ_le m
    have h' : (N (m + 1) : ℝ) ≤ 4 * N m := by exact_mod_cast h
    rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
    nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) m]
  clear hj
  exact hanti (Nat.sub_le L j)

theorem r_mul_le (L : ℕ) :
    (N L : ℝ) / 4 ^ L * ∑ j ∈ Finset.range (L + 1), (Z j : ℝ) / 4 ^ j ≤ 1 := by
  have key : ∀ j ∈ Finset.range (L + 1),
      (N L : ℝ) / 4 ^ L * ((Z j : ℝ) / 4 ^ j) ≤ ((Z j * N (L - j) : ℕ) : ℝ) / 4 ^ L := by
    intro j hj
    have hjL : j ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h1 := r_anti L j hjL
    have h2 : (0 : ℝ) ≤ (Z j : ℝ) / 4 ^ j := by positivity
    have h3 : (4 : ℝ) ^ L = 4 ^ (L - j) * 4 ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hjL]
    calc (N L : ℝ) / 4 ^ L * ((Z j : ℝ) / 4 ^ j)
        ≤ (N (L - j) : ℝ) / 4 ^ (L - j) * ((Z j : ℝ) / 4 ^ j) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = ((Z j * N (L - j) : ℕ) : ℝ) / 4 ^ L := by
          rw [h3, Nat.cast_mul]
          field_simp
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum key).trans ?_
  rw [← Finset.sum_div, ← Nat.cast_sum]
  have h4 := sum_ZN_le L
  have h5 : (((∑ j ∈ Finset.range (L + 1), Z j * N (L - j) : ℕ)) : ℝ) ≤ 4 ^ L := by
    exact_mod_cast h4
  exact (div_le_one (by positivity)).mpr h5

theorem r_tendsto : Tendsto (fun L : ℕ => (N L : ℝ) / 4 ^ L) atTop (𝓝 0) := by
  have hinv : Tendsto (fun L : ℕ => (∑ j ∈ Finset.range (L + 1), (Z j : ℝ) / 4 ^ j)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp sum_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
    (Eventually.of_forall fun L => by positivity) ?_
  filter_upwards [sum_tendsto.eventually_ge_atTop 1] with L hL
  have hS : (0 : ℝ) < ∑ j ∈ Finset.range (L + 1), (Z j : ℝ) / 4 ^ j := by linarith
  rw [← one_div, le_div_iff₀ hS]
  exact r_mul_le L

/- The events G j are null -/

theorem card_G (j t : ℕ) :
    ((walks (j + t)).filter fun w : Fin (j + t) → ℤ × ℤ =>
      ∀ k ∈ Finset.Icc (1 : ℕ) t, pos w (j + k) ≠ pos w j).card = 4 ^ j * N t := by
  have hG : ((walks (j + t)).filter fun w : Fin (j + t) → ℤ × ℤ =>
      ∀ k ∈ Finset.Icc (1 : ℕ) t, pos w (j + k) ≠ pos w j) =
      (walks (j + t)).filter fun w : Fin (j + t) → ℤ × ℤ =>
        True ∧ ∀ k ∈ Finset.Icc (1 : ℕ) t, pos (last j t w) k ≠ (0 : ℤ × ℤ) := by
    refine Finset.filter_congr fun w _ => ?_
    simp only [true_and]
    refine forall₂_congr fun k _ => ?_
    rw [pos_last, pos_first j t w j le_rfl]
    constructor
    · intro h h0
      exact h (by rw [h0, add_zero])
    · intro h h0
      exact h (by simpa using h0)
  rw [hG, card_split j t (fun _ => True)
    (fun v => ∀ k ∈ Finset.Icc (1 : ℕ) t, pos v k ≠ (0 : ℤ × ℤ)),
    Finset.filter_true_of_mem (fun _ _ => trivial), card_walks]
  rfl

theorem G_le (j t : ℕ) : μ (G j) ≤ ENNReal.ofReal ((N t : ℝ) / 4 ^ t) := by
  have hsub : G j ⊆ {s : Path | (fun w : Fin (j + t) → ℤ × ℤ =>
      ∀ k ∈ Finset.Icc (1 : ℕ) t, pos w (j + k) ≠ pos w j) (restr (j + t) s)} := by
    intro s hs k hk
    have hk1 := (Finset.mem_Icc.1 hk)
    have h1 : j < j + k := by omega
    have h2 := hs (j + k) h1
    rwa [pos_restr (j + t) (j + k) (by omega), pos_restr (j + t) j (by omega)] at h2
  refine (measure_mono hsub).trans ?_
  rw [measure_cyl (j + t) (fun w : Fin (j + t) → ℤ × ℤ =>
      ∀ k ∈ Finset.Icc (1 : ℕ) t, pos w (j + k) ≠ pos w j), card_G]
  have h4 : (ENNReal.ofReal 4) = (4 : ℝ≥0∞) := by
    simp
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num), h4]
  push_cast
  rw [pow_add]
  exact le_of_eq (ENNReal.mul_div_mul_left _ _ (by positivity) (by simp))

theorem G_null (j : ℕ) : μ (G j) = 0 := by
  have h : Tendsto (fun t : ℕ => ENNReal.ofReal ((N t : ℝ) / 4 ^ t)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal r_tendsto
    rwa [ENNReal.ofReal_zero] at this
  exact le_antisymm (ge_of_tendsto' h (fun t => G_le j t)) zero_le

theorem bad_subset :
    {s : Path | ¬ ∀ M : ℕ, ∃ n : ℕ, M ≤ Erdos1165.localTime coord n s (0, 0)} ⊆ ⋃ j, G j := by
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs
  push Not at hs
  obtain ⟨M, hM⟩ := hs
  have hfin : {k : ℕ | Erdos1165.position coord k s = (0, 0)}.Finite := by
    by_contra hinf
    obtain ⟨F, hFsub, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf M
    have hsub : F ⊆ (Finset.range (F.sup id + 1)).filter
        (fun k => Erdos1165.position coord k s = (0, 0)) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hFsub hk⟩
      have : k ≤ F.sup id := Finset.le_sup (f := id) hk
      omega
    have h1 := Finset.card_le_card hsub
    have h2 := hM (F.sup id)
    unfold Erdos1165.localTime at h2
    omega
  have h0 : (0 : ℕ) ∈ hfin.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rw [Erdos1165.position_zero]
    rfl
  set j := hfin.toFinset.max' ⟨0, h0⟩ with hj
  have hjmem : j ∈ hfin.toFinset := Finset.max'_mem _ _
  have hjpos : Erdos1165.position coord j s = (0, 0) := by
    simpa [Set.Finite.mem_toFinset] using hjmem
  refine Set.mem_iUnion.2 ⟨j, ?_⟩
  intro k hk hEq
  have hkmem : k ∈ hfin.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rw [hEq, hjpos]
  have := Finset.le_max' hfin.toFinset k hkmem
  omega

end OMA.Polya

theorem OMA.solution : OMA.R_Erdos1165_erdos_1165_variants_hao_li_okada_zheng_R1.H1 := by
  change ∀ᵐ s ∂OMA.Polya.μ, ∀ M : ℕ, ∃ n : ℕ, M ≤ Erdos1165.localTime OMA.Polya.coord n s (0, 0)
  rw [MeasureTheory.ae_iff]
  exact MeasureTheory.measure_mono_null OMA.Polya.bad_subset
    (MeasureTheory.measure_iUnion_null OMA.Polya.G_null)
