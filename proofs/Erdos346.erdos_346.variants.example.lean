import FormalConjectures.ErdosProblems.«346»

/-!
# Irregular Strongly Complete Sequence for Erdos Problem 346

We construct a strictly increasing sequence of positive integers that remains additively complete
after deleting any finite set of terms, becomes incomplete after deleting any infinite set of
terms, and satisfies liminf A(n+1)/A(n) = 1 and limsup A(n+1)/A(n) = top.
-/

namespace OMA.Erdos346Example

open Filter Topology Set

/-- Index-based finite subset sums of `a` restricted to `I`. -/
def idxSums (a : ℕ → ℕ) (I : Set ℕ) : Set ℕ :=
  {t | ∃ F : Finset ℕ, ↑F ⊆ I ∧ ∑ i ∈ F, a i = t}

lemma idxSums_mono {a : ℕ → ℕ} {I J : Set ℕ} (hIJ : I ⊆ J) :
    idxSums a I ⊆ idxSums a J := by
  rintro t ⟨F, hF, rfl⟩
  exact ⟨F, hF.trans hIJ, rfl⟩

lemma idxSums_add_new {a : ℕ → ℕ} {I J : Set ℕ} {i t : ℕ}
    (hIJ : I ⊆ J) (hiJ : i ∈ J) (hiI : i ∉ I) (ht : t ∈ idxSums a I) :
    t + a i ∈ idxSums a J := by
  obtain ⟨F, hF, hsum⟩ := ht
  have hiF : i ∉ F := fun h => hiI (hF h)
  refine ⟨insert i F, ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_insert] at hj ⊢
    rcases hj with rfl | hj
    · exact hiJ
    · exact hIJ (hF hj)
  · rw [Finset.sum_insert hiF, hsum]
    omega

lemma idxSums_complement {a : ℕ → ℕ} {B : Finset ℕ} {t : ℕ}
    (ht : t ∈ idxSums a (↑B : Set ℕ)) :
    (∑ i ∈ B, a i) - t ∈ idxSums a (↑B : Set ℕ) := by
  obtain ⟨F, hF, hsum⟩ := ht
  have hFB : F ⊆ B := by simpa using hF
  refine ⟨B \ F, by simp, ?_⟩
  rw [← Finset.sum_sdiff hFB, hsum, Nat.add_sub_cancel_right]

lemma idxSums_add_disjoint {a : ℕ → ℕ} {I J U : Set ℕ} {x y : ℕ}
    (hI : I ⊆ U) (hJ : J ⊆ U) (hdisj : ∀ i, i ∈ I → i ∈ J → False)
    (hx : x ∈ idxSums a I) (hy : y ∈ idxSums a J) :
    x + y ∈ idxSums a U := by
  obtain ⟨F, hF, hsumF⟩ := hx
  obtain ⟨G, hG, hsumG⟩ := hy
  have hFG : Disjoint F G := Finset.disjoint_left.mpr fun i hiF hiG => hdisj i (hF hiF) (hG hiG)
  refine ⟨F ∪ G, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact hI (hF hi)
    · exact hJ (hG hi)
  · rw [Finset.sum_union hFG, hsumF, hsumG]

lemma idxSums_congr_on {a c : ℕ → ℕ} {I : Set ℕ}
    (h : ∀ i, i ∈ I → a i = c i) : idxSums a I = idxSums c I := by
  ext t
  constructor
  · rintro ⟨F, hF, hsum⟩
    exact ⟨F, hF, by rw [← hsum]; exact Finset.sum_congr rfl fun i hi => (h i (hF hi)).symm⟩
  · rintro ⟨F, hF, hsum⟩
    exact ⟨F, hF, by rw [← hsum]; exact Finset.sum_congr rfl fun i hi => h i (hF hi)⟩

lemma term_le_finset_sum (a : ℕ → ℕ) {F : Finset ℕ} {i : ℕ} (hi : i ∈ F) :
    a i ≤ ∑ j ∈ F, a j :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi

lemma idxSums_restrict_below {a : ℕ → ℕ} (ha : Monotone a) {m k z : ℕ}
    (hz : z ∈ idxSums a (Set.Ici m)) (hzk : z < a k) :
    z ∈ idxSums a (Set.Ico m k) := by
  obtain ⟨F, hF, hsum⟩ := hz
  refine ⟨F, fun i hi => ⟨hF hi, ?_⟩, hsum⟩
  by_contra hnot
  have hki : a k ≤ a i := ha (Nat.le_of_not_gt hnot)
  have hile : a i ≤ z := hsum ▸ term_le_finset_sum a hi
  omega

lemma even_neg_one_pow {n : ℕ} (h : Even n) : (-1 : ℤ) ^ n = 1 := by
  rcases h with ⟨k, rfl⟩
  rw [show k + k = 2 * k by omega, pow_mul]
  norm_num

lemma odd_neg_one_pow {n : ℕ} (h : Odd n) : (-1 : ℤ) ^ n = -1 := by
  rcases h with ⟨k, rfl⟩
  rw [pow_add, pow_mul, pow_one]
  norm_num

lemma neg_one_pow_cases (n : ℕ) : (-1 : ℤ) ^ n = 1 ∨ (-1 : ℤ) ^ n = -1 := by
  rcases Nat.even_or_odd n with h | h
  · exact Or.inl (even_neg_one_pow h)
  · exact Or.inr (odd_neg_one_pow h)

/-- Alternating unperturbed offset. -/
def parityPerturbation (n : ℕ) : ℕ := if Even n then 1 else 0

lemma parityPerturbation_le_one (n : ℕ) : parityPerturbation n ≤ 1 := by
  unfold parityPerturbation
  split_ifs <;> omega

lemma parityPerturbation_difference (n : ℕ) :
    (parityPerturbation (n + 1) : ℤ) - parityPerturbation n = -((-1 : ℤ) ^ n) := by
  rcases Nat.even_or_odd n with hn | hn
  · have hn1 : ¬ Even (n + 1) := by simp [Nat.even_add_one, hn]
    simp only [parityPerturbation, if_pos hn, if_neg hn1, even_neg_one_pow hn]
    norm_num
  · have hn0 : ¬ Even n := Nat.not_even_iff_odd.mpr hn
    have hn1 : Even (n + 1) := hn.add_one
    simp only [parityPerturbation, if_neg hn0, if_pos hn1, odd_neg_one_pow hn]
    norm_num

/-- Step transition kind: unit increment or prefix-sum jump with offset `b`. -/
inductive StepKind
  | inc
  | pref (b : ℕ)

/-- Tail-recursive state `(a (r + 3), a 0 + ... + a (r + 2))`. -/
def genState (rule : ℕ → StepKind) : ℕ → ℕ × ℕ
  | 0 => (5, 6)
  | r + 1 =>
      let s := genState rule r
      let nextVal := match rule (r + 3) with
        | .inc => s.1 + 1
        | .pref b => s.2 + b
      (nextVal, s.2 + s.1)

/-- Sequence generated from step schedule `rule`. -/
def genSeq (rule : ℕ → StepKind) : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | r + 3 => (genState rule r).1

@[simp] lemma genSeq_zero (rule : ℕ → StepKind) : genSeq rule 0 = 1 := rfl
@[simp] lemma genSeq_one (rule : ℕ → StepKind) : genSeq rule 1 = 2 := rfl
@[simp] lemma genSeq_two (rule : ℕ → StepKind) : genSeq rule 2 = 3 := rfl
@[simp] lemma genSeq_three (rule : ℕ → StepKind) : genSeq rule 3 = 5 := rfl

@[simp] lemma genSeq_add_three (rule : ℕ → StepKind) (r : ℕ) :
    genSeq rule (r + 3) = (genState rule r).1 := rfl

/-- Prefix sum `a 0 + ... + a (n - 1)`. -/
def prefixSum (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, a i

@[simp] lemma prefixSum_zero (a : ℕ → ℕ) : prefixSum a 0 = 0 := by simp [prefixSum]

lemma prefixSum_succ (a : ℕ → ℕ) (n : ℕ) :
    prefixSum a (n + 1) = prefixSum a n + a n := by
  simp [prefixSum, Finset.sum_range_succ]

lemma prefixSum_mono (a : ℕ → ℕ) {m n : ℕ} (hmn : m ≤ n) : prefixSum a m ≤ prefixSum a n :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hmn)

lemma genState_snd (rule : ℕ → StepKind) (r : ℕ) :
    (genState rule r).2 = prefixSum (genSeq rule) (r + 3) := by
  induction r with
  | zero => norm_num [genState, prefixSum, genSeq, Finset.sum_range_succ]
  | succ r ih =>
      rw [genState, show r + 1 + 3 = (r + 3) + 1 by omega, prefixSum_succ, ih]
      rfl

lemma genSeq_step_inc (rule : ℕ → StepKind) {n : ℕ} (hn : 3 ≤ n) (h : rule n = .inc) :
    genSeq rule (n + 1) = genSeq rule n + 1 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 3 r] at h ⊢
  rw [show r + 3 + 1 = (r + 1) + 3 by omega, genSeq_add_three, genState]
  dsimp only
  rw [h]
  rfl

lemma genSeq_step_pref (rule : ℕ → StepKind) {n b : ℕ} (hn : 3 ≤ n) (h : rule n = .pref b) :
    genSeq rule (n + 1) = prefixSum (genSeq rule) n + b := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 3 r] at h ⊢
  rw [show r + 3 + 1 = (r + 1) + 3 by omega, genSeq_add_three, genState]
  dsimp only
  rw [h, genState_snd]

lemma genState_lower (rule : ℕ → StepKind) (r : ℕ) :
    r + 5 ≤ (genState rule r).1 ∧ r + 6 ≤ (genState rule r).2 := by
  induction r with
  | zero => norm_num [genState]
  | succ r ih =>
      rw [genState]
      rcases rule (r + 3) with _ | b <;> (simp only; omega)

lemma genSeq_ge_succ (rule : ℕ → StepKind) (n : ℕ) : n + 1 ≤ genSeq rule n := by
  rcases n with _ | _ | _ | r
  · norm_num [genSeq]
  · norm_num [genSeq]
  · norm_num [genSeq]
  · have h := (genState_lower rule r).1
    rw [genSeq_add_three]
    omega

lemma genSeq_pos (rule : ℕ → StepKind) (n : ℕ) : 0 < genSeq rule n := by
  have h := genSeq_ge_succ rule n
  omega

lemma genSeq_ge_five (rule : ℕ → StepKind) {n : ℕ} (hn : 3 ≤ n) : 5 ≤ genSeq rule n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := (genState_lower rule r).1
  rw [Nat.add_comm 3 r, genSeq_add_three]
  omega

lemma prefixSum_genSeq_ge_six (rule : ℕ → StepKind) {n : ℕ} (hn : 3 ≤ n) :
    6 ≤ prefixSum (genSeq rule) n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := (genState_lower rule r).2
  rw [Nat.add_comm 3 r, ← genState_snd]
  omega

/-- Admissibility condition on a rule schedule. -/
def AdmissibleRule (rule : ℕ → StepKind) : Prop :=
  ∀ n, 3 ≤ n → match rule n with
    | .inc => True
    | .pref b => 4 * b ≤ genSeq rule n

lemma genSeq_strictMono (rule : ℕ → StepKind) (hadm : AdmissibleRule rule) :
    StrictMono (genSeq rule) := by
  apply strictMono_nat_of_lt_succ
  intro n
  by_cases hn : n < 4
  · interval_cases n
    · norm_num [genSeq]
    · norm_num [genSeq]
    · norm_num [genSeq, genState]
    · rcases hr3 : rule 3 with _ | b
      · rw [genSeq_step_inc rule (by omega) hr3]; omega
      · rw [genSeq_step_pref rule (by omega) hr3]
        have hp3 := prefixSum_genSeq_ge_six rule (n := 3) (by omega)
        simp only [genSeq_three]
        omega
  · rcases hcur : rule n with _ | b
    · rw [genSeq_step_inc rule (by omega) hcur]; omega
    · rw [genSeq_step_pref rule (by omega) hcur]
      have hps : prefixSum (genSeq rule) n =
          prefixSum (genSeq rule) (n - 1) + genSeq rule (n - 1) := by
        have hp := prefixSum_succ (genSeq rule) (n - 1)
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hp
      rcases hprev : rule (n - 1) with _ | b'
      · have hinc := genSeq_step_inc rule (n := n - 1) (by omega) hprev
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hinc
        have hp6 := prefixSum_genSeq_ge_six rule (n := n - 1) (by omega)
        omega
      · have hpref := genSeq_step_pref rule (n := n - 1) (by omega) hprev
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hpref
        have hadm' := hadm (n - 1) (by omega)
        rw [hprev] at hadm'
        dsimp only at hadm'
        have hg5 := genSeq_ge_five rule (n := n - 1) (by omega)
        omega

lemma genState_congr {r1 r2 : ℕ → StepKind} {r : ℕ}
    (h : ∀ n, 3 ≤ n → n < r + 3 → r1 n = r2 n) :
    genState r1 r = genState r2 r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [genState, genState]
      have hs : genState r1 r = genState r2 r := ih fun n hn hlt => h n hn (by omega)
      rw [hs, h (r + 3) (by omega) (by omega)]

lemma genSeq_congr {r1 r2 : ℕ → StepKind} {N : ℕ}
    (h : ∀ n, 3 ≤ n → n < N → r1 n = r2 n) :
    ∀ n < N + 1, genSeq r1 n = genSeq r2 n := by
  intro n hn
  by_cases hn3 : n < 3
  · interval_cases n <;> rfl
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn3)
    rw [Nat.add_comm 3 r, genSeq_add_three, genSeq_add_three]
    exact congrArg Prod.fst (genState_congr fun i hi hil => h i hi (by omega))

/-- Sum of `a (N + 1), ..., a (N + q)`. -/
def tailBlockSum (a : ℕ → ℕ) (N q : ℕ) : ℕ :=
  ∑ j ∈ Finset.range q, a (N + 1 + j)

@[simp] lemma tailBlockSum_zero (a : ℕ → ℕ) (N : ℕ) : tailBlockSum a N 0 = 0 := by
  simp [tailBlockSum]

lemma tailBlockSum_succ (a : ℕ → ℕ) (N q : ℕ) :
    tailBlockSum a N (q + 1) = tailBlockSum a N q + a (N + q + 1) := by
  simp only [tailBlockSum, Finset.sum_range_succ]
  congr 2
  omega

lemma prefixSum_add_tailBlockSum (a : ℕ → ℕ) (N q : ℕ) :
    prefixSum a (N + q + 1) = prefixSum a (N + 1) + tailBlockSum a N q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show N + (q + 1) + 1 = (N + q + 1) + 1 by omega, prefixSum_succ, ih, tailBlockSum_succ]
      rw [show N + q + 1 = N + 1 + q by omega]
      omega

lemma tailBlockSum_ge_length {a : ℕ → ℕ} (ha : ∀ n, 0 < a n) (N q : ℕ) :
    q ≤ tailBlockSum a N q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [tailBlockSum_succ]
      have h := ha (N + q + 1)
      omega

/- Permanent interval propagation across both step kinds -/

lemma interval_certificate_propagates
    (rule : ℕ → StepKind) {m N u L : ℕ}
    (hmN : m ≤ N) (hN3 : 3 ≤ N)
    (hadm : AdmissibleRule rule)
    (hinterval : ∀ t, u ≤ t → t ≤ u + L → t ∈ idxSums (genSeq rule) (Set.Icc m N))
    (hlock1 : 4 * prefixSum (genSeq rule) (N + 1) ≤ 4 * (L + 1) + 3 * genSeq rule N)
    (hlock2 : prefixSum (genSeq rule) (N + 1) ≤ L + prefixSum (genSeq rule) N) :
    ∀ q t, u ≤ t → t ≤ u + L + tailBlockSum (genSeq rule) N q →
      t ∈ idxSums (genSeq rule) (Set.Icc m (N + q)) := by
  have ha_mono : Monotone (genSeq rule) := (genSeq_strictMono rule hadm).monotone
  intro q
  induction q with
  | zero =>
      intro t hut htu
      simpa using hinterval t hut htu
  | succ q ih =>
      intro t hut htu
      have hNn : N ≤ N + q := Nat.le_add_right N q
      have haN_le : genSeq rule N ≤ genSeq rule (N + q) := ha_mono hNn
      have hps_le : prefixSum (genSeq rule) N ≤ prefixSum (genSeq rule) (N + q) :=
        prefixSum_mono (genSeq rule) hNn
      have hpref : prefixSum (genSeq rule) (N + 1) + tailBlockSum (genSeq rule) N q =
          prefixSum (genSeq rule) (N + q) + genSeq rule (N + q) := by
        rw [← prefixSum_succ, prefixSum_add_tailBlockSum]
      have hoverlap : genSeq rule (N + q + 1) ≤ L + tailBlockSum (genSeq rule) N q + 1 := by
        rcases hstep : rule (N + q) with _ | b
        · have hinc := genSeq_step_inc rule (n := N + q) (by omega) hstep
          omega
        · have hpr := genSeq_step_pref rule (n := N + q) (by omega) hstep
          have hb := hadm (N + q) (by omega)
          rw [hstep] at hb
          dsimp only at hb
          omega
      rw [tailBlockSum_succ] at htu
      by_cases hold : t ≤ u + L + tailBlockSum (genSeq rule) N q
      · exact idxSums_mono (Set.Icc_subset_Icc_right (by omega)) (ih t hut hold)
      · have hrep := ih (t - genSeq rule (N + q + 1)) (by omega) (by omega)
        have hadd := idxSums_add_new
          (a := genSeq rule) (I := Set.Icc m (N + q)) (J := Set.Icc m (N + (q + 1)))
          (i := N + q + 1) (t := t - genSeq rule (N + q + 1))
          (Set.Icc_subset_Icc_right (by omega))
          (by constructor <;> omega)
          (by simp only [Set.mem_Icc, not_and_or]; omega) hrep
        convert hadd using 1
        omega

lemma permanent_interval_certificate
    (rule : ℕ → StepKind) {m N u L : ℕ}
    (hmN : m ≤ N) (hN3 : 3 ≤ N)
    (hadm : AdmissibleRule rule)
    (hinterval : ∀ t, u ≤ t → t ≤ u + L → t ∈ idxSums (genSeq rule) (Set.Icc m N))
    (hlock1 : 4 * prefixSum (genSeq rule) (N + 1) ≤ 4 * (L + 1) + 3 * genSeq rule N)
    (hlock2 : prefixSum (genSeq rule) (N + 1) ≤ L + prefixSum (genSeq rule) N) :
    ∃ H, ∀ t, H ≤ t → t ∈ idxSums (genSeq rule) (Set.Ici m) := by
  refine ⟨u, fun t hut => ?_⟩
  let q := t - u
  have hq : q ≤ tailBlockSum (genSeq rule) N q := tailBlockSum_ge_length (genSeq_pos rule) N q
  have hrep := interval_certificate_propagates rule hmN hN3 hadm hinterval hlock1 hlock2
    q t hut (by omega)
  exact idxSums_mono (fun i hi => hi.1) hrep

/-- Provisional sequence unperturbed from `cut` onward. -/
structure Approximation where
  rule : ℕ → StepKind
  cut : ℕ
  cut_ge : 3 ≤ cut
  admissible : AdmissibleRule rule
  eventualParity : ∀ n, cut ≤ n → rule n = .pref (parityPerturbation n)

namespace Approximation

def seq (s : Approximation) : ℕ → ℕ := genSeq s.rule

lemma seq_pos (s : Approximation) (n : ℕ) : 0 < s.seq n := genSeq_pos s.rule n

lemma seq_strictMono (s : Approximation) : StrictMono s.seq :=
  genSeq_strictMono s.rule s.admissible

def initial : Approximation where
  rule := fun n => .pref (parityPerturbation n)
  cut := 3
  cut_ge := by omega
  admissible := fun n hn => by
    dsimp only
    have h1 := Nat.mul_le_mul_left 4 (parityPerturbation_le_one n)
    have h2 := genSeq_ge_five (fun k => .pref (parityPerturbation k)) hn
    omega
  eventualParity := fun _ _ => rfl

/-- At stage `j`, install `j + 2` unit increments at `K .. K + j + 1`, then `.pref (j + 4)` at
`K + j + 2`, then resume `.pref (parityPerturbation n)`. -/
def modifiedRule (s : Approximation) (j K n : ℕ) : StepKind :=
  if n < K then s.rule n
  else if n < K + j + 2 then .inc
  else if n = K + j + 2 then .pref (j + 4)
  else .pref (parityPerturbation n)

lemma modifiedRule_before (s : Approximation) {j K n : ℕ} (hn : n < K) :
    modifiedRule s j K n = s.rule n := by simp [modifiedRule, hn]

lemma modifiedRule_inc (s : Approximation) {j K n : ℕ} (h1 : K ≤ n) (h2 : n < K + j + 2) :
    modifiedRule s j K n = .inc := by
  simp [modifiedRule, Nat.not_lt_of_ge h1, h2]

lemma modifiedRule_jump (s : Approximation) (j K : ℕ) :
    modifiedRule s j K (K + j + 2) = .pref (j + 4) := by
  have h1 : ¬ K + j + 2 < K := by omega
  simp [modifiedRule, h1]

lemma modifiedRule_after (s : Approximation) {j K n : ℕ} (hn : K + j + 2 < n) :
    modifiedRule s j K n = .pref (parityPerturbation n) := by
  have h1 : ¬ n < K := by omega
  have h2 : ¬ n < K + j + 2 := by omega
  have h3 : n ≠ K + j + 2 := by omega
  simp [modifiedRule, h1, h2, h3]

lemma genSeq_modifiedRule_eq (s : Approximation) {j K n : ℕ} (hn : n ≤ K) :
    genSeq (modifiedRule s j K) n = s.seq n :=
  genSeq_congr (N := K) (fun _ _ hil => modifiedRule_before s hil) n (by omega)

def extend (s : Approximation) (j K : ℕ) (hK : s.cut ≤ K) (hKbig : 4 * j + 16 ≤ K) :
    Approximation where
  rule := modifiedRule s j K
  cut := K + j + 3
  cut_ge := s.cut_ge.trans (hK.trans (by omega))
  admissible := by
    intro n hn
    by_cases h1 : n < K
    · rw [modifiedRule_before s h1]
      have hseq := genSeq_modifiedRule_eq s (j := j) h1.le
      have hadm := s.admissible n hn
      cases hr : s.rule n with
      | inc => trivial
      | pref b =>
          rw [hr] at hadm
          dsimp only at hadm ⊢
          rw [hseq]
          exact hadm
    · by_cases h2 : n < K + j + 2
      · rw [modifiedRule_inc s (Nat.le_of_not_gt h1) h2]
        trivial
      · by_cases h3 : n = K + j + 2
        · subst h3
          rw [modifiedRule_jump]
          dsimp only
          have hge := genSeq_ge_succ (modifiedRule s j K) (K + j + 2)
          omega
        · rw [modifiedRule_after s (by omega)]
          dsimp only
          have hp := Nat.mul_le_mul_left 4 (parityPerturbation_le_one n)
          have hg := genSeq_ge_five (modifiedRule s j K) hn
          omega
  eventualParity := fun n hn => modifiedRule_after s (by omega)

lemma extend_seq_eq (s : Approximation) (j K : ℕ) (_hK : s.cut ≤ K) (_hKbig : 4 * j + 16 ≤ K)
    {n : ℕ} (hn : n ≤ K) : (s.extend j K _hK _hKbig).seq n = s.seq n :=
  genSeq_modifiedRule_eq s hn

end Approximation

/- Graham bounded-gap descent on unperturbed tails -/

lemma Approximation.unperturbed_pref (s : Approximation) {n : ℕ} (hn : s.cut ≤ n) :
    s.seq (n + 1) = prefixSum s.seq n + parityPerturbation n :=
  genSeq_step_pref s.rule (s.cut_ge.trans hn) (s.eventualParity n hn)

lemma Approximation.graham_recurrence (s : Approximation) {n : ℕ} (hn : s.cut ≤ n) :
    (s.seq (n + 2) : ℤ) = s.seq (n + 1) + s.seq n - (-1 : ℤ) ^ n := by
  have h1 := s.unperturbed_pref hn
  have h2 := s.unperturbed_pref (show s.cut ≤ n + 1 by omega)
  rw [show n + 1 + 1 = n + 2 by omega, prefixSum_succ] at h2
  have hnat : s.seq (n + 2) + parityPerturbation n =
      s.seq (n + 1) + s.seq n + parityPerturbation (n + 1) := by omega
  have hcast : (s.seq (n + 2) : ℤ) + parityPerturbation n =
      s.seq (n + 1) + s.seq n + parityPerturbation (n + 1) := by exact_mod_cast hnat
  have hdiff := parityPerturbation_difference n
  omega

lemma graham_block_sum (x : ℕ → ℕ) (K L q : ℕ)
    (hrec : ∀ n, K ≤ n → (x (n + 2) : ℤ) = x (n + 1) + x n - (-1 : ℤ) ^ n)
    (hKL : K ≤ L) :
    (∑ k ∈ Finset.range q, (x (L + k) : ℤ)) =
      (x (L + q + 1) : ℤ) - x (L + 1) + ∑ k ∈ Finset.range q, (-1 : ℤ) ^ (L + k) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hr := hrec (L + q) (by omega)
      rw [show L + (q + 1) + 1 = L + q + 2 by omega]
      omega

lemma alternating_odd_even_block (l q : ℕ) :
    ∑ k ∈ Finset.range (2 * q), (-1 : ℤ) ^ (2 * l + 1 + k) = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show 2 * (q + 1) = (2 * q + 1) + 1 by omega, Finset.sum_range_succ,
        Finset.sum_range_succ, ih]
      have hodd : Odd (2 * l + 1 + 2 * q) := ⟨l + q, by omega⟩
      have heven : Even (2 * l + 1 + (2 * q + 1)) := ⟨l + q + 1, by omega⟩
      rw [odd_neg_one_pow hodd, even_neg_one_pow heven]
      norm_num

lemma graham_even_block (x : ℕ → ℕ) (K r q : ℕ)
    (hrec : ∀ n, K ≤ n → (x (n + 2) : ℤ) = x (n + 1) + x n - (-1 : ℤ) ^ n)
    (hr : 1 ≤ r) (hKr : K ≤ 2 * r - 1) :
    (∑ k ∈ Finset.range q, (x (2 * (r + k)) : ℤ)) + q =
      (x (2 * (r + q) - 1) : ℤ) - x (2 * r - 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ]
      have hstep := hrec (2 * (r + q) - 1) (by omega)
      have hodd : Odd (2 * (r + q) - 1) := ⟨r + q - 1, by omega⟩
      rw [odd_neg_one_pow hodd] at hstep
      rw [show 2 * (r + q) - 1 + 1 = 2 * (r + q) by omega,
        show 2 * (r + q) - 1 + 2 = 2 * (r + (q + 1)) - 1 by omega] at hstep
      omega

lemma graham_odd_block (x : ℕ → ℕ) (K r q : ℕ)
    (hrec : ∀ n, K ≤ n → (x (n + 2) : ℤ) = x (n + 1) + x n - (-1 : ℤ) ^ n)
    (hr : 1 ≤ r) (hKr : K ≤ 2 * r - 2) :
    (∑ k ∈ Finset.range q, (x (2 * (r + k) - 1) : ℤ)) =
      (x (2 * (r + q) - 2) : ℤ) - x (2 * r - 2) + q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ]
      have hstep := hrec (2 * (r + q) - 2) (by omega)
      have heven : Even (2 * (r + q) - 2) := ⟨r + q - 1, by omega⟩
      rw [even_neg_one_pow heven] at hstep
      rw [show 2 * (r + q) - 2 + 1 = 2 * (r + q) - 1 by omega,
        show 2 * (r + q) - 2 + 2 = 2 * (r + (q + 1)) - 2 by omega] at hstep
      omega

lemma graham_odd_term_sub_mem (x : ℕ → ℕ) (K m r t : ℕ)
    (hrec : ∀ n, K ≤ n → (x (n + 2) : ℤ) = x (n + 1) + x n - (-1 : ℤ) ^ n)
    (hr : 1 ≤ r) (hKr : K ≤ 2 * r - 1) (hmr : m ≤ 2 * r - 1) :
    x (2 * (r + t) - 1) - t ∈ idxSums x (Set.Ici m) := by
  let E : Finset ℕ := (Finset.range t).image (fun k => 2 * (r + k))
  have hnot : 2 * r - 1 ∉ E := by
    intro hmem
    obtain ⟨k, _, heq⟩ := Finset.mem_image.mp hmem
    omega
  have hsumE : (∑ i ∈ E, x i) = ∑ k ∈ Finset.range t, x (2 * (r + k)) :=
    Finset.sum_image (fun i _ j _ hij => by omega)
  have hblock := graham_even_block x K r t hrec hr hKr
  have hnat : (∑ k ∈ Finset.range t, x (2 * (r + k))) + t + x (2 * r - 1) =
      x (2 * (r + t) - 1) := by
    apply Int.ofNat_inj.mp
    push_cast
    omega
  refine ⟨insert (2 * r - 1) E, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · exact hmr
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
      change m ≤ 2 * (r + k)
      omega
  · rw [Finset.sum_insert hnot, hsumE]
    omega

lemma graham_even_term_sub_mem (x : ℕ → ℕ) (K m l s t : ℕ)
    (hrec : ∀ n, K ≤ n → (x (n + 2) : ℤ) = x (n + 1) + x n - (-1 : ℤ) ^ n)
    (hKL : K ≤ 2 * l + 1) (hmL : m ≤ 2 * l + 1) (ht : t < x (2 * l + 2)) :
    let d := x (2 * l + 2) - 1 - t
    x (2 * (l + 2 + s + d)) - t ∈ idxSums x (Set.Ici m) := by
  dsimp only
  let d := x (2 * l + 2) - 1 - t
  let h := l + 2 + s
  let A : Finset ℕ := (Finset.range (2 * s)).image (fun k => 2 * l + 1 + k)
  let B : Finset ℕ := (Finset.range (d + 1)).image (fun k => 2 * (h + k) - 1)
  have hd : d + 1 + t = x (2 * l + 2) := by dsimp [d]; omega
  have hlow := graham_block_sum x K (2 * l + 1) (2 * s) hrec hKL
  rw [alternating_odd_even_block l s,
    show 2 * l + 1 + 2 * s + 1 = 2 * h - 2 by dsimp [h]; omega] at hlow
  have hhigh := graham_odd_block x K h (d + 1) hrec (by dsimp [h]; omega) (by dsimp [h]; omega)
  rw [show 2 * (h + (d + 1)) - 2 = 2 * (h + d) by omega] at hhigh
  have hsumA : (∑ i ∈ A, x i) = ∑ k ∈ Finset.range (2 * s), x (2 * l + 1 + k) :=
    Finset.sum_image (fun i _ j _ hij => by omega)
  have hsumB : (∑ i ∈ B, x i) = ∑ k ∈ Finset.range (d + 1), x (2 * (h + k) - 1) :=
    Finset.sum_image (fun i _ j _ hij => by dsimp only [h] at hij; omega)
  have htotal : (∑ i ∈ A, x i) + (∑ i ∈ B, x i) + t = x (2 * (h + d)) := by
    rw [hsumA, hsumB]
    apply Int.ofNat_inj.mp
    push_cast
    have hd' : ((d + 1 + t : ℕ) : ℤ) = x (2 * l + 2) := by exact_mod_cast hd
    rw [show 2 * l + 2 = 2 * l + 1 + 1 by omega] at hd'
    omega
  have hdisjoint : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    obtain ⟨ka, hka, ha⟩ := Finset.mem_image.mp hiA
    obtain ⟨kb, _, hb⟩ := Finset.mem_image.mp hiB
    have hka' : ka < 2 * s := Finset.mem_range.mp hka
    dsimp only [h] at hb
    omega
  refine ⟨A ∪ B, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_union] at hi
    rcases hi with hi | hi
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
      change m ≤ 2 * l + 1 + k
      omega
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
      change m ≤ 2 * (h + k) - 1
      dsimp [h]
      omega
  · rw [Finset.sum_union hdisjoint]
    dsimp only [h, d] at htotal ⊢
    omega

lemma graham_even_term_add_mem (x : ℕ → ℕ) (K m r t : ℕ)
    (hrec : ∀ n, K ≤ n → (x (n + 2) : ℤ) = x (n + 1) + x n - (-1 : ℤ) ^ n)
    (hKr : K ≤ 2 * r) (hmr : m ≤ 2 * r) :
    x (2 * (r + t)) + t ∈ idxSums x (Set.Ici m) := by
  let E : Finset ℕ := (Finset.range t).image (fun k => 2 * (r + 1 + k) - 1)
  have hnot : 2 * r ∉ E := by
    intro hmem
    obtain ⟨k, _, heq⟩ := Finset.mem_image.mp hmem
    omega
  have hsumE : (∑ i ∈ E, x i) = ∑ k ∈ Finset.range t, x (2 * (r + 1 + k) - 1) :=
    Finset.sum_image (fun i _ j _ hij => by omega)
  have hblock := graham_odd_block x K (r + 1) t hrec (by omega) (by omega)
  have hnat : x (2 * r) + (∑ k ∈ Finset.range t, x (2 * (r + 1 + k) - 1)) =
      x (2 * (r + t)) + t := by
    apply Int.ofNat_inj.mp
    push_cast
    rw [show 2 * (r + 1) - 2 = 2 * r by omega,
      show 2 * (r + 1 + t) - 2 = 2 * (r + t) by omega] at hblock
    omega
  refine ⟨insert (2 * r) E, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · exact hmr
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
      change m ≤ 2 * (r + 1 + k) - 1
      omega
  · rw [Finset.sum_insert hnot, hsumE, hnat]

lemma graham_odd_term_add_mem (x : ℕ → ℕ) (K m L r t : ℕ)
    (hrec : ∀ n, K ≤ n → (x (n + 2) : ℤ) = x (n + 1) + x n - (-1 : ℤ) ^ n)
    (hmL : m ≤ L) (ht : t ≤ x L) (hLr : L < 2 * r - 1) (hKr : K ≤ 2 * r - 1) :
    let d := x L - t
    x (2 * (r + d) - 1) + t ∈ idxSums x (Set.Ici m) := by
  dsimp only
  let d := x L - t
  let E : Finset ℕ := (Finset.range d).image (fun k => 2 * (r + k))
  have hnot1 : 2 * r - 1 ∉ E := by
    intro hmem
    obtain ⟨k, _, heq⟩ := Finset.mem_image.mp hmem
    omega
  have hnot2 : L ∉ insert (2 * r - 1) E := by
    simp only [Finset.mem_insert, not_or]
    refine ⟨by omega, fun hmem => ?_⟩
    obtain ⟨k, _, heq⟩ := Finset.mem_image.mp hmem
    omega
  have hsumE : (∑ i ∈ E, x i) = ∑ k ∈ Finset.range d, x (2 * (r + k)) :=
    Finset.sum_image (fun i _ j _ hij => by omega)
  have hblock := graham_even_block x K r d hrec (by omega) hKr
  have hd : d + t = x L := by dsimp [d]; omega
  have hnat : x L + x (2 * r - 1) + (∑ k ∈ Finset.range d, x (2 * (r + k))) =
      x (2 * (r + d) - 1) + t := by
    apply Int.ofNat_inj.mp
    push_cast
    have hd' : ((d + t : ℕ) : ℤ) = x L := by exact_mod_cast hd
    omega
  refine ⟨insert L (insert (2 * r - 1) E), ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_insert] at hi
    rcases hi with rfl | rfl | hi
    · exact hmL
    · exact hmL.trans hLr.le
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
      change m ≤ 2 * (r + k)
      omega
  · rw [Finset.sum_insert hnot2, Finset.sum_insert hnot1, hsumE]
    simpa [d, Nat.add_assoc] using hnat

lemma Approximation.eventually_lower_neighborhood (s : Approximation) (m R : ℕ) :
    ∃ H, ∀ n, H ≤ n → ∀ t, t ≤ R → s.seq n - t ∈ idxSums s.seq (Set.Ici m) := by
  let l := max s.cut m + R + 1
  let X := s.seq (2 * l + 2)
  let E := l + 2 + X
  have hKL : s.cut ≤ 2 * l + 1 := by dsimp [l]; omega
  have hmL : m ≤ 2 * l + 1 := by dsimp [l]; omega
  have hX : R < X := by
    have hlower := genSeq_ge_succ s.rule (2 * l + 2)
    change 2 * l + 2 + 1 ≤ s.seq (2 * l + 2) at hlower
    dsimp [X, l] at hlower ⊢
    omega
  refine ⟨2 * E + 1, fun n hn t htR => ?_⟩
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hkE : E + 1 ≤ k := by dsimp [E] at hn ⊢; omega
    let d := X - 1 - t
    let q := k - (l + 2 + d)
    have hmem := graham_even_term_sub_mem s.seq s.cut m l q t
      (fun j hj => s.graham_recurrence hj) hKL hmL (htR.trans_lt hX)
    dsimp only at hmem
    have hindex : 2 * (l + 2 + q + (X - 1 - t)) = n := by dsimp [q, d, E] at hkE ⊢; omega
    rwa [hindex] at hmem
  · have hkE : E ≤ k := by dsimp [E] at hn ⊢; omega
    let r := k + 1 - t
    have hmem := graham_odd_term_sub_mem s.seq s.cut m r t
      (fun j hj => s.graham_recurrence hj)
      (by dsimp [r, E, l] at hkE ⊢; omega)
      (by dsimp [r, E, l] at hkE ⊢; omega)
      (by dsimp [r, E, l] at hkE ⊢; omega)
    have hindex : 2 * (r + t) - 1 = n := by dsimp [r, E, l] at hkE ⊢; omega
    rwa [hindex] at hmem

lemma Approximation.eventually_upper_neighborhood (s : Approximation) (m R : ℕ) :
    ∃ H, ∀ n, H ≤ n → ∀ t, t ≤ R → s.seq n + t ∈ idxSums s.seq (Set.Ici m) := by
  let L := max s.cut m + R + 1
  let X := s.seq L
  let E := L + X + R + 3
  have hmL : m ≤ L := by dsimp [L]; omega
  have hX : R < X := by
    have hlower := genSeq_ge_succ s.rule L
    change L + 1 ≤ s.seq L at hlower
    dsimp [X, L] at hlower ⊢
    omega
  refine ⟨2 * E + 1, fun n hn t htR => ?_⟩
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hkE : E + 1 ≤ k := by dsimp [E] at hn ⊢; omega
    let r := k - t
    have hmem := graham_even_term_add_mem s.seq s.cut m r t
      (fun j hj => s.graham_recurrence hj)
      (by dsimp [r, E, L] at hkE ⊢; omega)
      (by dsimp [r, E, L] at hkE ⊢; omega)
    have hindex : 2 * (r + t) = n := by dsimp [r, E, L] at hkE ⊢; omega
    rwa [hindex] at hmem
  · have hkE : E ≤ k := by dsimp [E] at hn ⊢; omega
    let d := X - t
    let r := k + 1 - d
    have hLr : L < 2 * r - 1 := by dsimp [r, d, E] at hkE ⊢; omega
    have hKr : s.cut ≤ 2 * r - 1 := by dsimp [L] at hLr; omega
    have hmem := graham_odd_term_add_mem s.seq s.cut m L r t
      (fun j hj => s.graham_recurrence hj) hmL (htR.trans hX.le) hLr hKr
    dsimp only at hmem
    have hindex : 2 * (r + (s.seq L - t)) - 1 = n := by
      change 2 * (r + d) - 1 = n
      dsimp [r, d, E] at hkE ⊢
      omega
    rwa [hindex] at hmem

lemma Approximation.eventually_full_neighborhood (s : Approximation) (m R : ℕ) :
    ∃ H, ∀ n, H ≤ n → ∀ z, s.seq n - R ≤ z → z ≤ s.seq n + R →
      z ∈ idxSums s.seq (Set.Ici m) := by
  obtain ⟨Hlo, hlo⟩ := s.eventually_lower_neighborhood m R
  obtain ⟨Hhi, hhi⟩ := s.eventually_upper_neighborhood m R
  refine ⟨max Hlo Hhi, fun n hn z hzl hzu => ?_⟩
  by_cases hz : z ≤ s.seq n
  · have hmem := hlo n ((le_max_left _ _).trans hn) (s.seq n - z) (by omega)
    rwa [show s.seq n - (s.seq n - z) = z by omega] at hmem
  · have hmem := hhi n ((le_max_right _ _).trans hn) (z - s.seq n) (by omega)
    rwa [show s.seq n + (z - s.seq n) = z by omega] at hmem

/-- Sum of `a i` for `m ≤ i ≤ r`. -/
def blockTotal (a : ℕ → ℕ) (m r : ℕ) : ℕ := ∑ i ∈ Finset.Ico m (r + 1), a i

lemma prefixSum_add_blockTotal (a : ℕ → ℕ) {m r : ℕ} (hmr : m ≤ r + 1) :
    prefixSum a m + blockTotal a m r = prefixSum a (r + 1) := by
  simpa [prefixSum, blockTotal] using Finset.sum_range_add_sum_Ico a hmr

lemma blockTotal_succ (a : ℕ → ℕ) {m r : ℕ} (hmr : m ≤ r + 1) :
    blockTotal a m (r + 1) = blockTotal a m r + a (r + 1) := by
  simpa [blockTotal, Nat.add_assoc] using Finset.sum_Ico_succ_top hmr a

lemma blockTotal_ge_last (a : ℕ → ℕ) {m r : ℕ} (hmr : m ≤ r) :
    a r ≤ blockTotal a m r :=
  term_le_finset_sum a (Finset.mem_Ico.mpr ⟨hmr, Nat.lt_succ_self r⟩)

lemma Approximation.eventually_next_le_blockTotal (s : Approximation) (m : ℕ) :
    ∃ R, m ≤ R ∧ ∀ r, R ≤ r → s.seq (r + 1) ≤ blockTotal s.seq m r := by
  let R := max s.cut (max m (prefixSum s.seq m))
  refine ⟨R, by simp [R], fun r hRr => ?_⟩
  have hcut : s.cut ≤ r := (le_max_left _ _).trans hRr
  have hm : m ≤ r := (le_max_of_le_right (le_max_left _ _)).trans hRr
  have hpm : prefixSum s.seq m ≤ r := (le_max_of_le_right (le_max_right _ _)).trans hRr
  have hpref := prefixSum_add_blockTotal s.seq (m := m) (r := r) (by omega)
  rw [prefixSum_succ] at hpref
  have hrec := s.unperturbed_pref hcut
  have hble : parityPerturbation r ≤ 1 := parityPerturbation_le_one r
  have har := genSeq_ge_succ s.rule r
  change r + 1 ≤ s.seq r at har
  omega

lemma finite_gap_extend (a : ℕ → ℕ) {m r T w : ℕ}
    (hmr : m ≤ r + 1) (hT : T = blockTotal a m r) (hnext : a (r + 1) ≤ T)
    (hcover : ∀ n, n ≤ T → ∃ z, z ∈ idxSums a (Set.Ico m (r + 1)) ∧ n ≤ z ∧ z ≤ n + w) :
    ∀ n, n ≤ blockTotal a m (r + 1) →
      ∃ z, z ∈ idxSums a (Set.Ico m (r + 2)) ∧ n ≤ z ∧ z ≤ n + w := by
  intro n hn
  rw [blockTotal_succ a hmr, ← hT] at hn
  by_cases hnT : n ≤ T
  · obtain ⟨z, hz, hnz, hzw⟩ := hcover n hnT
    exact ⟨z, idxSums_mono (Set.Ico_subset_Ico_right (by omega)) hz, hnz, hzw⟩
  · obtain ⟨z, hz, hnz, hzw⟩ := hcover (n - a (r + 1)) (by omega)
    refine ⟨z + a (r + 1), ?_, by omega, by omega⟩
    exact idxSums_add_new (Set.Ico_subset_Ico_right (by omega))
      (by constructor <;> omega) (by simp) hz

lemma Approximation.bounded_gap (s : Approximation) (m : ℕ) :
    ∃ w, ∀ n, ∃ z, z ∈ idxSums s.seq (Set.Ici m) ∧ n ≤ z ∧ z ≤ n + w := by
  obtain ⟨R, hmR, hnext⟩ := s.eventually_next_le_blockTotal m
  let w := blockTotal s.seq m R
  have hblocks : ∀ q n, n ≤ blockTotal s.seq m (R + q) →
      ∃ z, z ∈ idxSums s.seq (Set.Ico m (R + q + 1)) ∧ n ≤ z ∧ z ≤ n + w := by
    intro q
    induction q with
    | zero =>
        intro n hn
        exact ⟨w, ⟨Finset.Ico m (R + 1), by simp, by simp [w, blockTotal]⟩, by omega, by omega⟩
    | succ q ih =>
        intro n hn
        have hext := finite_gap_extend s.seq (m := m) (r := R + q)
          (T := blockTotal s.seq m (R + q)) (w := w) (by omega) rfl (hnext (R + q) (by omega)) ih
        simpa [Nat.add_assoc] using hext n hn
  refine ⟨w, fun n => ?_⟩
  have hlast := blockTotal_ge_last s.seq (hmR.trans (Nat.le_add_right R n))
  have hlower := genSeq_ge_succ s.rule (R + n)
  change R + n + 1 ≤ s.seq (R + n) at hlower
  obtain ⟨z, hz, hnz, hzw⟩ := hblocks n n (by omega)
  exact ⟨z, idxSums_mono (fun i hi => hi.1) hz, hnz, hzw⟩

lemma block_gap_complement (a : ℕ → ℕ) {m r H A B w : ℕ}
    (hQ : ∀ n, H ≤ n → n ≤ A → ∃ z, z ∈ idxSums a (Set.Ico m (r + 1)) ∧ n ≤ z ∧ z ≤ n + w)
    (hB : B = blockTotal a m r) (hHB : H + w ≤ B) (hAB : A + w ≤ B) :
    ∀ n, B - A - w ≤ n → n ≤ B - H - w →
      ∃ z, z ∈ idxSums a (Set.Ico m (r + 1)) ∧ n ≤ z ∧ z ≤ n + w := by
  intro n hnlo hnhi
  let p := B - (n + w)
  obtain ⟨z, hz, hpz, hzp⟩ := hQ p (by dsimp [p]; omega) (by dsimp [p]; omega)
  have hz' : z ∈ idxSums a (↑(Finset.Ico m (r + 1)) : Set ℕ) := by simpa using hz
  have hzcomp := idxSums_complement hz'
  have htotal : (∑ i ∈ Finset.Ico m (r + 1), a i) = B := by simpa [blockTotal] using hB.symm
  rw [htotal] at hzcomp
  refine ⟨B - z, by simpa using hzcomp, ?_, ?_⟩ <;> (dsimp [p] at hpz hzp; omega)

lemma translated_gap_decreases (a : ℕ → ℕ) {m r H B u w : ℕ}
    (hw : 1 ≤ w) (hmr : m ≤ r + 1)
    (hQ : ∀ n, H ≤ n → n ≤ B → ∃ z, z ∈ idxSums a (Set.Ico m (r + 1)) ∧ n ≤ z ∧ z ≤ n + w)
    (hu : u ∈ idxSums a (Set.Ici (r + 1)))
    (hu1 : u + 1 ∈ idxSums a (Set.Ici (r + 1))) :
    ∀ n, H + u + 1 ≤ n → n ≤ B + u →
      ∃ z, z ∈ idxSums a (Set.Ici m) ∧ n ≤ z ∧ z ≤ n + (w - 1) := by
  intro n hnlo hnhi
  let p := n - u - 1
  obtain ⟨z, hz, hpz, hzw⟩ := hQ p (by dsimp [p]; omega) (by dsimp [p]; omega)
  have hdisj : ∀ i, i ∈ Set.Ico m (r + 1) → i ∈ Set.Ici (r + 1) → False :=
    fun _ hi hj => (not_lt_of_ge hj) hi.2
  by_cases hzp : z = p
  · refine ⟨z + (u + 1), idxSums_add_disjoint (fun i hi => hi.1) (fun i hi => hmr.trans hi)
      hdisj hz hu1, ?_, ?_⟩ <;> (dsimp [p] at hzp; omega)
  · refine ⟨z + u, idxSums_add_disjoint (fun i hi => hi.1) (fun i hi => hmr.trans hi)
      hdisj hz hu, by omega, by omega⟩

lemma Approximation.graham_upper_step (s : Approximation) {n : ℕ} (hn : s.cut ≤ n) :
    s.seq (n + 2) ≤ s.seq (n + 1) + s.seq n + 1 := by
  have hrec := s.graham_recurrence hn
  rcases neg_one_pow_cases n with hp | hp <;> rw [hp] at hrec <;> omega

lemma Approximation.graham_lower_step (s : Approximation) {n : ℕ} (hn : s.cut ≤ n) :
    s.seq (n + 1) + s.seq n ≤ s.seq (n + 2) + 1 := by
  have hrec := s.graham_recurrence hn
  rcases neg_one_pow_cases n with hp | hp <;> rw [hp] at hrec <;> omega

lemma Approximation.consecutive_translations (s : Approximation) {r : ℕ}
    (hcut : s.cut ≤ r + 1) :
    ∃ u, u ∈ idxSums s.seq (Set.Ici (r + 1)) ∧ u + 1 ∈ idxSums s.seq (Set.Ici (r + 1)) ∧
      u ≤ s.seq (r + 3) ∧ s.seq (r + 3) ≤ u + 1 := by
  have hone : s.seq (r + 3) ∈ idxSums s.seq (Set.Ici (r + 1)) :=
    ⟨{r + 3}, fun i hi => by simp only [Finset.mem_coe, Finset.mem_singleton] at hi; subst i; change r + 1 ≤ r + 3; omega, by simp⟩
  have hpair : s.seq (r + 1) + s.seq (r + 2) ∈ idxSums s.seq (Set.Ici (r + 1)) := by
    refine ⟨{r + 1, r + 2}, ?_, Finset.sum_pair (by omega)⟩
    intro i hi
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> (change r + 1 ≤ _; omega)
  have hrec := s.graham_recurrence hcut
  rw [show r + 1 + 2 = r + 3 by omega, show r + 1 + 1 = r + 2 by omega] at hrec
  rcases Nat.even_or_odd (r + 1) with heven | hodd
  · rw [even_neg_one_pow heven] at hrec
    have heq : s.seq (r + 3) + 1 = s.seq (r + 1) + s.seq (r + 2) := by omega
    exact ⟨s.seq (r + 3), hone, heq.symm ▸ hpair, by omega, by omega⟩
  · rw [odd_neg_one_pow hodd] at hrec
    have heq : s.seq (r + 1) + s.seq (r + 2) + 1 = s.seq (r + 3) := by omega
    exact ⟨s.seq (r + 1) + s.seq (r + 2), hpair, heq.symm ▸ hone, by omega, by omega⟩

lemma Approximation.eventually_blockTotal_add_le_two_next (s : Approximation) (m C : ℕ) :
    ∃ R, m ≤ R ∧ ∀ r, R ≤ r → blockTotal s.seq m r + C ≤ 2 * s.seq (r + 1) := by
  let R := max (s.cut + 1) (max m (C + 2))
  refine ⟨R, by simp [R], fun r hR => ?_⟩
  have hcutPrev : s.cut ≤ r - 1 := by dsimp [R] at hR; omega
  have hcut : s.cut ≤ r := hcutPrev.trans (Nat.sub_le r 1)
  have hm : m ≤ r := by dsimp [R] at hR; omega
  have hC : C + 2 ≤ r := by dsimp [R] at hR; omega
  have hprev := genSeq_ge_succ s.rule (r - 1)
  change r - 1 + 1 ≤ s.seq (r - 1) at hprev
  have hlower := s.graham_lower_step hcutPrev
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r), show r - 1 + 2 = r + 1 by omega] at hlower
  have hupper := s.graham_upper_step hcut
  have hpref := prefixSum_add_blockTotal s.seq (m := m) (r := r) (by omega)
  have hgen := s.unperturbed_pref (n := r + 1) (by omega)
  rw [show r + 1 + 1 = r + 2 by omega] at hgen
  omega

lemma Approximation.gap_descent (s : Approximation) (m H w : ℕ) (hw : 1 ≤ w)
    (hgap : ∀ n, H ≤ n → ∃ z, z ∈ idxSums s.seq (Set.Ici m) ∧ n ≤ z ∧ z ≤ n + w) :
    ∃ H', ∀ n, H' ≤ n → ∃ z, z ∈ idxSums s.seq (Set.Ici m) ∧ n ≤ z ∧ z ≤ n + (w - 1) := by
  let C := prefixSum s.seq m + H + w + 6
  obtain ⟨Hnear, hnear⟩ := s.eventually_full_neighborhood m C
  obtain ⟨Rmargin, _, hmargin⟩ := s.eventually_blockTotal_add_le_two_next m (w + 1)
  obtain ⟨Rnext, _, hnext⟩ := s.eventually_next_le_blockTotal m
  let R := max Rmargin (max Rnext (max Hnear (H + w + m + s.cut + C + 3)))
  have hmR : m ≤ R := by dsimp [R]; omega
  have hlocal : ∀ r, R ≤ r → ∀ n, s.seq (r + 3) - C ≤ n → n ≤ s.seq (r + 4) - C →
      ∃ z, z ∈ idxSums s.seq (Set.Ici m) ∧ n ≤ z ∧ z ≤ n + (w - 1) := by
    intro r hRr n hnlo hnhi
    have hrMargin : Rmargin ≤ r := (le_max_left _ _).trans hRr
    have hrNext : Rnext ≤ r := (le_max_of_le_right (le_max_left _ _)).trans hRr
    have hrNear : Hnear ≤ r + 3 := by dsimp [R] at hRr; omega
    have hm : m ≤ r := hmR.trans hRr
    have hcut : s.cut ≤ r + 1 := by dsimp [R] at hRr; omega
    let T := blockTotal s.seq m r
    let A := s.seq (r + 1) - w - 1
    let B := T - H - w
    have hlast : s.seq r ≤ T := blockTotal_ge_last s.seq hm
    have hrlower := genSeq_ge_succ s.rule r
    change r + 1 ≤ s.seq r at hrlower
    have hHT : H + w ≤ T := by dsimp [R] at hRr; omega
    have hxw : w + 1 ≤ s.seq (r + 1) := by
      have hl := genSeq_ge_succ s.rule (r + 1)
      change r + 1 + 1 ≤ s.seq (r + 1) at hl
      dsimp [R] at hRr
      omega
    have hAT : A + w ≤ T := by
      have hnxt := hnext r hrNext
      dsimp [A, T]
      omega
    have hQlow : ∀ p, H ≤ p → p ≤ A →
        ∃ z, z ∈ idxSums s.seq (Set.Ico m (r + 1)) ∧ p ≤ z ∧ z ≤ p + w := by
      intro p hpH hpA
      obtain ⟨z, hz, hpz, hzw⟩ := hgap p hpH
      exact ⟨z, idxSums_restrict_below s.seq_strictMono.monotone hz (by dsimp [A] at hpA; omega),
        hpz, hzw⟩
    have hQhigh := block_gap_complement s.seq hQlow (B := T) rfl hHT hAT
    have hcentral : ∀ p, H ≤ p → p ≤ B →
        ∃ z, z ∈ idxSums s.seq (Set.Ico m (r + 1)) ∧ p ≤ z ∧ z ≤ p + w := by
      intro p hpH hpB
      by_cases hpA : p ≤ A
      · exact hQlow p hpH hpA
      · have hmargin' := hmargin r hrMargin
        exact hQhigh p (by dsimp [T, A] at hmargin' ⊢; omega) (by simpa [B] using hpB)
    obtain ⟨u, hu, hu1, hule, hule1⟩ := s.consecutive_translations hcut
    have htranslated := translated_gap_decreases s.seq hw (hmR.trans (hRr.trans (by omega)))
      hcentral hu hu1
    have hJupper : s.seq (r + 4) ≤ B + u + C := by
      have hpref := prefixSum_add_blockTotal s.seq (m := m) (r := r) (by omega)
      have hble : parityPerturbation (r + 1) ≤ 1 := parityPerturbation_le_one _
      have hgen := s.unperturbed_pref hcut
      rw [show r + 1 + 1 = r + 2 by omega] at hgen
      have hupper := s.graham_upper_step (show s.cut ≤ r + 2 by omega)
      rw [show r + 2 + 2 = r + 4 by omega, show r + 2 + 1 = r + 3 by omega] at hupper
      dsimp [B, T, C]
      omega
    by_cases hncenter : n ≤ s.seq (r + 3) + C
    · exact ⟨n, hnear (r + 3) hrNear n hnlo hncenter, le_rfl, by omega⟩
    · exact htranslated n (by omega) (by dsimp [B] at hJupper ⊢; omega)
  let H' := s.seq (R + 3) - C
  refine ⟨H', ?_⟩
  have hchain : ∀ q n, H' ≤ n → n ≤ s.seq (R + q + 4) - C →
      ∃ z, z ∈ idxSums s.seq (Set.Ici m) ∧ n ≤ z ∧ z ≤ n + (w - 1) := by
    intro q
    induction q with
    | zero => exact fun n hnlo hnhi => hlocal R (le_refl R) n hnlo (by simpa using hnhi)
    | succ q ih =>
        intro n hnlo hnhi
        by_cases hprev : n ≤ s.seq (R + q + 4) - C
        · exact ih n hnlo hprev
        · exact hlocal (R + q + 1) (by omega) n
            (by simpa [Nat.add_assoc] using Nat.le_of_lt (Nat.lt_of_not_ge hprev))
            (by simpa [Nat.add_assoc] using hnhi)
  intro n hn
  let q := n + C
  have hlower := genSeq_ge_succ s.rule (R + q + 4)
  change R + q + 4 + 1 ≤ s.seq (R + q + 4) at hlower
  exact hchain q n hn (by dsimp [q] at hlower ⊢; omega)

lemma Approximation.gap_bound_to_completeness (s : Approximation) (m : ℕ) :
    ∀ w H, (∀ n, H ≤ n → ∃ z, z ∈ idxSums s.seq (Set.Ici m) ∧ n ≤ z ∧ z ≤ n + w) →
      ∃ H', ∀ n, H' ≤ n → n ∈ idxSums s.seq (Set.Ici m)
  | 0, H, hgap => by
      refine ⟨H, fun n hn => ?_⟩
      obtain ⟨z, hz, hnz, hzn⟩ := hgap n hn
      have hzeq : z = n := by omega
      rwa [hzeq] at hz
  | w + 1, H, hgap => by
      obtain ⟨H', hgap'⟩ := s.gap_descent m H (w + 1) (by omega) hgap
      exact s.gap_bound_to_completeness m w H' (by simpa using hgap')

lemma Approximation.every_tail_complete (s : Approximation) (m : ℕ) :
    ∃ H, ∀ n, H ≤ n → n ∈ idxSums s.seq (Set.Ici m) := by
  obtain ⟨w, hgap⟩ := s.bounded_gap m
  exact s.gap_bound_to_completeness m w 0 (by simpa using hgap)

/- Permanent certificate extraction -/

structure PermanentCertificate (s : Approximation) (m : ℕ) where
  N : ℕ
  u : ℕ
  L : ℕ
  start_le : m ≤ N
  three_le : 3 ≤ N
  interval : ∀ t, u ≤ t → t ≤ u + L → t ∈ idxSums s.seq (Set.Icc m N)
  lock1 : 4 * prefixSum s.seq (N + 1) ≤ 4 * (L + 1) + 3 * s.seq N
  lock2 : prefixSum s.seq (N + 1) ≤ L + prefixSum s.seq N

lemma prefixSum_ge_len {a : ℕ → ℕ} (ha : ∀ n, 0 < a n) (n : ℕ) : n ≤ prefixSum a n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [prefixSum_succ]
      have hp := ha n
      omega

lemma Approximation.certificate_nonempty (s : Approximation) (m : ℕ) :
    Nonempty (PermanentCertificate s m) := by
  obtain ⟨H, hcomplete⟩ := s.every_tail_complete m
  let N := max m (max (2 * H) (4 * (prefixSum s.seq m + 2 * H) + s.cut + 4))
  have hmN : m ≤ N := le_max_left _ _
  have hcut1 : s.cut + 1 ≤ N := by dsimp [N]; omega
  have hcutN : s.cut ≤ N := by omega
  have h2HN : 2 * H ≤ N := by dsimp [N]; omega
  have hLockN : 4 * (prefixSum s.seq m + 2 * H) ≤ N := by dsimp [N]; omega
  let T := blockTotal s.seq m N
  have hpref : prefixSum s.seq m + T = prefixSum s.seq (N + 1) :=
    prefixSum_add_blockTotal s.seq (by omega)
  have hgen2 := s.unperturbed_pref (n := N + 1) (by omega)
  rw [show N + 1 + 1 = N + 2 by omega] at hgen2
  have hupper := s.graham_upper_step hcutN
  have hlowPrev := s.graham_lower_step (n := N - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ N), show N - 1 + 2 = N + 1 by omega] at hlowPrev
  have hge5 := genSeq_ge_five s.rule (n := N - 1) (by have := s.cut_ge; omega)
  change 5 ≤ s.seq (N - 1) at hge5
  have hTlt : T < 2 * s.seq (N + 1) := by omega
  have hlast : s.seq N ≤ T := blockTotal_ge_last s.seq hmN
  have hNlarge := genSeq_ge_succ s.rule N
  change N + 1 ≤ s.seq N at hNlarge
  have hpsN := prefixSum_ge_len s.seq_pos N
  have htwoH : 2 * H ≤ T := by omega
  let L := T - 2 * H
  have hLT : L + 2 * H = T := by dsimp [L]; omega
  have hsets : Set.Ico m (N + 1) = Set.Icc m N := by
    ext i; simp only [Set.mem_Ico, Set.mem_Icc]; omega
  have hfirst : ∀ t, H ≤ t → t ≤ s.seq (N + 1) - 1 →
      t ∈ idxSums s.seq (Set.Ico m (N + 1)) := fun t htH hta =>
    idxSums_restrict_below s.seq_strictMono.monotone (hcomplete t htH) (by omega)
  have hsecond : ∀ t, T - s.seq (N + 1) + 1 ≤ t → t ≤ T - H →
      t ∈ idxSums s.seq (Set.Ico m (N + 1)) := by
    intro t htlo hthi
    let q := T - t
    have hqmem : q ∈ idxSums s.seq (↑(Finset.Ico m (N + 1)) : Set ℕ) := by
      simpa using hfirst q (by dsimp [q]; omega) (by dsimp [q]; omega)
    have hcomp := idxSums_complement hqmem
    have htotal : ∑ i ∈ Finset.Ico m (N + 1), s.seq i = T := rfl
    rw [htotal, show T - q = t by dsimp [q]; omega] at hcomp
    simpa using hcomp
  refine ⟨⟨N, H, L, hmN, s.cut_ge.trans hcutN, ?_, by omega, by omega⟩⟩
  intro t htH htu
  have htmem : t ∈ idxSums s.seq (Set.Ico m (N + 1)) := by
    by_cases hta : t ≤ s.seq (N + 1) - 1
    · exact hfirst t htH hta
    · exact hsecond t (by omega) (by omega)
  rwa [hsets] at htmem

noncomputable def Approximation.certificate (s : Approximation) (m : ℕ) :
    PermanentCertificate s m := Classical.choice (s.certificate_nonempty m)

/- Stagewise construction -/

noncomputable def stages : ℕ → Approximation
  | 0 => Approximation.initial
  | j + 1 =>
      let s := stages j
      let K := max s.cut ((s.certificate j).N + 1) + 4 * j + 30
      s.extend j K (by dsimp [K]; omega) (by dsimp [K]; omega)

noncomputable def perturbationIndex (j : ℕ) : ℕ :=
  max (stages j).cut (((stages j).certificate j).N + 1) + 4 * j + 30

noncomputable def jumpIndex (j : ℕ) : ℕ := perturbationIndex j + j + 2

lemma stages_succ (j : ℕ) :
    stages (j + 1) = (stages j).extend j (perturbationIndex j)
      (by dsimp [perturbationIndex]; omega) (by dsimp [perturbationIndex]; omega) := rfl

lemma stages_cut_succ (j : ℕ) : (stages (j + 1)).cut = jumpIndex j + 1 := rfl

lemma perturbationIndex_strictMono : StrictMono perturbationIndex := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hcut : (stages (j + 1)).cut ≤ perturbationIndex (j + 1) := by
    dsimp [perturbationIndex]; omega
  rw [stages_cut_succ] at hcut
  dsimp [jumpIndex] at hcut
  omega

lemma jumpIndex_strictMono : StrictMono jumpIndex := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hp : perturbationIndex j < perturbationIndex (j + 1) :=
    perturbationIndex_strictMono (Nat.lt_succ_self j)
  dsimp [jumpIndex]
  omega

lemma stages_cut_mono : Monotone (fun j => (stages j).cut) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [stages_cut_succ]
  dsimp [jumpIndex, perturbationIndex]
  omega

lemma stages_cut_ge_index (j : ℕ) : j + 3 ≤ (stages j).cut := by
  induction j with
  | zero => decide
  | succ j ih =>
      rw [stages_cut_succ]
      dsimp [jumpIndex, perturbationIndex]
      omega

lemma stages_rule_succ_eq (j : ℕ) {n : ℕ} (hn : n < (stages j).cut) :
    (stages (j + 1)).rule n = (stages j).rule n := by
  rw [stages_succ]
  apply Approximation.modifiedRule_before
  dsimp [perturbationIndex]
  omega

lemma stages_rule_stable {j k n : ℕ} (hjk : j ≤ k) (hn : n < (stages j).cut) :
    (stages k).rule n = (stages j).rule n := by
  induction k with
  | zero =>
      obtain rfl : j = 0 := by omega
      rfl
  | succ k ih =>
      by_cases hj : j = k + 1
      · subst hj; rfl
      · have hjk' : j ≤ k := by omega
        rw [stages_rule_succ_eq k (hn.trans_le (stages_cut_mono hjk')), ih hjk']

noncomputable def finalRule (n : ℕ) : StepKind := (stages (n + 1)).rule n

noncomputable def finalSeq : ℕ → ℕ := genSeq finalRule

lemma finalRule_eq_stage {j n : ℕ} (hn : n < (stages j).cut) :
    finalRule n = (stages j).rule n := by
  by_cases hj : j ≤ n + 1
  · exact stages_rule_stable hj hn
  · have hncut : n < (stages (n + 1)).cut := by have := stages_cut_ge_index (n + 1); omega
    exact (stages_rule_stable (by omega) hncut).symm

lemma finalSeq_eq_stage {j n : ℕ} (hn : n ≤ (stages j).cut) :
    finalSeq n = (stages j).seq n :=
  genSeq_congr (N := (stages j).cut) (fun _ _ hin => finalRule_eq_stage hin) n (by omega)

lemma finalSeq_eq_at_perturbation (j : ℕ) {n : ℕ} (hn : n ≤ perturbationIndex j) :
    finalSeq n = (stages j).seq n := by
  have hsub : n ≤ (stages (j + 1)).cut := by rw [stages_cut_succ]; dsimp [jumpIndex]; omega
  rw [finalSeq_eq_stage hsub, stages_succ]
  exact Approximation.extend_seq_eq (stages j) j (perturbationIndex j) _ _ hn

lemma finalRule_admissible : AdmissibleRule finalRule := by
  intro n hn
  have hncut : n < (stages (n + 1)).cut := by have := stages_cut_ge_index (n + 1); omega
  have hseq := finalSeq_eq_stage hncut.le
  have hadm := (stages (n + 1)).admissible n hn
  change match finalRule n with | .inc => True | .pref b => 4 * b ≤ finalSeq n
  rw [finalRule]
  cases hr : (stages (n + 1)).rule n with
  | inc => trivial
  | pref b =>
      rw [hr] at hadm
      dsimp only at hadm ⊢
      rw [hseq]
      exact hadm

lemma finalSeq_pos (n : ℕ) : 0 < finalSeq n := genSeq_pos finalRule n

lemma finalSeq_ge_succ (n : ℕ) : n + 1 ≤ finalSeq n := genSeq_ge_succ finalRule n

lemma finalSeq_strictMono : StrictMono finalSeq :=
  genSeq_strictMono finalRule finalRule_admissible

/- Flat runs and jump structure of finalSeq -/

lemma finalRule_inc_on_run (j t : ℕ) (ht : t < j + 2) :
    finalRule (perturbationIndex j + t) = .inc := by
  have hcut : perturbationIndex j + t < (stages (j + 1)).cut := by
    rw [stages_cut_succ]; dsimp [jumpIndex]; omega
  rw [finalRule_eq_stage hcut, stages_succ]
  exact Approximation.modifiedRule_inc (stages j) (by omega) (by omega)

lemma finalSeq_on_run (j t : ℕ) (ht : t ≤ j + 2) :
    finalSeq (perturbationIndex j + t) = finalSeq (perturbationIndex j) + t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hprev := ih (by omega)
      have hrule := finalRule_inc_on_run j t (by omega)
      have h3 : 3 ≤ perturbationIndex j + t := by dsimp [perturbationIndex]; omega
      have hstep := genSeq_step_inc finalRule h3 hrule
      change finalSeq (perturbationIndex j + t + 1) = finalSeq (perturbationIndex j + t) + 1 at hstep
      rw [show perturbationIndex j + (t + 1) = perturbationIndex j + t + 1 by omega, hstep, hprev]
      omega

lemma finalRule_at_jump (j : ℕ) : finalRule (jumpIndex j) = .pref (j + 4) := by
  have hcut : jumpIndex j < (stages (j + 1)).cut := by rw [stages_cut_succ]; omega
  rw [finalRule_eq_stage hcut, stages_succ]
  exact Approximation.modifiedRule_jump (stages j) j (perturbationIndex j)

lemma finalSeq_after_jump (j : ℕ) :
    finalSeq (jumpIndex j + 1) = prefixSum finalSeq (jumpIndex j) + (j + 4) := by
  have h3 : 3 ≤ jumpIndex j := by dsimp [jumpIndex, perturbationIndex]; omega
  exact genSeq_step_pref finalRule h3 (finalRule_at_jump j)

lemma stages_rule_inv (k i : ℕ) :
    (∃ b, (stages k).rule i = .pref b) ∨
    (∃ j < k, perturbationIndex j ≤ i ∧ i < jumpIndex j) := by
  induction k with
  | zero => exact Or.inl ⟨parityPerturbation i, rfl⟩
  | succ k ih =>
      rw [stages_succ]
      change (∃ b, Approximation.modifiedRule (stages k) k (perturbationIndex k) i = .pref b) ∨ _
      by_cases h1 : i < perturbationIndex k
      · rw [Approximation.modifiedRule_before _ h1]
        rcases ih with ⟨b, hb⟩ | ⟨j, hjk, hj1, hj2⟩
        · exact Or.inl ⟨b, hb⟩
        · exact Or.inr ⟨j, by omega, hj1, hj2⟩
      · by_cases h2 : i < perturbationIndex k + k + 2
        · exact Or.inr ⟨k, Nat.lt_succ_self k, Nat.le_of_not_gt h1, h2⟩
        · by_cases h3 : i = perturbationIndex k + k + 2
          · subst h3
            rw [Approximation.modifiedRule_jump]
            exact Or.inl ⟨k + 4, rfl⟩
          · rw [Approximation.modifiedRule_after _ (by omega)]
            exact Or.inl ⟨parityPerturbation i, rfl⟩

/- Verification of all five properties in Erdos346.erdos_346.variants.example -/

lemma final_isAddStronglyCompleteNatSeq : IsAddStronglyCompleteNatSeq finalSeq := by
  intro m
  let cert := (stages m).certificate m
  have hNle : cert.N + 1 ≤ perturbationIndex m := by dsimp [perturbationIndex, cert]; omega
  have heq : ∀ i, i ∈ Set.Icc m cert.N → finalSeq i = (stages m).seq i :=
    fun i hi => finalSeq_eq_at_perturbation m (by have := hi.2; omega)
  have hinterval : ∀ t, cert.u ≤ t → t ≤ cert.u + cert.L →
      t ∈ idxSums finalSeq (Set.Icc m cert.N) := by
    intro t htu hut
    rw [idxSums_congr_on heq]
    exact cert.interval t htu hut
  have hpref1 : prefixSum finalSeq (cert.N + 1) = prefixSum (stages m).seq (cert.N + 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiLt : i < cert.N + 1 := Finset.mem_range.mp hi
    exact finalSeq_eq_at_perturbation m (by omega)
  have hpref0 : prefixSum finalSeq cert.N = prefixSum (stages m).seq cert.N := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiLt : i < cert.N := Finset.mem_range.mp hi
    exact finalSeq_eq_at_perturbation m (by omega)
  have hseqN : finalSeq cert.N = (stages m).seq cert.N :=
    finalSeq_eq_at_perturbation m (by omega)
  obtain ⟨H, htail⟩ := permanent_interval_certificate finalRule cert.start_le cert.three_le
    finalRule_admissible hinterval
    (by change 4 * prefixSum finalSeq (cert.N + 1) ≤ 4 * (cert.L + 1) + 3 * finalSeq cert.N;
        rw [hpref1, hseqN]; exact cert.lock1)
    (by change prefixSum finalSeq (cert.N + 1) ≤ cert.L + prefixSum finalSeq cert.N;
        rw [hpref1, hpref0]; exact cert.lock2)
  rw [IsAddComplete, Filter.eventually_atTop]
  refine ⟨H, fun t ht => ?_⟩
  obtain ⟨F, hF, hsum⟩ := htail t ht
  refine ⟨F.image finalSeq, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp hx
    have hmi : m ≤ i := hF hiF
    refine ⟨i - m, ?_⟩
    dsimp only
    rw [show m + (i - m) = i by omega]
  · change ∑ i ∈ F, finalSeq i = t at hsum
    rw [Finset.sum_image (fun i _ j _ hij => finalSeq_strictMono.injective hij), hsum]

lemma final_infinite_diff_not_complete {B : Set ℕ} (hB : B ⊆ Set.range finalSeq) (hB' : B.Infinite) :
    ¬ IsAddComplete (Set.range finalSeq \ B) := by
  have hpre : (finalSeq ⁻¹' B).Infinite := by
    intro hfin
    refine hB' <| (hfin.image finalSeq).subset fun b hb => ?_
    obtain ⟨m, rfl⟩ := hB hb
    exact ⟨m, hb, rfl⟩
  rw [IsAddComplete, Filter.not_eventually, Filter.frequently_atTop]
  intro H
  obtain ⟨p₀, hp₀B, hp₀⟩ := hpre.exists_gt 0
  obtain ⟨i, hiB, hi⟩ := hpre.exists_gt (max p₀ (max (H + 3) ((stages (p₀ + 1)).cut)))
  have hp₀val : 2 ≤ finalSeq p₀ := by
    have h := finalSeq_ge_succ p₀
    omega
  have hi3 : 3 ≤ i := by omega
  rcases stages_rule_inv (i + 1) i with ⟨b, hb⟩ | ⟨j, _, hj1, hj2⟩
  · -- Case 1: finalRule i = .pref b
    have hstep := genSeq_step_pref finalRule hi3 hb
    change finalSeq (i + 1) = prefixSum finalSeq i + b at hstep
    have hHi : H ≤ finalSeq (i + 1) - 1 := by
      have hl := finalSeq_ge_succ (i + 1)
      omega
    refine ⟨finalSeq (i + 1) - 1, hHi, ?_⟩
    rintro ⟨C, hC, hsumC⟩
    let S := (Finset.range i).erase p₀
    have hCsub : C ⊆ S.image finalSeq := by
      intro c hc
      obtain ⟨⟨k, rfl⟩, hcB⟩ := hC hc
      have hle : finalSeq k ≤ ∑ x ∈ C, x :=
        Finset.single_le_sum (f := fun j => j) (fun _ _ => Nat.zero_le _) hc
      have hki : k < i := by
        by_contra hcon
        rcases Nat.lt_or_ge k (i + 1) with hk | hk
        · obtain rfl : k = i := by omega
          exact hcB hiB
        · have hge : finalSeq (i + 1) ≤ finalSeq k := finalSeq_strictMono.monotone hk
          have hpos1 := finalSeq_pos (i + 1)
          omega
      refine Finset.mem_image.mpr ⟨k, Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr hki⟩, rfl⟩
      rintro rfl
      exact hcB hp₀B
    have h1 : ∑ x ∈ C, x ≤ ∑ k ∈ S, finalSeq k :=
      (Finset.sum_le_sum_of_subset hCsub).trans
        (Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _)
    have he := Finset.add_sum_erase (Finset.range i) finalSeq
      (Finset.mem_range.mpr (by omega : p₀ < i))
    change finalSeq p₀ + ∑ k ∈ S, finalSeq k = prefixSum finalSeq i at he
    omega
  · -- Case 2: i lies in flat run [perturbationIndex j, jumpIndex j)
    have hp₀j : p₀ < perturbationIndex j := by
      by_contra hcon
      have hjp : j + 1 ≤ p₀ + 1 := by
        have hcut_le : j + 3 ≤ (stages j).cut := stages_cut_ge_index j
        dsimp [perturbationIndex] at hcon
        omega
      have hcut_mono : (stages (j + 1)).cut ≤ (stages (p₀ + 1)).cut := stages_cut_mono hjp
      rw [stages_cut_succ] at hcut_mono
      omega
    let K' := jumpIndex j
    have hstep := finalSeq_after_jump j
    change finalSeq (K' + 1) = prefixSum finalSeq K' + (j + 4) at hstep
    have hHK' : H ≤ finalSeq (K' + 1) - 1 := by
      have hl := finalSeq_ge_succ (K' + 1)
      change K' + 1 + 1 ≤ finalSeq (K' + 1) at hl
      have hiK' : i < K' := hj2
      omega
    refine ⟨finalSeq (K' + 1) - 1, hHK', ?_⟩
    rintro ⟨C, hC, hsumC⟩
    let S := ((Finset.range (K' + 1)).erase i).erase p₀
    have hCsub : C ⊆ S.image finalSeq := by
      intro c hc
      obtain ⟨⟨k, rfl⟩, hcB⟩ := hC hc
      have hle : finalSeq k ≤ ∑ x ∈ C, x :=
        Finset.single_le_sum (f := fun j => j) (fun _ _ => Nat.zero_le _) hc
      have hkK' : k < K' + 1 := by
        by_contra hcon
        have hge : finalSeq (K' + 1) ≤ finalSeq k :=
          finalSeq_strictMono.monotone (Nat.le_of_not_gt hcon)
        omega
      refine Finset.mem_image.mpr ⟨k, Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr hkK'⟩⟩, rfl⟩
      · rintro rfl; exact hcB hp₀B
      · rintro rfl; exact hcB hiB
    have h1 : ∑ x ∈ C, x ≤ ∑ k ∈ S, finalSeq k :=
      (Finset.sum_le_sum_of_subset hCsub).trans
        (Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _)
    have he1 := Finset.add_sum_erase (Finset.range (K' + 1)) finalSeq
      (Finset.mem_range.mpr (show i < K' + 1 by have := hj2; dsimp [K']; omega))
    have he2 := Finset.add_sum_erase ((Finset.range (K' + 1)).erase i) finalSeq
      (Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (show p₀ < K' + 1 by have := hj2; dsimp [K']; omega)⟩)
    change finalSeq p₀ + ∑ k ∈ S, finalSeq k = ∑ k ∈ (Finset.range (K' + 1)).erase i, finalSeq k at he2
    have htot : (∑ k ∈ Finset.range (K' + 1), finalSeq k) = prefixSum finalSeq K' + finalSeq K' :=
      prefixSum_succ finalSeq K'
    have hrunK' : finalSeq K' = finalSeq (perturbationIndex j) + (j + 2) :=
      finalSeq_on_run j (j + 2) (le_refl _)
    have hige : finalSeq (perturbationIndex j) ≤ finalSeq i := finalSeq_strictMono.monotone hj1
    omega

lemma jump_ratio_bound (j : ℕ) :
    (j + 1) * finalSeq (jumpIndex j) ≤ 2 * finalSeq (jumpIndex j + 1) := by
  have hafter := finalSeq_after_jump j
  have hrun := finalSeq_on_run j (j + 2) (le_refl _)
  change finalSeq (jumpIndex j) = finalSeq (perturbationIndex j) + (j + 2) at hrun
  have hsub : Finset.Ico (perturbationIndex j) (jumpIndex j) ⊆ Finset.range (jumpIndex j) := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  have hcard : (Finset.Ico (perturbationIndex j) (jumpIndex j)).card = j + 2 := by
    simp [jumpIndex]
    omega
  have hsum_ge : (j + 2) * finalSeq (perturbationIndex j) ≤ prefixSum finalSeq (jumpIndex j) := by
    calc
      (j + 2) * finalSeq (perturbationIndex j)
          = ∑ _k ∈ Finset.Ico (perturbationIndex j) (jumpIndex j), finalSeq (perturbationIndex j) := by
            rw [Finset.sum_const, hcard, smul_eq_mul]
      _ ≤ ∑ k ∈ Finset.Ico (perturbationIndex j) (jumpIndex j), finalSeq k :=
            Finset.sum_le_sum fun k hk => finalSeq_strictMono.monotone (Finset.mem_Ico.mp hk).1
      _ ≤ prefixSum finalSeq (jumpIndex j) := Finset.sum_le_sum_of_subset hsub
  have hKj_ge : j + 2 ≤ finalSeq (perturbationIndex j) := by
    have h1 : j + 1 ≤ perturbationIndex j := by dsimp [perturbationIndex]; omega
    have hl := finalSeq_ge_succ (perturbationIndex j)
    omega
  have htwo : finalSeq (jumpIndex j) ≤ 2 * finalSeq (perturbationIndex j) := by omega
  have hmul : (j + 2) * finalSeq (jumpIndex j) ≤ (j + 2) * (2 * finalSeq (perturbationIndex j)) :=
    Nat.mul_le_mul_left (j + 2) htwo
  have hmul2 : (j + 1) * finalSeq (jumpIndex j) ≤ (j + 2) * finalSeq (jumpIndex j) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [show (j + 2) * (2 * finalSeq (perturbationIndex j)) =
      2 * ((j + 2) * finalSeq (perturbationIndex j)) by ring] at hmul
  omega

lemma final_liminf_and_limsup :
    liminf (fun n => finalSeq (n + 1) / (finalSeq n : ℝ)) atTop = 1 ∧
    limsup (fun n => finalSeq (n + 1) / (finalSeq n : ENNReal)) atTop = ⊤ := by
  have h1 : ∀ j, finalSeq (perturbationIndex j + 1) = finalSeq (perturbationIndex j) + 1 :=
    fun j => finalSeq_on_run j 1 (by omega)
  constructor
  · let f : ℕ → ℝ := fun n => finalSeq (n + 1) / (finalSeq n : ℝ)
    have hf_ge : ∀ n, 1 ≤ f n := by
      intro n
      dsimp [f]
      have hp : (0 : ℝ) < finalSeq n := by exact_mod_cast finalSeq_pos n
      have hm : (finalSeq n : ℝ) ≤ finalSeq (n + 1) := by
        exact_mod_cast (finalSeq_strictMono (Nat.lt_succ_self n)).le
      exact (one_le_div hp).mpr hm
    rw [Filter.liminf_eq]
    apply le_antisymm
    · refine csSup_le ⟨1, Filter.eventually_atTop.mpr ⟨0, fun n _ => hf_ge n⟩⟩ ?_
      intro a ha
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ha
      by_contra hnot
      have ha1 : 0 < a - 1 := by linarith
      obtain ⟨M, hM⟩ := exists_nat_gt (1 / (a - 1))
      let j := max N M
      have hKjN : N ≤ perturbationIndex j :=
        (le_max_left N M).trans (perturbationIndex_strictMono.id_le j)
      have hle : a ≤ f (perturbationIndex j) := hN (perturbationIndex j) hKjN
      have hAK : (M : ℝ) < finalSeq (perturbationIndex j) := by
        have hnat : M < finalSeq (perturbationIndex j) := by
          have h1' : M ≤ j := le_max_right N M
          have h2' : j ≤ perturbationIndex j := perturbationIndex_strictMono.id_le j
          have h3' := finalSeq_ge_succ (perturbationIndex j)
          omega
        exact_mod_cast hnat
      have hp0 : (0 : ℝ) < finalSeq (perturbationIndex j) := by
        exact_mod_cast finalSeq_pos (perturbationIndex j)
      have hfKj : f (perturbationIndex j) = 1 + 1 / (finalSeq (perturbationIndex j) : ℝ) := by
        dsimp [f]
        rw [h1 j]
        push_cast
        field_simp [hp0.ne']
      have hmul1 : 1 < (M : ℝ) * (a - 1) := (div_lt_iff₀ ha1).mp hM
      have hmul2 : (M : ℝ) * (a - 1) < finalSeq (perturbationIndex j) * (a - 1) :=
        mul_lt_mul_of_pos_right hAK ha1
      have hdiv : 1 / (finalSeq (perturbationIndex j) : ℝ) < a - 1 :=
        (div_lt_iff₀ hp0).mpr (by linarith)
      linarith
    · refine le_csSup ?_ (Filter.eventually_atTop.mpr ⟨0, fun n _ => hf_ge n⟩)
      refine ⟨2, fun a ha => ?_⟩
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ha
      have hKjN : N ≤ perturbationIndex N := perturbationIndex_strictMono.id_le N
      have hle : a ≤ f (perturbationIndex N) := hN (perturbationIndex N) hKjN
      have hp1 : (1 : ℝ) ≤ finalSeq (perturbationIndex N) := by
        exact_mod_cast finalSeq_pos (perturbationIndex N)
      have hp0 : (0 : ℝ) < finalSeq (perturbationIndex N) := by linarith
      have hf2 : f (perturbationIndex N) ≤ 2 := by
        dsimp [f]
        rw [h1 N, div_le_iff₀ hp0]
        push_cast
        linarith
      linarith
  · let g : ℕ → ENNReal := fun n => finalSeq (n + 1) / (finalSeq n : ENNReal)
    rw [Filter.limsup_eq, eq_top_iff]
    refine le_sInf fun a ha => ?_
    rw [top_le_iff]
    by_contra hne
    obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt hne
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ha
    let j := max N (2 * M)
    have hK'N : N ≤ jumpIndex j := (le_max_left N (2 * M)).trans (jumpIndex_strictMono.id_le j)
    have hle : g (jumpIndex j) ≤ a := hN (jumpIndex j) hK'N
    have hAn0 : (finalSeq (jumpIndex j) : ENNReal) ≠ 0 :=
      Nat.cast_ne_zero.mpr (finalSeq_pos (jumpIndex j)).ne'
    have hAntop : (finalSeq (jumpIndex j) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hgeM : (M : ENNReal) ≤ g (jumpIndex j) := by
      dsimp [g]
      rw [ENNReal.le_div_iff_mul_le (Or.inl hAn0) (Or.inl hAntop)]
      have hnat : M * finalSeq (jumpIndex j) ≤ finalSeq (jumpIndex j + 1) := by
        have hstep := jump_ratio_bound j
        have hjM : 2 * M ≤ j := le_max_right N (2 * M)
        have hmul : (2 * M) * finalSeq (jumpIndex j) ≤ (j + 1) * finalSeq (jumpIndex j) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.mul_assoc] at hmul
        omega
      exact_mod_cast hnat
    exact not_lt_of_ge (hgeM.trans hle) hM

end OMA.Erdos346Example

theorem OMA.solution : type_of% @Erdos346.erdos_346.variants.example :=
  ⟨OMA.Erdos346Example.finalSeq,
   OMA.Erdos346Example.finalSeq_strictMono,
   OMA.Erdos346Example.final_isAddStronglyCompleteNatSeq,
   fun _ hB hB' => OMA.Erdos346Example.final_infinite_diff_not_complete hB hB',
   OMA.Erdos346Example.final_liminf_and_limsup.1,
   OMA.Erdos346Example.final_liminf_and_limsup.2⟩
