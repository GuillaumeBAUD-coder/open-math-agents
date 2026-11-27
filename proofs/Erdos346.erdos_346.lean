import FormalConjectures.ErdosProblems.«346»

/-!
# Counterexample to Erdos Problem 346

We construct a strictly increasing sequence of positive integers with successive ratios bounded
below by 6/5 that remains additively complete after deleting any finite set of terms, becomes
incomplete after deleting any infinite set of terms, and has infinitely many ratios at least 17/10,
so its successive ratios do not converge to the golden ratio.
-/

namespace OMA.Erdos346Proof

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

/-- Tail-recursive state `(a (r + 3), a 0 + ... + a (r + 2))`. -/
def generatedState (b : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (5, 6)
  | r + 1 =>
      let s := generatedState b r
      (s.2 + b (r + 3), s.2 + s.1)

/-- Sequence generated from perturbation schedule `b`. -/
def generated (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | r + 3 => (generatedState b r).1

@[simp] lemma generated_zero (b : ℕ → ℕ) : generated b 0 = 1 := rfl
@[simp] lemma generated_one (b : ℕ → ℕ) : generated b 1 = 2 := rfl
@[simp] lemma generated_two (b : ℕ → ℕ) : generated b 2 = 3 := rfl
@[simp] lemma generated_three (b : ℕ → ℕ) : generated b 3 = 5 := rfl

@[simp] lemma generated_add_three (b : ℕ → ℕ) (r : ℕ) :
    generated b (r + 3) = (generatedState b r).1 := rfl

lemma generatedState_snd (b : ℕ → ℕ) (r : ℕ) :
    (generatedState b r).2 = ∑ i ∈ Finset.range (r + 3), generated b i := by
  induction r with
  | zero => norm_num [generatedState, generated, Finset.sum_range_succ]
  | succ r ih =>
      rw [generatedState, Finset.sum_range_succ, ih]
      rfl

lemma generated_recurrence (b : ℕ → ℕ) {n : ℕ} (hn : 3 ≤ n) :
    generated b (n + 1) = (∑ i ∈ Finset.range n, generated b i) + b n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 3 r, show r + 3 + 1 = (r + 1) + 3 by omega, generated_add_three,
    generatedState, generatedState_snd]

lemma generatedState_lower (b : ℕ → ℕ) (r : ℕ) :
    5 ≤ (generatedState b r).1 ∧ 6 ≤ (generatedState b r).2 := by
  induction r with
  | zero => norm_num [generatedState]
  | succ r ih =>
      simp only [generatedState]
      omega

lemma generated_pos (b : ℕ → ℕ) (n : ℕ) : 0 < generated b n := by
  rcases n with _ | _ | _ | r
  · norm_num [generated]
  · norm_num [generated]
  · norm_num [generated]
  · have h := (generatedState_lower b r).1
    rw [generated_add_three]
    omega

lemma generated_ge_four (b : ℕ → ℕ) {n : ℕ} (hn : 3 ≤ n) : 4 ≤ generated b n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := (generatedState_lower b r).1
  rw [Nat.add_comm 3 r, generated_add_three]
  omega

/-- Prefix sum `a 0 + ... + a (n - 1)`. -/
def prefixSum (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, a i

@[simp] lemma prefixSum_zero (a : ℕ → ℕ) : prefixSum a 0 = 0 := by simp [prefixSum]

lemma prefixSum_succ (a : ℕ → ℕ) (n : ℕ) :
    prefixSum a (n + 1) = prefixSum a n + a n := by
  simp [prefixSum, Finset.sum_range_succ]

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

/- Permanent interval propagation across admissible perturbations -/

lemma interval_certificate_propagates
    (a b : ℕ → ℕ) {m N u L : ℕ}
    (hmN : m ≤ N)
    (ha_mono : Monotone a)
    (hrec : ∀ n, N ≤ n → a (n + 1) = prefixSum a n + b n)
    (hadm : ∀ n, N ≤ n → 4 * b n ≤ a n)
    (hinterval : ∀ t, u ≤ t → t ≤ u + L → t ∈ idxSums a (Set.Icc m N))
    (hlock : 4 * prefixSum a (N + 1) ≤ 4 * (L + 1) + 3 * a N) :
    ∀ q t, u ≤ t → t ≤ u + L + tailBlockSum a N q →
      t ∈ idxSums a (Set.Icc m (N + q)) := by
  intro q
  induction q with
  | zero =>
      intro t hut htu
      simpa using hinterval t hut htu
  | succ q ih =>
      intro t hut htu
      have hNn : N ≤ N + q := Nat.le_add_right N q
      have haN_le : a N ≤ a (N + q) := ha_mono hNn
      have hbn : 4 * b (N + q) ≤ a (N + q) := hadm (N + q) hNn
      have hpref : prefixSum a (N + 1) + tailBlockSum a N q = prefixSum a (N + q) + a (N + q) := by
        rw [← prefixSum_succ, prefixSum_add_tailBlockSum]
      have hrecn : a (N + q + 1) = prefixSum a (N + q) + b (N + q) := hrec (N + q) hNn
      have hoverlap : a (N + q + 1) ≤ L + tailBlockSum a N q + 1 := by omega
      rw [tailBlockSum_succ] at htu
      by_cases hold : t ≤ u + L + tailBlockSum a N q
      · exact idxSums_mono (Set.Icc_subset_Icc_right (by omega)) (ih t hut hold)
      · have hrep := ih (t - a (N + q + 1)) (by omega) (by omega)
        have hadd := idxSums_add_new
          (a := a) (I := Set.Icc m (N + q)) (J := Set.Icc m (N + (q + 1)))
          (i := N + q + 1) (t := t - a (N + q + 1))
          (Set.Icc_subset_Icc_right (by omega))
          (by constructor <;> omega)
          (by simp only [Set.mem_Icc, not_and_or]; omega) hrep
        convert hadd using 1
        omega

lemma permanent_interval_certificate
    (a b : ℕ → ℕ) {m N u L : ℕ}
    (hmN : m ≤ N)
    (ha_pos : ∀ n, 0 < a n)
    (ha_mono : Monotone a)
    (hrec : ∀ n, N ≤ n → a (n + 1) = prefixSum a n + b n)
    (hadm : ∀ n, N ≤ n → 4 * b n ≤ a n)
    (hinterval : ∀ t, u ≤ t → t ≤ u + L → t ∈ idxSums a (Set.Icc m N))
    (hlock : 4 * prefixSum a (N + 1) ≤ 4 * (L + 1) + 3 * a N) :
    ∃ H, ∀ t, H ≤ t → t ∈ idxSums a (Set.Ici m) := by
  refine ⟨u, fun t hut => ?_⟩
  let q := t - u
  have hq : q ≤ tailBlockSum a N q := tailBlockSum_ge_length ha_pos N q
  have hrep := interval_certificate_propagates a b hmN ha_mono hrec hadm
    hinterval hlock q t hut (by omega)
  exact idxSums_mono (fun i hi => hi.1) hrep

lemma generatedState_congr {b c : ℕ → ℕ} {r : ℕ}
    (hbc : ∀ n, 3 ≤ n → n < r + 3 → b n = c n) :
    generatedState b r = generatedState c r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [generatedState, generatedState]
      have hs : generatedState b r = generatedState c r := ih fun n hn hlt => hbc n hn (by omega)
      rw [hs, hbc (r + 3) (by omega) (by omega)]

lemma generated_congr {b c : ℕ → ℕ} {N : ℕ}
    (hbc : ∀ n, 3 ≤ n → n < N → b n = c n) :
    ∀ n < N + 1, generated b n = generated c n := by
  intro n hn
  by_cases hn3 : n < 3
  · interval_cases n <;> rfl
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn3)
    rw [Nat.add_comm 3 r, generated_add_three, generated_add_three]
    exact congrArg Prod.fst (generatedState_congr fun i hi hil => hbc i hi (by omega))

lemma generated_second_order (b : ℕ → ℕ) {n : ℕ} (hn : 3 ≤ n) :
    generated b (n + 2) + b n = generated b (n + 1) + generated b n + b (n + 1) := by
  rw [generated_recurrence b hn, generated_recurrence b (show 3 ≤ n + 1 by omega),
    Finset.sum_range_succ]
  omega

lemma generated_strictMono (b : ℕ → ℕ)
    (hb : ∀ n, 3 ≤ n → 4 * b n ≤ generated b n) : StrictMono (generated b) := by
  apply strictMono_nat_of_lt_succ
  intro n
  by_cases hn : n < 4
  · interval_cases n
    · norm_num [generated]
    · norm_num [generated]
    · norm_num [generated, generatedState]
    · rw [generated_recurrence b (n := 3) (by omega)]
      have h3 : (∑ i ∈ Finset.range 3, generated b i) = 6 := by
        norm_num [generated, Finset.sum_range_succ]
      rw [h3]
      simp only [generated_three]
      omega
  · have hrec := generated_second_order b (n := n - 1) (by omega)
    have hpos := generated_pos b (n - 1)
    have hadm := hb (n - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n), show n - 1 + 2 = n + 1 by omega] at hrec
    omega

/-- Provisional sequence unperturbed from `cut` onward. -/
structure Approximation where
  b : ℕ → ℕ
  cut : ℕ
  cut_ge : 3 ≤ cut
  admissible : ∀ n, 3 ≤ n → 4 * b n ≤ generated b n
  eventualParity : ∀ n, cut ≤ n → b n = parityPerturbation n

namespace Approximation

def seq (s : Approximation) : ℕ → ℕ := generated s.b

lemma seq_pos (s : Approximation) (n : ℕ) : 0 < s.seq n := generated_pos s.b n

lemma seq_strictMono (s : Approximation) : StrictMono s.seq :=
  generated_strictMono s.b s.admissible

def initial : Approximation where
  b := parityPerturbation
  cut := 3
  cut_ge := by omega
  admissible := fun n hn =>
    (Nat.mul_le_mul_left 4 (parityPerturbation_le_one n)).trans (generated_ge_four _ hn)
  eventualParity := fun _ _ => rfl

def modifiedB (s : Approximation) (K n : ℕ) : ℕ :=
  if n < K then s.b n
  else if n = K then s.seq K / 4
  else parityPerturbation n

lemma modifiedB_before (s : Approximation) {K n : ℕ} (hn : n < K) :
    modifiedB s K n = s.b n := by simp [modifiedB, hn]

lemma modifiedB_at (s : Approximation) (K : ℕ) : modifiedB s K K = s.seq K / 4 := by
  simp [modifiedB]

lemma modifiedB_after (s : Approximation) {K n : ℕ} (hn : K < n) :
    modifiedB s K n = parityPerturbation n := by
  simp [modifiedB, Nat.not_lt_of_ge hn.le, hn.ne']

lemma generated_modifiedB_eq (s : Approximation) {K n : ℕ} (hn : n ≤ K) :
    generated (modifiedB s K) n = s.seq n :=
  generated_congr (N := K) (fun _ _ hil => modifiedB_before s hil) n (by omega)

def extend (s : Approximation) (K : ℕ) (hK : s.cut ≤ K) : Approximation where
  b := modifiedB s K
  cut := K + 1
  cut_ge := s.cut_ge.trans (hK.trans (Nat.le_add_right K 1))
  admissible := by
    intro n hn
    rcases lt_trichotomy n K with hlt | rfl | hgt
    · rw [modifiedB_before s hlt, generated_modifiedB_eq s hlt.le]
      exact s.admissible n hn
    · rw [modifiedB_at, generated_modifiedB_eq s (le_refl n), seq]
      exact Nat.mul_div_le (generated s.b n) 4
    · rw [modifiedB_after s hgt]
      exact (Nat.mul_le_mul_left 4 (parityPerturbation_le_one n)).trans (generated_ge_four _ hn)
  eventualParity := fun n hn => modifiedB_after s (by omega)

lemma extend_seq_eq (s : Approximation) (K : ℕ) (hK : s.cut ≤ K) {n : ℕ}
    (hn : n ≤ K) : (s.extend K hK).seq n = s.seq n :=
  generated_modifiedB_eq s hn

end Approximation

/- Graham bounded-gap descent on unperturbed tails -/

lemma Approximation.graham_recurrence (s : Approximation) {n : ℕ} (hn : s.cut ≤ n) :
    (s.seq (n + 2) : ℤ) = s.seq (n + 1) + s.seq n - (-1 : ℤ) ^ n := by
  have hnat := generated_second_order s.b (s.cut_ge.trans hn)
  have hbn := s.eventualParity n hn
  have hbn1 := s.eventualParity (n + 1) (by omega)
  have hcast : (s.seq (n + 2) : ℤ) + s.b n = s.seq (n + 1) + s.seq n + s.b (n + 1) := by
    exact_mod_cast hnat
  rw [hbn, hbn1] at hcast
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

lemma strictMono_nat_lower {a : ℕ → ℕ} (ha : StrictMono a) (ha0 : 0 < a 0) (n : ℕ) :
    n + 1 ≤ a n := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hstep : a n < a (n + 1) := ha (Nat.lt_succ_self n)
      omega

lemma Approximation.eventually_lower_neighborhood (s : Approximation) (m R : ℕ) :
    ∃ H, ∀ n, H ≤ n → ∀ t, t ≤ R → s.seq n - t ∈ idxSums s.seq (Set.Ici m) := by
  let l := max s.cut m + R + 1
  let X := s.seq (2 * l + 2)
  let E := l + 2 + X
  have hKL : s.cut ≤ 2 * l + 1 := by dsimp [l]; omega
  have hmL : m ≤ 2 * l + 1 := by dsimp [l]; omega
  have hX : R < X := by
    have hlower := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) (2 * l + 2)
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
    have hlower := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) L
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
  have hrec := generated_recurrence s.b (s.cut_ge.trans hcut)
  change s.seq (r + 1) = prefixSum s.seq r + s.b r at hrec
  have hble : s.b r ≤ 1 := s.eventualParity r hcut ▸ parityPerturbation_le_one r
  have har := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) r
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
  have hlower := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) (R + n)
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
  have hprev := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) (r - 1)
  have hlower := s.graham_lower_step hcutPrev
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r), show r - 1 + 2 = r + 1 by omega] at hlower
  have hupper := s.graham_upper_step hcut
  have hpref := prefixSum_add_blockTotal s.seq (m := m) (r := r) (by omega)
  have hgen := generated_recurrence s.b (n := r + 1) (s.cut_ge.trans (by omega))
  change s.seq (r + 2) = prefixSum s.seq (r + 1) + s.b (r + 1) at hgen
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
    have hrlower := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) r
    have hHT : H + w ≤ T := by dsimp [R] at hRr; omega
    have hxw : w + 1 ≤ s.seq (r + 1) := by
      have := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) (r + 1)
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
      have hble : s.b (r + 1) ≤ 1 := s.eventualParity (r + 1) hcut ▸ parityPerturbation_le_one _
      have hgen := generated_recurrence s.b (n := r + 1) (s.cut_ge.trans hcut)
      change s.seq (r + 2) = prefixSum s.seq (r + 1) + s.b (r + 1) at hgen
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
  have hlower := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) (R + q + 4)
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

/- Permanent certificate extraction via pure integer bounds -/

structure PermanentCertificate (s : Approximation) (m : ℕ) where
  N : ℕ
  u : ℕ
  L : ℕ
  start_le : m ≤ N
  three_le : 3 ≤ N
  interval : ∀ t, u ≤ t → t ≤ u + L → t ∈ idxSums s.seq (Set.Icc m N)
  lock : 4 * prefixSum s.seq (N + 1) ≤ 4 * (L + 1) + 3 * s.seq N

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
  -- Elementary bound: prefixSum s.seq (N + 1) < 2 * s.seq (N + 1)
  have hgen2 := generated_recurrence s.b (n := N + 1) (s.cut_ge.trans (by omega))
  change s.seq (N + 2) = prefixSum s.seq (N + 1) + s.b (N + 1) at hgen2
  have hupper := s.graham_upper_step hcutN
  have hlowPrev := s.graham_lower_step (n := N - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ N), show N - 1 + 2 = N + 1 by omega] at hlowPrev
  have hge4 := generated_ge_four s.b (n := N - 1) (by have := s.cut_ge; omega)
  change 4 ≤ s.seq (N - 1) at hge4
  have hTlt : T < 2 * s.seq (N + 1) := by omega
  have hlast : s.seq N ≤ T := blockTotal_ge_last s.seq hmN
  have hNlarge := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) N
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
  refine ⟨⟨N, H, L, hmN, s.cut_ge.trans hcutN, ?_, ?_⟩⟩
  · intro t htH htu
    have htmem : t ∈ idxSums s.seq (Set.Ico m (N + 1)) := by
      by_cases hta : t ≤ s.seq (N + 1) - 1
      · exact hfirst t htH hta
      · exact hsecond t (by omega) (by omega)
    rwa [hsets] at htmem
  · omega

noncomputable def Approximation.certificate (s : Approximation) (m : ℕ) :
    PermanentCertificate s m := Classical.choice (s.certificate_nonempty m)

/- Stagewise diagonal construction with explicit perturbation indices -/

noncomputable def stageStep (j : ℕ) (s : Approximation) : Approximation × ℕ :=
  let cert := s.certificate j
  let K := max s.cut cert.N + j + 70
  (s.extend K (by dsimp [K]; omega), K)

noncomputable def stages : ℕ → Approximation
  | 0 => Approximation.initial
  | j + 1 => (stageStep j (stages j)).1

noncomputable def perturbationIndex (j : ℕ) : ℕ :=
  max (stages j).cut ((stages j).certificate j).N + j + 70

lemma stages_succ (j : ℕ) :
    stages (j + 1) = (stages j).extend (perturbationIndex j)
      (by dsimp [perturbationIndex]; omega) := rfl

lemma stages_cut_succ (j : ℕ) : (stages (j + 1)).cut = perturbationIndex j + 1 := rfl

lemma stages_seq_succ_eq (j : ℕ) {n : ℕ} (hn : n ≤ perturbationIndex j) :
    (stages (j + 1)).seq n = (stages j).seq n :=
  Approximation.extend_seq_eq (stages j) (perturbationIndex j)
    (by dsimp [perturbationIndex]; omega) hn

lemma perturbationIndex_strictMono : StrictMono perturbationIndex := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hcut : (stages (j + 1)).cut ≤ perturbationIndex (j + 1) := by
    dsimp [perturbationIndex]; omega
  rw [stages_cut_succ] at hcut
  omega

lemma stages_cut_mono : Monotone (fun j => (stages j).cut) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [stages_cut_succ]
  dsimp [perturbationIndex]
  omega

lemma stages_cut_ge_index (j : ℕ) : j + 3 ≤ (stages j).cut := by
  induction j with
  | zero => decide
  | succ j ih =>
      rw [stages_cut_succ]
      dsimp [perturbationIndex]
      omega

lemma stages_b_succ_eq (j : ℕ) {n : ℕ} (hn : n < (stages j).cut) :
    (stages (j + 1)).b n = (stages j).b n := by
  rw [stages_succ]
  apply Approximation.modifiedB_before
  dsimp [perturbationIndex]
  omega

lemma stages_b_stable {j k n : ℕ} (hjk : j ≤ k) (hn : n < (stages j).cut) :
    (stages k).b n = (stages j).b n := by
  induction k with
  | zero =>
      obtain rfl : j = 0 := by omega
      rfl
  | succ k ih =>
      by_cases hj : j = k + 1
      · subst hj; rfl
      · have hjk' : j ≤ k := by omega
        rw [stages_b_succ_eq k (hn.trans_le (stages_cut_mono hjk')), ih hjk']

noncomputable def finalB (n : ℕ) : ℕ := (stages (n + 1)).b n

noncomputable def finalSeq : ℕ → ℕ := generated finalB

lemma finalB_eq_stage {j n : ℕ} (hn : n < (stages j).cut) : finalB n = (stages j).b n := by
  by_cases hj : j ≤ n + 1
  · exact stages_b_stable hj hn
  · have hncut : n < (stages (n + 1)).cut := by have := stages_cut_ge_index (n + 1); omega
    exact (stages_b_stable (by omega) hncut).symm

lemma finalSeq_eq_stage {j n : ℕ} (hn : n < (stages j).cut) :
    finalSeq n = (stages j).seq n :=
  generated_congr (N := n) (fun _ _ hin => finalB_eq_stage (hin.trans hn)) n (by omega)

lemma finalSeq_eq_at_perturbation (j : ℕ) {n : ℕ} (hn : n ≤ perturbationIndex j) :
    finalSeq n = (stages j).seq n :=
  (finalSeq_eq_stage (j := j + 1) (by rw [stages_cut_succ]; omega)).trans
    (stages_seq_succ_eq j hn)

lemma final_admissible (n : ℕ) (hn : 3 ≤ n) : 4 * finalB n ≤ finalSeq n := by
  have hncut : n < (stages (n + 1)).cut := by have := stages_cut_ge_index (n + 1); omega
  rw [finalB, finalSeq_eq_stage hncut]
  exact (stages (n + 1)).admissible n hn

lemma finalSeq_pos (n : ℕ) : 0 < finalSeq n := generated_pos finalB n

lemma finalSeq_strictMono : StrictMono finalSeq := generated_strictMono finalB final_admissible

/- Verification of the four Erdos 346 properties for finalSeq -/

lemma final_isAddStronglyCompleteNatSeq : IsAddStronglyCompleteNatSeq finalSeq := by
  intro m
  let cert := (stages m).certificate m
  have hNle : cert.N ≤ perturbationIndex m := by dsimp [perturbationIndex, cert]; omega
  have heq : ∀ i, i ∈ Set.Icc m cert.N → finalSeq i = (stages m).seq i :=
    fun i hi => finalSeq_eq_at_perturbation m (hi.2.trans hNle)
  have hinterval : ∀ t, cert.u ≤ t → t ≤ cert.u + cert.L →
      t ∈ idxSums finalSeq (Set.Icc m cert.N) := by
    intro t htu hut
    rw [idxSums_congr_on heq]
    exact cert.interval t htu hut
  have hpref : prefixSum finalSeq (cert.N + 1) = prefixSum (stages m).seq (cert.N + 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiLt : i < cert.N + 1 := Finset.mem_range.mp hi
    exact finalSeq_eq_at_perturbation m (by omega)
  have hseqN : finalSeq cert.N = (stages m).seq cert.N := finalSeq_eq_at_perturbation m hNle
  obtain ⟨H, htail⟩ := permanent_interval_certificate finalSeq finalB cert.start_le finalSeq_pos
    finalSeq_strictMono.monotone
    (fun n hn => generated_recurrence finalB (cert.three_le.trans hn))
    (fun n hn => final_admissible n (cert.three_le.trans hn))
    hinterval (by rw [hpref, hseqN]; exact cert.lock)
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
  · rw [Finset.sum_image (fun i _ j _ hij => finalSeq_strictMono.injective hij), hsum]

lemma final_infinite_diff_not_complete {B : Set ℕ} (hB : B ⊆ Set.range finalSeq) (hB' : B.Infinite) :
    ¬ IsAddComplete (Set.range finalSeq \ B) := by
  refine not_isAddComplete_range_diff_of_sum_range_le (n₀ := 3)
    (fun i j hij => finalSeq_strictMono (by omega)) (fun m hm => ?_) hB hB'
  have hrec := generated_recurrence finalB hm
  change finalSeq (m + 1) = (∑ i ∈ Finset.range m, finalSeq i) + finalB m at hrec
  omega

lemma final_growth_nat {n : ℕ} (hn5 : 5 ≤ n) : 6 * finalSeq n ≤ 5 * finalSeq (n + 1) := by
  have hrec0 := generated_second_order finalB (n := n - 2) (by omega)
  have hrec1 := generated_second_order finalB (n := n - 1) (by omega)
  rw [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] at hrec0
  rw [show n - 1 + 2 = n + 1 by omega, Nat.sub_add_cancel (by omega : 1 ≤ n)] at hrec1
  change finalSeq n + finalB (n - 2) =
    finalSeq (n - 1) + finalSeq (n - 2) + finalB (n - 1) at hrec0
  change finalSeq (n + 1) + finalB (n - 1) =
    finalSeq n + finalSeq (n - 1) + finalB n at hrec1
  have hmono := finalSeq_strictMono (show n - 2 < n - 1 by omega)
  have hadmPrev := final_admissible (n - 1) (by omega)
  omega

lemma final_isLacunary : IsLacunary finalSeq := by
  refine ⟨11 / 10, by norm_num, Filter.eventually_atTop.mpr ⟨5, fun n hn => ?_⟩⟩
  have hg := final_growth_nat hn
  have hp := finalSeq_pos n
  have hstrict : 11 * finalSeq n < 10 * finalSeq (n + 1) := by omega
  have hR : (11 : ℝ) * finalSeq n < 10 * finalSeq (n + 1) := by exact_mod_cast hstrict
  linarith

lemma finalB_at_perturbation (j : ℕ) :
    finalB (perturbationIndex j) = finalSeq (perturbationIndex j) / 4 := by
  calc
    finalB (perturbationIndex j) = (stages (j + 1)).b (perturbationIndex j) :=
      finalB_eq_stage (by rw [stages_cut_succ]; omega)
    _ = (stages j).seq (perturbationIndex j) / 4 := by
      rw [stages_succ]
      exact Approximation.modifiedB_at _ _
    _ = finalSeq (perturbationIndex j) / 4 := by
      rw [finalSeq_eq_at_perturbation j (le_refl _)]

lemma perturbation_jump_nat (j : ℕ) :
    17 * finalSeq (perturbationIndex j) ≤ 10 * finalSeq (perturbationIndex j + 1) := by
  let s := stages j
  let K := perturbationIndex j
  have hcut4 : s.cut + 4 ≤ K := by dsimp [K, s, perturbationIndex]; omega
  have hK70 : 70 ≤ K := by dsimp [K, perturbationIndex]; omega
  have hK3 : 3 ≤ K := by have := s.cut_ge; omega
  -- Relate finalSeq at K - 2, K - 1, K, K + 1 to stage j
  have heqK : finalSeq K = s.seq K := finalSeq_eq_at_perturbation j (le_refl _)
  have heqK1 : finalSeq (K - 1) = s.seq (K - 1) :=
    finalSeq_eq_at_perturbation j (Nat.sub_le _ _)
  have hprefEq : prefixSum finalSeq K = prefixSum s.seq K :=
    Finset.sum_congr rfl fun i hi =>
      finalSeq_eq_at_perturbation j (Finset.mem_range.mp hi).le
  have hrecNext : finalSeq (K + 1) = prefixSum s.seq K + s.seq K / 4 := by
    have hr := generated_recurrence finalB hK3
    change finalSeq (K + 1) = prefixSum finalSeq K + finalB K at hr
    rw [hr, hprefEq, finalB_at_perturbation, heqK]
  -- Unperturbed bounds at K - 2 and K - 1
  have hrecK : s.seq K = prefixSum s.seq (K - 1) + s.b (K - 1) := by
    have hr := generated_recurrence s.b (n := K - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ K)] at hr
    exact hr
  have hbK1 : s.b (K - 1) ≤ 1 :=
    s.eventualParity (K - 1) (by omega) ▸ parityPerturbation_le_one _
  have hps : prefixSum s.seq K = prefixSum s.seq (K - 1) + s.seq (K - 1) := by
    have hp := prefixSum_succ s.seq (K - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ K)] at hp
  have hupK : s.seq K ≤ s.seq (K - 1) + s.seq (K - 2) + 1 := by
    have hu := s.graham_upper_step (n := K - 2) (by omega)
    rwa [show K - 2 + 2 = K by omega, show K - 2 + 1 = K - 1 by omega] at hu
  have hmono : s.seq (K - 2) + 1 ≤ s.seq (K - 1) :=
    s.seq_strictMono (show K - 2 < K - 1 by omega)
  have hKlarge : 70 ≤ s.seq K := by
    have hl := strictMono_nat_lower s.seq_strictMono (s.seq_pos 0) K
    omega
  have hdiv : s.seq K < 4 * (s.seq K / 4) + 4 := by
    have hm := Nat.mod_lt (s.seq K) (by omega : 0 < 4)
    have hd := Nat.mod_add_div (s.seq K) 4
    omega
  rw [heqK, hrecNext]
  omega

lemma final_not_tendsto_goldenRatio :
    ¬ Tendsto (fun n => (finalSeq (n + 1) : ℝ) / (finalSeq n : ℝ))
      atTop (𝓝 ((1 + √5) / 2)) := by
  intro hTendsto
  have h12 : √((12 / 5 : ℝ) ^ 2) = 12 / 5 := Real.sqrt_sq (by norm_num)
  have hs5 : √(5 : ℝ) < 12 / 5 := by
    rw [← h12]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hlt17 : (1 + √5) / 2 < (17 : ℝ) / 10 := by linarith
  have hsub : Tendsto (fun j => (finalSeq (perturbationIndex j + 1) : ℝ) /
      (finalSeq (perturbationIndex j) : ℝ)) atTop (𝓝 ((1 + √5) / 2)) :=
    hTendsto.comp perturbationIndex_strictMono.tendsto_atTop
  have hev := Filter.eventually_atTop.mp (hsub.eventually_lt_const hlt17)
  obtain ⟨j, hj⟩ := hev
  have hlt := hj j (le_refl j)
  have hjump := perturbation_jump_nat j
  have hjumpR : (17 : ℝ) * finalSeq (perturbationIndex j) ≤
      10 * finalSeq (perturbationIndex j + 1) := by exact_mod_cast hjump
  have hpos : (0 : ℝ) < finalSeq (perturbationIndex j) := by
    exact_mod_cast finalSeq_pos (perturbationIndex j)
  have hge17 : (17 : ℝ) / 10 ≤
      (finalSeq (perturbationIndex j + 1) : ℝ) / finalSeq (perturbationIndex j) := by
    rw [div_le_div_iff₀ (by norm_num) hpos]
    linarith
  linarith

end OMA.Erdos346Proof

theorem OMA.solution : type_of% @Erdos346.erdos_346 := by
  intro hAll
  exact OMA.Erdos346Proof.final_not_tendsto_goldenRatio
    (hAll OMA.Erdos346Proof.final_isLacunary
      OMA.Erdos346Proof.final_isAddStronglyCompleteNatSeq
      fun B hB hB' => OMA.Erdos346Proof.final_infinite_diff_not_complete hB hB')
