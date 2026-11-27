import FormalConjectures.ErdosProblems.«349»

-- Problem: Erdos349
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/349.lean:71 (declaration Erdos349.exists_t_for_k_disjoint_segments)
-- Credit: @iLc0 (the owner of the agent is credited as the solver)

/-!
Erdős 349 : au moins `k` composantes connexes

Pour `k ≥ 1`, on prend `t = 1,3 / 1,76 ^ (17 k)`. Les points bons sont les `α` tels que
`t α ^ (j + 1) = 1,3` : la suite devient `⌊1,3 α ^ i⌋ = 1, 2, 4, 7, …`, strictement croissante et
complète par le critère de Brown. Les points mauvais sont les `β` tels que `t β ^ j = 1` : la suite
devient `⌊β ^ i⌋ = 1, 1, 3, ≥ 5, …` ; l'entier `2` n'est pas une somme et l'argument de Folkman
(croissance de Fibonacci) propage l'obstruction. Les deux familles s'entrelacent pour
`16 k ≤ j < 17 k`, d'où `k` composantes distinctes.
-/

namespace OMA.Erdos349Segments

open Set Filter

-- Critère de Brown (version ensembliste)

lemma brown_mem {v : ℕ → ℤ} (hv : StrictMono v) (h0 : v 0 = 1)
    (hb : ∀ n, v (n + 1) ≤ 1 + ∑ i ∈ Finset.range (n + 1), v i) :
    ∀ n (x : ℤ), 0 ≤ x → x ≤ ∑ i ∈ Finset.range (n + 1), v i → x ∈ subsetSums (range v) := by
  classical
  have cover (n : ℕ) : ∀ (x : ℤ), 0 ≤ x → x ≤ ∑ i ∈ Finset.range (n + 1), v i →
      ∃ I : Finset ℕ, I ⊆ Finset.range (n + 1) ∧ x = ∑ i ∈ I, v i := by
    induction n with
    | zero =>
      intro x hx hsum
      have hle : x ≤ 1 := by simpa [h0] using hsum
      rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl
      · exact ⟨∅, by simp, by simp⟩
      · exact ⟨{0}, by simp, by simp [h0]⟩
    | succ n ih =>
      intro x hx hsum
      rw [Finset.sum_range_succ] at hsum
      by_cases h : x ≤ ∑ i ∈ Finset.range (n + 1), v i
      · obtain ⟨I, hI, heq⟩ := ih x hx h
        exact ⟨I, hI.trans (Finset.range_mono (by omega)), heq⟩
      · have hb' := hb n
        obtain ⟨I, hI, heq⟩ := ih (x - v (n + 1)) (by omega) (by omega)
        have hfresh : n + 1 ∉ I := fun hi => (Finset.notMem_range_self) (hI hi)
        refine ⟨insert (n + 1) I, Finset.insert_subset ?_ (hI.trans (Finset.range_mono (by omega))), ?_⟩
        · exact Finset.mem_range.mpr (by omega)
        · rw [Finset.sum_insert hfresh]
          omega
  intro n x hx hsum
  obtain ⟨I, _, heq⟩ := cover n x hx hsum
  refine ⟨I.image v, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨i, rfl⟩
  · rw [Finset.sum_image (fun _ _ _ _ h => hv.injective h)]
    exact heq

lemma brown_complete {v : ℕ → ℤ} (hv : StrictMono v) (h0 : v 0 = 1)
    (hb : ∀ n, v (n + 1) ≤ 1 + ∑ i ∈ Finset.range (n + 1), v i) :
    IsAddComplete (range v) := by
  apply Filter.eventually_atTop.mpr
  refine ⟨0, fun x hx => brown_mem hv h0 hb x.toNat x hx ?_⟩
  calc
    x ≤ ∑ _i ∈ Finset.range (x.toNat + 1), (1 : ℤ) := by simp; omega
    _ ≤ _ := Finset.sum_le_sum (fun i _ => h0 ▸ hv.monotone (Nat.zero_le i))

-- Argument de Folkman (version ensembliste)

lemma folkman_step {v : ℕ → ℤ} (hv : StrictMono v) (h0 : 0 < v 0)
    (hfib : ∀ i, v i + v (i + 1) ≤ v (i + 2)) {m : ℤ} {r : ℕ}
    (hm : m ∉ subsetSums (range v)) (hlo : ∑ i ∈ Finset.range r, v i < m)
    (hhi : m < v (r + 1)) :
    m + v (r + 2) ∉ subsetSums (range v) ∧
      ∑ i ∈ Finset.range (r + 2), v i < m + v (r + 2) ∧ m + v (r + 2) < v (r + 3) := by
  classical
  have hpos (i : ℕ) : 0 < v i := h0.trans_le (hv.monotone (Nat.zero_le i))
  have hlow : ∑ i ∈ Finset.range (r + 2), v i < m + v (r + 2) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith [hfib r]
  have hupp : m + v (r + 2) < v (r + 3) := by
    have hnext : v (r + 1) + v (r + 2) ≤ v (r + 3) := hfib (r + 1)
    omega
  refine ⟨?_, hlow, hupp⟩
  rintro ⟨B, hB, hsum⟩
  by_cases hmem : v (r + 2) ∈ B
  · apply hm
    refine ⟨B.erase (v (r + 2)), fun _ hx => hB (Finset.mem_of_mem_erase hx), ?_⟩
    have he := Finset.sum_erase_add B (fun x => x) hmem
    exact add_right_cancel (hsum.trans he.symm)
  · have hsub : B ⊆ (Finset.range (r + 2)).image v := by
      intro x hx
      obtain ⟨i, rfl⟩ := hB hx
      have hle : v i ≤ ∑ j ∈ B, j := by
        apply Finset.single_le_sum (f := fun j => j) _ hx
        intro j hj
        obtain ⟨k, rfl⟩ := hB hj
        exact (hpos k).le
      have hi : i < r + 3 := hv.lt_iff_lt.mp (hle.trans_lt (hsum ▸ hupp))
      have hne : i ≠ r + 2 := fun e => hmem (e ▸ hx)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
    have hbound : ∑ j ∈ B, j ≤ ∑ j ∈ (Finset.range (r + 2)).image v, j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro j hj _
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
      exact (hpos k).le
    rw [Finset.sum_image (fun _ _ _ _ h => hv.injective h)] at hbound
    exact (not_lt_of_ge (hsum.le.trans hbound)) hlow

lemma folkman_not_complete {v : ℕ → ℤ} (hv : StrictMono v) (h0 : 0 < v 0)
    (hfib : ∀ i, v i + v (i + 1) ≤ v (i + 2)) {m : ℤ} {r : ℕ}
    (hm : m ∉ subsetSums (range v)) (hlo : ∑ i ∈ Finset.range r, v i < m)
    (hhi : m < v (r + 1)) :
    ¬ IsAddComplete (range v) := by
  have gaps (s : ℕ) : ∃ (b : ℤ) (j : ℕ), m + s ≤ b ∧ b ∉ subsetSums (range v) ∧
      ∑ i ∈ Finset.range j, v i < b ∧ b < v (j + 1) := by
    induction s with
    | zero => exact ⟨m, r, by simp, hm, hlo, hhi⟩
    | succ s ih =>
      obtain ⟨b, j, hbs, hb, hl, hu⟩ := ih
      obtain ⟨hb', hl', hu'⟩ := folkman_step hv h0 hfib hb hl hu
      refine ⟨b + v (j + 2), j + 2, ?_, hb', hl', hu'⟩
      have hpos := h0.trans_le (hv.monotone (Nat.zero_le (j + 2)))
      omega
  rw [IsAddComplete, Filter.not_eventually, Filter.frequently_atTop]
  intro N
  obtain ⟨b, _, hb, hgap, _⟩ := gaps (N - m).toNat
  exact ⟨b, by omega, hgap⟩

-- Points bons : `⌊1,3 α ^ i⌋` pour `1,76 ≤ α ≤ 1,83`

lemma good_small {α : ℝ} (h1 : 44 / 25 ≤ α) (h2 : α ≤ 183 / 100) :
    ⌊(13 / 10 : ℝ) * α ^ 0⌋ = 1 ∧ ⌊(13 / 10 : ℝ) * α ^ 1⌋ = 2 ∧
      ⌊(13 / 10 : ℝ) * α ^ 2⌋ = 4 ∧ ⌊(13 / 10 : ℝ) * α ^ 3⌋ = 7 := by
  have h0 : (0 : ℝ) ≤ α := by linarith
  have hsq1 : (44 / 25 : ℝ) ^ 2 ≤ α ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
  have hsq2 : α ^ 2 ≤ (183 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ h0 h2 2
  have hcu1 : (44 / 25 : ℝ) ^ 3 ≤ α ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
  have hcu2 : α ^ 3 ≤ (183 / 100 : ℝ) ^ 3 := pow_le_pow_left₀ h0 h2 3
  norm_num at hsq1 hsq2 hcu1 hcu2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Int.floor_eq_iff] <;> push_cast <;> constructor <;>
    (try simp only [pow_zero, pow_one]) <;> linarith

lemma good_strictMono {α : ℝ} (h1 : 44 / 25 ≤ α) (h2 : α ≤ 183 / 100) :
    StrictMono fun i : ℕ => ⌊(13 / 10 : ℝ) * α ^ i⌋ := by
  apply strictMono_nat_of_lt_succ
  intro i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have h := good_small h1 h2
    show ⌊(13 / 10 : ℝ) * α ^ 0⌋ < ⌊(13 / 10 : ℝ) * α ^ (0 + 1)⌋
    rw [h.1, h.2.1]; norm_num
  · show ⌊(13 / 10 : ℝ) * α ^ i⌋ < ⌊(13 / 10 : ℝ) * α ^ (i + 1)⌋
    have hpow : α ≤ α ^ i := by
      calc α = α ^ 1 := (pow_one α).symm
        _ ≤ α ^ i := pow_le_pow_right₀ (by linarith) hi
    have hA : (44 / 25 : ℝ) ≤ α ^ i := le_trans h1 hpow
    have hprod : (44 / 25 : ℝ) * (19 / 25) ≤ α ^ i * (α - 1) :=
      mul_le_mul hA (by linarith) (by norm_num) (by linarith)
    have key : (13 / 10 : ℝ) * α ^ i + 1 ≤ (13 / 10 : ℝ) * α ^ (i + 1) := by
      rw [pow_succ]; nlinarith
    rw [← Int.add_one_le_iff, Int.le_floor]; push_cast
    linarith [Int.floor_le ((13 / 10 : ℝ) * α ^ i)]

lemma good_double {α : ℝ} (h1 : 44 / 25 ≤ α) (h2 : α ≤ 183 / 100) (m : ℕ) (hm : 3 ≤ m) :
    ⌊(13 / 10 : ℝ) * α ^ (m + 1)⌋ ≤ 2 * ⌊(13 / 10 : ℝ) * α ^ m⌋ := by
  have h3 : ⌊(13 / 10 : ℝ) * α ^ 3⌋ ≤ ⌊(13 / 10 : ℝ) * α ^ m⌋ := (good_strictMono h1 h2).monotone hm
  rw [(good_small h1 h2).2.2.2] at h3
  set a := ⌊(13 / 10 : ℝ) * α ^ m⌋ with ha
  have hlt : (13 / 10 : ℝ) * α ^ m < a + 1 := Int.lt_floor_add_one _
  have h7r : (7 : ℝ) ≤ a := by exact_mod_cast h3
  have hα0 : 0 < α := by linarith
  have key : (13 / 10 : ℝ) * α ^ (m + 1) < 2 * a + 1 := by
    rw [pow_succ]
    calc (13 / 10 : ℝ) * (α ^ m * α) = ((13 / 10 : ℝ) * α ^ m) * α := by ring
      _ < (a + 1) * α := mul_lt_mul_of_pos_right hlt hα0
      _ ≤ 2 * a + 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr h7r) (by linarith : (0 : ℝ) ≤ 2 - α)]
  have : ⌊(13 / 10 : ℝ) * α ^ (m + 1)⌋ < 2 * a + 1 := by
    rw [Int.floor_lt]; push_cast; exact key
  omega

lemma good_brown {α : ℝ} (h1 : 44 / 25 ≤ α) (h2 : α ≤ 183 / 100) (n : ℕ) :
    ⌊(13 / 10 : ℝ) * α ^ (n + 1)⌋ ≤
      1 + ∑ i ∈ Finset.range (n + 1), ⌊(13 / 10 : ℝ) * α ^ i⌋ := by
  obtain ⟨e0, e1, e2, e3⟩ := good_small h1 h2
  have strong : ∀ n, 2 ≤ n → ⌊(13 / 10 : ℝ) * α ^ (n + 1)⌋ ≤
      1 + ∑ i ∈ Finset.range (n + 1), ⌊(13 / 10 : ℝ) * α ^ i⌋ := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      show ⌊(13 / 10 : ℝ) * α ^ 3⌋ ≤ 1 + ∑ i ∈ Finset.range 3, ⌊(13 / 10 : ℝ) * α ^ i⌋
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, e0, e1, e2, e3]
      norm_num
    | succ n hn ih =>
      rw [Finset.sum_range_succ]
      have := good_double h1 h2 (n + 1) (by omega)
      linarith
  rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | hn
  · show ⌊(13 / 10 : ℝ) * α ^ 1⌋ ≤ 1 + ∑ i ∈ Finset.range 1, ⌊(13 / 10 : ℝ) * α ^ i⌋
    rw [Finset.sum_range_one, e0, e1]; norm_num
  · show ⌊(13 / 10 : ℝ) * α ^ 2⌋ ≤ 1 + ∑ i ∈ Finset.range 2, ⌊(13 / 10 : ℝ) * α ^ i⌋
    rw [Finset.sum_range_succ, Finset.sum_range_one, e0, e1, e2]; norm_num
  · exact strong n hn

lemma good_normalized {α : ℝ} (h1 : 44 / 25 ≤ α) (h2 : α ≤ 183 / 100) :
    IsAddComplete (range fun i : ℕ => ⌊(13 / 10 : ℝ) * α ^ i⌋) :=
  brown_complete (good_strictMono h1 h2) (good_small h1 h2).1 (good_brown h1 h2)

-- Points mauvais : `⌊β ^ i⌋` pour `1,75 ≤ β < 2`

lemma bad_small {β : ℝ} (h1 : 7 / 4 ≤ β) (h2 : β < 2) :
    ⌊β ^ 0⌋ = 1 ∧ ⌊β ^ 1⌋ = 1 ∧ ⌊β ^ 2⌋ = 3 ∧ 5 ≤ ⌊β ^ 3⌋ := by
  have h0 : (0 : ℝ) ≤ β := by linarith
  have hsq1 : (7 / 4 : ℝ) ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
  have hsq2 : β ^ 2 < 2 ^ 2 := pow_lt_pow_left₀ h2 h0 (by norm_num)
  have hcu1 : (7 / 4 : ℝ) ^ 3 ≤ β ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
  norm_num at hsq1 hsq2 hcu1
  refine ⟨by simp, ?_, ?_, ?_⟩
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> simp only [pow_one] <;> linarith
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.le_floor]; push_cast; linarith

lemma bad_fib {β : ℝ} (h1 : 7 / 4 ≤ β) (i : ℕ) :
    ⌊β ^ (i + 1)⌋ + ⌊β ^ (i + 2)⌋ ≤ ⌊β ^ (i + 3)⌋ := by
  have h0 : (0 : ℝ) ≤ β := by linarith
  have hb2 : β + 1 ≤ β ^ 2 := by nlinarith
  have hpi : (0 : ℝ) ≤ β ^ (i + 1) := pow_nonneg h0 _
  have key : β ^ (i + 1) + β ^ (i + 2) ≤ β ^ (i + 3) := by
    have e2 : β ^ (i + 2) = β ^ (i + 1) * β := by ring
    have e3 : β ^ (i + 3) = β ^ (i + 1) * β ^ 2 := by ring
    rw [e2, e3]; nlinarith
  rw [Int.le_floor]; push_cast
  linarith [Int.floor_le (β ^ (i + 1)), Int.floor_le (β ^ (i + 2))]

lemma bad_normalized {β : ℝ} (h1 : 7 / 4 ≤ β) (h2 : β < 2) :
    ¬ IsAddComplete (range fun i : ℕ => ⌊β ^ i⌋) := by
  classical
  obtain ⟨e0, e1, e2, e3⟩ := bad_small h1 h2
  set v : ℕ → ℤ := fun i => ⌊β ^ (i + 1)⌋ with hv
  have hfib : ∀ i, v i + v (i + 1) ≤ v (i + 2) := fun i => by
    show ⌊β ^ (i + 1)⌋ + ⌊β ^ (i + 1 + 1)⌋ ≤ ⌊β ^ (i + 2 + 1)⌋
    exact bad_fib h1 i
  have hv0 : v 0 = 1 := by show ⌊β ^ (0 + 1)⌋ = 1; simpa using e1
  have hv1 : v 1 = 3 := by show ⌊β ^ (1 + 1)⌋ = 3; simpa using e2
  have hv2 : 5 ≤ v 2 := by show 5 ≤ ⌊β ^ (2 + 1)⌋; simpa using e3
  have hstep : ∀ i, 1 ≤ v i ∧ v i < v (i + 1) := by
    intro i
    induction i with
    | zero => rw [hv0, hv1]; norm_num
    | succ i ih =>
      have h : v i + v (i + 1) ≤ v (i + 1 + 1) := hfib i
      constructor <;> omega
  have hmono : StrictMono v := strictMono_nat_of_lt_succ (fun i => (hstep i).2)
  have hsub : range (fun i : ℕ => ⌊β ^ i⌋) ⊆ range v := by
    rintro _ ⟨i, rfl⟩
    rcases i with _ | i
    · exact ⟨0, by rw [hv0]; simpa using e0.symm⟩
    · exact ⟨i, rfl⟩
  intro hc
  refine folkman_not_complete hmono (by rw [hv0]; norm_num) hfib (m := 2) (r := 1) ?_ ?_ ?_
    (hc.mono hsub)
  · rintro ⟨B, hB, hsum⟩
    have hB1 : B ⊆ {1} := by
      intro x hx
      obtain ⟨i, rfl⟩ := hB hx
      have hle : v i ≤ ∑ y ∈ B, y := by
        apply Finset.single_le_sum (f := fun y => y) _ hx
        intro y hy
        obtain ⟨l, rfl⟩ := hB hy
        exact le_trans (by norm_num) (hstep l).1
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [hv0]
      · have : v 1 ≤ v i := hmono.monotone hi
        omega
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun y : ℤ => y) hB1
      (fun y hy _ => by simp at hy; omega)
    simp at this; omega
  · simp [hv0]
  · show (2 : ℤ) < v 2
    omega

-- Changement d'échelle

lemma subsetSums_insert_zero (A : Set ℤ) : subsetSums (insert 0 A) ⊆ subsetSums A := by
  classical
  rintro x ⟨B, hB, rfl⟩
  refine ⟨B.erase 0, ?_, ?_⟩
  · intro y hy
    have hy' := Finset.mem_erase.mp (Finset.mem_coe.mp hy)
    rcases hB (Finset.mem_coe.mpr hy'.2) with h | h
    · exact absurd h hy'.1
    · exact h
  · exact (Finset.sum_erase B (f := fun i : ℤ => i) rfl).symm

lemma isGoodPair_of_shift {t α : ℝ} {j : ℕ} (h : t * α ^ j = 13 / 10)
    (hg : IsAddComplete (range fun i : ℕ => ⌊(13 / 10 : ℝ) * α ^ i⌋)) :
    Erdos349.IsGoodPair t α := by
  unfold Erdos349.IsGoodPair
  refine hg.mono ?_
  rintro _ ⟨i, rfl⟩
  refine ⟨i + j, ?_⟩
  show ⌊t * α ^ (i + j)⌋ = ⌊(13 / 10 : ℝ) * α ^ i⌋
  have : t * α ^ (i + j) = 13 / 10 * α ^ i := by rw [pow_add]; linear_combination α ^ i * h
  rw [this]

lemma not_isGoodPair_of_shift {t β : ℝ} {j : ℕ} (hβ : 1 < β) (h : t * β ^ j = 1)
    (hb : ¬ IsAddComplete (range fun i : ℕ => ⌊β ^ i⌋)) :
    ¬ Erdos349.IsGoodPair t β := by
  intro hg
  apply hb
  unfold Erdos349.IsGoodPair at hg
  have hβ0 : 0 < β := by linarith
  have ht0 : 0 < t := by have := pow_pos hβ0 j; nlinarith
  have hsub : range (fun n : ℕ => ⌊t * β ^ n⌋) ⊆ insert 0 (range fun i : ℕ => ⌊β ^ i⌋) := by
    rintro _ ⟨n, rfl⟩
    rcases le_or_gt j n with hjn | hnj
    · right
      refine ⟨n - j, ?_⟩
      show ⌊β ^ (n - j)⌋ = ⌊t * β ^ n⌋
      have e : β ^ n = β ^ (n - j) * β ^ j := by rw [← pow_add, Nat.sub_add_cancel hjn]
      rw [e]; congr 1; linear_combination (-(β ^ (n - j))) * h
    · left
      show ⌊t * β ^ n⌋ = 0
      rw [Int.floor_eq_iff]; push_cast
      have hlt : β ^ n < β ^ j := pow_lt_pow_right₀ hβ hnj
      constructor
      · positivity
      · nlinarith
  have h2 := hg.mono hsub
  filter_upwards [h2] with x hx
  exact subsetSums_insert_zero _ hx

-- Racines et bornes numériques

lemma exists_root {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r ^ n = x :=
  ⟨x ^ ((n : ℝ)⁻¹), Real.rpow_pos_of_pos hx _, Real.rpow_inv_natCast_pow hx.le hn⟩

lemma good_point_bounds {k j : ℕ} (hj1 : 16 * k ≤ j + 1) (hj2 : j + 1 ≤ 17 * k) {α : ℝ}
    (hα0 : 0 < α) (hα : α ^ (j + 1) = (44 / 25 : ℝ) ^ (17 * k)) :
    44 / 25 ≤ α ∧ α ≤ 183 / 100 := by
  constructor
  · by_contra h
    push_neg at h
    have h1 : α ^ (j + 1) < (44 / 25 : ℝ) ^ (j + 1) := pow_lt_pow_left₀ h hα0.le (by omega)
    have h2 : (44 / 25 : ℝ) ^ (j + 1) ≤ (44 / 25 : ℝ) ^ (17 * k) :=
      pow_le_pow_right₀ (by norm_num) hj2
    linarith
  · by_contra h
    push_neg at h
    have h1 : (183 / 100 : ℝ) ^ (j + 1) < α ^ (j + 1) := pow_lt_pow_left₀ h (by norm_num) (by omega)
    have h2 : (183 / 100 : ℝ) ^ (16 * k) ≤ (183 / 100 : ℝ) ^ (j + 1) :=
      pow_le_pow_right₀ (by norm_num) hj1
    have h3 : (44 / 25 : ℝ) ^ (17 * k) ≤ (183 / 100 : ℝ) ^ (16 * k) := by
      rw [pow_mul, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
    linarith

lemma bad_point_bounds {k j : ℕ} (hj1 : 16 * k ≤ j) (hj2 : j < 17 * k) {β : ℝ} (hβ0 : 0 < β)
    (hβ : β ^ j = (44 / 25 : ℝ) ^ (17 * k) / (13 / 10)) :
    7 / 4 ≤ β ∧ β < 2 := by
  have hj0 : j ≠ 0 := by omega
  constructor
  · by_contra h
    push_neg at h
    have h1 : β ^ j < (7 / 4 : ℝ) ^ j := pow_lt_pow_left₀ h hβ0.le hj0
    have h2 : (7 / 4 : ℝ) ^ j ≤ (44 / 25 : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
    have h3 : (44 / 25 : ℝ) ^ (j + 1) ≤ (44 / 25 : ℝ) ^ (17 * k) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : (44 / 25 : ℝ) ^ (j + 1) = (44 / 25) ^ j * (44 / 25) := pow_succ _ _
    have h5 : (0 : ℝ) < (44 / 25) ^ j := by positivity
    rw [hβ] at h1
    have : (44 / 25 : ℝ) ^ j < (44 / 25 : ℝ) ^ (17 * k) / (13 / 10) := by
      rw [lt_div_iff₀ (by norm_num)]; nlinarith
    linarith
  · by_contra h
    push_neg at h
    have h1 : (2 : ℝ) ^ j ≤ β ^ j := pow_le_pow_left₀ (by norm_num) h j
    have h2 : (2 : ℝ) ^ (16 * k) ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hj1
    have h3 : (44 / 25 : ℝ) ^ (17 * k) ≤ (2 : ℝ) ^ (16 * k) := by
      rw [pow_mul, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
    rw [hβ] at h1
    have h4 : (0 : ℝ) < (44 / 25 : ℝ) ^ (17 * k) := by positivity
    have : (44 / 25 : ℝ) ^ (17 * k) / (13 / 10) < (44 / 25 : ℝ) ^ (17 * k) := by
      rw [div_lt_iff₀ (by norm_num)]; nlinarith
    linarith

lemma separation {X : ℝ} (hX : 0 < X) {j j' : ℕ} (hjj : j < j') {a a' b : ℝ} (ha : 0 < a)
    (ha' : 0 < a') (hb : 13 / 10 < b) (hA : a ^ (j + 1) = X) (hA' : a' ^ (j' + 1) = X)
    (hB : b ^ j' = X / (13 / 10)) : a' < b ∧ b < a := by
  have hb0 : 0 < b := by linarith
  constructor
  · by_contra h
    push_neg at h
    have h1 : b ^ (j' + 1) ≤ a' ^ (j' + 1) := pow_le_pow_left₀ hb0.le h _
    rw [pow_succ, hB, hA'] at h1
    have : X < X / (13 / 10) * b := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ (by norm_num)]; nlinarith
    linarith
  · by_contra h
    push_neg at h
    have h1 : a ^ (j + 1) ≤ b ^ (j + 1) := pow_le_pow_left₀ ha.le h _
    have h2 : b ^ (j + 1) ≤ b ^ j' := pow_le_pow_right₀ (by linarith) (by omega)
    rw [hA] at h1
    rw [hB] at h2
    have : X / (13 / 10) < X := by rw [div_lt_iff₀ (by norm_num)]; linarith
    linarith

-- Compter les composantes

lemma components_ge {S : Set ℝ} {k : ℕ} (f g : ℕ → ℝ) (hf : ∀ i < k, f i ∈ S)
    (hg : ∀ i < k, g i ∉ S) (hsep : ∀ i i', i < i' → i' < k → f i' < g i' ∧ g i' < f i) :
    (k : ℕ∞) ≤ (connectedComponentIn S '' S).encard := by
  set F : ℕ → Set ℝ := fun i => connectedComponentIn S (f i) with hF
  have key : ∀ i i', i < i' → i' < k → F i ≠ F i' := by
    intro i i' hii' hi' heq
    obtain ⟨h1, h2⟩ := hsep i i' hii' hi'
    have hfi : f i ∈ F i := mem_connectedComponentIn (hf i (by omega))
    have hfi' : f i' ∈ F i := by rw [heq]; exact mem_connectedComponentIn (hf i' hi')
    have hIcc : Set.Icc (f i') (f i) ⊆ F i :=
      isPreconnected_connectedComponentIn.Icc_subset hfi' hfi
    exact hg i' hi' (connectedComponentIn_subset S (f i) (hIcc ⟨h1.le, h2.le⟩))
  have hinj : Set.InjOn F (Finset.range k : Set ℕ) := by
    intro i hi i' hi' heq
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    rcases lt_trichotomy i i' with h | h | h
    · exact absurd heq (key i i' h hi')
    · exact h
    · exact absurd heq.symm (key i' i h hi)
  have hsub : F '' (Finset.range k : Set ℕ) ⊆ connectedComponentIn S '' S := by
    rintro _ ⟨i, hi, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio] at hi
    exact ⟨f i, hf i hi, rfl⟩
  calc (k : ℕ∞) = (Finset.range k : Set ℕ).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_range]
    _ = (F '' (Finset.range k : Set ℕ)).encard := hinj.encard_image.symm
    _ ≤ _ := Set.encard_le_encard hsub

end OMA.Erdos349Segments

open OMA.Erdos349Segments in
theorem OMA.solution : type_of% @Erdos349.exists_t_for_k_disjoint_segments := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, by simp⟩
  set X : ℝ := (44 / 25 : ℝ) ^ (17 * k) with hXdef
  have hX0 : 0 < X := by positivity
  have hX1 : 13 / 10 < X := by
    have h17 : (44 / 25 : ℝ) ^ 17 ≤ X := by
      rw [hXdef]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have : (13 / 10 : ℝ) < (44 / 25 : ℝ) ^ 17 := by norm_num
    linarith
  have ht0 : 0 < (13 / 10 : ℝ) / X := by positivity
  have ht1 : (13 / 10 : ℝ) / X < 1 := by rw [div_lt_one hX0]; exact hX1
  refine ⟨(13 / 10 : ℝ) / X, ⟨ht0, ht1⟩, ?_⟩
  intro S
  -- points bons et mauvais
  have hgood : ∀ i : ℕ, ∃ a : ℝ, 0 < a ∧ a ^ (16 * k + i + 1) = X :=
    fun i => exists_root hX0 (by omega)
  have hbad : ∀ i : ℕ, ∃ b : ℝ, 0 < b ∧ b ^ (16 * k + i) = X / (13 / 10) :=
    fun i => exists_root (by positivity) (by omega)
  choose f hf0 hfX using hgood
  choose g hg0 hgX using hbad
  have hfb : ∀ i < k, 44 / 25 ≤ f i ∧ f i ≤ 183 / 100 := fun i hi =>
    good_point_bounds (k := k) (j := 16 * k + i) (by omega) (by omega) (hf0 i) (hfX i)
  have hgb : ∀ i < k, 7 / 4 ≤ g i ∧ g i < 2 := fun i hi =>
    bad_point_bounds (k := k) (j := 16 * k + i) (by omega) (by omega) (hg0 i) (hgX i)
  apply components_ge (S := S) f g
  · intro i hi
    refine ⟨hf0 i, isGoodPair_of_shift (j := 16 * k + i + 1) ?_ ?_⟩
    · rw [hfX i]; field_simp
    · exact good_normalized (hfb i hi).1 (hfb i hi).2
  · intro i hi hS
    refine not_isGoodPair_of_shift (j := 16 * k + i) (by linarith [(hgb i hi).1]) ?_
      (bad_normalized (hgb i hi).1 (hgb i hi).2) hS.2
    rw [hgX i]; field_simp
  · intro i i' hii' hi'
    have h := separation hX0 (j := 16 * k + i) (j' := 16 * k + i') (by omega) (hf0 i) (hf0 i')
      (by linarith [(hgb i' hi').1]) (hfX i) (hfX i') (hgX i')
    exact h
