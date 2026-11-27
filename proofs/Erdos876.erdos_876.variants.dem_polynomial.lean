import FormalConjectures.ErdosProblems.«876»

/-! In each block use multiples of the denominator of a quadratic irrational
approximation. The signed errors are positive, comparable within a block,
and have total sum less than one. -/

open Filter Finset Real
open scoped BigOperators Topology
namespace OMA.PolynomialSumFree

private def pell (M : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1,0)
  | k+1 => let (p,q) := pell M k
           (M*p + (M^2-1)*q, p + M*q)

private noncomputable def root (M : ℕ) : ℝ := √((M:ℝ)^2-1)

private theorem embeddings (M : ℕ) (hM : 2 ≤ M) (k : ℕ) :
    let (p,q) := pell M k
    ((p:ℝ) + (q:ℝ)*root M = ((M:ℝ)+root M)^k) ∧
    ((p:ℝ) - (q:ℝ)*root M = ((M:ℝ)-root M)^k) := by
  have hMr : (2:ℝ) ≤ M := by exact_mod_cast hM
  have hn : 1 ≤ M^2 := by nlinarith
  have hroot : (root M)^2 = (M:ℝ)^2-1 := sq_sqrt (by nlinarith)
  induction k with
  | zero => simp [pell]
  | succ k ih =>
    obtain ⟨p,q,h⟩ : ∃ p q, pell M k = (p,q) := ⟨_,_,rfl⟩
    simp only [h] at ih
    simp only [pell,h,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hn,Nat.cast_pow,Nat.cast_one,
      pow_succ _ k, ← ih.1, ← ih.2]
    constructor <;> nlinarith only [congrArg (fun z : ℝ => (q:ℝ)*z) hroot]

private theorem pell_mono (M : ℕ) (hM : 1 ≤ M) : Monotone (fun k => (pell M k).2) := by
  apply monotone_nat_of_le_succ
  intro k
  obtain ⟨p,q,h⟩ : ∃ p q, pell M k = (p,q) := ⟨_,_,rfl⟩
  simp [pell,h]
  have := Nat.mul_le_mul_right q hM
  omega

private def idx (B n : ℕ) := Nat.log B (n+1)
private def mult (B n : ℕ) := B^(idx B n+1) + (n+1)
private def num (B n : ℕ) := mult B n * (pell (8*B^2) (idx B n+1)).2
private def nearInt (B n : ℕ) := mult B n * (pell (8*B^2) (idx B n+1)).1
private noncomputable def small (B : ℕ) := (8*B^2 : ℕ) - root (8*B^2)
private noncomputable def defect (B n : ℕ) : ℝ := (mult B n : ℝ)*(small B)^(idx B n+1)

private theorem idx_mono (B : ℕ) : Monotone (idx B) :=
  fun _ _ h => Nat.log_monotone (Nat.succ_le_succ h)

private theorem mult_bounds (B : ℕ) (hB : 2 ≤ B) (n : ℕ) :
    B^(idx B n+1) ≤ mult B n ∧ mult B n < 2*B^(idx B n+1) := by
  have hh := Nat.lt_pow_succ_log_self hB (n+1)
  change n+1 < B^(idx B n+1) at hh
  unfold mult
  omega

private theorem num_mono (B : ℕ) (hB : 2 ≤ B) : StrictMono (num B) := by
  have hm : Monotone (fun n => (pell (8*B^2) (idx B n+1)).2) :=
    fun _ _ h => pell_mono _ (by nlinarith) (Nat.succ_le_succ (idx_mono B h))
  have hp (n : ℕ) : 0 < (pell (8*B^2) (idx B n+1)).2 :=
    lt_of_lt_of_le (by simp [pell] : 0 < (pell (8*B^2) 1).2)
      (pell_mono _ (by nlinarith) (by omega))
  intro i j hij
  exact Nat.mul_lt_mul_of_lt_of_le
    (show mult B i < mult B j from Nat.add_lt_add_of_le_of_lt
      (Nat.pow_le_pow_right (by omega) (Nat.succ_le_succ (idx_mono B hij.le))) (by omega))
    (hm hij.le) (hp j)

private theorem defect_eq (B : ℕ) (hB : 2 ≤ B) (n : ℕ) :
    defect B n = (nearInt B n : ℝ) - (num B n : ℝ)*root (8*B^2) := by
  let M := 8*B^2
  have hh := embeddings M (by dsimp [M]; nlinarith) (idx B n+1)
  obtain ⟨p,q,h⟩ : ∃ p q, pell M (idx B n+1) = (p,q) := ⟨_,_,rfl⟩
  simp only [h] at hh
  change (mult B n : ℝ)*((M:ℝ)-root M)^(idx B n+1) = ↑(mult B n*(pell M _).1) - ↑(mult B n*(pell M _).2)*root M
  rw [← hh.2,h]
  push_cast
  ring

private theorem small_bounds (B : ℕ) (hB : 2 ≤ B) :
    0 < small B ∧ (B:ℝ)^2 * small B ≤ 1/8 := by
  let M := 8*B^2
  have hM : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast (show 2 ≤ M by dsimp [M]; nlinarith)
  have hr : (root M)^2 = (M:ℝ)^2-1 := sq_sqrt (by nlinarith)
  have hrr : 0 ≤ root M := sqrt_nonneg _
  have hpos : 0 < (M:ℝ)-root M := by nlinarith
  have h1 : ((M:ℝ)-root M)*((M:ℝ)+root M) = 1 := by nlinarith
  have hM' : (M:ℝ) = 8*(B:ℝ)^2 := by simp [M]
  change 0 < (M:ℝ)-root M ∧ _* ((M:ℝ)-root M) ≤ _
  exact ⟨hpos, by nlinarith only [h1, mul_nonneg hpos.le hrr, congrArg (fun z : ℝ => z*((M:ℝ)-root M)) hM']⟩

private theorem defect_bounds (B : ℕ) (hB : 2 ≤ B) (n : ℕ) :
    ((B:ℝ)*small B)^(idx B n+1) ≤ defect B n ∧
    defect B n < 2*((B:ℝ)*small B)^(idx B n+1) := by
  obtain ⟨lo,hi⟩ := mult_bounds B hB n
  have hp : 0 < (small B)^(idx B n+1) := pow_pos (small_bounds B hB).1 _
  rw [mul_pow]
  unfold defect
  constructor
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast lo) hp.le
  · rw [← mul_assoc]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hi) hp

private theorem defect_pos (B : ℕ) (hB : 2 ≤ B) (n : ℕ) : 0 < defect B n :=
  (pow_pos (mul_pos (by exact_mod_cast (show 0 < B by omega)) (small_bounds B hB).1) _).trans_le
    (defect_bounds B hB n).1

private theorem two_defects (B : ℕ) (hB : 2 ≤ B) {i n : ℕ} (hi : i ≤ n) :
    defect B n < 2*defect B i := by
  have hbr : (2:ℝ) ≤ B := by exact_mod_cast hB
  obtain ⟨hp,hu⟩ := small_bounds B hB
  have hcmp : (B:ℝ)*small B ≤ 1 := by
    have hh : (B:ℝ) ≤ (B:ℝ)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hh hp.le]
  exact (defect_bounds B hB n).2.trans_le (by
    gcongr
    exact (pow_le_pow_of_le_one (by positivity) hcmp (Nat.succ_le_succ (idx_mono B hi))).trans
      (defect_bounds B hB i).1)

private theorem total_defect (B : ℕ) (hB : 2 ≤ B) (T : Finset ℕ) :
    ∑ i ∈ T, defect B i < 1 := by
  classical
  have hs := small_bounds B hB
  have hsmallpos := hs.1
  have hb : 0 ≤ (B:ℝ) := Nat.cast_nonneg _
  have localBound (j : ℕ) :
      ∑ i ∈ T.filter (fun i => idx B i = j), defect B i ≤ (1/4:ℝ)*(1/2:ℝ)^j := by
    let U := T.filter (fun i => idx B i = j)
    have hU : U ⊆ range (B^(j+1)) := by
      intro i hi
      have h := Nat.lt_pow_succ_log_self hB (i+1)
      change i+1 < B^(idx B i + 1) at h
      rw [(mem_filter.mp hi).2] at h
      exact mem_range.mpr (by omega)
    have hcard : U.card ≤ B^(j+1) := by simpa using card_le_card hU
    calc
      _ ≤ ∑ _i ∈ U, 2*((B:ℝ)*small B)^(j+1) := by
        apply sum_le_sum
        intro i hi
        simpa [(mem_filter.mp hi).2] using (defect_bounds B hB i).2.le
      _ = U.card * (2*((B:ℝ)*small B)^(j+1)) := by simp
      _ ≤ (B:ℝ)^(j+1)*(2*((B:ℝ)*small B)^(j+1)) := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        positivity
      _ = 2*((B:ℝ)^2*small B)^(j+1) := by rw [mul_pow,mul_pow,← pow_mul]; ring
      _ ≤ 2*(1/8:ℝ)^(j+1) := by gcongr <;> first | positivity | exact hs.2
      _ ≤ (1/4:ℝ)*(1/2:ℝ)^j := by
        rw [pow_succ]
        have hle := pow_le_pow_left₀ (by norm_num : 0 ≤ (1/8:ℝ)) (by norm_num : (1/8:ℝ) ≤ 1/2) j
        linarith
  have hsum := sum_fiberwise_of_maps_to (g:=idx B) (s:=T) (t:=T.image (idx B))
    (fun i hi => mem_image_of_mem _ hi) (defect B)
  rw [← hsum]
  calc
    _ ≤ ∑ j ∈ T.image (idx B), (1/4:ℝ)*(1/2:ℝ)^j := sum_le_sum (fun j _ => localBound j)
    _ ≤ (1/4:ℝ)*2 := by
      rw [← mul_sum]
      gcongr
      have h := (summable_geometric_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)).sum_le_tsum
        (T.image (idx B)) (fun i _ => by positivity)
      rw [tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)] at h
      norm_num at h ⊢
      exact h
    _ < _ := by norm_num

private theorem num_pos (B : ℕ) (hB : 2 ≤ B) (n : ℕ) : 0 < num B n := by
  have h0 : 0 < num B 0 := by simp [num,mult,idx,pell]
  exact h0.trans_le ((num_mono B hB).monotone (Nat.zero_le n))

private theorem no_sum (B : ℕ) (hB : 2 ≤ B) (n : ℕ) (T : Finset ℕ) (ht : ∀ i ∈ T, i < n)
    (heq : num B n = ∑ i ∈ T, num B i) : False := by
  classical
  have he (m : ℕ) := defect_eq B hB m
  have hdiff : ∑ i ∈ T, defect B i - defect B n =
      (↑(∑ i ∈ T, nearInt B i) : ℝ) - nearInt B n := by
    simp only [he, sum_sub_distrib, ← sum_mul, heq, Nat.cast_sum]
    ring
  have htot := total_defect B hB T
  have hen : defect B n < 1 := by simpa using total_defect B hB {n}
  have hpos := defect_pos B hB n
  have hnonneg : 0 ≤ ∑ i ∈ T, defect B i := sum_nonneg fun i _ => (defect_pos B hB i).le
  have hnear : (∑ i ∈ T, nearInt B i) = nearInt B n := by
    have h1 : (∑ i ∈ T, nearInt B i) < nearInt B n + 1 := by
      exact_mod_cast (by linarith only [htot,hpos,hdiff] : (↑(∑ i ∈ T, nearInt B i):ℝ) < (nearInt B n:ℝ)+1)
    have h2 : nearInt B n < (∑ i ∈ T, nearInt B i) + 1 := by
      exact_mod_cast (by linarith only [hen,hnonneg,hdiff] : (nearInt B n:ℝ) < (↑(∑ i ∈ T, nearInt B i):ℝ)+1)
    omega
  rw [hnear,sub_self] at hdiff
  rcases lt_trichotomy T.card 1 with h|h|h
  · have : T = ∅ := card_eq_zero.mp (by omega)
    simp [this] at heq
    exact (num_pos B hB n).ne' heq
  · obtain ⟨i,hi⟩ := card_eq_one.mp h
    have hin := ht i (by simp [hi])
    simp [hi] at heq
    exact ((num_mono B hB) hin).ne heq.symm
  · obtain ⟨i,hi,j,hj,hij⟩ := one_lt_card.mp h
    have hsub : {i,j} ⊆ T := by intro z hz; simp at hz; rcases hz with rfl|rfl <;> assumption
    have hl := sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => (defect_pos B hB i).le)
    have h' : defect B i + defect B j ≤ ∑ i ∈ T, defect B i := by simpa [hij] using hl
    linarith only [h',hdiff,two_defects B hB (ht i hi).le,two_defects B hB (ht j hj).le]

private theorem range_sum_free (B : ℕ) (hB : 2 ≤ B) : Erdos876.IsSubsetSumFree (Set.range (num B)) := by
  classical
  rintro _ ⟨n,rfl⟩
  refine ⟨num_pos B hB n, ?_⟩
  rintro ⟨S,hS,heq⟩
  let T := (range n).filter fun i => num B i ∈ S
  have hT : ∀ i ∈ T, i < n := fun i hi => mem_range.mp (mem_filter.mp hi).1
  have him : T.image (num B) = S := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hi).2
    · intro hx
      obtain ⟨⟨i,rfl⟩,hlt⟩ := hS hx
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr ((num_mono B hB).lt_iff_lt.mp hlt),hx⟩,rfl⟩
  rw [← him, sum_image (fun _ _ _ _ h => (num_mono B hB).injective h)] at heq
  exact no_sum B hB n T hT heq


private theorem pell_bound (M : ℕ) (hM : 2 ≤ M) (k : ℕ) : ((pell M k).2 : ℝ) ≤ (2*(M:ℝ))^k := by
  have hMr : (2:ℝ) ≤ M := by exact_mod_cast hM
  have hr : (root M)^2 = (M:ℝ)^2-1 := sq_sqrt (by nlinarith)
  have hr0 : 0 ≤ root M := sqrt_nonneg _
  have hl : 1 ≤ root M := by nlinarith
  have hu : root M ≤ (M:ℝ) := by nlinarith
  have hh := (embeddings M hM k).1
  calc
    _ ≤ (pell M k).1 + ((pell M k).2:ℝ)*root M := by
      have hq : (0:ℝ) ≤ (pell M k).2 := Nat.cast_nonneg _
      have hp : (0:ℝ) ≤ (pell M k).1 := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hl hq]
    _ = _ := hh
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) _

private theorem growth (B : ℕ) (hB : 2 ≤ B) (δ : ℝ) (hδ : 0 < δ) (hpow : 16 ≤ (B:ℝ)^δ) (n : ℕ) :
    (num B n : ℝ) ≤ (32*(B:ℝ)^3)*((n:ℝ)+1)^(3+δ) := by
  let s := idx B n
  have hM : 2 ≤ 8*B^2 := by nlinarith
  have hP := pell_bound (8*B^2) hM (s+1)
  have hm : (mult B n:ℝ) ≤ 2*(B:ℝ)^(s+1) := by exact_mod_cast (mult_bounds B hB n).2.le
  have hx : (B:ℝ)^s ≤ (n:ℝ)+1 := by
    exact_mod_cast Nat.pow_le_of_le_log (by omega : n+1 ≠ 0) (le_refl (idx B n))
  have hbr : (0:ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hbase : 16*(B:ℝ)^3 ≤ (B:ℝ)^(3+δ) := by
    rw [rpow_add hbr]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ (B:ℝ)^3)]
  calc
    _ = (mult B n : ℝ)*((pell (8*B^2) (s+1)).2 : ℝ) := by simp [num,s]
    _ ≤ (2*(B:ℝ)^(s+1))*(2*(↑(8*B^2 : ℕ):ℝ))^(s+1) :=
      mul_le_mul hm hP (Nat.cast_nonneg _) (by positivity)
    _ = 2*(16*(B:ℝ)^3)^(s+1) := by
      push_cast
      rw [mul_assoc,← mul_pow]
      congr 2
      ring
    _ = (32*(B:ℝ)^3)*(16*(B:ℝ)^3)^s := by rw [pow_succ]; ring
    _ ≤ (32*(B:ℝ)^3)*((B:ℝ)^(3+δ))^s := by gcongr
    _ = (32*(B:ℝ)^3)*((B:ℝ)^s)^(3+δ) := by
      rw [← rpow_natCast ((B:ℝ)^(3+δ)) s, ← rpow_mul hbr.le, mul_comm (3+δ), rpow_mul hbr.le, rpow_natCast]
    _ ≤ _ := by gcongr <;> linarith

private theorem construction (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : Set ℕ, A.Infinite ∧ Erdos876.IsSubsetSumFree A ∧
      ∃ C : ℝ, ∀ k : ℕ, (Nat.nth (· ∈ A) k : ℝ) ≤ C*((k:ℝ)+1)^(3+δ) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨B,hpow,hB⟩ := ((ht.eventually_ge_atTop 16).and (eventually_ge_atTop (2:ℕ))).exists
  have hi := Set.infinite_range_of_injective (num_mono B hB).injective
  refine ⟨Set.range (num B),hi,range_sum_free B hB,32*(B:ℝ)^3,fun n => ?_⟩
  have he := Nat.nth_comp_of_strictMono (p:=(· ∈ Set.range (num B))) (n:=n) (num_mono B hB)
    (fun _ h => h) (fun hf => (hi hf).elim)
  have hh : Nat.nth (· ∈ Set.range (num B)) n = num B n := by simpa [Set.mem_range_self] using he.symm
  rw [hh]
  exact growth B hB δ hδ hpow n

end OMA.PolynomialSumFree

open OMA.PolynomialSumFree in
theorem OMA.solution : type_of% @Erdos876.erdos_876.variants.dem_polynomial := construction
