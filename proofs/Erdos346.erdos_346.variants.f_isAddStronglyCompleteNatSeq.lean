import FormalConjectures.ErdosProblems.«346»

/-! Graham's gap argument for subset sums of the modified Fibonacci sequence. -/

open Finset Erdos346

namespace OMA.Erdos346

def Sums (k t n : ℕ) : Prop :=
  ∃ S ⊆ Ico k t, ∑ i ∈ S, f i = n

def TailSums (k n : ℕ) : Prop :=
  ∃ t, Sums k t n

def total (k t : ℕ) : ℕ :=
  ∑ i ∈ Ico k t, f i

def Near (A : ℕ → Prop) (w x : ℕ) : Prop :=
  ∃ y, A y ∧ y ≤ x ∧ x ≤ y + w

lemma f_lt {a b : ℕ} (ha : 4 ≤ a) (hab : a < b) : f a < f b := by
  have h := erdos_346.variants.f_strictMono (show a - 4 < b - 4 by omega)
  change f (4 + (a-4)) < f (4 + (b-4)) at h
  rwa [show 4 + (a - 4) = a by omega, show 4 + (b - 4) = b by omega] at h

lemma f_le {a b : ℕ} (ha : 4 ≤ a) (hab : a ≤ b) : f a ≤ f b := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · exact (f_lt ha hab).le
  · rfl

lemma growth (n : ℕ) : n ≤ f (4 + n) := by
  induction n with
  | zero => omega
  | succ n ih => have h := f_lt (a := 4 + n) (b := 4 + (n+1)) (by omega) (by omega); omega

lemma large (n : ℕ) (hn : 4 ≤ n) : n - 4 ≤ f n := by
  simpa [show 4 + (n - 4) = n by omega] using growth (n - 4)

lemma step_bounds (m : ℕ) (hm : 1 ≤ m) :
    f (m + 2) ≤ f (m + 1) + f m + 1 ∧ f m + f (m + 1) ≤ f (m + 2) + 1 := by
  have h := erdos_346.variants.f_add_two m hm
  split_ifs at h <;> omega

lemma total_add (k t : ℕ) (hkt : k ≤ t) :
    total k (t+1) = f t + total k t := by
  unfold total
  rw [Nat.Ico_succ_right_eq_insert_Ico hkt, Finset.sum_insert (by simp)]

lemma total_exact (k t : ℕ) (hk : 1 ≤ k) (ht : k ≤ t) :
    total k t + f (k+1) + (if Even t then 1 else 0) =
      f (t+1) + (if Even k then 1 else 0) := by
  have hsplit : total k t + ∑ i ∈ range k, f i = ∑ i ∈ range t, f i := by
    have hsub : range k ⊆ range t := fun i hi => mem_range.mpr ((mem_range.mp hi).trans_le ht)
    have hdiff : range t \ range k = Ico k t := by
      ext i
      simp [Finset.mem_Ico]
      omega
    simpa [total, hdiff] using Finset.sum_sdiff (f := f) hsub
  have h1 := erdos_346.variants.sum_range_f k hk
  have h2 := erdos_346.variants.sum_range_f t (hk.trans ht)
  omega

lemma total_bounds (k t : ℕ) (hk : 1 ≤ k) (ht : k ≤ t) :
    f (t+1) ≤ total k t + f (k+1) + 1 ∧ total k t ≤ f (t+1) + 1 := by
  have h := total_exact k t hk ht
  split_ifs at h <;> omega

lemma sums_zero (k t : ℕ) : Sums k t 0 := ⟨∅, empty_subset _, by simp⟩

lemma sums_full (k t : ℕ) : Sums k t (total k t) := ⟨Ico k t, Subset.rfl, rfl⟩

lemma sums_mono {k k' t t' n : ℕ} (hk : k' ≤ k) (ht : t ≤ t') (h : Sums k t n) :
    Sums k' t' n := by
  obtain ⟨S, hS, hn⟩ := h
  refine ⟨S, fun i hi => ?_, hn⟩
  obtain ⟨ha, hb⟩ := Finset.mem_Ico.mp (hS hi)
  exact Finset.mem_Ico.mpr ⟨hk.trans ha, hb.trans_le ht⟩

lemma sums_append {k t n : ℕ} (hkt : k ≤ t) (h : Sums k t n) :
    Sums k (t+1) (n + f t) := by
  obtain ⟨S, hS, hn⟩ := h
  have htS : t ∉ S := fun ht => (Finset.mem_Ico.mp (hS ht)).2.false
  refine ⟨insert t S, ?_, ?_⟩
  · rw [Nat.Ico_succ_right_eq_insert_Ico hkt]
    exact Finset.insert_subset_insert t hS
  · rw [Finset.sum_insert htS, hn, Nat.add_comm]

lemma sums_single (k t : ℕ) (hkt : k ≤ t) : Sums k (t+1) (f t) := by
  simpa using sums_append hkt (sums_zero k t)

lemma sums_reflect {k t n : ℕ} (hn : Sums k t n) : Sums k t (total k t - n) := by
  obtain ⟨S, hS, hs⟩ := hn
  refine ⟨Ico k t \ S, sdiff_subset, ?_⟩
  have h := Finset.sum_sdiff (f := f) hS
  unfold total
  omega

lemma sums_of_tail_below {k t n : ℕ} (hk : 4 ≤ k) (ht : k ≤ t)
    (hn : n < f t) (h : TailSums k n) : Sums k t n := by
  obtain ⟨u, S, hS, hs⟩ := h
  refine ⟨S, fun i hi => ?_, hs⟩
  have start := (Finset.mem_Ico.mp (hS hi)).1
  refine Finset.mem_Ico.mpr ⟨start, ?_⟩
  by_contra! hti
  have hb : f i ≤ n := by rw [← hs]; exact Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) hi
  have hc := f_le (hk.trans ht) hti
  omega

lemma total_ge_current (k t : ℕ) (hk : 4 ≤ k) (ht : k + 4 + f (k+1) ≤ t) :
    f t ≤ total k t := by
  have h1 := (total_bounds k t (by omega) (by omega)).1
  have h2 := (step_bounds (t-1) (by omega)).2
  have h3 := large (t-1) (by omega)
  rw [show t-1+1 = t by omega, show t-1+2 = t+1 by omega] at h2
  omega

lemma bounded (k : ℕ) (hk : 4 ≤ k) : ∃ w, ∀ x, Near (TailSums k) w x := by
  let T := k + 4 + f (k+1)
  let w := total k T
  refine ⟨w, fun x => ?_⟩
  have aux (j : ℕ) : ∀ x ≤ total k (T+j), Near (Sums k (T+j)) w x := by
    induction j with
    | zero =>
      intro y hy
      simp only [Nat.add_zero] at hy ⊢
      exact ⟨0, sums_zero _ _, Nat.zero_le _, by simpa [w] using hy⟩
    | succ j ih =>
      intro y hy
      let t := T+j
      change y ≤ total k (t+1) at hy
      change Near (Sums k (t+1)) w y
      have hkt : k ≤ t := by dsimp [t, T]; omega
      by_cases hb : y ≤ total k t
      · obtain ⟨z, hz, hz₁, hz₂⟩ := ih y hb
        exact ⟨z, sums_mono le_rfl (Nat.le_succ _) hz, hz₁, hz₂⟩
      · have hft := total_ge_current k t hk (by dsimp [t,T]; omega)
        rw [total_add k t hkt] at hy
        have hrem : y-f t ≤ total k t := by omega
        obtain ⟨z, hz, hz₁, hz₂⟩ := ih (y-f t) hrem
        exact ⟨z + f t, sums_append hkt hz, by omega, by omega⟩
  have hchoose : x ≤ total k (T+x) := by
    have h1 := total_ge_current k (T+x) hk (by dsimp [T]; omega)
    have h2 := large (T+x) (by dsimp [T]; omega)
    have h3 : x ≤ T+x-4 := by dsimp [T]; omega
    exact h3.trans (h2.trans h1)
  obtain ⟨y, hy, h₁, h₂⟩ := aux x x hchoose
  exact ⟨y, ⟨_, hy⟩, h₁, h₂⟩

/-- Replacing one term by the two preceding terms changes the sum by one.
Iterating at every second index keeps the sign of the change fixed. -/
lemma expand (k b x : ℕ) (hb : 1 ≤ b) (hkb : k ≤ b) (hx : Sums k (b+1) x) (m : ℕ) :
    ∃ y, Sums k (b + 2*m + 1) y ∧
      y + f b + (if Even b then 0 else m) =
        x + f (b + 2*m) + (if Even b then m else 0) := by
  induction m with
  | zero => exact ⟨x, by simpa using hx, by simp⟩
  | succ m ih =>
    obtain ⟨y, hy, heq⟩ := ih
    have hs := sums_append (t := b + 2*m + 1) (by omega) hy
    have h := erdos_346.variants.f_add_two (b+2*m) (by omega)
    have hp : Even (b + 2*m) ↔ Even b := by
      simp [Nat.even_add]
    simp only [hp] at h
    refine ⟨y + f (b + 2*m + 1), ?_, ?_⟩
    · exact sums_mono le_rfl (by omega) hs
    · rw [show b + 2*(m+1) = b + 2*m+2 by omega]
      by_cases he : Even b <;> simp only [he, if_true, if_false] at h heq ⊢ <;> omega

lemma expand_at (k t m x : ℕ) (hkt : k + 2*m ≤ t) (ht : 1 + 2*m ≤ t)
    (hx : Sums k (t-2*m+1) x) :
    ∃ y, TailSums k y ∧
      y + f (t-2*m) + (if Even t then 0 else m) =
        x + f t + (if Even t then m else 0) := by
  let b := t-2*m
  have hbt : b+2*m = t := by dsimp [b]; omega
  have hpar : Even b ↔ Even t := by
    conv_rhs => rw [← hbt]
    simp [Nat.even_add]
  obtain ⟨y, hy, heq⟩ := expand k b x (by dsimp [b]; omega) (by dsimp [b]; omega) hx m
  simp only [hbt, hpar] at heq
  exact ⟨y, ⟨_, hy⟩, heq⟩

/-- Large individual terms have arbitrarily wide neighbourhoods of subset sums. -/
lemma near_terms (k r : ℕ) (hk : 4 ≤ k) :
    ∃ N, ∀ t ≥ N, ∀ x, x ≤ f t + r → f t ≤ x + r → TailSums k x := by
  let K := 2 * (k + r + 4)
  have hK : k ≤ K := by dsimp [K]; omega
  have hKe : Even K := even_two_mul _
  have hKL : k < K := by dsimp [K]; omega
  have hl := large K (by omega)
  have hl' := large (K+1) (by omega)
  have hKr : r ≤ f K := (show r ≤ K-4 by dsimp [K]; omega).trans hl
  have hKr' : r ≤ f (K+1) - 1 := by
    have : r+1 ≤ K+1-4 := by dsimp [K]; omega
    omega
  let D := f (K+1)-1
  let N := K + 2 + 2*(D + f K + r)
  refine ⟨N, ?_⟩
  intro t ht x hx₁ hx₂
  by_cases he : Even t
  · by_cases hpos : f t ≤ x
    · let m := x-f t
      have hmt : K + 2*m ≤ t := by dsimp [m, N] at *; omega
      obtain ⟨y, hy, heq⟩ := expand_at k t m (f (t-2*m))
        (by omega) (by omega) (sums_single k _ (by omega))
      rw [if_pos he, if_pos he] at heq
      have : y = x := by dsimp [m] at *; omega
      rwa [← this]
    · let m := D - (f t-x)
      let b := t-2*m
      have hmt : K + 2 + 2*m ≤ t := by dsimp [m, N] at *; omega
      have hbe : Even b := by
        have hb : b + 2*m = t := by dsimp [b]; omega
        rw [← hb] at he
        simpa [Nat.even_add] using he
      have hodd : ¬ Even (b-1) := by
        have h := Nat.even_add_one (n := b-1)
        rw [show b-1+1 = b by dsimp [b]; omega] at h
        exact h.mp hbe
      have htot := total_exact K (b-1) (by omega) (by dsimp [b]; omega)
      rw [if_neg hodd, if_pos hKe, show b-1+1 = b by dsimp [b]; omega] at htot
      have hbase : Sums k (b+1) (total K (b-1)) :=
        sums_mono hK (by omega) (sums_full _ _)
      obtain ⟨y, hy, heq⟩ := expand_at k t m (total K (b-1))
        (by omega) (by omega) hbase
      rw [if_pos he, if_pos he] at heq
      change y + f b = total K (b-1) + f t + m at heq
      have hm : m + (f t-x) = D := by dsimp [m]; omega
      have hd : D+1 = f (K+1) := by dsimp [D]; omega
      have : y = x := by omega
      rwa [← this]
  · by_cases hneg : x ≤ f t
    · let m := f t-x
      have hmt : K + 2*m ≤ t := by dsimp [m, N] at *; omega
      obtain ⟨y, hy, heq⟩ := expand_at k t m (f (t-2*m))
        (by omega) (by omega) (sums_single k _ (by omega))
      rw [if_neg he, if_neg he] at heq
      have : y = x := by dsimp [m] at *; omega
      rwa [← this]
    · let m := f K - (x-f t)
      let b := t-2*m
      have hmt : K+2+2*m ≤ t := by dsimp [m, N] at *; omega
      have hbase : Sums k (b+1) (f K + f b) :=
        sums_append (by dsimp [b]; omega)
          (sums_mono le_rfl (by dsimp [b]; omega) (sums_single k K hK))
      obtain ⟨y, hy, heq⟩ := expand_at k t m (f K+f b)
        (by omega) (by omega) hbase
      rw [if_neg he, if_neg he] at heq
      change y + f b + m = f K + f b + f t + 0 at heq
      have hm : m + (x-f t) = f K := by dsimp [m]; omega
      have : y = x := by omega
      rwa [← this]

lemma sums_le_total {k t n : ℕ} (h : Sums k t n) : n ≤ total k t := by
  obtain ⟨S, hS, rfl⟩ := h
  exact Finset.sum_le_sum_of_subset hS

/-- A subset sum below the next term uses only the terms of the finite block.
Complementation then extends the gap bound to the other end of the block. -/
lemma finite_near (k t C w x : ℕ) (hk : 4 ≤ k) (ht : k ≤ t)
    (h : ∀ n ≥ C, Near (TailSums k) w n)
    (hgap : total k t + w < 2*f t) (hx : C ≤ x) (hx' : x+C ≤ total k t) :
    Near (Sums k t) w x := by
  by_cases hb : x < f t
  · obtain ⟨y, hy, h₁, h₂⟩ := h x hx
    exact ⟨y, sums_of_tail_below hk ht (by omega) hy, h₁, h₂⟩
  · let z := total k t - x + w
    have hz : C ≤ z := by dsimp [z]; omega
    have hzt : z < f t := by dsimp [z]; omega
    obtain ⟨y, hy, h₁, h₂⟩ := h z hz
    have hfinite := sums_of_tail_below hk ht (show y < f t by omega) hy
    have hsum := sums_le_total hfinite
    exact ⟨total k t - y, sums_reflect hfinite, by dsimp [z] at *; omega,
      by dsimp [z] at *; omega⟩

lemma two_shifts (k t : ℕ) (hk : 4 ≤ k) (ht : k ≤ t) :
    ∃ u ≤ f (t+2), f (t+2) ≤ u+1 ∧
      ∀ y, Sums k t y → TailSums k (y+u) ∧ TailSums k (y+u+1) := by
  have h := erdos_346.variants.f_add_two t (by omega)
  have shifts (y : ℕ) (hy : Sums k t y) :
      TailSums k (y+f (t+2)) ∧ TailSums k (y+(f t + f (t+1))) := by
    constructor
    · exact ⟨_, sums_append (by omega) (sums_mono le_rfl (by omega) hy)⟩
    · exact ⟨_, by simpa only [Nat.add_assoc] using
        sums_append (show k ≤ t+1 by omega) (sums_append ht hy)⟩
  by_cases he : Even t
  · simp only [he, if_true, add_zero] at h
    refine ⟨f (t+2), le_rfl, by omega, fun y hy => ?_⟩
    obtain ⟨ha,hb⟩ := shifts y hy
    exact ⟨ha, by rwa [show y+f (t+2)+1 = y+(f t+f (t+1)) by omega]⟩
  · simp only [he, if_false, add_zero] at h
    refine ⟨f t + f (t+1), by omega, by omega, fun y hy => ?_⟩
    obtain ⟨ha,hb⟩ := shifts y hy
    exact ⟨hb, by rwa [show y+(f t+f (t+1))+1 = y+f (t+2) by omega]⟩

lemma find_block {N x : ℕ} (hN : 4 ≤ N) (hx : f N ≤ x) :
    ∃ m ≥ N, f m ≤ x ∧ x < f (m+1) := by
  have hex : ∃ j, x < f (N+j+1) := by
    refine ⟨x+4, ?_⟩
    have h := large (N+(x+4)+1) (by omega)
    omega
  refine ⟨N+Nat.find hex, by omega, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · simpa [h] using hx
  · have hh := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    rw [show N+(Nat.find hex-1)+1 = N+Nat.find hex by omega] at hh
    exact Nat.le_of_not_gt hh

lemma improve (k C w : ℕ) (hk : 4 ≤ k)
    (h : ∀ n ≥ C, Near (TailSums k) (w+1) n) :
    ∃ C', ∀ n ≥ C', Near (TailSums k) w n := by
  let r := C + f (k+1) + 4
  obtain ⟨N, hN⟩ := near_terms k r hk
  let T := N + k + w + 12
  refine ⟨f (T+2), ?_⟩
  intro x hx
  obtain ⟨m, hm, hmx, hmx'⟩ := find_block (N := T+2) (by dsimp [T]; omega) hx
  by_cases hleft : x ≤ f m + r
  · exact ⟨x, hN m (by dsimp [T] at hm; omega) x hleft (by omega), le_rfl, by omega⟩
  by_cases hright : f (m+1) ≤ x + r
  · exact ⟨x, hN (m+1) (by dsimp [T] at hm; omega) x (by omega) hright,
      le_rfl, by omega⟩
  let t := m-2
  have ht : k ≤ t := by dsimp [t,T] at *; omega
  have htm : t+2 = m := by dsimp [t,T] at *; omega
  have hg : total k t + (w+1) < 2*f t := by
    have htot := (total_bounds k t (by omega) ht).2
    have hstep := (step_bounds (t-1) (by omega)).1
    have hstep' := (step_bounds (t-2) (by dsimp [t,T] at *; omega)).2
    have hl := large (t-2) (by dsimp [t,T] at *; omega)
    rw [show t-1+2 = t+1 by omega, show t-1+1 = t by omega] at hstep
    rw [show t-2+1=t-1 by omega, show t-2+2=t by omega] at hstep'
    dsimp [t,T] at *
    omega
  obtain ⟨u, hu₁, hu₂, hu⟩ := two_shifts k t hk ht
  rw [htm] at hu₁ hu₂
  let z := x-u
  have hz : C ≤ z := by dsimp [z,r] at *; omega
  have hz' : z+C ≤ total k t := by
    have htot := (total_bounds k t (by omega) ht).1
    have hstep := (step_bounds (t+1) (by omega)).1
    rw [show t+1+2=m+1 by omega, show t+1+1=m by omega] at hstep
    dsimp [z,r] at *
    omega
  obtain ⟨y, hy, hy₁, hy₂⟩ := finite_near k t C (w+1) z hk ht h hg hz hz'
  have hpair := hu y hy
  by_cases hxy : x = y + u
  · exact ⟨y+u, hpair.1, by omega, by omega⟩
  · exact ⟨y+u+1, hpair.2, by dsimp [z] at *; omega, by dsimp [z] at *; omega⟩

lemma eventual_exact (k : ℕ) (hk : 4 ≤ k) :
    ∃ C, ∀ n ≥ C, TailSums k n := by
  obtain ⟨w, hw⟩ := bounded k hk
  have close (w : ℕ) (h : ∃ C, ∀ n ≥ C, Near (TailSums k) w n) :
      ∃ C, ∀ n ≥ C, TailSums k n := by
    induction w with
    | zero =>
      obtain ⟨C, hC⟩ := h
      refine ⟨C, fun n hn => ?_⟩
      obtain ⟨y, hy, h₁, h₂⟩ := hC n hn
      rwa [show n = y by omega]
    | succ w ih =>
      obtain ⟨C, hC⟩ := h
      exact ih (improve k C w hk hC)
  exact close w ⟨0, fun n _ => hw n⟩

end OMA.Erdos346

theorem OMA.solution : type_of% @Erdos346.erdos_346.variants.f_isAddStronglyCompleteNatSeq := by
  intro k
  let K := max k 4
  obtain ⟨C, hC⟩ := OMA.Erdos346.eventual_exact K (le_max_right _ _)
  refine Filter.eventually_atTop.mpr ⟨C, fun x hx => ?_⟩
  obtain ⟨t, S, hS, hs⟩ := hC x hx
  refine ⟨S.image f, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have hiK := (Finset.mem_Ico.mp (hS hi)).1
    have hik : k ≤ i := (le_max_left _ _).trans hiK
    refine ⟨i-k, ?_⟩
    change f (k+(i-k)) = f i
    rw [show k+(i-k) = i by omega]
  · rw [Finset.sum_image]
    · exact hs.symm
    · intro i hi j hj heq
      have hi4 := (le_max_right k 4).trans (Finset.mem_Ico.mp (hS hi)).1
      have hj4 := (le_max_right k 4).trans (Finset.mem_Ico.mp (hS hj)).1
      rcases lt_trichotomy i j with h | h | h
      · exact ((OMA.Erdos346.f_lt hi4 h).ne heq).elim
      · exact h
      · exact ((OMA.Erdos346.f_lt hj4 h).ne heq.symm).elim
