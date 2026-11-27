import FormalConjectures.ErdosProblems.«346»

/-!
# Strong completeness of Graham's Fibonacci sequence

Graham, A property of Fibonacci numbers, Fibonacci Quarterly 2 (1964), 1–10.
https://www.fq.math.ca/Scanned/2-1/graham.pdf
-/

-- Credit: @mmiranda2

namespace OMA.Graham

open Erdos346 Finset

def windowSum (k n : ℕ) : ℕ := ∑ i ∈ Ico k n, f i

def prefixRep (k n x : ℕ) : Prop :=
  ∃ s : Finset ℕ, s ⊆ Ico k n ∧ ∑ i ∈ s, f i = x

def tailRep (k x : ℕ) : Prop := ∃ n, prefixRep k n x

lemma f_mono {a b : ℕ} (ha : 4 ≤ a) (hab : a ≤ b) : f a ≤ f b := by
  have h := erdos_346.variants.f_strictMono.monotone
    (show a - 4 ≤ b - 4 by omega)
  simpa [show 4 + (a - 4) = a by omega, show 4 + (b - 4) = b by omega] using h

lemma f_strict {a b : ℕ} (ha : 4 ≤ a) (hab : a < b) : f a < f b := by
  have h := erdos_346.variants.f_strictMono (show a - 4 < b - 4 by omega)
  simpa [show 4 + (a - 4) = a by omega, show 4 + (b - 4) = b by omega] using h

lemma f_ge_index (i : ℕ) : i ≤ f (4 + i) := by
  induction i with
  | zero => omega
  | succ i ih =>
    have := f_strict (a := 4 + i) (b := 4 + (i + 1)) (by omega) (by omega)
    omega

lemma sum_identity {k n : ℕ} (hk : k ≤ n) (hn : 1 ≤ n) :
    windowSum k n + (∑ i ∈ range k, f i) + (if Even n then 1 else 0) = f (n + 1) := by
  have h := erdos_346.variants.sum_range_f n hn
  have hs := Finset.sum_range_add_sum_Ico f hk
  unfold windowSum
  omega

lemma sum_succ {k n : ℕ} (h : k ≤ n) : windowSum k (n + 1) = windowSum k n + f n := by
  unfold windowSum
  rw [Finset.sum_Ico_succ_top h]

lemma rep_weaken {k k' n n' x : ℕ} (hk : k' ≤ k) (hn : n ≤ n')
    (h : prefixRep k n x) : prefixRep k' n' x := by
  rcases h with ⟨s, hs, hx⟩
  refine ⟨s, fun i hi => ?_, hx⟩
  have hmem := mem_Ico.mp (hs hi)
  exact mem_Ico.mpr ⟨hk.trans hmem.1, hmem.2.trans_le hn⟩

lemma rep_all (k n : ℕ) : prefixRep k n (windowSum k n) := ⟨Ico k n, by rfl, rfl⟩

lemma rep_add {k n x j : ℕ} (hk : k ≤ j) (hn : n ≤ j)
    (h : prefixRep k n x) : prefixRep k (j + 1) (x + f j) := by
  classical
  rcases h with ⟨s, hs, hx⟩
  have hnot : j ∉ s := fun h => by have := (mem_Ico.mp (hs h)).2; omega
  refine ⟨insert j s, ?_, ?_⟩
  · intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · exact mem_Ico.mpr ⟨hk, by omega⟩
    · have hm := mem_Ico.mp (hs hi)
      exact mem_Ico.mpr ⟨hm.1, by omega⟩
  · rw [sum_insert hnot, hx, Nat.add_comm]

lemma rep_complement {k n x : ℕ} (h : prefixRep k n x) :
    prefixRep k n (windowSum k n - x) := by
  classical
  rcases h with ⟨s, hs, hx⟩
  refine ⟨Ico k n \ s, sdiff_subset, ?_⟩
  have hsum := sum_sdiff (f := f) hs
  unfold windowSum
  omega

lemma rep_clip {k n x : ℕ} (hk : 4 ≤ k) (hkn : k ≤ n) (hx : x < f n)
    (h : tailRep k x) : prefixRep k n x := by
  rcases h with ⟨b, s, hs, hxsum⟩
  refine ⟨s, fun i hi => ?_, hxsum⟩
  have hm := mem_Ico.mp (hs hi)
  refine mem_Ico.mpr ⟨hm.1, ?_⟩
  by_contra! hni
  have hfi := f_mono (hk.trans hkn) hni
  have hisum : f i ≤ ∑ j ∈ s, f j :=
    single_le_sum (fun j _ => Nat.zero_le (f j)) hi
  omega

lemma f_growth (D : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, D ≤ f n ∧ f n + D ≤ f (n + 1) ∧ f (n + 1) + D ≤ 2 * f n := by
  refine ⟨D + 9, fun n hn => ?_⟩
  have h0 := f_ge_index (n - 4)
  have h1 := f_ge_index (n - 5)
  have h2 := f_ge_index (n - 6)
  have ha := erdos_346.variants.f_add_two (n - 1) (by omega)
  have hb := erdos_346.variants.f_add_two (n - 2) (by omega)
  simp only [show 4 + (n - 4) = n by omega] at h0
  simp only [show 4 + (n - 5) = n - 1 by omega] at h1
  simp only [show 4 + (n - 6) = n - 2 by omega] at h2
  simp only [show n - 1 + 2 = n + 1 by omega, show n - 1 + 1 = n by omega] at ha
  simp only [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] at hb
  split_ifs at ha <;> split_ifs at hb <;> omega

-- The two ways to use the next three indices give totals differing by one.
lemma gadget {k n y : ℕ} (hkn : k ≤ n) (hn : 1 ≤ n) (hy : prefixRep k n y) :
    let b := min (f n + f (n + 1)) (f (n + 2))
    tailRep k (y + b) ∧ tailRep k (y + b + 1) := by
  have hr := erdos_346.variants.f_add_two n hn
  have ha : tailRep k (y + (f n + f (n + 1))) := by
    refine ⟨n + 2, ?_⟩
    rw [← Nat.add_assoc]
    exact rep_add (j := n + 1) (by omega) (le_refl _) (rep_add hkn (le_refl n) hy)
  have hb : tailRep k (y + f (n + 2)) :=
    ⟨n + 3, rep_add (by omega) (by omega) hy⟩
  dsimp
  by_cases he : Even n
  · simp only [if_pos he] at hr
    have hmin : min (f n + f (n + 1)) (f (n + 2)) = f (n + 2) := min_eq_right (by omega)
    rw [hmin]
    exact ⟨hb, by convert ha using 1 <;> omega⟩
  · simp only [if_neg he] at hr
    have hmin : min (f n + f (n + 1)) (f (n + 2)) = f n + f (n + 1) := min_eq_left (by omega)
    rw [hmin]
    exact ⟨ha, by convert hb using 1 <;> omega⟩

lemma range_sum_large (k D : ℕ) :
    D + 1 ≤ ∑ i ∈ range (k + D + 6), f i := by
  have h := f_ge_index (k + D + 1)
  have hsum : f (4 + (k + D + 1)) ≤ ∑ i ∈ range (k + D + 6), f i :=
    single_le_sum (fun i _ => Nat.zero_le (f i)) (mem_range.mpr (by omega))
  omega

lemma expand_even {s j C y : ℕ} (hs : s ≤ j) (hj : 1 ≤ j) (he : Even j)
    (hy : prefixRep s (j + 1) y) (hval : y + C = f j) (t : ℕ) :
    ∃ z, prefixRep s (j + 2 * t + 1) z ∧ z + C = f (j + 2 * t) + t := by
  induction t with
  | zero => exact ⟨y, by simpa using hy, by simpa using hval⟩
  | succ t ih =>
    obtain ⟨z, hz, hval⟩ := ih
    have hpar : Even (j + 2 * t) := by
      rw [Nat.even_iff] at he ⊢
      omega
    have hr := erdos_346.variants.f_add_two (j + 2 * t) (by omega)
    simp only [if_pos hpar] at hr
    refine ⟨z + f (j + 2 * t + 1), ?_, ?_⟩
    · exact rep_weaken (le_refl s) (by omega)
        (rep_add (by omega) (le_refl _) hz)
    · rw [show j + 2 * (t + 1) = j + 2 * t + 2 by omega]
      omega

-- Near an even-indexed term, expanding the final term of a consecutive sum
-- adds one each time. Starting the sum farther out lets it begin below that term.
lemma near_even (k D : ℕ) :
    ∃ N, ∀ n ≥ N, Even n → ∀ x, f n ≤ x + D → x ≤ f n + D → tailRep k x := by
  let s := k + D + 6
  let C := ∑ i ∈ range s, f i
  have hCD : D + 1 ≤ C := range_sum_large k D
  refine ⟨s + 2 * (C + D) + 2, fun n hn he x hx hx' => ?_⟩
  let t := x + C - f n
  let j := n - 2 * t
  have ht : t ≤ C + D := by dsimp [t]; omega
  have hj : s + 2 ≤ j := by dsimp [j]; omega
  have hnj : j + 2 * t = n := by dsimp [j]; omega
  have hje : Even j := by
    rw [Nat.even_iff] at he ⊢
    omega
  have hj' : ¬ Even (j - 1) := by
    rw [Nat.even_iff] at hje ⊢
    omega
  have hsum := sum_identity (k := s) (n := j - 1) (by omega) (by omega)
  simp only [← show C = ∑ i ∈ range s, f i from rfl, if_neg hj',
    show j - 1 + 1 = j by omega] at hsum
  have hstart : prefixRep s (j + 1) (windowSum s (j - 1)) :=
    rep_weaken (le_refl s) (by omega) (rep_all _ _)
  obtain ⟨z, hz, hval⟩ := expand_even (by omega) (by omega) hje hstart (by omega) t
  have hzx : z = x := by rw [hnj] at hval; dsimp [t] at hval; omega
  exact ⟨j + 2 * t + 1, hzx ▸ rep_weaken (show k ≤ s by dsimp [s]; omega) (le_refl _) hz⟩

-- Complementation in a finite window supplies the neighborhoods of odd-indexed terms.
lemma near_term (k D : ℕ) :
    ∃ N, ∀ n ≥ N, ∀ x, f n ≤ x + D → x ≤ f n + D → tailRep k x := by
  let s := k + D + 6
  let C := ∑ i ∈ range s, f i
  have hCD : D + 1 ≤ C := range_sum_large k D
  obtain ⟨Ne, he⟩ := near_even s (C + D)
  obtain ⟨Ng, hg⟩ := f_growth (C + D + 1)
  refine ⟨Ne + Ng + s, fun n hn x hx hx' => ?_⟩
  have hks : k ≤ s := by dsimp [s]; omega
  by_cases hp : Even n
  · obtain ⟨b, hb⟩ := he n (by omega) hp x (by omega) (by omega)
    exact ⟨b, rep_weaken hks (le_refl _) hb⟩
  have hp' : Even (n + 1) := by
    rw [Nat.even_iff] at hp ⊢
    omega
  have hr := erdos_346.variants.f_add_two n (by omega)
  simp only [if_neg hp] at hr
  have hs := sum_identity (k := s) (n := n + 1) (by omega) (by omega)
  simp only [← show C = ∑ i ∈ range s, f i from rfl, if_pos hp'] at hs
  rw [show n + 1 + 1 = n + 2 by omega] at hs
  have htot : windowSum s (n + 1) + C = f n + f (n + 1) := by omega
  have hlarge := (hg (n + 1) (by omega)).1
  have hxs : x ≤ windowSum s (n + 1) := by omega
  let y := windowSum s (n + 1) - x
  have hym : f (n + 1) ≤ y + (C + D) := by dsimp [y]; omega
  have hyp : y ≤ f (n + 1) + (C + D) := by dsimp [y]; omega
  have hylt : y < f (n + 1) := by dsimp [y]; omega
  have hy := rep_clip (k := s) (by dsimp [s]; omega) (by omega) hylt
    (he (n + 1) (by omega) hp' y hym hyp)
  have hx' : windowSum s (n + 1) - y = x := by dsimp [y]; omega
  exact ⟨n + 1, hx' ▸ rep_weaken hks (le_refl _) (rep_complement hy)⟩

def boundedGaps (k w : ℕ) : Prop :=
  ∃ L, ∀ x ≥ L, ∃ y, tailRep k y ∧ x ≤ y ∧ y ≤ x + w

lemma initial_gaps (k : ℕ) : ∃ w, boundedGaps k w := by
  let C := ∑ i ∈ range k, f i
  obtain ⟨N, hN⟩ := f_growth (C + 1)
  let b := N + k + 5
  let w := windowSum k b
  have cover (j : ℕ) : ∀ x ≤ windowSum k (b + j),
      ∃ y, prefixRep k (b + j) y ∧ x ≤ y ∧ y ≤ x + w := by
    induction j with
    | zero =>
      intro x hx
      simp only [Nat.add_zero] at hx ⊢
      exact ⟨w, rep_all _ _, hx, by omega⟩
    | succ j ih =>
      intro x hx
      change x ≤ windowSum k (b + j + 1) at hx
      have hs := sum_succ (k := k) (n := b + j) (by dsimp [b]; omega)
      have hg := (hN (b + j) (by dsimp [b]; omega)).2.1
      have hi := sum_identity (k := k) (n := b + j) (by dsimp [b]; omega) (by dsimp [b]; omega)
      change windowSum k (b + j) + C + _ = _ at hi
      have hOverlap : f (b + j) ≤ windowSum k (b + j) + 1 := by split_ifs at hi <;> omega
      by_cases hOld : x ≤ windowSum k (b + j)
      · obtain ⟨y, hy, hxy, hyx⟩ := ih x hOld
        exact ⟨y, rep_weaken (le_refl k) (by omega) hy, hxy, hyx⟩
      · let z := x - f (b + j)
        have hz : z ≤ windowSum k (b + j) := by dsimp [z]; omega
        obtain ⟨y, hy, hzy, hyz⟩ := ih z hz
        exact ⟨y + f (b + j), rep_add (by dsimp [b]; omega) (le_refl _) hy,
          by dsimp [z] at hzy; omega, by dsimp [z] at hyz; omega⟩
  have grow (j : ℕ) : j ≤ windowSum k (b + j) := by
    induction j with
    | zero => omega
    | succ j ih =>
      have hs := sum_succ (k := k) (n := b + j) (by dsimp [b]; omega)
      have hp := (hN (b + j) (by dsimp [b]; omega)).1
      change j + 1 ≤ windowSum k (b + j + 1)
      omega
  refine ⟨w, 0, fun x _ => ?_⟩
  obtain ⟨y, hy, hxy, hyx⟩ := cover x x (grow x)
  exact ⟨y, ⟨b + x, hy⟩, hxy, hyx⟩

-- Below the next term every global representation is already in the window.
-- Complementation covers the upper part of the window.
lemma prefix_gaps {k L w n x : ℕ}
    (h : ∀ x ≥ L, ∃ y, tailRep k y ∧ x ≤ y ∧ y ≤ x + w)
    (hk : 4 ≤ k) (hkn : k ≤ n)
    (hwide : windowSum k n + 2 * w + 2 ≤ 2 * f n)
    (hx : L ≤ x) (hxs : x + w + L ≤ windowSum k n) :
    ∃ y, prefixRep k n y ∧ x ≤ y ∧ y ≤ x + w := by
  by_cases hp : x + w < f n
  · obtain ⟨y, hy, hxy, hyx⟩ := h x hx
    exact ⟨y, rep_clip hk hkn (by omega) hy, hxy, hyx⟩
  let z := windowSum k n - (x + w)
  have hz : L ≤ z := by dsimp [z]; omega
  obtain ⟨y, hy, hzy, hyz⟩ := h z hz
  have hylt : y < f n := by dsimp [z] at hyz; omega
  refine ⟨windowSum k n - y, rep_complement (rep_clip hk hkn hylt hy), ?_, ?_⟩
  · dsimp [z] at hzy hyz
    omega
  · dsimp [z] at hzy hyz
    omega

lemma between_terms (N x : ℕ) (hN : 4 ≤ N) (hx : f (N + 2) ≤ x) :
    ∃ n ≥ N, f (n + 2) ≤ x ∧ x < f (n + 3) := by
  let P := fun j : ℕ => x < f (N + j + 3)
  have hP : ∃ j, P j := by
    refine ⟨x + 4, ?_⟩
    have hg := f_ge_index (N + x + 3)
    dsimp [P]
    rw [show N + (x + 4) + 3 = 4 + (N + x + 3) by omega]
    omega
  classical
  let j := Nat.find hP
  have hj : P j := Nat.find_spec hP
  refine ⟨N + j, by omega, ?_, hj⟩
  by_cases hz : j = 0
  · simpa [hz] using hx
  · have hnot : ¬ P (j - 1) := Nat.find_min hP (by change j - 1 < j; omega)
    dsimp [P] at hnot
    rw [show N + (j - 1) + 3 = N + j + 2 by omega] at hnot
    omega

lemma shrink_gaps {k w : ℕ} (hk : 4 ≤ k) (h : boundedGaps k (w + 1)) :
    boundedGaps k w := by
  obtain ⟨L, hL⟩ := h
  let C := ∑ i ∈ range k, f i
  let D := C + L + (w + 1) + 5
  obtain ⟨Nn, hn⟩ := near_term k D
  obtain ⟨Ng, hg⟩ := f_growth (2 * (w + 1) + 2)
  let N := Nn + Ng + k + 1
  refine ⟨f (N + 2), fun x hx => ?_⟩
  obtain ⟨n, hnN, hlow, hhigh⟩ := between_terms N x (by dsimp [N]; omega) hx
  by_cases hnear : x ≤ f (n + 2) + D
  · exact ⟨x, hn (n + 2) (by dsimp [N] at hnN; omega) x (by omega) hnear,
      le_refl x, by omega⟩
  by_cases hnear' : f (n + 3) ≤ x + D
  · exact ⟨x, hn (n + 3) (by dsimp [N] at hnN; omega) x hnear' (by omega),
      le_refl x, by omega⟩
  have hkn : k ≤ n := by dsimp [N] at hnN; omega
  have h1n : 1 ≤ n := by omega
  let b := min (f n + f (n + 1)) (f (n + 2))
  have hbupper : b ≤ f (n + 2) := min_le_right _ _
  have hblower : f (n + 2) ≤ b + 1 := by
    have hr := erdos_346.variants.f_add_two n h1n
    dsimp [b]
    rw [Nat.min_def]
    split_ifs at hr ⊢ <;> omega
  have hs := sum_identity hkn h1n
  change windowSum k n + C + _ = _ at hs
  have hEnd : f (n + 3) ≤ b + windowSum k n + C + 3 := by
    have hr := erdos_346.variants.f_add_two (n + 1) (by omega)
    rw [show n + 1 + 2 = n + 3 by omega, show n + 1 + 1 = n + 2 by omega] at hr
    split_ifs at hs <;> split_ifs at hr <;> omega
  have hg' := (hg n (by dsimp [N] at hnN; omega)).2.2
  let z := x - (b + 1)
  have hzx : z + b + 1 = x := by dsimp [z, D] at *; omega
  have hzL : L ≤ z := by dsimp [D] at hnear; omega
  have hzs : z + (w + 1) + L ≤ windowSum k n := by dsimp [D] at hnear'; omega
  obtain ⟨y, hy, hzy, hyz⟩ := prefix_gaps hL hk hkn (by omega) hzL hzs
  obtain ⟨ha, hb⟩ := gadget hkn h1n hy
  by_cases hEq : y = z
  · exact ⟨y + b + 1, hb, by omega, by omega⟩
  · exact ⟨y + b, ha, by omega, by omega⟩

lemma gaps_zero {k : ℕ} (hk : 4 ≤ k) (w : ℕ) (h : boundedGaps k w) :
    boundedGaps k 0 := by
  induction w with
  | zero => exact h
  | succ w ih => exact ih (shrink_gaps hk h)

lemma complete_tail (k : ℕ) (hk : 4 ≤ k) :
    IsAddComplete (Set.range fun m => f (k + m)) := by
  obtain ⟨w, hw⟩ := initial_gaps k
  obtain ⟨L, hL⟩ := gaps_zero hk w hw
  apply Filter.eventually_atTop.mpr
  refine ⟨L, fun x hx => ?_⟩
  obtain ⟨y, ⟨n, s, hs, hy⟩, hxy, hyx⟩ := hL x hx
  classical
  have hinj : Set.InjOn f (↑s : Set ℕ) := by
    intro a ha b hb hab
    have ha' := (mem_Ico.mp (hs ha)).1
    have hb' := (mem_Ico.mp (hs hb)).1
    rcases lt_trichotomy a b with hlt | heq | hlt
    · exact False.elim ((ne_of_lt (f_strict (hk.trans ha') hlt)) hab)
    · exact heq
    · exact False.elim ((ne_of_gt (f_strict (hk.trans hb') hlt)) hab)
  refine ⟨s.image f, ?_, ?_⟩
  · intro u hu
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hu
    have hi' := (mem_Ico.mp (hs hi)).1
    exact ⟨i - k, congrArg f (Nat.add_sub_of_le hi')⟩
  · rw [sum_image (fun a ha b hb hab => hinj ha hb hab), hy]
    omega

end OMA.Graham

theorem OMA.solution : type_of% @Erdos346.erdos_346.variants.f_isAddStronglyCompleteNatSeq := by
  intro k
  apply IsAddComplete.mono _ (OMA.Graham.complete_tail (k + 4) (by omega))
  rintro _ ⟨m, rfl⟩
  exact ⟨4 + m, congrArg Erdos346.f (Nat.add_assoc k 4 m).symm⟩
