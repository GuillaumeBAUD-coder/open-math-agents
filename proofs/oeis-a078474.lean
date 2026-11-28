import OMAStatements.S_oeis_a078474

namespace SRGen

open Filter Topology

/-- The token morphism with images σ. -/
def tau (σ : ℕ → List ℕ) (s : List ℕ) : List ℕ := s.flatMap σ

lemma tau_cons (σ : ℕ → List ℕ) (x : ℕ) (s : List ℕ) : tau σ (x :: s) = σ x ++ tau σ s := by
  simp [tau]

lemma tau_append (σ : ℕ → List ℕ) (u v : List ℕ) : tau σ (u ++ v) = tau σ u ++ tau σ v := by
  simp [tau]

lemma tau_single (σ : ℕ → List ℕ) (x : ℕ) : tau σ [x] = σ x := by
  simp [tau]

lemma tauIter_append (σ : ℕ → List ℕ) (p : ℕ) (u v : List ℕ) :
    (tau σ)^[p] (u ++ v) = (tau σ)^[p] u ++ (tau σ)^[p] v := by
  induction p generalizing u v with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, tau_append, ih]

/-- All tokens of s are below K. -/
def Below (K : ℕ) (s : List ℕ) : Prop := ∀ x ∈ s, x < K

/-- The images of the tokens below K stay below K. -/
def Closed (K : ℕ) (σ : ℕ → List ℕ) : Prop := ∀ x, x < K → ∀ y ∈ σ x, y < K

lemma below_append {K : ℕ} {u v : List ℕ} (hu : Below K u) (hv : Below K v) :
    Below K (u ++ v) := by
  intro y hy
  rcases List.mem_append.mp hy with h | h
  · exact hu y h
  · exact hv y h

lemma below_tau {K : ℕ} {σ : ℕ → List ℕ} (hσ : Closed K σ) {s : List ℕ} (hs : Below K s) :
    Below K (tau σ s) := by
  intro y hy
  simp only [tau, List.mem_flatMap] at hy
  obtain ⟨x, hx, hy⟩ := hy
  exact hσ x (hs x hx) y hy

lemma below_tauIter {K : ℕ} {σ : ℕ → List ℕ} (hσ : Closed K σ) (p : ℕ) {s : List ℕ}
    (hs : Below K s) : Below K ((tau σ)^[p] s) := by
  induction p generalizing s with
  | zero => exact hs
  | succ p ih =>
    rw [Function.iterate_succ_apply]
    exact ih (below_tau hσ hs)

lemma tauIter_nil (σ : ℕ → List ℕ) (p : ℕ) : (tau σ)^[p] [] = [] :=
  Function.iterate_fixed (show tau σ [] = [] from rfl) p

/-- The word of a token list. -/
def flatW (tok : ℕ → List ℕ) (s : List ℕ) : List ℕ := s.flatMap tok

lemma flatW_append (tok : ℕ → List ℕ) (u v : List ℕ) :
    flatW tok (u ++ v) = flatW tok u ++ flatW tok v := by
  simp [flatW]

lemma count01 : ∀ l : List ℕ, (∀ x ∈ l, x ≤ 1) → l.count 0 + l.count 1 = l.length
  | [], _ => rfl
  | x :: l, h => by
    have hx := h x (by simp)
    have ih := count01 l (fun y hy => h y (by simp [hy]))
    interval_cases x <;> simp <;> omega

/-- The counts of a letter along an infinite word agree with those of its prefixes. -/
lemma count_eq_take (W : ℕ → ℕ) (L : List ℕ) (b : ℕ)
    (hW : ∀ i, i < L.length → W i = L.getD i 0) :
    ∀ N, N ≤ L.length → Nat.count (fun i => W i = b) N = (L.take N).count b := by
  intro N
  induction N with
  | zero => intro _; simp
  | succ N ih =>
    intro hN
    have hN' : N < L.length := by omega
    rw [Nat.count_succ, ih (by omega), List.take_add_one, List.getElem?_eq_getElem hN',
      List.count_append, hW N hN', List.getD_eq_getElem _ _ hN']
    simp [List.count_singleton]

/-- For a word, the number of letters 0 minus c times the number of letters 1. -/
noncomputable def gL (c : ℝ) (L : List ℕ) : ℝ := (L.count 0 : ℝ) - c * (L.count 1 : ℝ)

lemma gL_append (c : ℝ) (u v : List ℕ) : gL c (u ++ v) = gL c u + gL c v := by
  simp only [gL, List.count_append]
  push_cast
  ring

lemma gL_nil (c : ℝ) : gL c [] = 0 := by simp [gL]

/-- The deviation of a token list: the deviation of its word. -/
noncomputable def gT (c : ℝ) (tok : ℕ → List ℕ) (s : List ℕ) : ℝ := gL c (flatW tok s)

lemma gT_append (c : ℝ) (tok : ℕ → List ℕ) (u v : List ℕ) :
    gT c tok (u ++ v) = gT c tok u + gT c tok v := by
  unfold gT
  rw [flatW_append, gL_append]

lemma gT_nil (c : ℝ) (tok : ℕ → List ℕ) : gT c tok [] = 0 := by simp [gT, flatW, gL]

/-- The position, counted from 1, of the n-th letter b of W. -/
noncomputable def aPos (W : ℕ → ℕ) (b : ℕ) (n : ℕ) : ℕ := Nat.nth (fun i => W i = b) (n - 1) + 1

/-- The deviation of the first N letters of W. -/
noncomputable def Dz (W : ℕ → ℕ) (c : ℝ) (N : ℕ) : ℝ :=
  (Nat.count (fun i => W i = 0) N : ℝ) - c * (Nat.count (fun i => W i = 1) N : ℝ)

lemma count01_nat (W : ℕ → ℕ) (hW : ∀ i, W i ≤ 1) (N : ℕ) :
    Nat.count (fun i => W i = 0) N + Nat.count (fun i => W i = 1) N = N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.count_succ, Nat.count_succ]
    have := hW N
    split_ifs <;> omega

/-- A scan of the listed positions (counted from 1) of the letter b in a word V. -/
def dataChk (V : List ℕ) (b : ℕ) (data : List ℕ) : Bool :=
  (List.range data.length).all fun j =>
    decide (1 ≤ data.getD j 0) && decide (data.getD j 0 ≤ V.length) &&
      decide (V.getD (data.getD j 0 - 1) 0 = b) &&
        decide ((V.take (data.getD j 0 - 1)).count b = j)

/-- The listed positions of b in W, read off a prefix V of W by a scan. -/
theorem data_of_chk (W : ℕ → ℕ) (V : List ℕ) (b : ℕ) (data : List ℕ)
    (hW : ∀ i, i < V.length → W i = V.getD i 0) (h : dataChk V b data = true) :
    ∀ j, j < data.length → aPos W b (j + 1) = data.getD j 0 := by
  intro j hj
  unfold dataChk at h
  rw [List.all_eq_true] at h
  have hj' := h j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hj'
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hj'
  have hWd : W (data.getD j 0 - 1) = b := by rw [hW _ (by omega)]; exact h3
  have hc : Nat.count (fun i => W i = b) (data.getD j 0 - 1) = j := by
    rw [count_eq_take W V b hW _ (by omega)]
    exact h4
  have hn : Nat.nth (fun i => W i = b) j = data.getD j 0 - 1 := by
    have h := Nat.nth_count (p := fun i => W i = b) hWd
    rw [hc] at h
    exact h
  unfold aPos
  rw [show j + 1 - 1 = j by omega, hn]
  omega

end SRGen

/-!
# OEIS A078474: a(n) = A284680(1) + ... + A284680(n)

Irvine's conjecture (Jul 16 2022) for Zumkeller's nested recurrence. Let X be A284680 indexed from
0, the fixed point of mu: 0 -> 1, 1 -> 1000 started at 1, and C(n) the number of 1s among its first
n letters. Both images begin with 1 and hold exactly one 1, so the image of letter j starts at
L(j) = j + 3 C(j), C(L(j)) = j, and the 1s of X are exactly the L(j) (`image`, `one_iff`). With
T = C o C, T(p + 1) - T(p) is 1 exactly when p starts a long image 1000 (`T_succ`), and X(q) = 0 exactly
when one of q - 1, q - 2, q - 3 starts a long image (`key`). Hence n - C(n) and
T(n - 1) + T(n - 2) + T(n - 3) have the same increments (`rec_C`), so C satisfies the recursion of
the entry, and by strong induction every solution equals C (`solution_eq`).
-/

namespace OMA.S_oeis_a078474





/-! ### The morphism -/

lemma mu_append : ∀ u v : List ℕ, mu (u ++ v) = mu u ++ mu v
  | [], _ => rfl
  | 0 :: u, v => by
    show 1 :: mu (u ++ v) = 1 :: (mu u ++ mu v)
    rw [mu_append u v]
  | 1 :: u, v => by
    show 1 :: 0 :: 0 :: 0 :: mu (u ++ v) = 1 :: 0 :: 0 :: 0 :: (mu u ++ mu v)
    rw [mu_append u v]
  | (y + 2) :: u, v => by
    show (y + 2) :: mu (u ++ v) = (y + 2) :: (mu u ++ mu v)
    rw [mu_append u v]

/-- Letters stay 0 or 1; the image has three more letters per 1 and one letter 1 per letter. -/
lemma mu_props : ∀ l : List ℕ, (∀ y ∈ l, y ≤ 1) →
    (∀ y ∈ mu l, y ≤ 1) ∧ (mu l).length = l.length + 3 * l.count 1 ∧ (mu l).count 1 = l.length
  | [], _ => ⟨by simp [mu], rfl, rfl⟩
  | y :: l, h => by
    have hy : y ≤ 1 := h y (by simp)
    obtain ⟨ih1, ih2, ih3⟩ := mu_props l (fun z hz => h z (by simp [hz]))
    interval_cases y
    · refine ⟨?_, ?_, ?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · norm_num
        · exact ih1 z hz
      · show (1 :: mu l).length = (0 :: l).length + 3 * (0 :: l).count 1
        simp [ih2]
        omega
      · show (1 :: mu l).count 1 = (0 :: l).length
        simp [ih3]
    · refine ⟨?_, ?_, ?_⟩
      · intro z hz
        simp only [show mu (1 :: l) = 1 :: 0 :: 0 :: 0 :: mu l from rfl, List.mem_cons] at hz
        rcases hz with rfl | rfl | rfl | rfl | hz
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · exact ih1 z hz
      · show (1 :: 0 :: 0 :: 0 :: mu l).length = (1 :: l).length + 3 * (1 :: l).count 1
        simp [ih2]
        omega
      · show (1 :: 0 :: 0 :: 0 :: mu l).count 1 = (1 :: l).length
        simp [ih3]

lemma muIter_letters : ∀ m, ∀ y ∈ muIter m, y ≤ 1
  | 0 => by simp [muIter]
  | m + 1 => (mu_props _ (muIter_letters m)).1

lemma muIter_head : ∀ m, ∃ t, muIter m = 1 :: t
  | 0 => ⟨[], rfl⟩
  | m + 1 => by
    obtain ⟨t, ht⟩ := muIter_head m
    exact ⟨0 :: 0 :: 0 :: mu t, by show mu (muIter m) = _; rw [ht]; rfl⟩

lemma muIter_length : ∀ m, m + 1 ≤ (muIter m).length
  | 0 => le_rfl
  | m + 1 => by
    have ih := muIter_length m
    obtain ⟨t, ht⟩ := muIter_head m
    have hc : 1 ≤ (muIter m).count 1 := by rw [ht]; simp
    show m + 1 + 1 ≤ (mu (muIter m)).length
    rw [(mu_props _ (muIter_letters m)).2.1]
    omega

lemma muIter_prefix_succ : ∀ m, muIter m <+: muIter (m + 1)
  | 0 => ⟨[0, 0, 0], rfl⟩
  | m + 1 => by
    obtain ⟨r, hr⟩ := muIter_prefix_succ m
    refine ⟨mu r, ?_⟩
    show mu (muIter m) ++ mu r = mu (muIter (m + 1))
    rw [← hr, mu_append]

lemma muIter_prefix {m m' : ℕ} (h : m ≤ m') : muIter m <+: muIter m' := by
  induction m', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m' _ ih => exact ih.trans (muIter_prefix_succ m')

/-! ### The fixed point indexed from 0 -/

/-- A284680 indexed from 0. -/
def X (i : ℕ) : ℕ := x (i + 1)

lemma X_eq (m i : ℕ) (hi : i < (muIter m).length) : X i = (muIter m).getD i 0 := by
  have hi1 : i < (muIter (i + 1)).length := by have := muIter_length (i + 1); omega
  show (muIter (i + 1)).getD (i + 1 - 1) 0 = _
  rw [Nat.add_sub_cancel]
  rcases le_total m (i + 1) with h | h
  · obtain ⟨r, hr⟩ := muIter_prefix h
    rw [← hr, List.getD_append _ _ _ _ hi]
  · obtain ⟨r, hr⟩ := muIter_prefix h
    rw [← hr, List.getD_append _ _ _ _ hi1]

lemma X_le (i : ℕ) : X i ≤ 1 := by
  have hi : i < (muIter (i + 1)).length := by have := muIter_length (i + 1); omega
  rw [X_eq _ i hi, List.getD_eq_getElem _ _ hi]
  exact muIter_letters _ _ (List.getElem_mem hi)

/-- The number of 1s among the first n letters. -/
noncomputable def C (n : ℕ) : ℕ := Nat.count (fun i => X i = 1) n

/-- The start of the image of letter j. -/
noncomputable def L (j : ℕ) : ℕ := j + 3 * C j

lemma C_succ (n : ℕ) : C (n + 1) = C n + (if X n = 1 then 1 else 0) := by
  unfold C
  rw [Nat.count_succ]

lemma C_le (n : ℕ) : C n ≤ n := Nat.count_le _

lemma X_zero : X 0 = 1 := by rw [X_eq 0 0 (by decide)]; rfl

lemma C_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ C n := by
  have h1 : C 1 = 1 := by rw [C_succ, show C 0 = 0 from Nat.count_zero _, X_zero]; rfl
  have := Nat.count_monotone (fun i => X i = 1) hn
  unfold C at h1 ⊢
  omega

/-- The image of letter j occupies the positions L j, ..., L j + |mu [X j]| - 1, and C (L j) = j. -/
lemma image (j : ℕ) :
    (∀ t, t < (mu [X j]).length → X (L j + t) = (mu [X j]).getD t 0) ∧ C (L j) = j := by
  have hlen : j + 2 ≤ (muIter (j + 1)).length := muIter_length (j + 1)
  set u := (muIter (j + 1)).take j with hu
  have hX : X j = (muIter (j + 1)).getD j 0 := X_eq _ j (by omega)
  have htake : (muIter (j + 1)).take (j + 1) = u ++ [X j] := by
    rw [hu, hX, List.take_add_one, List.getElem?_eq_getElem (by omega),
      List.getD_eq_getElem _ _ (by omega)]
    rfl
  have hul : ∀ y ∈ u, y ≤ 1 := fun y hy => muIter_letters _ _ (List.mem_of_mem_take hy)
  obtain ⟨-, hlu, hcu⟩ := mu_props u hul
  have hulen : u.length = j := by rw [hu, List.length_take]; omega
  have hcount : u.count 1 = C j := (SRGen.count_eq_take X (muIter (j + 1)) 1 (X_eq _) j (by omega)).symm
  have hLj : (mu u).length = L j := by rw [hlu, hulen, hcount]; rfl
  have hpre : mu u ++ mu [X j] <+: muIter (j + 2) := by
    rw [← mu_append, ← htake]
    obtain ⟨r, hr⟩ := List.take_prefix (j + 1) (muIter (j + 1))
    refine ⟨mu r, ?_⟩
    rw [← mu_append, hr]
    rfl
  obtain ⟨r, hr⟩ := hpre
  have hXP : ∀ i, i < (mu u ++ mu [X j]).length → X i = (mu u ++ mu [X j]).getD i 0 := by
    intro i hi
    have hi' : i < (muIter (j + 2)).length := by
      rw [← hr, List.length_append]
      omega
    rw [X_eq _ i hi', ← hr, List.getD_append _ _ _ _ hi]
  constructor
  · intro t ht
    rw [hXP _ (by rw [List.length_append]; omega), List.getD_append_right _ _ _ _ (by omega), hLj,
      Nat.add_sub_cancel_left]
  · have := SRGen.count_eq_take X (mu u ++ mu [X j]) 1 hXP (L j) (by rw [List.length_append]; omega)
    unfold C
    rw [this, List.take_append, ← hLj, List.take_of_length_le le_rfl, Nat.sub_self, List.take_zero,
      List.append_nil, hcu, hulen]

lemma L_succ (j : ℕ) : L (j + 1) = L j + 1 + 3 * (if X j = 1 then 1 else 0) := by
  unfold L
  rw [C_succ]
  ring

lemma X_L (j : ℕ) : X (L j) = 1 := by
  have h := (image j).1 0
  have hx := X_le j
  interval_cases hj : X j
  · simpa [mu] using h (by simp [mu])
  · simpa [mu] using h (by simp [mu])

lemma X_long (j : ℕ) (hj : X j = 1) :
    X (L j + 1) = 0 ∧ X (L j + 2) = 0 ∧ X (L j + 3) = 0 := by
  have h := (image j).1
  rw [hj] at h
  exact ⟨by simpa [mu] using h 1 (by simp [mu]), by simpa [mu] using h 2 (by simp [mu]),
    by simpa [mu] using h 3 (by simp [mu])⟩

lemma L_mono : StrictMono L := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [L_succ]
  omega

/-- Every position lies in the image of exactly one letter. -/
lemma cover (p : ℕ) : ∃ j, L j ≤ p ∧ p < L (j + 1) := by
  have hex : ∃ k, p < L k := ⟨p + 1, by unfold L; omega⟩
  set k := Nat.find hex with hk
  have hkp : p < L k := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0] at hkp
    simp [L, C] at hkp
  refine ⟨k - 1, ?_, by rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]⟩
  have := Nat.find_min hex (show k - 1 < k by omega)
  omega

lemma one_iff (p : ℕ) : X p = 1 ↔ ∃ j, L j = p := by
  constructor
  · intro hp
    obtain ⟨j, h1, h2⟩ := cover p
    refine ⟨j, ?_⟩
    by_contra hne
    have hs := L_succ j
    by_cases hj : X j = 1
    · rw [if_pos hj] at hs
      obtain ⟨e1, e2, e3⟩ := X_long j hj
      have : p = L j + 1 ∨ p = L j + 2 ∨ p = L j + 3 := by omega
      rcases this with rfl | rfl | rfl <;> omega
    · rw [if_neg hj] at hs
      omega
  · rintro ⟨j, rfl⟩
    exact X_L j

lemma zero_long (q : ℕ) (hq : X q = 0) : ∃ j t, X j = 1 ∧ 1 ≤ t ∧ t ≤ 3 ∧ q = L j + t := by
  obtain ⟨j, h1, h2⟩ := cover q
  have hne : q ≠ L j := by
    intro h
    rw [h, X_L] at hq
    omega
  have hs := L_succ j
  by_cases hj : X j = 1
  · rw [if_pos hj] at hs
    exact ⟨j, q - L j, hj, by omega, by omega, by omega⟩
  · rw [if_neg hj] at hs
    omega

/-! ### The recursion -/

/-- p starts the image 1000 of a letter 1. -/
def longStart (p : ℕ) : Prop := X p = 1 ∧ X (C p) = 1

lemma longStart_iff (s : ℕ) : longStart s ↔ ∃ j, s = L j ∧ X j = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨j, rfl⟩ := (one_iff s).mp h1
    rw [(image j).2] at h2
    exact ⟨j, rfl, h2⟩
  · rintro ⟨j, rfl, hj⟩
    exact ⟨X_L j, by rw [(image j).2]; exact hj⟩

noncomputable def T (p : ℕ) : ℕ := C (C p)

open Classical in
lemma T_succ (p : ℕ) : T (p + 1) = T p + (if longStart p then 1 else 0) := by
  unfold T longStart
  rw [C_succ p]
  by_cases h1 : X p = 1
  · rw [if_pos h1, C_succ (C p)]
    by_cases h2 : X (C p) = 1
    · rw [if_pos h2, if_pos ⟨h1, h2⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.2)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]
    simp

open Classical in
/-- X q = 0 exactly when one of q - 1, q - 2, q - 3 starts a long image. -/
lemma key (q : ℕ) (hq : 3 ≤ q) :
    (if X q = 1 then 0 else 1) = (if longStart (q - 1) then 1 else 0) +
      (if longStart (q - 2) then 1 else 0) + (if longStart (q - 3) then 1 else 0) := by
  have hnot : ∀ s, longStart s → X (s + 1) = 0 ∧ X (s + 2) = 0 ∧ X (s + 3) = 0 := by
    intro s hs
    obtain ⟨j, rfl, hj⟩ := (longStart_iff s).mp hs
    exact X_long j hj
  have hone : ∀ s, longStart s → X s = 1 := fun s hs => hs.1
  by_cases h1 : X q = 1
  · rw [if_pos h1]
    have n1 : ¬longStart (q - 1) := fun h => by
      have := (hnot _ h).1; rw [show q - 1 + 1 = q by omega, h1] at this; omega
    have n2 : ¬longStart (q - 2) := fun h => by
      have := (hnot _ h).2.1; rw [show q - 2 + 2 = q by omega, h1] at this; omega
    have n3 : ¬longStart (q - 3) := fun h => by
      have := (hnot _ h).2.2; rw [show q - 3 + 3 = q by omega, h1] at this; omega
    rw [if_neg n1, if_neg n2, if_neg n3]
  · have h0 : X q = 0 := by have := X_le q; omega
    rw [if_neg h1]
    obtain ⟨j, t, hj, ht1, ht3, rfl⟩ := zero_long _ h0
    have hs : longStart (L j) := (longStart_iff _).mpr ⟨j, rfl, hj⟩
    obtain ⟨e1, e2, e3⟩ := X_long j hj
    have hLj := X_L j
    -- a long start s' at distance 1 or 2 before L j would put a 0 on L j
    have hbefore : ∀ d, 1 ≤ d → d ≤ 2 → d ≤ L j → ¬longStart (L j - d) := by
      intro d hd1 hd2 hdl h
      obtain ⟨f1, f2, -⟩ := hnot _ h
      rcases (show d = 1 ∨ d = 2 by omega) with rfl | rfl
      · rw [show L j - 1 + 1 = L j by omega, hLj] at f1; omega
      · rw [show L j - 2 + 2 = L j by omega, hLj] at f2; omega
    have hinside : ∀ e, 1 ≤ e → e ≤ 2 → ¬longStart (L j + e) := by
      intro e he1 he2 h
      have := hone _ h
      rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl
      · rw [e1] at this; omega
      · rw [e2] at this; omega
    have hLj3 : 3 ≤ L j + t := hq
    rcases (show t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl
    · rw [if_pos (by simpa using hs)]
      have n2 : ¬longStart (L j + 1 - 2) := by
        rw [show L j + 1 - 2 = L j - 1 by omega]; exact hbefore 1 le_rfl (by norm_num) (by omega)
      have n3 : ¬longStart (L j + 1 - 3) := by
        rw [show L j + 1 - 3 = L j - 2 by omega]; exact hbefore 2 (by norm_num) le_rfl (by omega)
      rw [if_neg n2, if_neg n3]
    · have n1 : ¬longStart (L j + 2 - 1) := by
        rw [show L j + 2 - 1 = L j + 1 by omega]; exact hinside 1 le_rfl (by norm_num)
      have p2 : longStart (L j + 2 - 2) := by rw [show L j + 2 - 2 = L j by omega]; exact hs
      have n3 : ¬longStart (L j + 2 - 3) := by
        rw [show L j + 2 - 3 = L j - 1 by omega]; exact hbefore 1 le_rfl (by norm_num) (by omega)
      rw [if_neg n1, if_pos p2, if_neg n3]
    · have n1 : ¬longStart (L j + 3 - 1) := by
        rw [show L j + 3 - 1 = L j + 2 by omega]; exact hinside 2 (by norm_num) le_rfl
      have n2 : ¬longStart (L j + 3 - 2) := by
        rw [show L j + 3 - 2 = L j + 1 by omega]; exact hinside 1 le_rfl (by norm_num)
      have p3 : longStart (L j + 3 - 3) := by rw [show L j + 3 - 3 = L j by omega]; exact hs
      rw [if_neg n1, if_neg n2, if_pos p3]

lemma C_small : C 1 = 1 ∧ C 2 = 1 ∧ C 3 = 1 ∧ C 4 = 1 := by
  have h : ∀ i, i < 4 → X i = [1, 0, 0, 0].getD i 0 := fun i hi =>
    X_eq 1 i (by have e : (muIter 1).length = 4 := rfl; omega)
  have e := fun N (hN : N ≤ 4) => SRGen.count_eq_take X [1, 0, 0, 0] 1 h N hN
  unfold C
  exact ⟨e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num), e 4 (by norm_num)⟩

/-- C satisfies the recursion: C n + T (n - 1) + T (n - 2) + T (n - 3) = n for n >= 4. -/
lemma rec_C (n : ℕ) (hn : 4 ≤ n) : C n + T (n - 1) + T (n - 2) + T (n - 3) = n := by
  induction n, hn using Nat.le_induction with
  | base =>
    obtain ⟨c1, c2, c3, c4⟩ := C_small
    simp only [T, show 4 - 1 = 3 from rfl, show 4 - 2 = 2 from rfl, show 4 - 3 = 1 from rfl, c1, c2,
      c3, c4]
  | succ n hn ih =>
    have hk := key n (by omega)
    have t1 := T_succ (n - 1)
    have t2 := T_succ (n - 2)
    have t3 := T_succ (n - 3)
    rw [show n - 1 + 1 = n by omega] at t1
    rw [show n - 2 + 1 = n - 1 by omega] at t2
    rw [show n - 3 + 1 = n - 2 by omega] at t3
    have hc := C_succ n
    rw [show n + 1 - 1 = n by omega, show n + 1 - 2 = n - 1 by omega, show n + 1 - 3 = n - 2 by omega]
    split_ifs at hk t1 t2 t3 hc <;> omega

/-! ### The conjecture -/

lemma solution_eq (a : ℕ → ℕ) (h : IsSolution a) : ∀ n, 1 ≤ n → a n = C n := by
  obtain ⟨h1, h2, h3, hrec⟩ := h
  obtain ⟨c1, c2, c3, -⟩ := C_small
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | rfl | h4
    · rw [h1, c1]
    · rw [h2, c2]
    · rw [h3, c3]
    · have hr := hrec n h4
      have hC := rec_C n h4
      have step : ∀ i, 1 ≤ i → i ≤ 3 → a (a (n - i)) = T (n - i) := by
        intro i hi1 hi3
        rw [ih (n - i) (by omega) (by omega)]
        have hp := C_pos (n - i) (by omega)
        have hl := C_le (n - i)
        rw [ih (C (n - i)) (by omega) hp]
        rfl
      rw [step 1 le_rfl (by norm_num), step 2 (by norm_num) (by norm_num),
        step 3 (by norm_num) le_rfl] at hr
      have : (a n : ℤ) = C n := by
        rw [hr]
        have := congrArg (fun m : ℕ => (m : ℤ)) hC
        push_cast at this
        linarith
      exact_mod_cast this

lemma sum_x (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, x k = C n := by
  induction n with
  | zero => simp [C]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, C_succ]
    have hx : x (n + 1) = X n := rfl
    have := X_le n
    rw [hx]
    split_ifs <;> omega

/-- Irvine's conjecture: A078474 is the sequence of partial sums of A284680. -/
theorem conjecture : ∀ a : ℕ → ℕ, IsSolution a → ∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ Finset.Icc 1 n, x k :=
  fun a h n hn => by rw [solution_eq a h n hn, sum_x]

end OMA.S_oeis_a078474

theorem OMA.solution : type_of% @OMA.S_oeis_a078474.main :=
  OMA.S_oeis_a078474.conjecture
