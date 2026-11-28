import OMAStatements.S_oeis_a288997

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
# SRGen two-block maps: positions of 1 squeezed by a Beatty sequence

Kimberling's maps 00 -> 0010, 01 -> x, 10 -> y (A289011, A289071, A289239, A289242) are read by
StringReplace from the left. On a word with letters 0, 1 and no factor 11 the pass reads consecutive
pairs (`pass2_append`), and when every image holds exactly one 1, the n-th 1 of the fixed point W is
the 1 in the image of the n-th pair of W:
`a(n) + O(2n - 2) + 3 = 4n + off(W(2n-2), W(2n-1))` (`rec_of_chain`), with O the counting function of
the 1s and off the index of the 1 in the image. The stable prefixes `chain` (`S_(k+1)` is the pass over
the even prefix of `S_k`) are prefixes of the iterates whether or not the iterates are nested.

The reference is b(n) = 2n + isqrt(2n^2) = floor(n (2 + sqrt 2)), with counting function
CB(N) = N - isqrt((N + 1)^2 / 2) (`le_CB_iff`); it satisfies the same recursion with the offsets
00: 2, 01: 2, 10: 1 (`bB_rec`). `compare` turns a finite table on the offsets into a(n) <= b(n) for
all n, and `lower` gives b(n - 1) < a(n) for any nonnegative offsets. `ones_window` and
`zeros_window` turn these into bounds for the positions of 1 and of 0.
-/

namespace SRGen

open Filter Topology

/-! ### The pass -/

/-- One pass of StringReplace with the rules 00 -> img 0 0, 01 -> img 0 1, 10 -> img 1 0 over a
finite word, read from the left: where 00, 01 or 10 starts it is replaced by its image, and any
other letter (a 1 before a 1, or a final letter) is copied. -/
def pass2 (img : ℕ → ℕ → List ℕ) : List ℕ → List ℕ
  | 0 :: 0 :: l => img 0 0 ++ pass2 img l
  | 0 :: 1 :: l => img 0 1 ++ pass2 img l
  | 1 :: 0 :: l => img 1 0 ++ pass2 img l
  | x :: l => x :: pass2 img l
  | [] => []

/-- Letters 0 and 1 and no factor 11. -/
def good : List ℕ → Bool
  | [] => true
  | [x] => decide (x ≤ 1)
  | x :: y :: l => decide (x ≤ 1) && !(decide (x = 1) && decide (y = 1)) && good (y :: l)

lemma good_tail {x : ℕ} {l : List ℕ} (h : good (x :: l) = true) : good l = true := by
  rcases l with _ | ⟨y, l⟩
  · rfl
  · simp only [good, Bool.and_eq_true] at h
    exact h.2

lemma good_head {x : ℕ} {l : List ℕ} (h : good (x :: l) = true) : x ≤ 1 := by
  rcases l with _ | ⟨y, l⟩
  · simpa [good] using h
  · simp only [good, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1

lemma good_pair {x y : ℕ} {l : List ℕ} (h : good (x :: y :: l) = true) : ¬(x = 1 ∧ y = 1) := by
  simp only [good, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at h
  tauto

lemma good_letters : ∀ l : List ℕ, good l = true → ∀ x ∈ l, x ≤ 1
  | [], _ => by simp
  | x :: l, h => by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact good_head h
    · exact good_letters l (good_tail h) z hz

lemma good_take : ∀ (l : List ℕ) (n : ℕ), good l = true → good (l.take n) = true
  | [], _, _ => by simp [good]
  | [x], n, h => by rcases n with _ | n <;> simp_all [good]
  | x :: y :: l, n, h => by
    rcases n with _ | _ | n
    · simp [good]
    · simp only [List.take_succ_cons, List.take_zero, good]
      exact decide_eq_true (good_head h)
    · have ih := good_take (y :: l) (n + 1) (good_tail h)
      rw [List.take_succ_cons] at ih
      rw [List.take_succ_cons, List.take_succ_cons]
      simp only [good, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, ih⟩

/-- On a good word, a pass splits after an even prefix. -/
lemma pass2_append (img : ℕ → ℕ → List ℕ) :
    ∀ (n : ℕ) (u v : List ℕ), u.length = 2 * n → good u = true →
      pass2 img (u ++ v) = pass2 img u ++ pass2 img v
  | 0, u, v, hu, _ => by
    have h0 : u = [] := List.eq_nil_of_length_eq_zero (by simpa using hu)
    subst h0
    rfl
  | n + 1, x :: y :: u, v, hu, hg => by
    have hx := good_head hg
    have hy := good_head (good_tail hg)
    have hxy := good_pair hg
    have ih := pass2_append img n u v (by simp at hu; omega) (good_tail (good_tail hg))
    simp only [List.cons_append]
    interval_cases x <;> interval_cases y
    · simp only [pass2, ih, List.append_assoc]
    · simp only [pass2, ih, List.append_assoc]
    · simp only [pass2, ih, List.append_assoc]
    · exact absurd ⟨rfl, rfl⟩ hxy
  | n + 1, [], _, hu, _ => by simp at hu
  | n + 1, [_], _, hu, _ => by simp at hu; omega

lemma good_suffix : ∀ (a b : List ℕ), good (a ++ b) = true → good b = true
  | [], _, h => h
  | _ :: a, b, h => good_suffix a b (good_tail h)

lemma good_append : ∀ (a b : List ℕ), good a = true → good b = true →
    ¬(a.getLast? = some 1 ∧ b.head? = some 1) → good (a ++ b) = true
  | [], b, _, hb, _ => hb
  | [x], [], ha, _, _ => ha
  | [x], y :: b, ha, hb, hj => by
    have hx := good_head ha
    simp only [List.getLast?_singleton, List.head?_cons, Option.some.injEq] at hj
    simp only [List.singleton_append, good, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨⟨hx, by tauto⟩, hb⟩
  | x :: y :: a, b, ha, hb, hj => by
    have ih := good_append (y :: a) b (good_tail ha) hb (by simpa using hj)
    simp only [List.cons_append] at ih ⊢
    simp only [good, Bool.and_eq_true] at ha ⊢
    exact ⟨ha.1, ih⟩

/-- The images of a two-block map of the sqrt 2 family: 00 -> 0010, the images of 01 and 10 are
good words of length 3 with one letter 1, and an image ending in 1 is never followed by an image
beginning with 1 inside a good word. -/
structure Imgs (img : ℕ → ℕ → List ℕ) : Prop where
  h00 : img 0 0 = [0, 0, 1, 0]
  h01 : (img 0 1).length = 3 ∧ (img 0 1).count 1 = 1 ∧ good (img 0 1) = true
  h10 : (img 1 0).length = 3 ∧ (img 1 0).count 1 = 1 ∧ good (img 1 0) = true
  junction : ∀ p q r s : ℕ, p ≤ 1 → q ≤ 1 → r ≤ 1 → s ≤ 1 → ¬(p = 1 ∧ q = 1) →
    ¬(r = 1 ∧ s = 1) → ¬(q = 1 ∧ r = 1) →
      ¬((img p q).getLast? = some 1 ∧ (img r s).head? = some 1)

section Images

variable {img : ℕ → ℕ → List ℕ} (hI : Imgs img)
include hI

lemma img_props (p q : ℕ) (hp : p ≤ 1) (hq : q ≤ 1) (hpq : ¬(p = 1 ∧ q = 1)) :
    good (img p q) = true ∧ (img p q).count 1 = 1 ∧ (img p q).length + p + q = 4 := by
  interval_cases p <;> interval_cases q
  · rw [hI.h00]; decide
  · exact ⟨hI.h01.2.2, hI.h01.2.1, by rw [hI.h01.1]⟩
  · exact ⟨hI.h10.2.2, hI.h10.2.1, by rw [hI.h10.1]⟩
  · exact absurd ⟨rfl, rfl⟩ hpq

/-- On a good word of even length 2n, the pass is good, holds n letters 1, and has 4n minus the
number of 1s of the word letters; it begins like the image of the first pair. -/
lemma pass2_props : ∀ (n : ℕ) (u : List ℕ), u.length = 2 * n → good u = true →
    good (pass2 img u) = true ∧ (pass2 img u).count 1 = n ∧
      (pass2 img u).length + u.count 1 = 4 * n ∧
      (∀ x y u', u = x :: y :: u' → (pass2 img u).head? = (img x y).head?)
  | 0, u, hu, _ => by
    have h0 : u = [] := List.eq_nil_of_length_eq_zero (by simpa using hu)
    subst h0
    refine ⟨rfl, rfl, rfl, fun x y u' h => by simp at h⟩
  | n + 1, x :: y :: u, hu, hg => by
    have hx := good_head hg
    have hy := good_head (good_tail hg)
    have hxy := good_pair hg
    have hgu := good_tail (good_tail hg)
    have hlen : u.length = 2 * n := by simp at hu; omega
    obtain ⟨ih1, ih2, ih3, ih4⟩ := pass2_props n u hlen hgu
    obtain ⟨hi1, hi2, hi3⟩ := img_props hI x y hx hy hxy
    have hpass : pass2 img (x :: y :: u) = img x y ++ pass2 img u := by
      interval_cases x <;> interval_cases y
      · simp only [pass2]
      · simp only [pass2]
      · simp only [pass2]
      · exact absurd ⟨rfl, rfl⟩ hxy
    have hne : img x y ≠ [] := by
      intro h
      rw [h] at hi3
      simp at hi3
      omega
    rw [hpass]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply good_append _ _ hi1 ih1
      rcases u with _ | ⟨z, _ | ⟨t, u'⟩⟩
      · simp [pass2]
      · simp at hlen
        omega
      · have hz := good_head (good_tail (good_tail hg))
        have ht := good_head (good_tail (good_tail (good_tail hg)))
        have hzt := good_pair (good_tail (good_tail hg))
        have hyz := good_pair (good_tail hg)
        rw [ih4 z t u' rfl]
        exact hI.junction x y z t hx hy hz ht hxy hzt hyz
    · rw [List.count_append, hi2, ih2]
      ring
    · rw [List.length_append, List.count_cons, List.count_cons]
      interval_cases x <;> interval_cases y <;> simp at hi3 ⊢ <;> omega
    · intro x' y' u' h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact List.head?_append_of_ne_nil _ hne
  | n + 1, [], hu, _ => by simp at hu
  | n + 1, [_], hu, _ => by simp at hu; omega

end Images

/-! ### Stable prefixes -/

/-- The longest prefix of even length. -/
def evenPart (l : List ℕ) : List ℕ := l.take (2 * (l.length / 2))

lemma evenPart_length (l : List ℕ) : (evenPart l).length = 2 * (l.length / 2) := by
  unfold evenPart
  rw [List.length_take]
  omega

/-- The stable prefixes: S 0 = 00 and S (k + 1) is the pass over the even prefix of S k. -/
def chain (img : ℕ → ℕ → List ℕ) : ℕ → List ℕ
  | 0 => [0, 0]
  | k + 1 => pass2 img (evenPart (chain img k))

section Chain

variable {img : ℕ → ℕ → List ℕ} (hI : Imgs img)
include hI

lemma chain_good : ∀ k, good (chain img k) = true
  | 0 => rfl
  | k + 1 => (pass2_props hI _ _ (evenPart_length _) (good_take _ _ (chain_good k))).1

lemma chain_head : ∀ k, ∃ t, chain img k = 0 :: 0 :: t
  | 0 => ⟨[], rfl⟩
  | k + 1 => by
    obtain ⟨t, ht⟩ := chain_head k
    have he : evenPart (chain img k) = 0 :: 0 :: t.take (2 * ((t.length + 2) / 2) - 2) := by
      rw [ht]
      unfold evenPart
      simp only [List.length_cons]
      rw [show 2 * ((t.length + 1 + 1) / 2) = (2 * ((t.length + 2) / 2) - 2) + 2 by omega]
      rfl
    refine ⟨1 :: 0 :: pass2 img (t.take (2 * ((t.length + 2) / 2) - 2)), ?_⟩
    show pass2 img (evenPart (chain img k)) = _
    rw [he]
    simp only [pass2, hI.h00, List.cons_append, List.nil_append]

end Chain

/-- A good word of length 2n has at most n letters 1. -/
lemma good_count_le : ∀ (n : ℕ) (u : List ℕ), u.length = 2 * n → good u = true → u.count 1 ≤ n
  | 0, u, hu, _ => by
    rw [List.eq_nil_of_length_eq_zero (by simpa using hu : u.length = 0)]
    simp
  | n + 1, x :: y :: u, hu, hg => by
    have ih := good_count_le n u (by simp at hu; omega) (good_tail (good_tail hg))
    have hxy := good_pair hg
    have hx := good_head hg
    have hy := good_head (good_tail hg)
    rw [List.count_cons, List.count_cons]
    interval_cases x <;> interval_cases y <;> simp <;> omega
  | n + 1, [], hu, _ => by simp at hu
  | n + 1, [_], hu, _ => by simp at hu; omega

section Chain2

variable {img : ℕ → ℕ → List ℕ} (hI : Imgs img)
include hI

lemma chain_length : ∀ k, k + 2 ≤ (chain img k).length
  | 0 => le_rfl
  | k + 1 => by
    have ih := chain_length k
    obtain ⟨t, ht⟩ := chain_head hI k
    set m := (chain img k).length / 2 with hm
    have hev := evenPart_length (chain img k)
    have hg := good_take _ (2 * m) (chain_good hI k)
    have h := (pass2_props hI m _ hev hg).2.2.1
    have hc : (evenPart (chain img k)).count 1 + 1 ≤ m := by
      have he : evenPart (chain img k) = 0 :: 0 :: t.take (2 * m - 2) := by
        unfold evenPart
        rw [← hm, ht, show 2 * m = (2 * m - 2) + 2 by
          have : 2 ≤ (chain img k).length := le_trans (by omega) ih
          omega]
        rfl
      have hlen : (t.take (2 * m - 2)).length = 2 * (m - 1) := by
        have h1 := congrArg List.length he
        rw [hev] at h1
        simp only [List.length_cons] at h1
        omega
      have hgood : good (t.take (2 * m - 2)) = true := by
        have := hg
        unfold evenPart at he
        rw [he] at this
        exact good_tail (good_tail this)
      have := good_count_le (m - 1) _ hlen hgood
      rw [he, List.count_cons, List.count_cons]
      have : 1 ≤ m := by
        have : 2 ≤ (chain img k).length := le_trans (by omega) ih
        omega
      simp
      omega
    show k + 1 + 2 ≤ (pass2 img (evenPart (chain img k))).length
    have hL : 2 ≤ (chain img k).length := le_trans (by omega) ih
    omega

end Chain2

lemma pass2_prefix (img : ℕ → ℕ → List ℕ) {u w : List ℕ} (h : u <+: w) (n : ℕ)
    (hu : u.length = 2 * n) (hg : good u = true) : pass2 img u <+: pass2 img w := by
  obtain ⟨r, rfl⟩ := h
  rw [pass2_append img n u r hu hg]
  exact List.prefix_append _ _

lemma evenPart_prefix (l : List ℕ) : evenPart l <+: l := List.take_prefix _ _

section Chain3

variable {img : ℕ → ℕ → List ℕ} (hI : Imgs img)
include hI

lemma chain_prefix_succ : ∀ k, chain img k <+: chain img (k + 1)
  | 0 => by
    show [0, 0] <+: pass2 img (evenPart [0, 0])
    rw [show evenPart [0, 0] = [0, 0] from rfl, show pass2 img [0, 0] = img 0 0 ++ [] from rfl,
      hI.h00]
    exact ⟨[1, 0], rfl⟩
  | k + 1 => by
    have ih := chain_prefix_succ k
    show pass2 img (evenPart (chain img k)) <+: pass2 img (evenPart (chain img (k + 1)))
    have hle : 2 * ((chain img k).length / 2) ≤ 2 * ((chain img (k + 1)).length / 2) := by
      have := ih.length_le
      omega
    have hpre : evenPart (chain img k) <+: evenPart (chain img (k + 1)) := by
      unfold evenPart
      obtain ⟨r, hr⟩ := ih
      rw [← hr] at hle ⊢
      have e1 : (chain img k).take (2 * ((chain img k).length / 2)) =
          (chain img k ++ r).take (2 * ((chain img k).length / 2)) :=
        (List.take_append_of_le_length (by omega)).symm
      rw [e1, show 2 * ((chain img k ++ r).length / 2) =
        2 * ((chain img k).length / 2) + (2 * ((chain img k ++ r).length / 2) -
          2 * ((chain img k).length / 2)) by omega, List.take_add]
      exact List.prefix_append _ _
    exact pass2_prefix img hpre _ (evenPart_length _) (good_take _ _ (chain_good hI k))

lemma chain_prefix {j k : ℕ} (h : j ≤ k) : chain img j <+: chain img k := by
  induction k, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k _ ih => exact ih.trans (chain_prefix_succ hI k)

/-- The stable prefixes are prefixes of the iterates of the pass, nested or not. -/
lemma chain_iter (it : ℕ → List ℕ) (h0 : it 0 = [0, 0]) (hs : ∀ k, it (k + 1) = pass2 img (it k)) :
    ∀ k, chain img k <+: it k
  | 0 => by rw [h0]; exact List.prefix_refl _
  | k + 1 => by
    rw [hs k]
    exact pass2_prefix img ((evenPart_prefix _).trans (chain_iter it h0 hs k)) _
      (evenPart_length _) (good_take _ _ (chain_good hI k))

/-- A word read off the iterates at index i + 1 is read off every stable prefix. -/
lemma W_chain (it : ℕ → List ℕ) (h0 : it 0 = [0, 0]) (hs : ∀ k, it (k + 1) = pass2 img (it k))
    (W : ℕ → ℕ) (hW : ∀ i, W i = (it (i + 1)).getD i 0) :
    ∀ k i, i < (chain img k).length → W i = (chain img k).getD i 0 := by
  intro k i hi
  have hi1 : i < (chain img (i + 1)).length := by
    have := chain_length hI (i + 1)
    omega
  obtain ⟨r, hr⟩ := chain_iter hI it h0 hs (i + 1)
  rw [hW i, ← hr, List.getD_append _ _ _ _ hi1]
  rcases le_total k (i + 1) with h | h
  · obtain ⟨s, hs'⟩ := chain_prefix hI h
    rw [← hs', List.getD_append _ _ _ _ hi]
  · obtain ⟨s, hs'⟩ := chain_prefix hI h
    rw [← hs', List.getD_append _ _ _ _ hi1]

end Chain3

/-! ### The recursion of the positions of 1 -/

lemma good_getD : ∀ (l : List ℕ) (i : ℕ), good l = true → i + 1 < l.length →
    ¬(l.getD i 0 = 1 ∧ l.getD (i + 1) 0 = 1)
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | x :: y :: l, 0, hg, _ => by simpa using good_pair hg
  | x :: y :: l, i + 1, hg, hi => by
    have := good_getD (y :: l) i (good_tail hg) (by simp at hi ⊢; omega)
    simpa using this

lemma pass2_pair (img : ℕ → ℕ → List ℕ) (x y : ℕ) (hx : x ≤ 1) (hy : y ≤ 1)
    (hxy : ¬(x = 1 ∧ y = 1)) : pass2 img [x, y] = img x y := by
  interval_cases x <;> interval_cases y
  · simp [pass2]
  · simp [pass2]
  · simp [pass2]
  · exact absurd ⟨rfl, rfl⟩ hxy

section Rec

variable {img : ℕ → ℕ → List ℕ} (hI : Imgs img)
include hI

/-- In the fixed point W, the n-th letter 1 is the 1 of the image of the n-th pair of W:
a(n) + O(2n - 2) + 3 = 4n + off(W(2n - 2), W(2n - 1)), with O the counting function of the 1s and
off the index of the 1 in an image. -/
theorem pair_image (W : ℕ → ℕ)
    (hW : ∀ k i, i < (chain img k).length → W i = (chain img k).getD i 0) (off : ℕ → ℕ → ℕ)
    (hoff : ∀ p q, p ≤ 1 → q ≤ 1 → ¬(p = 1 ∧ q = 1) → off p q < (img p q).length ∧
      (img p q).getD (off p q) 0 = 1 ∧ ((img p q).take (off p q)).count 1 = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ t, W t = 1 ∧ Nat.count (fun i => W i = 1) t = n - 1 ∧
      t + Nat.count (fun i => W i = 1) (2 * n - 2) + 4 =
        4 * n + off (W (2 * n - 2)) (W (2 * n - 1)) := by
  have hClen : 2 * n + 1 + 2 ≤ (chain img (2 * n + 1)).length := chain_length hI _
  have hCg : good (chain img (2 * n + 1)) = true := chain_good hI _
  set C := chain img (2 * n + 1) with hC
  set x := C.getD (2 * n - 2) 0 with hxdef
  set y := C.getD (2 * n - 1) 0 with hydef
  set u := C.take (2 * n - 2) with hu
  have hux : C.take (2 * n) = u ++ [x, y] := by
    have e : 2 * n = (2 * n - 2) + 2 := by omega
    rw [e, List.take_add]
    congr 1
    rw [hxdef, hydef, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    apply List.ext_getElem
    · simp
      omega
    · intro i h1 h2
      simp at h2
      interval_cases i
      · simp
      · simp
        congr 1
        omega
  have hulen : u.length = 2 * (n - 1) := by
    rw [hu, List.length_take]
    omega
  have hug : good u = true := good_take _ _ hCg
  have h2g : good (C.take (2 * n)) = true := good_take _ _ hCg
  have hxy3 : good (u ++ [x, y]) = true := by rw [← hux]; exact h2g
  have hxyl := good_letters _ hxy3
  have hx1 : x ≤ 1 := hxyl x (by simp)
  have hy1 : y ≤ 1 := hxyl y (by simp)
  have hxy : ¬(x = 1 ∧ y = 1) := good_pair (good_suffix u [x, y] hxy3)
  have hpass : pass2 img (C.take (2 * n)) = pass2 img u ++ img x y := by
    rw [hux, pass2_append img (n - 1) u [x, y] hulen hug, pass2_pair img x y hx1 hy1 hxy]
  have hpre : pass2 img (C.take (2 * n)) <+: chain img (2 * n + 1 + 1) := by
    show _ <+: pass2 img (evenPart C)
    refine pass2_prefix img ?_ n (by rw [List.length_take]; omega) h2g
    unfold evenPart
    rw [show 2 * (C.length / 2) = 2 * n + (2 * (C.length / 2) - 2 * n) by omega, List.take_add]
    exact List.prefix_append _ _
  set P := pass2 img u ++ img x y with hP
  have hWP : ∀ i, i < P.length → W i = P.getD i 0 := by
    intro i hi
    obtain ⟨r, hr⟩ := hpre
    rw [hpass] at hr
    have hi' : i < (chain img (2 * n + 1 + 1)).length := by
      rw [← hr, List.length_append]
      omega
    rw [hW _ i hi', ← hr, List.getD_append _ _ _ _ hi]
  obtain ⟨hp1, hp2, hp3, -⟩ := pass2_props hI (n - 1) u hulen hug
  obtain ⟨ho1, ho2, ho3⟩ := hoff x y hx1 hy1 hxy
  have hPlen : P.length = (pass2 img u).length + (img x y).length := by
    rw [hP, List.length_append]
  have hWt : W ((pass2 img u).length + off x y) = 1 := by
    rw [hWP _ (by omega), hP, List.getD_append_right _ _ _ _ (by omega)]
    simpa using ho2
  have hcount : Nat.count (fun i => W i = 1) ((pass2 img u).length + off x y) = n - 1 := by
    rw [count_eq_take W P 1 hWP _ (by omega), hP, List.take_append, List.take_of_length_le (by omega),
      List.count_append, hp2, show (pass2 img u).length + off x y - (pass2 img u).length = off x y by
        omega, ho3]
    rfl
  have hcu : Nat.count (fun i => W i = 1) (2 * n - 2) = u.count 1 :=
    count_eq_take W C 1 (hW _) (2 * n - 2) (by omega)
  have hWx : W (2 * n - 2) = x :=
    hW (2 * n + 1) _ (lt_of_lt_of_le (show 2 * n - 2 < 2 * n + 1 + 2 by omega) hClen)
  have hWy : W (2 * n - 1) = y :=
    hW (2 * n + 1) _ (lt_of_lt_of_le (show 2 * n - 1 < 2 * n + 1 + 2 by omega) hClen)
  refine ⟨(pass2 img u).length + off x y, hWt, hcount, ?_⟩
  rw [hcu, hWx, hWy]
  omega

/-- In the fixed point W, the n-th letter 1 is the 1 of the image of the n-th pair of W:
a(n) + O(2n - 2) + 3 = 4n + off(W(2n - 2), W(2n - 1)). -/
theorem rec_of_chain (W : ℕ → ℕ)
    (hW : ∀ k i, i < (chain img k).length → W i = (chain img k).getD i 0) (off : ℕ → ℕ → ℕ)
    (hoff : ∀ p q, p ≤ 1 → q ≤ 1 → ¬(p = 1 ∧ q = 1) → off p q < (img p q).length ∧
      (img p q).getD (off p q) 0 = 1 ∧ ((img p q).take (off p q)).count 1 = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    aPos W 1 n + Nat.count (fun i => W i = 1) (2 * n - 2) + 3 =
      4 * n + off (W (2 * n - 2)) (W (2 * n - 1)) := by
  obtain ⟨t, ht1, ht2, ht3⟩ := pair_image hI W hW off hoff n hn
  have hnth : Nat.nth (fun i => W i = 1) (n - 1) = t := by
    have h := Nat.nth_count (p := fun i => W i = 1) ht1
    rw [ht2] at h
    exact h
  unfold aPos
  rw [hnth]
  omega

theorem ones_infinite (W : ℕ → ℕ)
    (hW : ∀ k i, i < (chain img k).length → W i = (chain img k).getD i 0) (off : ℕ → ℕ → ℕ)
    (hoff : ∀ p q, p ≤ 1 → q ≤ 1 → ¬(p = 1 ∧ q = 1) → off p q < (img p q).length ∧
      (img p q).getD (off p q) 0 = 1 ∧ ((img p q).take (off p q)).count 1 = 0) :
    {i | W i = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨t, ht1, ht2, -⟩ := pair_image hI W hW off hoff (B + 2) (by omega)
  have h1 : t ≤ B := hB ht1
  have h2 := Nat.count_le (p := fun i => W i = 1) (n := t)
  omega

lemma W_letters (W : ℕ → ℕ)
    (hW : ∀ k i, i < (chain img k).length → W i = (chain img k).getD i 0) (i : ℕ) : W i ≤ 1 := by
  have hi : i < (chain img (i + 1)).length := by have := chain_length hI (i + 1); omega
  rw [hW _ i hi, List.getD_eq_getElem _ _ hi]
  exact good_letters _ (chain_good hI _) _ (List.getElem_mem hi)

lemma W_no11 (W : ℕ → ℕ)
    (hW : ∀ k i, i < (chain img k).length → W i = (chain img k).getD i 0) (n : ℕ) :
    ¬(W (2 * n) = 1 ∧ W (2 * n + 1) = 1) := by
  have hl : 2 * n + 1 < (chain img (2 * n + 1)).length := by
    have := chain_length hI (2 * n + 1)
    omega
  rw [hW (2 * n + 1) (2 * n) (by omega), hW (2 * n + 1) (2 * n + 1) hl]
  exact good_getD (chain img (2 * n + 1)) (2 * n) (chain_good hI _) hl

end Rec

lemma W_zero (img : ℕ → ℕ → List ℕ) (W : ℕ → ℕ)
    (hW : ∀ k i, i < (chain img k).length → W i = (chain img k).getD i 0) : W 0 = 0 := by
  rw [hW 0 0 (by simp [chain])]
  rfl

lemma zeros_infinite (W : ℕ → ℕ) (hW01 : ∀ i, W i ≤ 1)
    (hW11 : ∀ n, ¬(W (2 * n) = 1 ∧ W (2 * n + 1) = 1)) : {i | W i = 0}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have h0 := hW01 (2 * B + 2)
  have h1 := hW01 (2 * B + 3)
  have h11 := hW11 (B + 1)
  rw [show 2 * (B + 1) = 2 * B + 2 by ring, show 2 * B + 2 + 1 = 2 * B + 3 by ring] at h11
  by_cases ha : W (2 * B + 2) = 0
  · have := hB (show 2 * B + 2 ∈ {i | W i = 0} from ha)
    omega
  · have hb : W (2 * B + 3) = 0 := by omega
    have := hB (show 2 * B + 3 ∈ {i | W i = 0} from hb)
    omega

/-! ### The reference b(n) = floor(n (2 + sqrt 2)) -/

/-- b(n) = 2n + isqrt(2n^2) = floor(n (2 + sqrt 2)). -/
def bB (n : ℕ) : ℕ := 2 * n + Nat.sqrt (2 * n ^ 2)

/-- CB(N) = N - isqrt((N + 1)^2 / 2), the number of n >= 1 with b(n) <= N (`le_CB_iff`). -/
def CB (N : ℕ) : ℕ := N - Nat.sqrt ((N + 1) ^ 2 / 2)

/-- CB is the counting function of b: with x = N + 1 - n, both sides say that
(x - n)^2 - 2n^2 = 2x^2 - (N + 1)^2 is positive. -/
lemma le_CB_iff (n N : ℕ) (hn : 1 ≤ n) : bB n ≤ N ↔ n ≤ CB N := by
  unfold bB CB
  constructor
  · intro h
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le h
    have hs : 2 * n ^ 2 < (Nat.sqrt (2 * n ^ 2) + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have hlt : Nat.sqrt ((N + 1) ^ 2 / 2) < n + Nat.sqrt (2 * n ^ 2) + e + 1 := by
      rw [Nat.sqrt_lt', Nat.div_lt_iff_lt_mul (by norm_num), he]
      nlinarith
    omega
  · intro h
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le h
    have hr : (N + 1) ^ 2 / 2 < (Nat.sqrt ((N + 1) ^ 2 / 2) + 1) ^ 2 := Nat.lt_succ_sqrt' _
    rw [Nat.div_lt_iff_lt_mul (by norm_num)] at hr
    set r := Nat.sqrt ((N + 1) ^ 2 / 2) with hrdef
    have hN : N = n + r + e := by omega
    rw [hN] at hr
    have hxn : n ≤ r + e := by
      by_contra hc
      nlinarith
    have hs : Nat.sqrt (2 * n ^ 2) < r + e + 1 - n := by
      rw [Nat.sqrt_lt']
      obtain ⟨f, hf⟩ := Nat.exists_eq_add_of_le hxn
      have hr' : (n + (r + e) + 1) ^ 2 < 2 * (r + e + 1) ^ 2 := by
        have : (r + 1) ^ 2 ≤ (r + e + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        rw [show n + (r + e) + 1 = n + r + e + 1 by ring]
        omega
      rw [hf] at hr'
      rw [hf, show n + f + 1 - n = f + 1 by omega]
      nlinarith
    omega

lemma bB_succ (n : ℕ) : bB n + 3 ≤ bB (n + 1) := by
  unfold bB
  have h1 := Nat.sqrt_le' (2 * n ^ 2)
  have h2 : Nat.sqrt (2 * n ^ 2) < 2 * n + 1 := by
    rw [Nat.sqrt_lt', show (2 * n + 1) ^ 2 = 2 * n ^ 2 + (2 * n ^ 2 + 4 * n + 1) by ring]
    exact Nat.lt_add_of_pos_right (by positivity)
  have h3 : Nat.sqrt (2 * n ^ 2) + 1 ≤ Nat.sqrt (2 * (n + 1) ^ 2) := by
    rw [Nat.le_sqrt']
    nlinarith [sq_nonneg n]
  omega

lemma bB_mono {j k : ℕ} (h : j ≤ k) : bB j ≤ bB k := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => have := bB_succ k; omega

lemma two_mul_lt_bB (n : ℕ) (hn : 1 ≤ n) : 2 * n < bB n := by
  unfold bB
  have : 1 ≤ Nat.sqrt (2 * n ^ 2) := by
    rw [Nat.le_sqrt']
    nlinarith
  omega

lemma CB_mono (N : ℕ) : CB N ≤ CB (N + 1) := by
  rcases Nat.eq_zero_or_pos (CB N) with h | h
  · omega
  · exact (le_CB_iff _ _ h).mp (le_trans ((le_CB_iff _ _ h).mpr le_rfl) (Nat.le_succ N))

lemma CB_two (N : ℕ) : CB (N + 2) ≤ CB N + 1 := by
  rcases le_or_gt (CB (N + 2)) 1 with h | h
  · omega
  · have hb := (le_CB_iff (CB (N + 2)) (N + 2) (by omega)).mpr le_rfl
    have hs := bB_succ (CB (N + 2) - 1)
    rw [show CB (N + 2) - 1 + 1 = CB (N + 2) by omega] at hs
    have := (le_CB_iff (CB (N + 2) - 1) N (by omega)).mp (by omega)
    omega

lemma CB_odd (n : ℕ) (hn : 1 ≤ n) : CB (2 * n - 1) + Nat.sqrt (2 * n ^ 2) + 1 = 2 * n := by
  unfold CB
  rw [show 2 * n - 1 + 1 = 2 * n by omega, show (2 * n) ^ 2 / 2 = 2 * n ^ 2 by
    rw [show (2 * n) ^ 2 = 2 * (2 * n ^ 2) by ring]; omega]
  have : Nat.sqrt (2 * n ^ 2) < 2 * n := by
    rw [Nat.sqrt_lt']
    nlinarith
  omega

/-- b satisfies the two-block recursion with the offsets 00: 2, 01: 2, 10: 1. -/
lemma bB_rec (n : ℕ) (hn : 1 ≤ n) : bB n + CB (2 * n - 1) + 1 = 4 * n := by
  have := CB_odd n hn
  unfold bB
  omega

/-! ### The comparison -/

lemma aPos_le_iff (W : ℕ → ℕ) (b : ℕ) (hinf : {i | W i = b}.Infinite) (n N : ℕ) (hn : 1 ≤ n) :
    aPos W b n ≤ N ↔ n ≤ Nat.count (fun i => W i = b) N := by
  unfold aPos
  have := Nat.lt_nth_iff_count_lt (p := fun i => W i = b) hinf (a := n - 1) (b := N)
  constructor
  · intro h
    have := this.mpr (by omega)
    omega
  · intro h
    have := this.mp (by omega)
    omega

/-- If W satisfies the two-block recursion with offsets `off` and the table holds, then every
position of 1 is at most b(n) = floor(n (2 + sqrt 2)). -/
theorem compare (W : ℕ → ℕ) (hinf : {i | W i = 1}.Infinite) (hW01 : ∀ i, W i ≤ 1)
    (hW11 : ∀ n, ¬(W (2 * n) = 1 ∧ W (2 * n + 1) = 1)) (off : ℕ → ℕ → ℕ)
    (hrec : ∀ n, 1 ≤ n → aPos W 1 n + Nat.count (fun i => W i = 1) (2 * n - 2) + 3 =
      4 * n + off (W (2 * n - 2)) (W (2 * n - 1)))
    (htable : ∀ s1 s2 t1 t2 D : ℕ, s1 ≤ 1 → s2 ≤ 1 → t1 ≤ 1 → t2 ≤ 1 → s1 + s2 ≤ 1 →
      t1 + t2 ≤ 1 → t1 ≤ D + s1 → t1 + t2 ≤ D + s1 + s2 → off s1 s2 + t1 ≤ 2 + D) :
    ∀ n, 1 ≤ n → aPos W 1 n ≤ bB n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hcount : ∀ N, N < bB n → CB N ≤ Nat.count (fun i => W i = 1) N := by
      intro N hN
      rcases Nat.eq_zero_or_pos (CB N) with h0 | hpos
      · omega
      · have hb := (le_CB_iff _ _ hpos).mpr le_rfl
        have hc : CB N < n := by
          by_contra hc
          have := bB_mono (show n ≤ CB N by omega)
          omega
        have := ih (CB N) hc hpos
        exact (aPos_le_iff W 1 hinf _ _ hpos).mp (by omega)
    have h2n := two_mul_lt_bB n hn
    have c0 := hcount (2 * n - 2) (by omega)
    have c1 := hcount (2 * n - 1) (by omega)
    have c2 := hcount (2 * n) (by omega)
    have hs1 := hW01 (2 * n - 2)
    have hs2 := hW01 (2 * n - 1)
    have hs12 : W (2 * n - 2) + W (2 * n - 1) ≤ 1 := by
      have := hW11 (n - 1)
      rw [show 2 * (n - 1) = 2 * n - 2 by omega, show 2 * n - 2 + 1 = 2 * n - 1 by omega] at this
      omega
    have k1 : Nat.count (fun i => W i = 1) (2 * n - 1) =
        Nat.count (fun i => W i = 1) (2 * n - 2) + W (2 * n - 2) := by
      rw [show 2 * n - 1 = 2 * n - 2 + 1 by omega, Nat.count_succ]
      split_ifs <;> omega
    have k2 : Nat.count (fun i => W i = 1) (2 * n) =
        Nat.count (fun i => W i = 1) (2 * n - 1) + W (2 * n - 1) := by
      have e := Nat.count_succ (fun i => W i = 1) (2 * n - 1)
      rw [show 2 * n - 1 + 1 = 2 * n by omega] at e
      rw [e]
      split_ifs <;> omega
    have m1 := CB_mono (2 * n - 2)
    have m2 := CB_mono (2 * n - 1)
    have m3 := CB_two (2 * n - 2)
    rw [show 2 * n - 2 + 1 = 2 * n - 1 by omega] at m1
    rw [show 2 * n - 1 + 1 = 2 * n by omega] at m2
    rw [show 2 * n - 2 + 2 = 2 * n by omega] at m3
    have hr := hrec n hn
    have hb := bB_rec n hn
    have ht := htable (W (2 * n - 2)) (W (2 * n - 1)) (CB (2 * n - 1) - CB (2 * n - 2))
      (CB (2 * n) - CB (2 * n - 1)) (Nat.count (fun i => W i = 1) (2 * n - 2) - CB (2 * n - 2))
      hs1 hs2 (by omega) (by omega) hs12 (by omega) (by omega) (by omega)
    omega

/-- For any nonnegative offsets, the n-th 1 comes after b(n - 1). -/
theorem lower (W : ℕ → ℕ) (hinf : {i | W i = 1}.Infinite) (hW01 : ∀ i, W i ≤ 1)
    (hW11 : ∀ n, ¬(W (2 * n) = 1 ∧ W (2 * n + 1) = 1))
    (hrec : ∀ n, 1 ≤ n → 4 * n ≤ aPos W 1 n + Nat.count (fun i => W i = 1) (2 * n - 2) + 3) :
    ∀ n, 1 ≤ n → bB (n - 1) < aPos W 1 n := by
  have hpairs : ∀ m, Nat.count (fun i => W i = 1) (2 * m) ≤ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.count_succ, Nat.count_succ]
      have := hW11 m
      have h0 := hW01 (2 * m)
      have h1 := hW01 (2 * m + 1)
      split_ifs <;> omega
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have : n = 1 := by omega
      subst this
      unfold aPos bB
      simp
    · have hc : Nat.count (fun i => W i = 1) (2 * n - 2) ≤ 1 + CB (2 * n - 3) := by
        rcases le_or_gt (Nat.count (fun i => W i = 1) (2 * n - 2)) 1 with hle | hgt
        · omega
        · set c := Nat.count (fun i => W i = 1) (2 * n - 2) with hcdef
          have hcn : c < n := by
            have := hpairs (n - 1)
            rw [show 2 * (n - 1) = 2 * n - 2 by omega] at this
            omega
          have ha : aPos W 1 c ≤ 2 * n - 2 := (aPos_le_iff W 1 hinf _ _ (by omega)).mpr le_rfl
          have := ih c hcn (by omega)
          have := (le_CB_iff (c - 1) (2 * n - 3) (by omega)).mp (by omega)
          omega
      have hr := hrec n hn
      have hcb := CB_odd (n - 1) (by omega)
      rw [show 2 * (n - 1) - 1 = 2 * n - 3 by omega] at hcb
      unfold bB
      omega

/-! ### The windows of the positions of 1 and of 0 -/

lemma sqrt_two_mul_lt (n : ℕ) (hn : 1 ≤ n) : (Nat.sqrt (2 * n ^ 2) : ℝ) < n * Real.sqrt 2 := by
  have h1 := Nat.sqrt_le' (2 * n ^ 2)
  have hne : Nat.sqrt (2 * n ^ 2) ^ 2 ≠ 2 * n ^ 2 := by
    intro h
    have hr : Real.sqrt 2 = (Nat.sqrt (2 * n ^ 2) : ℝ) / n := by
      rw [eq_div_iff (by positivity)]
      have : ((Nat.sqrt (2 * n ^ 2) : ℕ) : ℝ) ^ 2 = 2 * (n : ℝ) ^ 2 := by exact_mod_cast h
      have hs : (0 : ℝ) ≤ (Nat.sqrt (2 * n ^ 2) : ℝ) := Nat.cast_nonneg _
      rw [← Real.sqrt_sq hs, this, Real.sqrt_mul (by norm_num), Real.sqrt_sq (Nat.cast_nonneg _)]
    exact irrational_sqrt_two (⟨(Nat.sqrt (2 * n ^ 2) : ℚ) / n, by rw [hr]; push_cast; ring⟩)
  have hlt : ((Nat.sqrt (2 * n ^ 2) : ℕ) : ℝ) ^ 2 < ((n : ℝ) * Real.sqrt 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    have : Nat.sqrt (2 * n ^ 2) ^ 2 < 2 * n ^ 2 := lt_of_le_of_ne h1 hne
    have : ((Nat.sqrt (2 * n ^ 2) ^ 2 : ℕ) : ℝ) < ((2 * n ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt

lemma sqrt_two_mul_gt (m : ℕ) : (m : ℝ) * Real.sqrt 2 < Nat.sqrt (2 * m ^ 2) + 1 := by
  have h := Nat.lt_succ_sqrt' (2 * m ^ 2)
  have h' : ((2 * m ^ 2 : ℕ) : ℝ) < ((Nat.sqrt (2 * m ^ 2) + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast h
  push_cast at h'
  have hlt : ((m : ℝ) * Real.sqrt 2) ^ 2 < ((Nat.sqrt (2 * m ^ 2) : ℝ) + 1) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt

/-- The window of the positions of 1: 0 < (2 + sqrt 2) n - a(n) < 2 + sqrt 2. -/
theorem ones_window (W : ℕ → ℕ) (hinf : {i | W i = 1}.Infinite) (hW01 : ∀ i, W i ≤ 1)
    (hW11 : ∀ n, ¬(W (2 * n) = 1 ∧ W (2 * n + 1) = 1)) (off : ℕ → ℕ → ℕ)
    (hrec : ∀ n, 1 ≤ n → aPos W 1 n + Nat.count (fun i => W i = 1) (2 * n - 2) + 3 =
      4 * n + off (W (2 * n - 2)) (W (2 * n - 1)))
    (htable : ∀ s1 s2 t1 t2 D : ℕ, s1 ≤ 1 → s2 ≤ 1 → t1 ≤ 1 → t2 ≤ 1 → s1 + s2 ≤ 1 →
      t1 + t2 ≤ 1 → t1 ≤ D + s1 → t1 + t2 ≤ D + s1 + s2 → off s1 s2 + t1 ≤ 2 + D)
    (n : ℕ) (hn : 1 ≤ n) :
    0 < (2 + Real.sqrt 2) * n - aPos W 1 n ∧ (2 + Real.sqrt 2) * n - aPos W 1 n < 2 + Real.sqrt 2 := by
  have hu := compare W hinf hW01 hW11 off hrec htable n hn
  have hl := lower W hinf hW01 hW11 (fun k hk => by have := hrec k hk; omega) n hn
  have hu' : (aPos W 1 n : ℝ) ≤ 2 * n + Nat.sqrt (2 * n ^ 2) := by
    unfold bB at hu
    exact_mod_cast hu
  have hl' : 2 * ((n - 1 : ℕ) : ℝ) + Nat.sqrt (2 * (n - 1) ^ 2) + 1 ≤ aPos W 1 n := by
    unfold bB at hl
    exact_mod_cast hl
  have h1 := sqrt_two_mul_lt n hn
  have h2 := sqrt_two_mul_gt (n - 1)
  have hn1 : ((n - 1 : ℕ) : ℝ) = n - 1 := by push_cast [hn]; ring
  rw [hn1] at hl' h2
  constructor <;> nlinarith

/-- From the window: a(n)/n -> 2 + sqrt 2. -/
theorem ones_limit (W : ℕ → ℕ)
    (hwin : ∀ n, 1 ≤ n → 0 < (2 + Real.sqrt 2) * n - aPos W 1 n ∧
      (2 + Real.sqrt 2) * n - aPos W 1 n < 2 + Real.sqrt 2) :
    Tendsto (fun n : ℕ => (aPos W 1 n : ℝ) / n) atTop (𝓝 (2 + Real.sqrt 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => (2 + Real.sqrt 2) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨h1, h2⟩ := hwin n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.norm_eq_abs, show (aPos W 1 n : ℝ) / n - (2 + Real.sqrt 2) =
    -(((2 + Real.sqrt 2) * n - aPos W 1 n) / n) by field_simp; ring, abs_neg,
    abs_of_pos (div_pos h1 hnpos)]
  exact div_le_div_of_nonneg_right h2.le hnpos.le

/-- The window of the positions of 0: 2n^2 <= (a0(n) + 1)^2 and a0(n)^2 < 2 (n + 1)^2. -/
theorem zeros_window (W : ℕ → ℕ) (hinf : {i | W i = 1}.Infinite) (hW01 : ∀ i, W i ≤ 1)
    (hW11 : ∀ n, ¬(W (2 * n) = 1 ∧ W (2 * n + 1) = 1)) (off : ℕ → ℕ → ℕ)
    (hrec : ∀ n, 1 ≤ n → aPos W 1 n + Nat.count (fun i => W i = 1) (2 * n - 2) + 3 =
      4 * n + off (W (2 * n - 2)) (W (2 * n - 1)))
    (htable : ∀ s1 s2 t1 t2 D : ℕ, s1 ≤ 1 → s2 ≤ 1 → t1 ≤ 1 → t2 ≤ 1 → s1 + s2 ≤ 1 →
      t1 + t2 ≤ 1 → t1 ≤ D + s1 → t1 + t2 ≤ D + s1 + s2 → off s1 s2 + t1 ≤ 2 + D)
    (hinf0 : {i | W i = 0}.Infinite) (n : ℕ) (hn : 1 ≤ n) :
    2 * n ^ 2 ≤ (aPos W 0 n + 1) ^ 2 ∧ aPos W 0 n ^ 2 < 2 * (n + 1) ^ 2 := by
  obtain ⟨N, hN⟩ : ∃ N, N = aPos W 0 n := ⟨_, rfl⟩
  rw [← hN]
  have hZ : Nat.count (fun i => W i = 0) N = n := by
    have hZp := Nat.count_nth_of_infinite hinf0 (n - 1)
    have hWp : W (Nat.nth (fun i => W i = 0) (n - 1)) = 0 := Nat.nth_mem_of_infinite hinf0 (n - 1)
    rw [hN]
    unfold aPos
    rw [Nat.count_succ, if_pos hWp, hZp]
    omega
  have h01 := count01_nat W hW01 N
  have hN1 : 1 ≤ N := by rw [hN]; unfold aPos; omega
  -- at most 1 + CB(N - 1) letters 1 before N
  have hup : Nat.count (fun i => W i = 1) N ≤ 1 + CB (N - 1) := by
    rcases le_or_gt (Nat.count (fun i => W i = 1) N) 1 with hle | hgt
    · omega
    · set c := Nat.count (fun i => W i = 1) N
      have ha : aPos W 1 c ≤ N := (aPos_le_iff W 1 hinf _ _ (by omega)).mpr le_rfl
      have hl := lower W hinf hW01 hW11 (fun k hk => by have := hrec k hk; omega) c (by omega)
      have := (le_CB_iff (c - 1) (N - 1) (by omega)).mp (by omega)
      omega
  -- at least CB(N) letters 1 before N
  have hlo : CB N ≤ Nat.count (fun i => W i = 1) N := by
    rcases Nat.eq_zero_or_pos (CB N) with h0 | hpos
    · omega
    · have hb := (le_CB_iff _ _ hpos).mpr le_rfl
      have hu := compare W hinf hW01 hW11 off hrec htable (CB N) hpos
      exact (aPos_le_iff W 1 hinf _ _ hpos).mp (by omega)
  unfold CB at hup hlo
  rw [show N - 1 + 1 = N by omega] at hup
  obtain ⟨r1, hr1⟩ : ∃ r, r = Nat.sqrt ((N + 1) ^ 2 / 2) := ⟨_, rfl⟩
  obtain ⟨r0, hr0⟩ : ∃ r, r = Nat.sqrt (N ^ 2 / 2) := ⟨_, rfl⟩
  rw [← hr1] at hlo
  rw [← hr0] at hup
  constructor
  · -- n <= isqrt((N + 1)^2 / 2)
    have hs : n ≤ r1 := by omega
    rw [hr1, Nat.le_sqrt'] at hs
    have := Nat.div_mul_le_self ((N + 1) ^ 2) 2
    nlinarith
  · -- isqrt(N^2 / 2) <= n
    have hr0N : r0 < N := by
      rw [hr0, Nat.sqrt_lt']
      exact Nat.div_lt_self (by positivity) (by norm_num)
    have hs : r0 < n + 1 := by omega
    rw [hr0, Nat.sqrt_lt', Nat.div_lt_iff_lt_mul (by norm_num)] at hs
    linarith

end SRGen

/-!
# SRGen two-block maps with exact Beatty positions, and the Pell word

When the offsets of a two-block map turn its recursion into that of b(n) = 2n + isqrt(2n^2) =
floor(n (2 + sqrt 2)), the positions of 1 are b(n) exactly (`exact_bB`); with the constant offset 2
they are b(n + 1) - 3 (`exact_bB_shift`). The Pell word, the fixed point of 0 -> 001, 1 -> 0, is the
fixed point of the two-block map 00 -> 0010, 01 -> 001, 10 -> 010 (Dekking and Keane,
arXiv:2202.13548, Theorem 4): the pass commutes with the Pell morphism on good words of even length
(`pass2_pellM`, checked on the three pairs), so every stable prefix of the map is a prefix of an image
of 0 (`chainDK_prefix`), and the 1s of the Pell word are at the b(n) (`pellP_one_iff`). A map whose
1s are at b(n + 1) - 3 is the Pell word without its first three letters (`shift_of_rec`).
-/

namespace SRGen

/-! ### Exact positions -/

lemma count_pairs (W : ℕ → ℕ) (hW01 : ∀ i, W i ≤ 1)
    (hW11 : ∀ n, ¬(W (2 * n) = 1 ∧ W (2 * n + 1) = 1)) :
    ∀ m, Nat.count (fun i => W i = 1) (2 * m) ≤ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.count_succ, Nat.count_succ]
    have := hW11 m
    have h0 := hW01 (2 * m)
    have h1 := hW01 (2 * m + 1)
    split_ifs <;> omega

lemma bB_one : bB 1 = 3 := by
  have h : Nat.sqrt 2 = 1 := Nat.sqrt_add_eq 1 (a := 1) (by norm_num)
  simp [bB, h]

/-- If the positions of 1 satisfy a(n) + O(2n - 1) + 1 = 4n, the recursion of b (`bB_rec`), they
are the b(n). -/
theorem exact_bB (W : ℕ → ℕ) (hinf : {i | W i = 1}.Infinite) (hW01 : ∀ i, W i ≤ 1)
    (hW11 : ∀ n, ¬(W (2 * n) = 1 ∧ W (2 * n + 1) = 1))
    (hrec : ∀ n, 1 ≤ n → aPos W 1 n + Nat.count (fun i => W i = 1) (2 * n - 1) + 1 = 4 * n) :
    ∀ n, 1 ≤ n → aPos W 1 n = bB n := by
  have hpairs := count_pairs W hW01 hW11
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hcle : Nat.count (fun i => W i = 1) (2 * n - 1) ≤ n :=
      le_trans (Nat.count_monotone _ (show 2 * n - 1 ≤ 2 * n by omega)) (hpairs n)
    have hr := hrec n hn
    have hclt : Nat.count (fun i => W i = 1) (2 * n - 1) < n := by
      by_contra h
      have := (aPos_le_iff W 1 hinf n (2 * n - 1) hn).mpr (by omega)
      omega
    have hCBlt : CB (2 * n - 1) < n := by
      by_contra h
      have := (le_CB_iff n (2 * n - 1) hn).mpr (by omega)
      have := two_mul_lt_bB n hn
      omega
    have key : Nat.count (fun i => W i = 1) (2 * n - 1) = CB (2 * n - 1) := by
      apply le_antisymm
      · rcases Nat.eq_zero_or_pos (Nat.count (fun i => W i = 1) (2 * n - 1)) with h0 | hpos
        · omega
        · have ha := (aPos_le_iff W 1 hinf _ (2 * n - 1) hpos).mpr le_rfl
          rw [ih _ hclt hpos] at ha
          exact (le_CB_iff _ (2 * n - 1) hpos).mp ha
      · rcases Nat.eq_zero_or_pos (CB (2 * n - 1)) with h0 | hpos
        · omega
        · have hb := (le_CB_iff _ (2 * n - 1) hpos).mpr le_rfl
          rw [← ih _ hCBlt hpos] at hb
          exact (aPos_le_iff W 1 hinf _ (2 * n - 1) hpos).mp hb
    have hb := bB_rec n hn
    omega

/-- If the positions of 1 satisfy a(n) + O(2n - 2) + 3 = 4n + 2 (every offset 2), they are the
b(n + 1) - 3. -/
theorem exact_bB_shift (W : ℕ → ℕ) (hinf : {i | W i = 1}.Infinite) (hW01 : ∀ i, W i ≤ 1)
    (hW11 : ∀ n, ¬(W (2 * n) = 1 ∧ W (2 * n + 1) = 1))
    (hrec : ∀ n, 1 ≤ n → aPos W 1 n + Nat.count (fun i => W i = 1) (2 * n - 2) + 3 = 4 * n + 2) :
    ∀ n, 1 ≤ n → aPos W 1 n = bB (n + 1) - 3 := by
  have hpairs := count_pairs W hW01 hW11
  have hb3 : ∀ k, 1 ≤ k → 3 ≤ bB k := fun k hk => by have := two_mul_lt_bB k hk; omega
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hcle : Nat.count (fun i => W i = 1) (2 * n - 2) ≤ n - 1 := by
      have := hpairs (n - 1)
      rwa [show 2 * (n - 1) = 2 * n - 2 by omega] at this
    have hr := hrec n hn
    have hCB1 : 1 ≤ CB (2 * n + 1) := (le_CB_iff 1 (2 * n + 1) le_rfl).mp (by rw [bB_one]; omega)
    have hCBle : CB (2 * n + 1) ≤ n := by
      by_contra h
      have := (le_CB_iff (n + 1) (2 * n + 1) (by omega)).mpr (by omega)
      have := two_mul_lt_bB (n + 1) (by omega)
      omega
    have key : Nat.count (fun i => W i = 1) (2 * n - 2) + 1 = CB (2 * n + 1) := by
      apply le_antisymm
      · rcases Nat.eq_zero_or_pos (Nat.count (fun i => W i = 1) (2 * n - 2)) with h0 | hpos
        · omega
        · have ha := (aPos_le_iff W 1 hinf _ (2 * n - 2) hpos).mpr le_rfl
          rw [ih _ (by omega) hpos] at ha
          have := hb3 (Nat.count (fun i => W i = 1) (2 * n - 2) + 1) (by omega)
          exact (le_CB_iff _ (2 * n + 1) (by omega)).mp (by omega)
      · rcases Nat.eq_zero_or_pos (CB (2 * n + 1) - 1) with h0 | hpos
        · omega
        · have hb := (le_CB_iff (CB (2 * n + 1) - 1 + 1) (2 * n + 1) (by omega)).mpr (by omega)
          have ha := ih (CB (2 * n + 1) - 1) (by omega) hpos
          have hle : aPos W 1 (CB (2 * n + 1) - 1) ≤ 2 * n - 2 := by
            rw [ha]
            have := hb3 (CB (2 * n + 1) - 1 + 1) (by omega)
            omega
          have := (aPos_le_iff W 1 hinf _ (2 * n - 2) hpos).mp hle
          omega
    have hb := bB_rec (n + 1) (by omega)
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega] at hb
    omega

/-- A letter is 1 exactly where a position of 1 falls. -/
lemma one_iff_aPos (W : ℕ → ℕ) (hinf : {i | W i = 1}.Infinite) (i : ℕ) :
    W i = 1 ↔ ∃ n, 1 ≤ n ∧ aPos W 1 n = i + 1 := by
  constructor
  · intro h
    refine ⟨Nat.count (fun i => W i = 1) i + 1, by omega, ?_⟩
    unfold aPos
    rw [Nat.add_sub_cancel, Nat.nth_count (p := fun i => W i = 1) h]
  · rintro ⟨n, hn, h⟩
    unfold aPos at h
    have hm := Nat.nth_mem_of_infinite hinf (n - 1)
    rw [show Nat.nth (fun i => W i = 1) (n - 1) = i by omega] at hm
    exact hm

/-! ### The Pell morphism -/

/-- The Pell morphism 0 -> 001, 1 -> 0 on lists (other letters are copied). -/
def pellM : List ℕ → List ℕ
  | 0 :: l => 0 :: 0 :: 1 :: pellM l
  | 1 :: l => 0 :: pellM l
  | x :: l => x :: pellM l
  | [] => []

lemma pellM_append : ∀ u v : List ℕ, pellM (u ++ v) = pellM u ++ pellM v
  | [], _ => rfl
  | 0 :: u, v => by
    show 0 :: 0 :: 1 :: pellM (u ++ v) = 0 :: 0 :: 1 :: (pellM u ++ pellM v)
    rw [pellM_append u v]
  | 1 :: u, v => by
    show 0 :: pellM (u ++ v) = 0 :: (pellM u ++ pellM v)
    rw [pellM_append u v]
  | (x + 2) :: u, v => by
    show (x + 2) :: pellM (u ++ v) = (x + 2) :: (pellM u ++ pellM v)
    rw [pellM_append u v]

lemma pellM_head : ∀ l : List ℕ, good l = true → (pellM l).head? = none ∨ (pellM l).head? = some 0
  | [], _ => Or.inl rfl
  | x :: l, h => by
    have hx := good_head h
    interval_cases x
    · exact Or.inr rfl
    · exact Or.inr rfl

lemma pellM_good : ∀ l : List ℕ, good l = true → good (pellM l) = true
  | [], _ => rfl
  | x :: l, h => by
    have hx := good_head h
    have ih := pellM_good l (good_tail h)
    have hd := pellM_head l (good_tail h)
    interval_cases x
    · show good ([0, 0, 1] ++ pellM l) = true
      apply good_append _ _ (by decide) ih
      rcases hd with hd | hd <;> simp [hd]
    · show good ([0] ++ pellM l) = true
      exact good_append _ _ (by decide) ih (by simp)

lemma pellM_length : ∀ l : List ℕ, good l = true → (pellM l).length = l.length + 2 * l.count 0
  | [], _ => rfl
  | x :: l, h => by
    have hx := good_head h
    have ih := pellM_length l (good_tail h)
    interval_cases x
    · have h1 : (0 :: l).count 0 = l.count 0 + 1 := by simp
      show (0 :: 0 :: 1 :: pellM l).length = (0 :: l).length + 2 * (0 :: l).count 0
      rw [h1]
      simp only [List.length_cons, ih]
      omega
    · have h1 : (1 :: l).count 0 = l.count 0 := by simp
      show (0 :: pellM l).length = (1 :: l).length + 2 * (1 :: l).count 0
      rw [h1]
      simp only [List.length_cons, ih]
      omega

lemma pellM_iterate_append (m : ℕ) : ∀ u v : List ℕ, pellM^[m] (u ++ v) = pellM^[m] u ++ pellM^[m] v := by
  induction m with
  | zero => intro u v; rfl
  | succ m ih =>
    intro u v
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      pellM_append]

lemma pellM_iterate_good (m : ℕ) (u : List ℕ) (hu : good u = true) : good (pellM^[m] u) = true := by
  induction m with
  | zero => exact hu
  | succ m ih => rw [Function.iterate_succ_apply']; exact pellM_good _ ih

lemma pellM_iterate_even (m : ℕ) (u : List ℕ) (hu : good u = true) (n : ℕ) (hn : u.length = 2 * n) :
    ∃ k, (pellM^[m] u).length = 2 * k := by
  induction m with
  | zero => exact ⟨n, hn⟩
  | succ m ih =>
    obtain ⟨k, hk⟩ := ih
    rw [Function.iterate_succ_apply', pellM_length _ (pellM_iterate_good m u hu), hk]
    exact ⟨k + (pellM^[m] u).count 0, by ring⟩

/-! ### The two-block map of the Pell word -/

/-- The images of 00, 01 and 10 under the two-block map whose fixed point is the Pell word. -/
def imgDK (p q : ℕ) : List ℕ := if p = 0 then (if q = 0 then [0, 0, 1, 0] else [0, 0, 1]) else [0, 1, 0]

lemma hIDK : Imgs imgDK := by
  refine ⟨rfl, by decide, by decide, ?_⟩
  intro p q r s hp hq hr hs
  interval_cases p <;> interval_cases q <;> interval_cases r <;> interval_cases s <;> decide

lemma pass2_pellM_pair (x y : ℕ) (hx : x ≤ 1) (hy : y ≤ 1) (hxy : ¬(x = 1 ∧ y = 1)) :
    ∃ m, (pellM [x, y]).length = 2 * m ∧ good (pellM [x, y]) = true ∧
      pass2 imgDK (pellM [x, y]) = pellM (imgDK x y) := by
  interval_cases x <;> interval_cases y
  · exact ⟨3, rfl, by decide, by decide⟩
  · exact ⟨2, rfl, by decide, by decide⟩
  · exact ⟨2, rfl, by decide, by decide⟩
  · exact absurd ⟨rfl, rfl⟩ hxy

/-- The pass commutes with the Pell morphism on good words of even length. -/
lemma pass2_pellM : ∀ (n : ℕ) (u : List ℕ), u.length = 2 * n → good u = true →
    pass2 imgDK (pellM u) = pellM (pass2 imgDK u)
  | 0, u, hu, _ => by
    rw [List.eq_nil_of_length_eq_zero (by simpa using hu : u.length = 0)]
    rfl
  | n + 1, x :: y :: u, hu, hg => by
    have hx := good_head hg
    have hy := good_head (good_tail hg)
    have hxy := good_pair hg
    have hul : u.length = 2 * n := by simp at hu; omega
    have ih := pass2_pellM n u hul (good_tail (good_tail hg))
    obtain ⟨m, hm, hgm, hpm⟩ := pass2_pellM_pair x y hx hy hxy
    have e1 : pellM (x :: y :: u) = pellM [x, y] ++ pellM u := by
      rw [← pellM_append]
      rfl
    have e2 : pass2 imgDK (x :: y :: u) = imgDK x y ++ pass2 imgDK u := by
      have := pass2_append imgDK 1 [x, y] u rfl (good_take (x :: y :: u) 2 hg)
      rw [pass2_pair imgDK x y hx hy hxy] at this
      exact this
    rw [e1, e2, pass2_append imgDK m _ _ hm hgm, ih, hpm, pellM_append]
  | n + 1, [], hu, _ => by simp at hu
  | n + 1, [_], hu, _ => by simp at hu; omega

lemma pass2_pellM_iterate (u : List ℕ) (hu : good u = true) (n : ℕ) (hn : u.length = 2 * n) :
    ∀ m, pass2 imgDK (pellM^[m] u) = pellM^[m] (pass2 imgDK u) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    obtain ⟨k, hk⟩ := pellM_iterate_even m u hu n hn
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      pass2_pellM k _ hk (pellM_iterate_good m u hu), ih]

/-! ### The images of 0 -/

/-- The images of 0 under the powers of the Pell morphism. -/
def pIt (m : ℕ) : List ℕ := pellM^[m] [0]

lemma pIt_succ (m : ℕ) : pIt (m + 1) = pellM (pIt m) := by
  unfold pIt
  rw [Function.iterate_succ_apply']

lemma pIt_good (m : ℕ) : good (pIt m) = true := pellM_iterate_good m [0] rfl

lemma pIt_head : ∀ m, ∃ t, pIt m = 0 :: t
  | 0 => ⟨[], rfl⟩
  | m + 1 => by
    obtain ⟨t, ht⟩ := pIt_head m
    exact ⟨0 :: 1 :: pellM t, by rw [pIt_succ, ht]; rfl⟩

lemma pIt_length : ∀ m, m + 1 ≤ (pIt m).length
  | 0 => le_rfl
  | m + 1 => by
    have ih := pIt_length m
    obtain ⟨t, ht⟩ := pIt_head m
    have hc : 1 ≤ (pIt m).count 0 := by rw [ht]; simp
    rw [pIt_succ, pellM_length _ (pIt_good m)]
    omega

lemma pIt_prefix_succ : ∀ m, pIt m <+: pIt (m + 1)
  | 0 => ⟨[0, 1], rfl⟩
  | m + 1 => by
    obtain ⟨r, hr⟩ := pIt_prefix_succ m
    refine ⟨pellM r, ?_⟩
    rw [pIt_succ m, pIt_succ (m + 1), ← hr, pellM_append]

lemma pIt_prefix {m m' : ℕ} (h : m ≤ m') : pIt m <+: pIt m' := by
  induction m', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m' _ ih => exact ih.trans (pIt_prefix_succ m')

/-- The image of 0 is 001, so pIt (m + 1) = pIt m pIt m (image of 1). -/
lemma pIt_succ_eq (m : ℕ) : pIt (m + 1) = pIt m ++ pIt m ++ pellM^[m] [1] := by
  unfold pIt
  rw [Function.iterate_succ_apply]
  show pellM^[m] ([0] ++ [0] ++ [1]) = _
  rw [pellM_iterate_append, pellM_iterate_append]

lemma pIt_double (m : ℕ) : pIt m ++ pIt m <+: pIt (m + 1) := by
  rw [pIt_succ_eq]
  exact List.prefix_append _ _

lemma good_of_prefix {u w : List ℕ} (h : u <+: w) (hw : good w = true) : good u = true := by
  rw [List.prefix_iff_eq_take.mp h]
  exact good_take _ _ hw

/-- The pass maps pIt m pIt m (the image of 00) to pIt (m + 1) pIt m (the image of 0010). -/
lemma pass2_double (m : ℕ) : pass2 imgDK (pIt m ++ pIt m) = pIt (m + 1) ++ pIt m := by
  have e : pIt m ++ pIt m = pellM^[m] [0, 0] := (pellM_iterate_append m [0] [0]).symm
  rw [e, pass2_pellM_iterate [0, 0] rfl 1 rfl m]
  show pellM^[m] ([0, 0, 1] ++ [0]) = pellM^[m + 1] [0] ++ pellM^[m] [0]
  rw [pellM_iterate_append, Function.iterate_succ_apply]
  rfl

/-- Every stable prefix of the two-block map is a prefix of an image of 0. -/
lemma chainDK_prefix : ∀ k, ∃ M, chain imgDK k <+: pIt M
  | 0 => ⟨1, ⟨[1], rfl⟩⟩
  | k + 1 => by
    obtain ⟨M, hM⟩ := chainDK_prefix k
    set E := evenPart (chain imgDK k) with hE
    have hEM : E <+: pIt M := (evenPart_prefix _).trans hM
    set m := E.length with hm
    have hD1 : pIt m ++ pIt m <+: pIt (max M (m + 1)) :=
      (pIt_double m).trans (pIt_prefix (le_max_right _ _))
    have hE1 : E <+: pIt (max M (m + 1)) := hEM.trans (pIt_prefix (le_max_left _ _))
    have hlen : E.length ≤ (pIt m ++ pIt m).length := by
      have := pIt_length m
      rw [List.length_append]
      omega
    have hED : E <+: pIt m ++ pIt m := List.prefix_of_prefix_length_le hE1 hD1 hlen
    refine ⟨m + 2, ?_⟩
    show pass2 imgDK E <+: pIt (m + 2)
    have h1 := pass2_prefix imgDK hED _ (evenPart_length _)
      (good_take _ _ (chain_good hIDK k))
    rw [pass2_double] at h1
    refine h1.trans ?_
    have h2 : pIt (m + 1) ++ pIt m <+: pIt (m + 1) ++ pIt (m + 1) :=
      (List.prefix_append_right_inj _).mpr (pIt_prefix_succ m)
    exact h2.trans (pIt_double (m + 1))

/-- The Pell word, indexed from 0: letter i of the (i + 1)-th image of 0. -/
def pellP (i : ℕ) : ℕ := (pIt (i + 1)).getD i 0

lemma pellP_of_pIt (m i : ℕ) (hi : i < (pIt m).length) : pellP i = (pIt m).getD i 0 := by
  have hi1 : i < (pIt (i + 1)).length := by have := pIt_length (i + 1); omega
  unfold pellP
  rcases le_total m (i + 1) with h | h
  · obtain ⟨r, hr⟩ := pIt_prefix h
    rw [← hr, List.getD_append _ _ _ _ hi]
  · obtain ⟨r, hr⟩ := pIt_prefix h
    rw [← hr, List.getD_append _ _ _ _ hi1]

/-- The fixed point of the two-block map, read off its stable prefixes. -/
def WDK (i : ℕ) : ℕ := (chain imgDK (i + 1)).getD i 0

lemma hWDK : ∀ k i, i < (chain imgDK k).length → WDK i = (chain imgDK k).getD i 0 := by
  intro k i hi
  have hi1 : i < (chain imgDK (i + 1)).length := by have := chain_length hIDK (i + 1); omega
  unfold WDK
  rcases le_total k (i + 1) with h | h
  · obtain ⟨s, hs⟩ := chain_prefix hIDK h
    rw [← hs, List.getD_append _ _ _ _ hi]
  · obtain ⟨s, hs⟩ := chain_prefix hIDK h
    rw [← hs, List.getD_append _ _ _ _ hi1]

/-- Dekking and Keane: the fixed point of the two-block map is the Pell word. -/
lemma WDK_eq (i : ℕ) : WDK i = pellP i := by
  obtain ⟨M, r, hr⟩ := chainDK_prefix (i + 1)
  have hi : i < (chain imgDK (i + 1)).length := by have := chain_length hIDK (i + 1); omega
  have hiM : i < (pIt M).length := by
    rw [← hr, List.length_append]
    omega
  unfold WDK
  rw [pellP_of_pIt M i hiM, ← hr, List.getD_append _ _ _ _ hi]

/-- The index of the 1 in the image of a pair under the two-block map of the Pell word. -/
def offDK (p _q : ℕ) : ℕ := if p = 0 then 2 else 1

lemma hoffDK : ∀ p q, p ≤ 1 → q ≤ 1 → ¬(p = 1 ∧ q = 1) → offDK p q < (imgDK p q).length ∧
    (imgDK p q).getD (offDK p q) 0 = 1 ∧ ((imgDK p q).take (offDK p q)).count 1 = 0 := by
  intro p q hp hq _
  interval_cases p <;> interval_cases q <;> decide

/-- The 1s of the Pell word are at the b(n) = floor(n (2 + sqrt 2)). -/
theorem pellP_one_iff (i : ℕ) : pellP i = 1 ↔ ∃ n, 1 ≤ n ∧ bB n = i + 1 := by
  have hinf := ones_infinite hIDK WDK hWDK offDK hoffDK
  have h01 := W_letters hIDK WDK hWDK
  have h11 := W_no11 hIDK WDK hWDK
  have hrec : ∀ n, 1 ≤ n → aPos WDK 1 n + Nat.count (fun i => WDK i = 1) (2 * n - 1) + 1 =
      4 * n := by
    intro n hn
    have hr := rec_of_chain hIDK WDK hWDK offDK hoffDK n hn
    have hs := h01 (2 * n - 2)
    have hc : Nat.count (fun i => WDK i = 1) (2 * n - 1) =
        Nat.count (fun i => WDK i = 1) (2 * n - 2) + (if WDK (2 * n - 2) = 1 then 1 else 0) := by
      rw [show 2 * n - 1 = 2 * n - 2 + 1 by omega, Nat.count_succ]
    unfold offDK at hr
    split_ifs at hr hc <;> omega
  have hex := exact_bB WDK hinf h01 h11 hrec
  rw [← WDK_eq, one_iff_aPos WDK hinf]
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, by rw [← hex n hn]; exact h⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, by rw [hex n hn]; exact h⟩

lemma pellP_le (i : ℕ) : pellP i ≤ 1 := by
  rw [← WDK_eq]
  exact W_letters hIDK WDK hWDK i

/-- A word whose 1s satisfy a(n) + O(2n - 2) + 3 = 4n + 2 is the Pell word without its first three
letters. -/
theorem shift_of_rec (W : ℕ → ℕ) (hinf : {i | W i = 1}.Infinite) (hW01 : ∀ i, W i ≤ 1)
    (hW11 : ∀ n, ¬(W (2 * n) = 1 ∧ W (2 * n + 1) = 1))
    (hrec : ∀ n, 1 ≤ n → aPos W 1 n + Nat.count (fun i => W i = 1) (2 * n - 2) + 3 = 4 * n + 2) :
    ∀ i, W i = pellP (i + 3) := by
  have hex := exact_bB_shift W hinf hW01 hW11 hrec
  have hb3 : ∀ k, 1 ≤ k → 3 ≤ bB k := fun k hk => by have := two_mul_lt_bB k hk; omega
  intro i
  have hiff : W i = 1 ↔ pellP (i + 3) = 1 := by
    rw [one_iff_aPos W hinf, pellP_one_iff]
    constructor
    · rintro ⟨n, hn, h⟩
      rw [hex n hn] at h
      have := hb3 (n + 1) (by omega)
      exact ⟨n + 1, by omega, by omega⟩
    · rintro ⟨m, hm, h⟩
      have hm2 : 2 ≤ m := by
        by_contra hc
        have : m = 1 := by omega
        rw [this, bB_one] at h
        omega
      refine ⟨m - 1, by omega, ?_⟩
      rw [hex (m - 1) (by omega), show m - 1 + 1 = m by omega]
      omega
  have h1 := hW01 i
  have h2 := pellP_le (i + 3)
  by_cases hw : W i = 1
  · rw [hw, eq_comm]
    exact hiff.mp hw
  · have : pellP (i + 3) ≠ 1 := fun h => hw (hiff.mpr h)
    omega

end SRGen

/-!
# OEIS A288997: A288997(n) = A171588(n + 3) for all n > 0

Dekking's conjecture (Mar 21 2022): the fixed point of the mapping 00 -> 0010, 01 -> 001, 10 -> 001
started at 00 is the Pell word without its first three letters. The fixed point has no factor 11, so
a pass reads it in consecutive pairs, every image holds one 1, and that 1 is always at index 2: with O
the counting function of the 1s, a(n) + O(2n - 2) + 3 = 4n + 2 for the n-th 1 (`SRGen.rec_of_chain`).
The sequence b(n + 1) - 3, with b(n) = 2n + isqrt(2n^2) = floor(n (2 + sqrt 2)), satisfies the same
recursion (`SRGen.bB_rec`), and the recursion determines the positions, so the 1s are at the
b(n + 1) - 3 (`SRGen.exact_bB_shift`). The 1s of the Pell word are at the b(n) (`SRGen.pellP_one_iff`):
Dekking and Keane (arXiv:2202.13548, Theorem 4) showed that the Pell word is the fixed point of
00 -> 0010, 01 -> 001, 10 -> 010, whose recursion is that of b, by the commutation of that map with
the Pell morphism on the pairs 00, 01, 10 (`SRGen.pass2_pellM`). Comparing the letters gives the
conjecture (`SRGen.shift_of_rec`). `data` and `data_pell` read the listed terms of both entries off
the definitions.
-/

namespace OMA.S_oeis_a288997








/-! ### The two-block map -/

/-- The images of the pairs 00, 01 and 10. -/
def img (p q : ℕ) : List ℕ := if p = 0 then (if q = 0 then [0, 0, 1, 0] else [0, 0, 1]) else [0, 0, 1]

lemma step_eq : ∀ w, step w = SRGen.pass2 img w
  | [] => rfl
  | [x] => by rcases x with _ | _ | x <;> rfl
  | 0 :: 0 :: l => by
    show 0 :: 0 :: 1 :: 0 :: step l = img 0 0 ++ SRGen.pass2 img l
    rw [step_eq l]
    rfl
  | 0 :: 1 :: l => by
    show 0 :: 0 :: 1 :: step l = img 0 1 ++ SRGen.pass2 img l
    rw [step_eq l]
    rfl
  | 0 :: (y + 2) :: l => by
    show 0 :: step ((y + 2) :: l) = 0 :: SRGen.pass2 img ((y + 2) :: l)
    rw [step_eq ((y + 2) :: l)]
  | 1 :: 0 :: l => by
    show 0 :: 0 :: 1 :: step l = img 1 0 ++ SRGen.pass2 img l
    rw [step_eq l]
    rfl
  | 1 :: (y + 1) :: l => by
    show 1 :: step ((y + 1) :: l) = 1 :: SRGen.pass2 img ((y + 1) :: l)
    rw [step_eq ((y + 1) :: l)]
  | (x + 2) :: l => by
    show (x + 2) :: step l = (x + 2) :: SRGen.pass2 img l
    rw [step_eq l]

lemma hI : SRGen.Imgs img := by
  refine ⟨rfl, by decide, by decide, ?_⟩
  intro p q r s hp hq hr hs
  interval_cases p <;> interval_cases q <;> interval_cases r <;> interval_cases s <;> decide

lemma hW : ∀ k i, i < (SRGen.chain img k).length → W i = (SRGen.chain img k).getD i 0 :=
  SRGen.W_chain hI iter rfl (fun _ => step_eq _) W (fun _ => rfl)

/-- The index of the 1 in the image of a pair: 2 for all three. -/
def off (_p _q : ℕ) : ℕ := 2

lemma hoff : ∀ p q, p ≤ 1 → q ≤ 1 → ¬(p = 1 ∧ q = 1) → off p q < (img p q).length ∧
    (img p q).getD (off p q) 0 = 1 ∧ ((img p q).take (off p q)).count 1 = 0 := by
  intro p q hp hq _
  interval_cases p <;> interval_cases q <;> decide

lemma hrec (n : ℕ) (hn : 1 ≤ n) :
    SRGen.aPos W 1 n + Nat.count (fun i => W i = 1) (2 * n - 2) + 3 = 4 * n + 2 :=
  SRGen.rec_of_chain hI W hW off hoff n hn

/-! ### The Pell word -/

lemma pell_eq : ∀ w, pell w = SRGen.pellM w
  | [] => rfl
  | 0 :: l => by
    show 0 :: 0 :: 1 :: pell l = 0 :: 0 :: 1 :: SRGen.pellM l
    rw [pell_eq l]
  | 1 :: l => by
    show 0 :: pell l = 0 :: SRGen.pellM l
    rw [pell_eq l]
  | (x + 2) :: l => by
    show (x + 2) :: pell l = (x + 2) :: SRGen.pellM l
    rw [pell_eq l]

lemma pellIter_eq : ∀ m, pellIter m = SRGen.pIt m
  | 0 => rfl
  | m + 1 => by
    show pell (pellIter m) = SRGen.pIt (m + 1)
    rw [pellIter_eq m, pell_eq, SRGen.pIt_succ]

/-! ### The listed terms -/

/-- The listed terms of OMA.S_oeis_a288997. -/
def dataList : List ℕ := [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1,
  0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0,
  1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0]

/-- The listed terms of A171588. -/
def dataPell : List ℕ := [0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0,
  0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1,
  0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0,
  1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1]

lemma chain9_check : (List.range dataList.length).all
    (fun j => decide (j < (SRGen.chain img 9).length) &&
      decide ((SRGen.chain img 9).getD j 0 = dataList.getD j 0)) = true := by
  decide +kernel

/-- The listed terms of A288997, read off the stable prefix S 9 by a kernel scan. -/
theorem data (j : ℕ) (hj : j < dataList.length) : a (j + 1) = dataList.getD j 0 := by
  have h := List.all_eq_true.mp chain9_check j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  show W j = _
  rw [hW 9 j h.1, h.2]

lemma pIt7_check : (List.range dataPell.length).all
    (fun j => decide (j < (SRGen.pIt 7).length) &&
      decide ((SRGen.pIt 7).getD j 0 = dataPell.getD j 0)) = true := by
  decide +kernel

/-- The listed terms of A171588, read off the seventh image of 0 by a kernel scan. -/
theorem data_pell (j : ℕ) (hj : j < dataPell.length) : pellWord (j + 1) = dataPell.getD j 0 := by
  have h := List.all_eq_true.mp pIt7_check j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have e : pellWord (j + 1) = SRGen.pellP j := by
    show (pellIter (j + 1)).getD (j + 1 - 1) 0 = _
    rw [pellIter_eq, Nat.add_sub_cancel]
    rfl
  rw [e, SRGen.pellP_of_pIt 7 j h.1, h.2]

/-! ### The conjecture -/

/-- Dekking's conjecture: A288997(n) = A171588(n + 3) for all n > 0. -/
theorem conjecture : ∀ n : ℕ, 0 < n → a n = pellWord (n + 3) := by
  intro n hn
  have h := SRGen.shift_of_rec W (SRGen.ones_infinite hI W hW off hoff) (SRGen.W_letters hI W hW)
    (SRGen.W_no11 hI W hW) hrec (n - 1)
  have e1 : n - 1 + 3 + 1 = n + 3 := by omega
  have e2 : n - 1 + 3 = n + 3 - 1 := by omega
  show W (n - 1) = (pellIter (n + 3)).getD (n + 3 - 1) 0
  rw [h, pellIter_eq]
  unfold SRGen.pellP
  rw [e1, e2]

end OMA.S_oeis_a288997

theorem OMA.solution : type_of% @OMA.S_oeis_a288997.main :=
  OMA.S_oeis_a288997.conjecture
