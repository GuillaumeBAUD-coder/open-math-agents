import OMAStatements.S_oeis_a081693

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
# OEIS A081693: B_n is the position of the n-th 1 in the fixed point of 0 -> 01, 1 -> 0000

Kimberling's conjecture (Apr 13 2017) for Sloane's mex pair. In the fixed point w = sig(w) of
sig: 0 -> 01, 1 -> 0000, the n-th 1 is the 1 of the image of the n-th 0: with z_n and o_n the
positions (from 1) of the n-th 0 and the n-th 1, the image of the first z_n - 1 letters has
2 (n - 1) + 4 (z_n - n) letters, so o_n = 4 z_n - 2n (`ones_eq`). The images 01 and 0000 give no
factor 11, so consecutive 0s are 1 or 2 apart (`zeros_gap`), and then d (d + 1) = 4d - 2. By strong
induction A_n = z_n (the mex of the earlier terms is z_n, because every m < z_n is a z_k or an o_k
with k < n, as o_k < z_n < o_n) and B_n = B_(n-1) + 4 (z_n - z_(n-1)) - 2 = o_n (`solution_eq`).
-/

namespace OMA.S_oeis_a081693






/-! ### The morphism -/

lemma sig_append : ∀ u v : List ℕ, sig (u ++ v) = sig u ++ sig v
  | [], _ => rfl
  | 0 :: u, v => by
    show 0 :: 1 :: sig (u ++ v) = 0 :: 1 :: (sig u ++ sig v)
    rw [sig_append u v]
  | 1 :: u, v => by
    show 0 :: 0 :: 0 :: 0 :: sig (u ++ v) = 0 :: 0 :: 0 :: 0 :: (sig u ++ sig v)
    rw [sig_append u v]
  | (x + 2) :: u, v => by
    show (x + 2) :: sig (u ++ v) = (x + 2) :: (sig u ++ sig v)
    rw [sig_append u v]

lemma sig_head : ∀ l : List ℕ, SRGen.good l = true → (sig l).head? = none ∨ (sig l).head? = some 0
  | [], _ => Or.inl rfl
  | x :: l, h => by
    have hx := SRGen.good_head h
    interval_cases x
    · exact Or.inr rfl
    · exact Or.inr rfl

lemma sig_good : ∀ l : List ℕ, SRGen.good l = true → SRGen.good (sig l) = true
  | [], _ => rfl
  | x :: l, h => by
    have hx := SRGen.good_head h
    have ih := sig_good l (SRGen.good_tail h)
    have hd := sig_head l (SRGen.good_tail h)
    interval_cases x
    · show SRGen.good ([0, 1] ++ sig l) = true
      apply SRGen.good_append _ _ (by decide) ih
      rcases hd with hd | hd <;> simp [hd]
    · show SRGen.good ([0, 0, 0, 0] ++ sig l) = true
      exact SRGen.good_append _ _ (by decide) ih (by simp)

/-- Lengths and letters 1 of an image: each 0 gives two letters and one 1, each 1 four letters. -/
lemma sig_counts : ∀ l : List ℕ, SRGen.good l = true →
    (sig l).length = 2 * l.count 0 + 4 * l.count 1 ∧ (sig l).count 1 = l.count 0
  | [], _ => ⟨rfl, rfl⟩
  | x :: l, h => by
    have hx := SRGen.good_head h
    obtain ⟨ih1, ih2⟩ := sig_counts l (SRGen.good_tail h)
    interval_cases x
    · have e0 : (0 :: l).count 0 = l.count 0 + 1 := by simp
      have e1 : (0 :: l).count 1 = l.count 1 := by simp
      have e2 : (0 :: 1 :: sig l).count 1 = (sig l).count 1 + 1 := by simp
      show (0 :: 1 :: sig l).length = _ ∧ (0 :: 1 :: sig l).count 1 = _
      rw [e0, e1, e2]
      simp only [List.length_cons]
      omega
    · have e0 : (1 :: l).count 0 = l.count 0 := by simp
      have e1 : (1 :: l).count 1 = l.count 1 + 1 := by simp
      have e2 : (0 :: 0 :: 0 :: 0 :: sig l).count 1 = (sig l).count 1 := by simp
      show (0 :: 0 :: 0 :: 0 :: sig l).length = _ ∧ (0 :: 0 :: 0 :: 0 :: sig l).count 1 = _
      rw [e0, e1, e2]
      simp only [List.length_cons]
      omega

lemma sigIter_good : ∀ m, SRGen.good (sigIter m) = true
  | 0 => rfl
  | m + 1 => sig_good _ (sigIter_good m)

lemma sigIter_head : ∀ m, ∃ t, sigIter m = 0 :: t
  | 0 => ⟨[], rfl⟩
  | m + 1 => by
    obtain ⟨t, ht⟩ := sigIter_head m
    exact ⟨1 :: sig t, by show sig (sigIter m) = _; rw [ht]; rfl⟩

lemma sigIter_length : ∀ m, m + 1 ≤ (sigIter m).length
  | 0 => le_rfl
  | m + 1 => by
    have ih := sigIter_length m
    obtain ⟨t, ht⟩ := sigIter_head m
    have hc : 1 ≤ (sigIter m).count 0 := by rw [ht]; simp
    have hl := SRGen.count01 (sigIter m) (SRGen.good_letters _ (sigIter_good m))
    show m + 1 + 1 ≤ (sig (sigIter m)).length
    rw [(sig_counts _ (sigIter_good m)).1]
    omega

lemma sigIter_prefix_succ : ∀ m, sigIter m <+: sigIter (m + 1)
  | 0 => ⟨[1], rfl⟩
  | m + 1 => by
    obtain ⟨r, hr⟩ := sigIter_prefix_succ m
    refine ⟨sig r, ?_⟩
    show sig (sigIter m) ++ sig r = sig (sigIter (m + 1))
    rw [← hr, sig_append]

lemma sigIter_prefix {m m' : ℕ} (h : m ≤ m') : sigIter m <+: sigIter m' := by
  induction m', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m' _ ih => exact ih.trans (sigIter_prefix_succ m')

lemma w_eq (m i : ℕ) (hi : i < (sigIter m).length) : w i = (sigIter m).getD i 0 := by
  have hi1 : i < (sigIter (i + 1)).length := by have := sigIter_length (i + 1); omega
  unfold w
  rcases le_total m (i + 1) with h | h
  · obtain ⟨r, hr⟩ := sigIter_prefix h
    rw [← hr, List.getD_append _ _ _ _ hi]
  · obtain ⟨r, hr⟩ := sigIter_prefix h
    rw [← hr, List.getD_append _ _ _ _ hi1]

lemma w_le (i : ℕ) : w i ≤ 1 := by
  have hi : i < (sigIter (i + 1)).length := by have := sigIter_length (i + 1); omega
  rw [w_eq _ i hi, List.getD_eq_getElem _ _ hi]
  exact SRGen.good_letters _ (sigIter_good _) _ (List.getElem_mem hi)

lemma w_no11 (i : ℕ) : ¬(w i = 1 ∧ w (i + 1) = 1) := by
  have hl : i + 1 < (sigIter (i + 2)).length := by have := sigIter_length (i + 2); omega
  rw [w_eq (i + 2) i (by omega), w_eq (i + 2) (i + 1) hl]
  exact SRGen.good_getD _ i (sigIter_good _) hl

/-! ### The positions -/

lemma count_w (m N : ℕ) (hN : N ≤ (sigIter m).length) (b : ℕ) :
    Nat.count (fun i => w i = b) N = ((sigIter m).take N).count b :=
  SRGen.count_eq_take w (sigIter m) b (w_eq m) N hN

/-- The 0 at index j (the n-th 0, n = 1 + the number of 0s before it) produces a 1 at index
4 (j + 1) - 2n - 1, the n-th 1. -/
lemma image_one (j : ℕ) (hj : w j = 0) :
    w (4 * (j + 1) - 2 * (Nat.count (fun i => w i = 0) j + 1) - 1) = 1 ∧
      Nat.count (fun i => w i = 1) (4 * (j + 1) - 2 * (Nat.count (fun i => w i = 0) j + 1) - 1) =
        Nat.count (fun i => w i = 0) j := by
  have hul : j + 2 ≤ (sigIter (j + 1)).length := sigIter_length (j + 1)
  have hug : SRGen.good (sigIter (j + 1)) = true := sigIter_good _
  have hd : (sigIter (j + 1)).drop j = 0 :: (sigIter (j + 1)).drop (j + 1) := by
    rw [List.drop_eq_getElem_cons (by omega)]
    congr 1
    have := w_eq (j + 1) j (by omega)
    rw [List.getD_eq_getElem _ _ (by omega)] at this
    rw [← this]
    exact hj
  set u' := (sigIter (j + 1)).take j with hu'
  have hu'g : SRGen.good u' = true := SRGen.good_take _ _ hug
  have hu'l : u'.length = j := by rw [hu', List.length_take]; omega
  have hc0 : u'.count 0 = Nat.count (fun i => w i = 0) j := (count_w (j + 1) j (by omega) 0).symm
  have h01 := SRGen.count01 u' (SRGen.good_letters _ hu'g)
  obtain ⟨hlen, hone⟩ := sig_counts u' hu'g
  set r := sig ((sigIter (j + 1)).drop (j + 1)) with hr
  have hsig : sigIter (j + 2) = sig u' ++ (0 :: 1 :: r) := by
    show sig (sigIter (j + 1)) = _
    conv_lhs => rw [← List.take_append_drop j (sigIter (j + 1))]
    rw [sig_append, hd]
    rfl
  have ht : 4 * (j + 1) - 2 * (Nat.count (fun i => w i = 0) j + 1) - 1 = (sig u').length + 1 := by
    rw [hlen]
    omega
  have hlen2 : (sig u').length + 2 ≤ (sigIter (j + 2)).length := by
    rw [hsig, List.length_append]
    simp
  rw [ht]
  constructor
  · rw [w_eq (j + 2) _ (by omega), hsig, List.getD_append_right _ _ _ _ (by omega),
      show (sig u').length + 1 - (sig u').length = 1 by omega]
    rfl
  · rw [count_w (j + 2) _ (by omega) 1, hsig, List.take_append, List.take_of_length_le (by omega),
      List.count_append, hone, hc0, show (sig u').length + 1 - (sig u').length = 1 by omega]
    rfl

lemma zeros_infinite : {i | w i = 0}.Infinite := by
  apply SRGen.zeros_infinite w w_le
  intro n h
  exact w_no11 (2 * n) h

lemma ones_infinite : {i | w i = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨j, hj, hjB⟩ := zeros_infinite.exists_gt (B + 1)
  have h := (image_one j hj).1
  have := hB h
  have hc : Nat.count (fun i => w i = 0) j ≤ j := Nat.count_le _
  omega

/-- The 1-based positions of the n-th 0 and of the n-th 1 satisfy o_n = 4 z_n - 2n. -/
lemma ones_eq (n : ℕ) (hn : 1 ≤ n) : SRGen.aPos w 1 n = 4 * SRGen.aPos w 0 n - 2 * n := by
  set j := Nat.nth (fun i => w i = 0) (n - 1) with hjdef
  have hj : w j = 0 := Nat.nth_mem_of_infinite zeros_infinite (n - 1)
  have hcj : Nat.count (fun i => w i = 0) j = n - 1 := Nat.count_nth_of_infinite zeros_infinite _
  obtain ⟨h1, h2⟩ := image_one j hj
  rw [hcj] at h1 h2
  have hnth := Nat.nth_count (p := fun i => w i = 1) h1
  rw [h2] at hnth
  have hjn : n - 1 ≤ j := by rw [← hcj]; exact Nat.count_le _
  unfold SRGen.aPos
  rw [hnth, ← hjdef]
  omega

lemma letter_iff (b : ℕ) (hinf : {i | w i = b}.Infinite) (i : ℕ) :
    w i = b ↔ ∃ n, 1 ≤ n ∧ SRGen.aPos w b n = i + 1 := by
  constructor
  · intro h
    refine ⟨Nat.count (fun i => w i = b) i + 1, by omega, ?_⟩
    unfold SRGen.aPos
    rw [Nat.add_sub_cancel, Nat.nth_count (p := fun i => w i = b) h]
  · rintro ⟨n, hn, h⟩
    unfold SRGen.aPos at h
    have hm := Nat.nth_mem_of_infinite hinf (n - 1)
    rw [show Nat.nth (fun i => w i = b) (n - 1) = i by omega] at hm
    exact hm

lemma aPos_lt_iff (b : ℕ) (hinf : {i | w i = b}.Infinite) (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    SRGen.aPos w b k < SRGen.aPos w b n ↔ k < n := by
  unfold SRGen.aPos
  have h := (Nat.nth_strictMono hinf).lt_iff_lt (a := k - 1) (b := n - 1)
  constructor
  · intro hlt
    have := h.mp (by omega)
    omega
  · intro hlt
    have := h.mpr (by omega)
    omega

/-- Consecutive 0s are 1 or 2 apart. -/
lemma zeros_gap (n : ℕ) (hn : 2 ≤ n) :
    SRGen.aPos w 0 (n - 1) < SRGen.aPos w 0 n ∧ SRGen.aPos w 0 n ≤ SRGen.aPos w 0 (n - 1) + 2 := by
  have hlt := (aPos_lt_iff 0 zeros_infinite (n - 1) n (by omega) (by omega)).mpr (by omega)
  refine ⟨hlt, ?_⟩
  set z := SRGen.aPos w 0 (n - 1) with hz
  have hc1 : n - 1 ≤ Nat.count (fun i => w i = 0) z :=
    (SRGen.aPos_le_iff w 0 zeros_infinite (n - 1) z (by omega)).mp le_rfl
  have hc2 : Nat.count (fun i => w i = 0) z < n := by
    by_contra h
    have := (SRGen.aPos_le_iff w 0 zeros_infinite n z (by omega)).mpr (by omega)
    omega
  have hno := w_no11 z
  have h0 := w_le z
  have h1 := w_le (z + 1)
  apply (SRGen.aPos_le_iff w 0 zeros_infinite n (z + 2) (by omega)).mpr
  rw [show z + 2 = z + 1 + 1 by ring, Nat.count_succ, Nat.count_succ]
  split_ifs <;> omega

lemma zeros_one : SRGen.aPos w 0 1 = 1 := by
  have h : w 0 = 0 := by rw [w_eq 1 0 (by decide)]; rfl
  have := (letter_iff 0 zeros_infinite 0).mp h
  obtain ⟨n, hn, hpos⟩ := this
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have : n = 1 := by omega
    rw [this] at hpos
    exact hpos
  · have := (aPos_lt_iff 0 zeros_infinite 1 n le_rfl (by omega)).mpr (by omega)
    unfold SRGen.aPos at this hpos ⊢
    omega

/-! ### The mex pair -/

lemma solution_eq (A B : ℕ → ℕ) (h : IsSolution A B) :
    ∀ n, 1 ≤ n → A n = SRGen.aPos w 0 n ∧ B n = SRGen.aPos w 1 n := by
  obtain ⟨hA, hB0, hB⟩ := h
  have hA0 : A 0 = 0 := by
    rw [hA 0]
    exact Nat.sInf_eq_zero.mpr (Or.inl (by simp))
  have hz1 : ∀ k, 1 ≤ k → 1 ≤ SRGen.aPos w 0 k := fun k _ => by unfold SRGen.aPos; omega
  have hzo : ∀ k, 1 ≤ k → SRGen.aPos w 0 k < SRGen.aPos w 1 k := by
    intro k hk
    rw [ones_eq k hk]
    have : k ≤ SRGen.aPos w 0 k := by
      unfold SRGen.aPos
      have := Nat.le_nth (p := fun i => w i = 0) (fun hf => absurd hf zeros_infinite) (n := k - 1)
      omega
    omega
  have hne : ∀ k k', 1 ≤ k → 1 ≤ k' → SRGen.aPos w 1 k ≠ SRGen.aPos w 0 k' := by
    intro k k' hk hk' he
    have h1 := (letter_iff 1 ones_infinite (SRGen.aPos w 1 k - 1)).mpr
      ⟨k, hk, by have := hz1 k hk; have := hzo k hk; omega⟩
    have h0 := (letter_iff 0 zeros_infinite (SRGen.aPos w 1 k - 1)).mpr
      ⟨k', hk', by have := hz1 k' hk'; omega⟩
    omega
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hmem : SRGen.aPos w 0 n ∈ {m : ℕ | ∀ i < n, A i ≠ m ∧ B i ≠ m} := by
      show ∀ i < n, A i ≠ SRGen.aPos w 0 n ∧ B i ≠ SRGen.aPos w 0 n
      intro i hi
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        rw [hA0, hB0]
        have := hz1 n hn
        omega
      · obtain ⟨e1, e2⟩ := ih i hi hpos
        rw [e1, e2]
        refine ⟨?_, hne i n hpos hn⟩
        have := (aPos_lt_iff 0 zeros_infinite i n hpos hn).mpr hi
        omega
    have hAn : A n = SRGen.aPos w 0 n := by
      rw [hA n]
      refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
      intro m hm'
      have hm : ∀ i < n, A i ≠ m ∧ B i ≠ m := hm'
      by_contra hlt
      rw [not_le] at hlt
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        exact (hm 0 (by omega)).1 hA0
      · have hw := w_le (m - 1)
        rcases Nat.eq_zero_or_pos (w (m - 1)) with hw0 | hw1
        · obtain ⟨k, hk, hkm⟩ := (letter_iff 0 zeros_infinite (m - 1)).mp hw0
          have hkn : k < n := (aPos_lt_iff 0 zeros_infinite k n hk hn).mp (by omega)
          have := (hm k hkn).1
          rw [(ih k hkn hk).1] at this
          omega
        · have hw1' : w (m - 1) = 1 := by omega
          obtain ⟨k, hk, hkm⟩ := (letter_iff 1 ones_infinite (m - 1)).mp hw1'
          have hlt2 : SRGen.aPos w 1 k < SRGen.aPos w 1 n := by
            have := hzo n hn
            omega
          have hkn : k < n := (aPos_lt_iff 1 ones_infinite k n hk hn).mp hlt2
          have := (hm k hkn).2
          rw [(ih k hkn hk).2] at this
          omega
    refine ⟨hAn, ?_⟩
    rw [hB n hn, hAn]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have e : n = 1 := by omega
      subst e
      simp only [Nat.sub_self, hB0, hA0, zeros_one, ones_eq 1 le_rfl]
    · obtain ⟨e1, e2⟩ := ih (n - 1) (by omega) (by omega)
      rw [e1, e2, ones_eq (n - 1) (by omega), ones_eq n hn]
      obtain ⟨g1, g2⟩ := zeros_gap n h2
      have hz := hz1 (n - 1) (by omega)
      have hk : n - 1 ≤ SRGen.aPos w 0 (n - 1) := by
        unfold SRGen.aPos
        have := Nat.le_nth (p := fun i => w i = 0) (fun hf => absurd hf zeros_infinite) (n := n - 1 - 1)
        omega
      rcases (show SRGen.aPos w 0 n = SRGen.aPos w 0 (n - 1) + 1 ∨
          SRGen.aPos w 0 n = SRGen.aPos w 0 (n - 1) + 2 by omega) with hd | hd
      · rw [hd]
        rw [show SRGen.aPos w 0 (n - 1) + 1 - SRGen.aPos w 0 (n - 1) = 1 by omega]
        omega
      · rw [hd]
        rw [show SRGen.aPos w 0 (n - 1) + 2 - SRGen.aPos w 0 (n - 1) = 2 by omega]
        omega

/-! ### The listed terms -/

/-- The listed terms of A081693 from B_1 on. -/
def dataList : List ℕ := [2, 8, 10, 12, 14, 16, 22, 28, 34, 40, 46, 48, 50, 52, 54, 60, 62, 64, 66,
  68, 74, 76, 78, 80, 82, 88, 90, 92, 94, 96, 102, 104, 106, 108, 110, 116, 122, 128, 134, 140,
  142, 144]

/-- The listed terms are the positions of 1 in A284683, read off the sixth image of 0 by a kernel
scan. -/
theorem data (j : ℕ) (hj : j < dataList.length) : pos1 (j + 1) = dataList.getD j 0 :=
  SRGen.data_of_chk w (sigIter 6) 1 dataList (w_eq 6) (by decide +kernel) j hj

/-! ### The conjecture -/

/-- Kimberling's conjecture: except for the initial 0, B_n is the position of the n-th 1 in the fixed
point of 0 -> 01, 1 -> 0000. -/
theorem conjecture : ∀ A B : ℕ → ℕ, IsSolution A B → ∀ n : ℕ, 1 ≤ n → B n = pos1 n :=
  fun A B h n hn => (solution_eq A B h n hn).2

end OMA.S_oeis_a081693

theorem OMA.solution : type_of% @OMA.S_oeis_a081693.main :=
  OMA.S_oeis_a081693.conjecture
