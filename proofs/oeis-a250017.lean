import OMAStatements.S_oeis_a250017
import Mathlib

/-!
Proof of the A250017 statement. The transfer step `ways (q+1) = ways q + T (ways q)` uses a
linear operator `T` that strictly raises the rank (center plus number of outer bits, at most 8),
so `T` is nilpotent: `T^[9] = 0`. Hence `G j q := (T^[j] (ways q)) 0` satisfies
`G j (q+1) = G j q + G (j+1) q` with `G 9 = 0`, and each `G j` is a polynomial in `q` of degree
`8 - j`, pinned down by the values `G j 0` from explicit vectors `T^[j] (ways 0)`.
-/

namespace OMA.Helpers

open OMA.S_oeis_a250017

/-- Weighted sum over a list of (state, weight) pairs. -/
def wsumA250017 : List (State × ℕ) → (State → ℕ) → ℕ
  | [], _ => 0
  | (t,w)::rest, f => w * f t + wsumA250017 rest f

/-- Outgoing weighted edges of a state. -/
def edgesA250017 (s : State) : List (State × ℕ) :=
  (List.finRange 80).filterMap fun t =>
    let w := S_oeis_a250017.multiplicity s t
    if w = 0 then none else some (t,w)

/-- The transfer operator. -/
def stepA250017 (f : State → ℕ) : State → ℕ := fun s => wsumA250017 (edgesA250017 s) f

theorem waysSuccA250017 (q : ℕ) :
    ways (q+1) = fun s => ways q s + stepA250017 (ways q) s := by
  funext s
  fin_cases s <;> rfl

theorem wsumAddA250017 (l : List (State × ℕ)) (f g : State → ℕ) :
    wsumA250017 l (fun s => f s + g s) = wsumA250017 l f + wsumA250017 l g := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨t, w⟩ := p
    simp only [wsumA250017, ih]
    ring

theorem stepAddA250017 (f g : State → ℕ) :
    stepA250017 (fun s => f s + g s) = fun s => stepA250017 f s + stepA250017 g s := by
  funext s
  exact wsumAddA250017 _ f g

theorem iterAddA250017 (j : ℕ) (f g : State → ℕ) :
    stepA250017^[j] (fun s => f s + g s) = fun s => stepA250017^[j] f s + stepA250017^[j] g s := by
  induction j generalizing f g with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      stepAddA250017, ih]

theorem wsumZeroA250017 (l : List (State × ℕ)) (f : State → ℕ)
    (h : ∀ p ∈ l, p.2 = 0 ∨ f p.1 = 0) : wsumA250017 l f = 0 := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨t, w⟩ := p
    simp only [wsumA250017]
    have h1 := h (t, w) (by simp)
    have h2 : wsumA250017 rest f = 0 := ih (fun p hp => h p (by simp [hp]))
    rcases h1 with h1 | h1 <;> simp_all

theorem memEdgesA250017 (s : State) (p : State × ℕ) (hp : p ∈ edgesA250017 s) :
    p.2 = S_oeis_a250017.multiplicity s p.1 ∧ S_oeis_a250017.multiplicity s p.1 ≠ 0 := by
  unfold edgesA250017 at hp
  rw [List.mem_filterMap] at hp
  obtain ⟨t, _, ht⟩ := hp
  by_cases h0 : S_oeis_a250017.multiplicity s t = 0
  · simp [h0] at ht
  · simp only [h0, if_false, Option.some.injEq] at ht
    subst ht
    exact ⟨rfl, h0⟩

/-- Rank of a state: center count plus number of occupied outer positions. -/
def rankA250017 (s : State) : ℕ :=
  s.val / 16 + s.val % 2 + s.val / 2 % 2 + s.val / 4 % 2 + s.val / 8 % 2

theorem rankLeA250017 : ∀ s : State, rankA250017 s ≤ 8 := by decide +kernel

theorem rankLtA250017 : ∀ s t : State, S_oeis_a250017.multiplicity s t ≠ 0 → rankA250017 s < rankA250017 t := by
  decide +kernel

theorem nilA250017 (f : State → ℕ) (j : ℕ) :
    ∀ s : State, 8 < rankA250017 s + j → (stepA250017^[j] f) s = 0 := by
  induction j with
  | zero =>
    intro s hs
    have := rankLeA250017 s
    omega
  | succ j ih =>
    intro s hs
    rw [Function.iterate_succ_apply']
    apply wsumZeroA250017
    intro p hp
    right
    obtain ⟨_, h2⟩ := memEdgesA250017 s p hp
    have := rankLtA250017 s p.1 h2
    exact ih p.1 (by omega)

/-- `G j q = (T^[j] (ways q)) 0`. -/
def gA250017 (j q : ℕ) : ℕ := (stepA250017^[j] (ways q)) 0

theorem gSuccA250017 (j q : ℕ) : gA250017 j (q+1) = gA250017 j q + gA250017 (j+1) q := by
  unfold gA250017
  rw [waysSuccA250017, iterAddA250017, Function.iterate_succ_apply]

theorem gNineA250017 (q : ℕ) : gA250017 9 q = 0 :=
  nilA250017 _ 9 0 (by simp [rankA250017])

/-- Table of `T^[0] (ways 0)`. -/
def vec0A250017 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Table of `T^[1] (ways 0)`. -/
def vec1A250017 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]

/-- Table of `T^[2] (ways 0)`. -/
def vec2A250017 : List ℕ :=
  [20, 10, 10, 4, 10, 10, 4, 4, 10, 4, 10, 4, 4, 4, 4, 4, 10, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 4, 4, 4, 4, 6, 4, 4, 8, 4, 8, 14, 14, 6, 4, 4, 14, 6, 4, 6, 6, 2, 30, 14, 14, 6, 14, 6, 6, 2, 14, 6, 6, 2, 6, 2, 2, 0, 14, 6, 6, 2, 6, 2, 2, 0, 6, 2, 2, 0, 2, 0, 0, 0]

/-- Table of `T^[3] (ways 0)`. -/
def vec3A250017 : List ℕ :=
  [852, 290, 302, 84, 302, 168, 84, 44, 290, 96, 168, 44, 84, 44, 44, 24, 329, 93, 96, 44, 96, 56, 56, 24, 93, 26, 56, 24, 44, 24, 24, 6, 116, 56, 84, 24, 84, 36, 36, 6, 56, 24, 36, 6, 24, 6, 6, 0, 150, 36, 36, 6, 36, 6, 6, 0, 36, 6, 6, 0, 6, 0, 0, 0, 36, 6, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0]

/-- Table of `T^[4] (ways 0)`. -/
def vec4A250017 : List ℕ :=
  [9984, 2388, 2532, 504, 2532, 768, 552, 144, 2388, 576, 768, 144, 504, 144, 144, 24, 2688, 552, 594, 144, 594, 162, 162, 24, 552, 126, 162, 24, 144, 24, 24, 0, 676, 162, 192, 24, 192, 24, 24, 0, 162, 24, 24, 0, 24, 0, 0, 0, 240, 24, 24, 0, 24, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Table of `T^[5] (ways 0)`. -/
def vec5A250017 : List ℕ :=
  [47712, 7788, 8112, 1080, 8112, 1296, 1152, 120, 7788, 1152, 1296, 120, 1080, 120, 120, 0, 8376, 1134, 1188, 120, 1188, 120, 120, 0, 1134, 120, 120, 0, 120, 0, 0, 0, 1260, 120, 120, 0, 120, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Table of `T^[6] (ways 0)`. -/
def vec6A250017 : List ℕ :=
  [105216, 10584, 10800, 720, 10800, 720, 720, 0, 10584, 720, 720, 0, 720, 0, 0, 0, 10944, 720, 720, 0, 720, 0, 0, 0, 720, 0, 0, 0, 0, 0, 0, 0, 720, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Table of `T^[7] (ways 0)`. -/
def vec7A250017 : List ℕ :=
  [106704, 5040, 5040, 0, 5040, 0, 0, 0, 5040, 0, 0, 0, 0, 0, 0, 0, 5040, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Table of `T^[8] (ways 0)`. -/
def vec8A250017 : List ℕ :=
  [40320, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem ways0A250017 : ways 0 = fun s => vec0A250017.getD s.val 0 := by
  funext s
  revert s
  decide +kernel

theorem vecStep0A250017 :
    stepA250017 (fun s => vec0A250017.getD s.val 0) = fun s => vec1A250017.getD s.val 0 := by
  funext s
  revert s
  decide +kernel

theorem vecStep1A250017 :
    stepA250017 (fun s => vec1A250017.getD s.val 0) = fun s => vec2A250017.getD s.val 0 := by
  funext s
  revert s
  decide +kernel

theorem vecStep2A250017 :
    stepA250017 (fun s => vec2A250017.getD s.val 0) = fun s => vec3A250017.getD s.val 0 := by
  funext s
  revert s
  decide +kernel

theorem vecStep3A250017 :
    stepA250017 (fun s => vec3A250017.getD s.val 0) = fun s => vec4A250017.getD s.val 0 := by
  funext s
  revert s
  decide +kernel

theorem vecStep4A250017 :
    stepA250017 (fun s => vec4A250017.getD s.val 0) = fun s => vec5A250017.getD s.val 0 := by
  funext s
  revert s
  decide +kernel

theorem vecStep5A250017 :
    stepA250017 (fun s => vec5A250017.getD s.val 0) = fun s => vec6A250017.getD s.val 0 := by
  funext s
  revert s
  decide +kernel

theorem vecStep6A250017 :
    stepA250017 (fun s => vec6A250017.getD s.val 0) = fun s => vec7A250017.getD s.val 0 := by
  funext s
  revert s
  decide +kernel

theorem vecStep7A250017 :
    stepA250017 (fun s => vec7A250017.getD s.val 0) = fun s => vec8A250017.getD s.val 0 := by
  funext s
  revert s
  decide +kernel

theorem iterVecA250017 :
    stepA250017^[0] (ways 0) = (fun s => vec0A250017.getD s.val 0) ∧
    stepA250017^[1] (ways 0) = (fun s => vec1A250017.getD s.val 0) ∧
    stepA250017^[2] (ways 0) = (fun s => vec2A250017.getD s.val 0) ∧
    stepA250017^[3] (ways 0) = (fun s => vec3A250017.getD s.val 0) ∧
    stepA250017^[4] (ways 0) = (fun s => vec4A250017.getD s.val 0) ∧
    stepA250017^[5] (ways 0) = (fun s => vec5A250017.getD s.val 0) ∧
    stepA250017^[6] (ways 0) = (fun s => vec6A250017.getD s.val 0) ∧
    stepA250017^[7] (ways 0) = (fun s => vec7A250017.getD s.val 0) ∧
    stepA250017^[8] (ways 0) = (fun s => vec8A250017.getD s.val 0) := by
  have h0 : stepA250017^[0] (ways 0) = (fun s => vec0A250017.getD s.val 0) := ways0A250017
  have h1 : stepA250017^[1] (ways 0) = (fun s => vec1A250017.getD s.val 0) := by
    rw [Function.iterate_succ_apply', h0, vecStep0A250017]
  have h2 : stepA250017^[2] (ways 0) = (fun s => vec2A250017.getD s.val 0) := by
    rw [Function.iterate_succ_apply', h1, vecStep1A250017]
  have h3 : stepA250017^[3] (ways 0) = (fun s => vec3A250017.getD s.val 0) := by
    rw [Function.iterate_succ_apply', h2, vecStep2A250017]
  have h4 : stepA250017^[4] (ways 0) = (fun s => vec4A250017.getD s.val 0) := by
    rw [Function.iterate_succ_apply', h3, vecStep3A250017]
  have h5 : stepA250017^[5] (ways 0) = (fun s => vec5A250017.getD s.val 0) := by
    rw [Function.iterate_succ_apply', h4, vecStep4A250017]
  have h6 : stepA250017^[6] (ways 0) = (fun s => vec6A250017.getD s.val 0) := by
    rw [Function.iterate_succ_apply', h5, vecStep5A250017]
  have h7 : stepA250017^[7] (ways 0) = (fun s => vec7A250017.getD s.val 0) := by
    rw [Function.iterate_succ_apply', h6, vecStep6A250017]
  have h8 : stepA250017^[8] (ways 0) = (fun s => vec8A250017.getD s.val 0) := by
    rw [Function.iterate_succ_apply', h7, vecStep7A250017]
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- Polynomial induction: a sequence with increments given by a known polynomial. -/
theorem polyIndA250017 (g h : ℕ → ℕ) (P Q : ℚ → ℚ) (hrec : ∀ q, g (q+1) = g q + h q)
    (hh : ∀ q, (h q : ℚ) = Q q) (h0 : (g 0 : ℚ) = P 0)
    (hP : ∀ x : ℚ, P (x + 1) = P x + Q x) : ∀ q : ℕ, (g q : ℚ) = P q := by
  intro q
  induction q with
  | zero => simpa using h0
  | succ q ih =>
    rw [hrec q]
    push_cast
    rw [ih, hh q, hP]

/-- Closed form of `G 0`. -/
def poly0A250017 (x : ℚ) : ℚ := (1 : ℚ) * x ^ 8 + (-239/35 : ℚ) * x ^ 7 + (353/15 : ℚ) * x ^ 6 + (-247/5 : ℚ) * x ^ 5 + (208/3 : ℚ) * x ^ 4 + (-338/5 : ℚ) * x ^ 3 + (632/15 : ℚ) * x ^ 2 + (-426/35 : ℚ) * x ^ 1

/-- Closed form of `G 1`. -/
def poly1A250017 (x : ℚ) : ℚ := (8 : ℚ) * x ^ 7 + (-99/5 : ℚ) * x ^ 6 + (269/5 : ℚ) * x ^ 5 + (-63 : ℚ) * x ^ 4 + (71 : ℚ) * x ^ 3 + (-216/5 : ℚ) * x ^ 2 + (66/5 : ℚ) * x ^ 1

/-- Closed form of `G 2`. -/
def poly2A250017 (x : ℚ) : ℚ := (56 : ℚ) * x ^ 6 + (246/5 : ℚ) * x ^ 5 + (252 : ℚ) * x ^ 4 + (170 : ℚ) * x ^ 3 + (244 : ℚ) * x ^ 2 + (404/5 : ℚ) * x ^ 1 + (20 : ℚ) * x ^ 0

/-- Closed form of `G 3`. -/
def poly3A250017 (x : ℚ) : ℚ := (336 : ℚ) * x ^ 5 + (1086 : ℚ) * x ^ 4 + (2620 : ℚ) * x ^ 3 + (3354 : ℚ) * x ^ 2 + (2588 : ℚ) * x ^ 1 + (852 : ℚ) * x ^ 0

/-- Closed form of `G 4`. -/
def poly4A250017 (x : ℚ) : ℚ := (1680 : ℚ) * x ^ 4 + (7704 : ℚ) * x ^ 3 + (17736 : ℚ) * x ^ 2 + (20592 : ℚ) * x ^ 1 + (9984 : ℚ) * x ^ 0

/-- Closed form of `G 5`. -/
def poly5A250017 (x : ℚ) : ℚ := (6720 : ℚ) * x ^ 3 + (33192 : ℚ) * x ^ 2 + (65304 : ℚ) * x ^ 1 + (47712 : ℚ) * x ^ 0

/-- Closed form of `G 6`. -/
def poly6A250017 (x : ℚ) : ℚ := (20160 : ℚ) * x ^ 2 + (86544 : ℚ) * x ^ 1 + (105216 : ℚ) * x ^ 0

/-- Closed form of `G 7`. -/
def poly7A250017 (x : ℚ) : ℚ := (40320 : ℚ) * x ^ 1 + (106704 : ℚ) * x ^ 0

/-- Closed form of `G 8`. -/
def poly8A250017 (x : ℚ) : ℚ := (40320 : ℚ) * x ^ 0

theorem g00A250017 : gA250017 0 0 = 0 := by
  unfold gA250017
  rw [iterVecA250017.1]
  decide +kernel

theorem g10A250017 : gA250017 1 0 = 0 := by
  unfold gA250017
  rw [iterVecA250017.2.1]
  decide +kernel

theorem g20A250017 : gA250017 2 0 = 20 := by
  unfold gA250017
  rw [iterVecA250017.2.2.1]
  decide +kernel

theorem g30A250017 : gA250017 3 0 = 852 := by
  unfold gA250017
  rw [iterVecA250017.2.2.2.1]
  decide +kernel

theorem g40A250017 : gA250017 4 0 = 9984 := by
  unfold gA250017
  rw [iterVecA250017.2.2.2.2.1]
  decide +kernel

theorem g50A250017 : gA250017 5 0 = 47712 := by
  unfold gA250017
  rw [iterVecA250017.2.2.2.2.2.1]
  decide +kernel

theorem g60A250017 : gA250017 6 0 = 105216 := by
  unfold gA250017
  rw [iterVecA250017.2.2.2.2.2.2.1]
  decide +kernel

theorem g70A250017 : gA250017 7 0 = 106704 := by
  unfold gA250017
  rw [iterVecA250017.2.2.2.2.2.2.2.1]
  decide +kernel

theorem g80A250017 : gA250017 8 0 = 40320 := by
  unfold gA250017
  rw [iterVecA250017.2.2.2.2.2.2.2.2]
  decide +kernel

theorem gClosed8A250017 (q : ℕ) : (gA250017 8 q : ℚ) = poly8A250017 q := by
  refine polyIndA250017 (gA250017 8) (gA250017 9) poly8A250017 (fun _ => 0) (gSuccA250017 8)
    (fun q => by simp [gNineA250017]) (by rw [g80A250017]; norm_num [poly8A250017])
    (fun x => by simp only [poly8A250017]; ring) q

theorem gClosed7A250017 (q : ℕ) : (gA250017 7 q : ℚ) = poly7A250017 q := by
  refine polyIndA250017 (gA250017 7) (gA250017 8) poly7A250017 poly8A250017 (gSuccA250017 7)
    gClosed8A250017 (by rw [g70A250017]; norm_num [poly7A250017])
    (fun x => by simp only [poly7A250017, poly8A250017]; ring) q

theorem gClosed6A250017 (q : ℕ) : (gA250017 6 q : ℚ) = poly6A250017 q := by
  refine polyIndA250017 (gA250017 6) (gA250017 7) poly6A250017 poly7A250017 (gSuccA250017 6)
    gClosed7A250017 (by rw [g60A250017]; norm_num [poly6A250017])
    (fun x => by simp only [poly6A250017, poly7A250017]; ring) q

theorem gClosed5A250017 (q : ℕ) : (gA250017 5 q : ℚ) = poly5A250017 q := by
  refine polyIndA250017 (gA250017 5) (gA250017 6) poly5A250017 poly6A250017 (gSuccA250017 5)
    gClosed6A250017 (by rw [g50A250017]; norm_num [poly5A250017])
    (fun x => by simp only [poly5A250017, poly6A250017]; ring) q

theorem gClosed4A250017 (q : ℕ) : (gA250017 4 q : ℚ) = poly4A250017 q := by
  refine polyIndA250017 (gA250017 4) (gA250017 5) poly4A250017 poly5A250017 (gSuccA250017 4)
    gClosed5A250017 (by rw [g40A250017]; norm_num [poly4A250017])
    (fun x => by simp only [poly4A250017, poly5A250017]; ring) q

theorem gClosed3A250017 (q : ℕ) : (gA250017 3 q : ℚ) = poly3A250017 q := by
  refine polyIndA250017 (gA250017 3) (gA250017 4) poly3A250017 poly4A250017 (gSuccA250017 3)
    gClosed4A250017 (by rw [g30A250017]; norm_num [poly3A250017])
    (fun x => by simp only [poly3A250017, poly4A250017]; ring) q

theorem gClosed2A250017 (q : ℕ) : (gA250017 2 q : ℚ) = poly2A250017 q := by
  refine polyIndA250017 (gA250017 2) (gA250017 3) poly2A250017 poly3A250017 (gSuccA250017 2)
    gClosed3A250017 (by rw [g20A250017]; norm_num [poly2A250017])
    (fun x => by simp only [poly2A250017, poly3A250017]; ring) q

theorem gClosed1A250017 (q : ℕ) : (gA250017 1 q : ℚ) = poly1A250017 q := by
  refine polyIndA250017 (gA250017 1) (gA250017 2) poly1A250017 poly2A250017 (gSuccA250017 1)
    gClosed2A250017 (by rw [g10A250017]; norm_num [poly1A250017])
    (fun x => by simp only [poly1A250017, poly2A250017]; ring) q

theorem gClosed0A250017 (q : ℕ) : (gA250017 0 q : ℚ) = poly0A250017 q := by
  refine polyIndA250017 (gA250017 0) (gA250017 1) poly0A250017 poly1A250017 (gSuccA250017 0)
    gClosed1A250017 (by rw [g00A250017]; norm_num [poly0A250017])
    (fun x => by simp only [poly0A250017, poly1A250017]; ring) q

theorem totalClosedA250017 (n : ℕ) :
    total n = (n:ℚ)^8 + 41/35*(n:ℚ)^7 + 56/15*(n:ℚ)^6 + 22/5*(n:ℚ)^5 +
      19/3*(n:ℚ)^4 + 17/5*(n:ℚ)^3 - 16/15*(n:ℚ)^2 + 36/35*n := by
  have h : total n = (gA250017 0 (n+1) : ℚ) := rfl
  rw [h, gClosed0A250017]
  simp only [poly0A250017]
  push_cast
  ring

theorem totalRecA250017 (n : ℕ) :
    total (n+9) = 9*total (n+8) - 36*total (n+7) + 84*total (n+6) - 126*total (n+5) +
      126*total (n+4) - 84*total (n+3) + 36*total (n+2) - 9*total (n+1) + total n := by
  simp only [totalClosedA250017]
  push_cast
  ring

open PowerSeries in
theorem totalGfA250017 :
    (1-X)^9 * mk total =
      (4*X*(5+183*X+1506*X^2+3974*X^3+3441*X^4+903*X^5+68*X^6) : PowerSeries ℚ) := by
  have key : (1-X)^9 * mk total =
      C 1 * (mk total * X ^ 0) - C 9 * (mk total * X ^ 1) +
        C 36 * (mk total * X ^ 2) - C 84 * (mk total * X ^ 3) +
        C 126 * (mk total * X ^ 4) - C 126 * (mk total * X ^ 5) +
        C 84 * (mk total * X ^ 6) - C 36 * (mk total * X ^ 7) +
        C 9 * (mk total * X ^ 8) - C 1 * (mk total * X ^ 9) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (4*X*(5+183*X+1506*X^2+3974*X^3+3441*X^4+903*X^5+68*X^6) : PowerSeries ℚ) =
      C 20 * X ^ 1 + C 732 * X ^ 2 + C 6024 * X ^ 3 + C 15896 * X ^ 4 + C 13764 * X ^ 5 +
        C 3612 * X ^ 6 + C 272 * X ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 10
  · interval_cases k <;> norm_num [totalClosedA250017]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 10 := ⟨k - 10, by omega⟩
    simp only [show 0 ≤ j + 10 by omega, show 1 ≤ j + 10 by omega, show 2 ≤ j + 10 by omega,
      show 3 ≤ j + 10 by omega, show 4 ≤ j + 10 by omega, show 5 ≤ j + 10 by omega,
      show 6 ≤ j + 10 by omega, show 7 ≤ j + 10 by omega, show 8 ≤ j + 10 by omega,
      show 9 ≤ j + 10 by omega, show j + 10 - 0 = j + 10 by omega,
      show j + 10 - 1 = j + 9 by omega, show j + 10 - 2 = j + 8 by omega,
      show j + 10 - 3 = j + 7 by omega, show j + 10 - 4 = j + 6 by omega,
      show j + 10 - 5 = j + 5 by omega, show j + 10 - 6 = j + 4 by omega,
      show j + 10 - 7 = j + 3 by omega, show j + 10 - 8 = j + 2 by omega,
      show j + 10 - 9 = j + 1 by omega, show ¬ (j + 10 = 1) by omega,
      show ¬ (j + 10 = 2) by omega, show ¬ (j + 10 = 3) by omega, show ¬ (j + 10 = 4) by omega,
      show ¬ (j + 10 = 5) by omega, show ¬ (j + 10 = 6) by omega, show ¬ (j + 10 = 7) by omega,
      if_true, if_false, totalClosedA250017]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a250017.main :=
  ⟨OMA.Helpers.totalClosedA250017, OMA.Helpers.totalRecA250017, OMA.Helpers.totalGfA250017⟩
