import OMAReductions.R_Erdos723_erdos_723_variants_eq_12_R1

/-!
# Extending an order-12 partial plane

A binary incidence matrix with 157 columns (points) has 13 ones in each
row (line). Distinct rows meet exactly once. Two distinct columns have at
most one common row. The last condition also follows geometrically from
the row intersection axiom. All sums below are over the integers.

The project attributes the general embedding bound to Metsch. This proof
works directly at order 12, first by completing a pencil and then by
finding a 13-point clique in the exceptional 143-line case. The input
partial plane is a hypothesis.
-/
namespace Order12Extension

def total (xs : List α) (f : α → Int) : Int :=
  match xs with
  | [] => 0
  | x :: rest => f x + total rest f

theorem total_congr (xs : List α) {f g : α → Int} (h : ∀ x ∈ xs, f x = g x) :
    total xs f = total xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [total]
    rw [h x (by simp), ih (fun t ht => h t (by simp [ht]))]

theorem total_add (xs : List α) (f g : α → Int) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [total, ih]; omega

theorem total_scale (xs : List α) (c : Int) (f : α → Int) :
    total xs (fun x => c * f x) = c * total xs f := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp only [total, ih, Int.mul_add]

theorem total_const (xs : List α) (c : Int) :
    total xs (fun _ => c) = (xs.length : Int) * c := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih, Int.add_mul, Int.add_comm]

theorem total_swap (xs : List α) (ys : List β) (f : α → β → Int) :
    total xs (fun x => total ys (f x)) = total ys (fun y => total xs (fun x => f x y)) := by
  induction xs with
  | nil => simp [total, total_const]
  | cons x xs ih => simp only [total, total_add, ih]

theorem total_nonpos (xs : List α) {f : α → Int} (h : ∀ x ∈ xs, f x ≤ 0) :
    total xs f ≤ 0 := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr := ih (fun t ht => h t (by simp [ht]))
    simp only [total]; omega

def sumF {n : Nat} (f : Fin n → Int) := total (List.finRange n) f

theorem sum_congr {f g : Fin n → Int} (h : ∀ x, f x = g x) : sumF f = sumF g :=
  total_congr _ (fun x _ => h x)

theorem sum_add (f g : Fin n → Int) :
    sumF (fun x => f x + g x) = sumF f + sumF g := total_add _ _ _

theorem sum_scale (c : Int) (f : Fin n → Int) :
    sumF (fun x => c * f x) = c * sumF f := total_scale _ _ _

theorem sum_const (c : Int) : sumF (n := n) (fun _ => c) = (n : Int) * c := by
  rw [sumF, total_const, List.length_finRange]

theorem sum_swap (f : Fin n → Fin m → Int) :
    sumF (fun i => sumF (f i)) = sumF (fun j => sumF (fun i => f i j)) := total_swap _ _ _

def spike [DecidableEq α] (x y : α) : Int := if x = y then 1 else 0

theorem total_spike [DecidableEq α] (xs : List α) (k : α) (h : xs.Nodup) :
    total xs (fun x => spike k x) = (if k ∈ xs then 1 else 0) := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    obtain ⟨hn, hd⟩ := List.nodup_cons.mp h
    change spike k x + total xs (fun z => spike k z) = _
    rw [ih hd]
    simp only [List.mem_cons, spike]
    by_cases he : k = x
    · subst k; simp [hn]
    · simp [he]

theorem sum_spike (k : Fin n) : sumF (spike k) = 1 := by
  simp [sumF, total_spike _ _ (List.nodup_finRange n), List.mem_finRange]

theorem sum_eval (k : Fin n) (f : Fin n → Int) :
    sumF (fun x => f x * spike k x) = f k := by
  calc
    _ = sumF (fun x => f k * spike k x) := by
      apply sum_congr; intro x; by_cases h : k = x <;> simp [spike,h]
    _ = _ := by rw [sum_scale, sum_spike, Int.mul_one]

abbrev Matrix (b : Nat) := Fin b → Fin 157 → Int

def degree (I : Matrix b) (x : Fin 157) : Int := sumF (fun i => I i x)

def dot (f g : Fin n → Int) : Int := sumF (fun x => f x * g x)

structure PartialPlane (I : Matrix b) : Prop where
  binary : ∀ i x, I i x = 0 ∨ I i x = 1
  size : ∀ i, sumF (I i) = 13
  overlap : ∀ i j, dot (I i) (I j) = 1 + 12 * spike i j
  uniqueJoin : ∀ p x : Fin 157, p ≠ x →
    sumF (fun i => I i p * I i x) ≤ 1

theorem degree_sum {I : Matrix b} (P : PartialPlane I) :
    sumF (degree I) = (b : Int)*13 := by
  unfold degree
  rw [sum_swap (fun x i => I i x)]
  exact (sum_congr P.size).trans (sum_const 13)

theorem degree_second_moment {I : Matrix b} (P : PartialPlane I) :
    sumF (fun x => degree I x * degree I x) = (b : Int) * ((b : Int)+12) := by
  calc
    _ = sumF (fun x => sumF (fun i => I i x * degree I x)) := by
      apply sum_congr; intro x
      change degree I x * sumF (fun i => I i x) = _
      rw [← sum_scale (degree I x) (fun i => I i x)]
      apply sum_congr; intro i; exact Int.mul_comm _ _
    _ = sumF (fun i => sumF (fun x => I i x * degree I x)) := sum_swap _
    _ = sumF (fun i => sumF (fun j => dot (I i) (I j))) := by
      apply sum_congr; intro i
      calc
        _ = sumF (fun x => sumF (fun j => I i x * I j x)) := by
          apply sum_congr; intro x; exact (sum_scale _ _).symm
        _ = _ := sum_swap _
    _ = sumF (fun _ : Fin b => (b : Int)+12) := by
      apply sum_congr; intro i
      rw [sum_congr (P.overlap i),sum_add,sum_const,sum_scale,sum_spike]
      grind
    _ = _ := sum_const _

/-- This polynomial is positive at integer degree 12 and nowhere else. -/
def score (k : Int) : Int := (13-k)*(k-11)

theorem score_sum {I : Matrix b} (P : PartialPlane I) :
    sumF (fun x => score (degree I x)) = (157-(b : Int))*((b : Int)-143) := by
  calc
    _ = sumF (fun x => -143 + (24 * degree I x + (-1) * (degree I x * degree I x))) := by
      apply sum_congr; intro x; unfold score; grind
    _ = _ := by
      rw [sum_add, sum_const, sum_add, sum_scale, sum_scale, degree_sum P, degree_second_moment P]
      grind

theorem exists_degree_twelve {I : Matrix b} (P : PartialPlane I) (lo : 143 < b) (hi : b < 157) :
    ∃ p, degree I p = 12 := by
  apply Classical.byContradiction
  intro h
  have nonpos : sumF (fun x => score (degree I x)) ≤ 0 := by
    apply total_nonpos; intro x _
    have hn : degree I x ≠ 12 := fun eq => h ⟨x, eq⟩
    unfold score
    by_cases low : degree I x ≤ 11
    · have hp := Int.mul_nonneg (show 0 ≤ 13-degree I x by omega)
          (show 0 ≤ 11-degree I x by omega)
      grind
    · have hp := Int.mul_nonneg (show 0 ≤ degree I x-13 by omega)
          (show 0 ≤ degree I x-11 by omega)
      grind
  rw [score_sum P] at nonpos
  have hpos := Int.mul_pos (show (0 : Int) < 157-b by omega) (show (0 : Int) < b-143 by omega)
  omega

def pencil (I : Matrix b) (p x : Fin 157) : Int := sumF (fun i => I i p * I i x)

/-- Add p and the points still unjoined to p. -/
def newLine (I : Matrix b) (p x : Fin 157) : Int :=
  1 + ((-1)*pencil I p x + 12*spike p x)

theorem pencil_self {I : Matrix b} (P : PartialPlane I) (p : Fin 157) :
    pencil I p p = degree I p := by
  apply sum_congr; intro i
  rcases P.binary i p with h|h <;> simp [h]

theorem pencil_nonneg {I : Matrix b} (P : PartialPlane I) (p x : Fin 157) :
    0 ≤ pencil I p x := by
  have : sumF (fun i => (-1)*(I i p * I i x)) ≤ 0 := by
    apply total_nonpos; intro i _
    rcases P.binary i p with h|h <;> rcases P.binary i x with k|k <;> simp [h,k]
  rw [sum_scale] at this
  unfold pencil; omega

theorem new_binary {I : Matrix b} (P : PartialPlane I) (p : Fin 157) (hd : degree I p = 12) :
    ∀ x, newLine I p x = 0 ∨ newLine I p x = 1 := by
  intro x
  by_cases he : p = x
  · subst x; simp [newLine, pencil_self P, hd, spike]
  · have h₁ := pencil_nonneg P p x
    have h₂ : pencil I p x ≤ 1 := P.uniqueJoin p x he
    simp [newLine, spike, he]; omega

theorem pencil_sum {I : Matrix b} (P : PartialPlane I) (p : Fin 157) :
    sumF (pencil I p) = 13*degree I p := by
  unfold pencil
  rw [sum_swap (fun x i => I i p * I i x)]
  calc
    _ = sumF (fun i => 13 * I i p) := by
      apply sum_congr; intro i; rw [sum_scale, P.size]; exact Int.mul_comm _ _
    _ = _ := sum_scale _ _

theorem new_size {I : Matrix b} (P : PartialPlane I) (p : Fin 157) (hd : degree I p = 12) :
    sumF (newLine I p) = 13 := by
  unfold newLine
  rw [sum_add, sum_const, sum_add, sum_scale, sum_scale, sum_spike, pencil_sum P, hd]
  decide

theorem pencil_dot {I : Matrix b} (P : PartialPlane I) (p : Fin 157) (j : Fin b) :
    dot (pencil I p) (I j) = degree I p + 12 * I j p := by
  calc
    _ = sumF (fun x => sumF (fun i => I i p * (I i x * I j x))) := by
      apply sum_congr; intro x
      rw [Int.mul_comm, pencil, ← sum_scale (I j x) (fun i => I i p * I i x)]
      apply sum_congr; intro i; grind
    _ = sumF (fun i => I i p * dot (I i) (I j)) := by
      rw [sum_swap]; apply sum_congr; intro i; exact sum_scale _ _
    _ = sumF (fun i => I i p + 12 * (I i p * spike j i)) := by
      apply sum_congr; intro i; rw [P.overlap]
      by_cases h : i = j
      · subst j; simp [spike]; grind
      · simp [spike,h,Ne.symm h]
    _ = _ := by rw [sum_add,sum_scale,sum_eval]; rfl

theorem new_meets_once {I : Matrix b} (P : PartialPlane I) (p : Fin 157)
    (hd : degree I p = 12) (j : Fin b) : dot (newLine I p) (I j) = 1 := by
  calc
    _ = sumF (fun x => I j x + ((-1)*(pencil I p x * I j x) + 12*(I j x * spike p x))) := by
      apply sum_congr; intro x; unfold newLine; grind
    _ = _ := by
      rw [sum_add,P.size,sum_add,sum_scale,sum_scale,sum_eval]
      change 13 + (-1 * dot (pencil I p) (I j) + 12 * I j p) = 1
      rw [pencil_dot P,hd]; grind

/-- For 144 through 156 lines a further line always exists. The explicit
    inequality against every old row follows from the overlap being 1
    whereas a row's self-intersection is 13. -/
theorem extension {I : Matrix b} (P : PartialPlane I) (lo : 143 < b) (hi : b < 157) :
    ∃ L : Fin 157 → Int, (∀ x, L x = 0 ∨ L x = 1) ∧ sumF L = 13 ∧
      (∀ j, dot L (I j) = 1) ∧ (∀ j, L ≠ I j) := by
  obtain ⟨p,hd⟩ := exists_degree_twelve P lo hi
  refine ⟨newLine I p,new_binary P p hd,new_size P p hd,new_meets_once P p hd,?_⟩
  intro j eq
  have h := new_meets_once P p hd j
  rw [eq,P.overlap] at h
  simp [spike] at h


theorem score_nonpos {k : Int} (h : k ≠ 12) : score k ≤ 0 := by
  unfold score
  by_cases low : k ≤ 11
  · exact Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
  · have hp := Int.mul_nonneg (show 0 ≤ k-13 by omega) (show 0 ≤ k-11 by omega)
    grind

theorem sum_mono {f g : Fin n → Int} (h : ∀ x, f x ≤ g x) : sumF f ≤ sumF g := by
  have hn : sumF (fun x => f x + (-1)*g x) ≤ 0 := by
    apply total_nonpos; intro x _; have := h x; omega
  rw [sum_add,sum_scale] at hn; omega

theorem zero_of_nonpos_sum_zero {f : Fin n → Int} (h : ∀ x, f x ≤ 0) (hs : sumF f = 0)
    (k : Fin n) : f k = 0 := by
  have hle : sumF f ≤ sumF (fun x => f k * spike k x) := by
    apply sum_mono; intro x
    by_cases he : k = x
    · subst x; simp [spike]
    · simpa [spike,he] using h x
  rw [sum_scale,sum_spike,hs] at hle
  have := h k; omega

/-- Exactly at 143 lines the pencil method either applies directly, or
    exactly 91 points have degree eleven and the other 66 have degree thirteen. -/
theorem boundary {I : Matrix 143} (P : PartialPlane I) (h : ¬∃ p, degree I p = 12) :
    (∀ x, degree I x = 11 ∨ degree I x = 13) ∧
    sumF (fun x => if degree I x = 11 then (1 : Int) else 0) = 91 := by
  have hz : sumF (fun x => score (degree I x)) = 0 := by rw [score_sum P]; decide
  have types (x) : degree I x = 11 ∨ degree I x = 13 := by
    have eq := zero_of_nonpos_sum_zero (fun y => score_nonpos (fun he => h ⟨y,he⟩)) hz x
    rcases Int.mul_eq_zero.mp eq with ha|ha <;> omega
  refine ⟨types, ?_⟩
  have mass := degree_sum P
  have eq : sumF (degree I) =
      sumF (fun x => 13 + (-2)*(if degree I x = 11 then (1 : Int) else 0)) := by
    apply sum_congr; intro x; rcases types x with hx|hx <;> simp [hx]
  rw [sum_add,sum_const,sum_scale] at eq
  omega

theorem total_map (xs : List α) (f : α → β) (g : β → Int) :
    total (xs.map f) g = total xs (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs h => simp only [List.map_cons,total,h]

theorem sum_succ (f : Fin (n+1) → Int) : sumF f = f 0 + sumF (fun i => f i.succ) := by
  simp [sumF,List.finRange_succ,total,total_map]

def prepend (L : Fin 157 → Int) (I : Matrix b) : Matrix (b+1) := Fin.cases L I

theorem extend_matrix {I : Matrix b} (P : PartialPlane I) {L : Fin 157 → Int}
    (binL : ∀ x, L x = 0 ∨ L x = 1) (sizeL : sumF L = 13)
    (meetL : ∀ j, dot L (I j) = 1) : PartialPlane (prepend L I) := by
  have no_old_pair (p x : Fin 157) (hx : p ≠ x) (hpL : L p = 1) (hxL : L x = 1)
      (i : Fin b) : I i p * I i x = 0 := by
    rcases P.binary i p with hp|hp
    · simp [hp]
    rcases P.binary i x with hq|hq
    · simp [hq]
    have bad : sumF (fun y => spike p y + spike x y) ≤ dot L (I i) := by
      apply sum_mono; intro y
      by_cases h : p = y
      · subst y; simp [spike, Ne.symm hx,hpL,hp]
      by_cases h' : x = y
      · subst y; simp [spike,h,hxL,hq]
      rcases binL y with hl|hl <;> rcases P.binary i y with hi|hi <;> simp [spike,h,h',hl,hi]
    rw [sum_add,sum_spike,sum_spike,meetL] at bad; omega
  refine ⟨?_,?_,?_,?_⟩
  · intro i; exact Fin.cases binL P.binary i
  · intro i; exact Fin.cases sizeL P.size i
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun c => ?_) j
    · change dot L L = _
      have eq : dot L L = sumF L := by
        apply sum_congr; intro x; rcases binL x with h|h <;> simp [h]
      rw [eq,sizeL]; simp [spike]
    · simpa [prepend,spike,Ne.symm (Fin.succ_ne_zero c)] using meetL c
    · have eq : dot (I a) L = dot L (I a) := sum_congr (fun _ => Int.mul_comm _ _)
      simpa [prepend,spike,Fin.succ_ne_zero a] using eq.trans (meetL a)
    · simpa [prepend,spike] using P.overlap a c
  · intro p x hx
    rw [sum_succ]
    change L p * L x + sumF (fun i => I i p * I i x) ≤ 1
    rcases binL p with hp|hp
    · simpa [hp] using P.uniqueJoin p x hx
    rcases binL x with hq|hq
    · simpa [hq] using P.uniqueJoin p x hx
    rw [sum_congr (no_old_pair p x hx hp hq),sum_const,hp,hq]
    simp

/-- Any valid starting system with at least 144 and at most 157 lines
    can be enlarged to a full 157-line matrix. The sequence prepends lines,
    so all old rows are preserved. -/
theorem reach_full {I : Matrix b} (P : PartialPlane I) (lo : 143 < b) (hi : b ≤ 157) :
    ∃ J : Matrix 157, PartialPlane J ∧ ∀ i, ∃ j, I i = J j := by
  generalize hdist : 157-b = distance
  induction distance generalizing b with
  | zero =>
    have hb : b = 157 := by omega
    subst b; exact ⟨I,P,fun i => ⟨i,rfl⟩⟩
  | succ d ih =>
    have hlt : b < 157 := by omega
    obtain ⟨L,binL,sizeL,meetL,_⟩ := extension P lo hlt
    obtain ⟨J,PJ,retain⟩ := ih (extend_matrix P binL sizeL meetL) (by omega) (by omega) (by omega)
    exact ⟨J,PJ,fun i => retain i.succ⟩


/-- The missing-neighbor matrix. Its diagonal is zero. -/
def missing (I : Matrix b) (p x : Fin 157) : Int :=
  1 + ((-1)*pencil I p x + (degree I p - 1)*spike p x)

theorem pencil_symm (I : Matrix b) (p x : Fin 157) : pencil I p x = pencil I x p :=
  sum_congr (fun _ => Int.mul_comm _ _)

theorem missing_diag {I : Matrix b} (P : PartialPlane I) (p : Fin 157) :
    missing I p p = 0 := by simp [missing,pencil_self P,spike]; omega

theorem missing_symm (I : Matrix b) (p x : Fin 157) : missing I p x = missing I x p := by
  by_cases eq : p = x
  · subst x; rfl
  · simp [missing,spike,eq,Ne.symm eq,pencil_symm I p x]

theorem missing_binary {I : Matrix b} (P : PartialPlane I) (p x : Fin 157) :
    missing I p x = 0 ∨ missing I p x = 1 := by
  by_cases eq : p = x
  · subst x; exact Or.inl (missing_diag P p)
  · have h₁ := pencil_nonneg P p x
    have h₂ : pencil I p x ≤ 1 := P.uniqueJoin p x eq
    simp [missing,spike,eq]; omega

theorem missing_sum {I : Matrix b} (P : PartialPlane I) (p : Fin 157) :
    sumF (missing I p) = 156 - 12 * degree I p := by
  unfold missing
  rw [sum_add,sum_const,sum_add,sum_scale,sum_scale,pencil_sum P,sum_spike]; omega

theorem pencil_pencil {I : Matrix b} (P : PartialPlane I) (p q : Fin 157) :
    dot (pencil I p) (pencil I q) = degree I p * degree I q + 12 * pencil I p q := by
  calc
    _ = sumF (fun x => sumF (fun i => I i q * (pencil I p x * I i x))) := by
      apply sum_congr; intro x
      change pencil I p x * sumF (fun i => I i q * I i x) = _
      rw [← sum_scale]
      apply sum_congr; intro i; grind
    _ = sumF (fun i => I i q * dot (pencil I p) (I i)) := by
      rw [sum_swap]; apply sum_congr; intro i; exact sum_scale _ _
    _ = sumF (fun i => degree I p * I i q + 12 * (I i p * I i q)) := by
      apply sum_congr; intro i; rw [pencil_dot P]; grind
    _ = _ := by rw [sum_add,sum_scale,sum_scale]; rfl

theorem missing_dot_fn {I : Matrix b} (p : Fin 157) (f : Fin 157 → Int) :
    dot (missing I p) f = sumF f - dot (pencil I p) f + (degree I p - 1)*f p := by
  calc
    _ = sumF (fun x => f x + ((-1)*(pencil I p x * f x) +
                (degree I p-1)*(f x * spike p x))) := by
      apply sum_congr; intro x; unfold missing; grind
    _ = _ := by rw [sum_add,sum_add,sum_scale,sum_scale,sum_eval]; unfold dot; omega

theorem dot_comm (f g : Fin n → Int) : dot f g = dot g f := sum_congr (fun _ => Int.mul_comm _ _)

/-- In the exceptional degree-eleven set, a missing pair has twelve common
    missing neighbors; a pair already joined has four. -/
theorem common_missing {I : Matrix 143} (P : PartialPlane I)
    {p q : Fin 157} (ne : p ≠ q) (hp : degree I p = 11) (hq : degree I q = 11) :
    dot (missing I p) (missing I q) = 4 + 8*missing I p q := by
  rw [missing_dot_fn, missing_sum P, dot_comm (pencil I p), missing_dot_fn, pencil_sum P,
      pencil_pencil P, hp, hq, missing_symm I q p]
  simp [missing,spike,ne]; rw [pencil_symm I q p]; grind


noncomputable section
open Classical

abbrev Family := Fin 157 → Prop
def mark (p : Prop) : Int := if p then 1 else 0
def wt (A : Family) : Int := sumF (fun x => mark (A x))

theorem wt_congr {A B : Family} (h : ∀ x, A x ↔ B x) : wt A = wt B := by
  apply sum_congr; intro x; simp only [mark,h x]

theorem wt_mono {A B : Family} (h : ∀ x, A x → B x) : wt A ≤ wt B := by
  apply sum_mono; intro x; unfold mark; split <;> split <;> grind

theorem wt_pos {A : Family} (h : 0 < wt A) : ∃ x, A x := by
  apply Classical.byContradiction; intro hn
  have zero : wt A = 0 := by
    calc
      _ = sumF (n := 157) (fun _ => 0) := by
        apply sum_congr; intro x; have : ¬A x := fun hx => hn ⟨x,hx⟩; simp [mark,this]
      _ = 0 := by rw [sum_const]; decide
  omega

theorem wt_split (A B : Family) :
    wt A = wt (fun x => A x ∧ B x) + wt (fun x => A x ∧ ¬B x) := by
  unfold wt; rw [← sum_add]; apply sum_congr; intro x
  by_cases ha : A x <;> by_cases hb : B x <;> simp [mark,ha,hb]

theorem wt_disjoint {A B : Family} (hd : ∀ x, A x → ¬B x) :
    wt (fun x => A x ∨ B x) = wt A + wt B := by
  unfold wt; rw [← sum_add]; apply sum_congr; intro x
  by_cases ha : A x
  · simp [mark,ha,hd x ha]
  · simp [mark,ha]

theorem wt_single (p : Fin 157) : wt (fun x => p = x) = 1 := by
  calc
    _ = sumF (spike p) := by
      apply sum_congr; intro x; by_cases h : p = x <;> simp [mark,spike,h]
    _ = 1 := sum_spike p

theorem wt_outside {U A : Family} (sub : ∀ x, A x → U x) :
    wt (fun x => U x ∧ ¬A x) = wt U - wt A := by
  have same : wt (fun x => U x ∧ A x) = wt A :=
    wt_congr (fun x => ⟨And.right,fun h => ⟨sub x h,h⟩⟩)
  have h := wt_split U A; omega

/-- A triangle-free 11-regular graph on 24 vertices contains an independent
    set of size 12. Construct it from the neighborhoods of one edge. -/
theorem independent_twelve (U : Family) (H : Fin 157 → Family) (order : wt U = 24)
    (sub : ∀ {v x}, H v x → U x)
    (symm : ∀ {v x}, H v x → H x v)
    (deg : ∀ v, U v → wt (H v) = 11)
    (triangle : ∀ {v w x}, H v w → H v x → ¬H w x) :
    ∃ C : Family, wt C = 12 ∧ (∀ x, C x → U x) ∧
      ∀ v x, C v → C x → ¬H v x := by
  obtain ⟨v,hv⟩ := wt_pos (A := U) (by omega)
  obtain ⟨w,hw⟩ := wt_pos (A := H v) (by rw [deg v hv]; decide)
  have uw := sub hw
  let A := H v
  let B := H w
  have ab : ∀ x, A x → ¬ B x := fun _ hx => triangle hw hx
  have pairCount : wt (fun x => A x ∨ B x) = 22 := by
    rw [wt_disjoint ab,deg v hv,deg w uw]
    decide
  let R : Family := fun x => U x ∧ ¬(A x ∨ B x)
  have rCount : wt R = 2 := by
    rw [show wt R = _ from wt_outside (A := fun x => A x ∨ B x)
        (U := U) (fun _ h => h.elim (fun e => sub e) (fun e => sub e)),order,pairCount]
    decide
  obtain ⟨t,ht⟩ := wt_pos (A := R) (by omega)
  obtain ⟨ut,out⟩ := ht
  have group_bound (D E : Family) (part : ∀ x, D x ∨ E x ↔ A x ∨ B x)
      (hD : ∀ a x, D a → D x → ¬H a x)
      (e11 : wt E = 11) (a : Fin 157) (ha : D a) (hta : H t a) :
      wt (fun x => E x ∧ H t x) ≤ 2 := by
    have contains : ∀ x, H a x → E x ∨ R x := by
      intro x ax
      by_cases he : E x
      · exact Or.inl he
      · refine Or.inr ⟨sub ax, ?_⟩
        intro hx
        rcases (part x).mpr hx with dx|ex
        · exact hD a x ha dx ax
        · exact he ex
    have small : wt (fun x => H a x ∧ ¬E x) ≤ 2 := by
      rw [←rCount]; apply wt_mono; intro x hx; exact (contains x hx.1).resolve_left hx.2
    have opposite := wt_split (H a) E
    rw [deg a (sub hta)] at opposite
    have disj : ∀ x, (H a x ∧ E x) → ¬(E x ∧ H t x) := by
      intro x ax tx; exact triangle hta tx.2 ax.1
    have bound : wt (fun x => (H a x ∧ E x) ∨ (E x ∧ H t x)) ≤ wt E :=
      wt_mono (fun _ hx => hx.elim And.right And.left)
    rw [wt_disjoint disj] at bound
    omega
  have ia : ∀ a x, A a → A x → ¬H a x := fun _ _ => triangle
  have ib : ∀ a x, B a → B x → ¬H a x := fun _ _ => triangle
  have side : (∀ x, A x → ¬H t x) ∨ (∀ x, B x → ¬H t x) := by
    apply Classical.byContradiction; intro neither
    have witness (D : Family) (h : ¬∀ x, D x → ¬H t x) : ∃ a, D a ∧ H t a := by
      apply Classical.byContradiction; intro hn; exact h (fun x dx tx => hn ⟨x,dx,tx⟩)
    obtain ⟨a,ha,ta⟩ := witness A (fun e => neither (Or.inl e))
    obtain ⟨b,hb,tb⟩ := witness B (fun e => neither (Or.inr e))
    have sB := group_bound A B (fun _ => Iff.rfl) ia (deg w uw) a ha ta
    have sA := group_bound B A (fun _ => or_comm) ib (deg v hv) b hb tb
    have rem_le := wt_mono (A := fun x => H t x ∧ ¬(A x ∨ B x)) (B := R)
      (fun x h => ⟨sub h.1,h.2⟩)
    have split_t := wt_split (H t) (fun x => A x ∨ B x)
    have partition : wt (fun x => H t x ∧ (A x ∨ B x)) =
       wt (fun x => A x ∧ H t x) + wt (fun x => B x ∧ H t x) := by
      rw [← wt_disjoint (A := fun x => A x ∧ H t x) (B := fun x => B x ∧ H t x)
          (fun x ha hb => ab x ha.1 hb.1)]
      apply wt_congr; intro x; constructor
      · intro ⟨ht,h⟩; exact h.elim (fun a => Or.inl ⟨a,ht⟩) (fun b => Or.inr ⟨b,ht⟩)
      · intro h; exact h.elim (fun a => ⟨a.2,Or.inl a.1⟩) (fun b => ⟨b.2,Or.inr b.1⟩)
    rw [deg t ut,partition] at split_t
    omega
  have finish (D : Family) (d11 : wt D = 11) (dt : ¬D t) (du : ∀ x, D x → U x)
      (di : ∀ a x, D a → D x → ¬H a x) (htd : ∀ x, D x → ¬H t x) :
      ∃ C : Family, wt C = 12 ∧ (∀ x, C x → U x) ∧ ∀ a x, C a → C x → ¬H a x := by
    refine ⟨fun x => D x ∨ t = x, ?_, ?_, ?_⟩
    · rw [wt_disjoint (A := D) (B := fun x => t = x) (fun _ dx h => dt (h ▸ dx)),d11,wt_single]
      decide
    · intro x hx; exact hx.elim (du x) (fun h => h ▸ ut)
    · intro a x ha hx
      rcases ha with da|rfl <;> rcases hx with dx|rfl
      · exact di a x da dx
      · exact fun e => htd a da (symm e)
      · exact htd x dx
      · exact fun e => triangle e e e
  rcases side with s|s
  · exact finish A (deg v hv) (fun h => out (Or.inl h)) (fun _ h => sub h) ia s
  · exact finish B (deg w uw) (fun h => out (Or.inr h)) (fun _ h => sub h) ib s


theorem three_sets {U A B C : Family}
    (sa : ∀ x, A x → U x) (sb : ∀ x, B x → U x) (sc : ∀ x, C x → U x) :
    wt A + wt B + wt C ≤ wt U + wt (fun x => A x ∧ B x) +
      wt (fun x => A x ∧ C x) + wt (fun x => B x ∧ C x) := by
  unfold wt
  repeat rw [←sum_add]
  apply sum_mono; intro x
  by_cases a : A x <;> by_cases b : B x <;> by_cases c : C x <;> by_cases u : U x <;>
    simp_all [mark]

def edge (I : Matrix b) (p x : Fin 157) : Prop := missing I p x = 1

theorem edge_mark {I : Matrix b} (P : PartialPlane I) (p x : Fin 157) :
    mark (edge I p x) = missing I p x := by
  rcases missing_binary P p x with h|h <;> simp [mark,edge,h]

theorem edge_irrefl {I : Matrix b} (P : PartialPlane I) (p : Fin 157) : ¬edge I p p := by
  simp [edge,missing_diag P]

theorem edge_flip {I : Matrix b} {x y : Fin 157} (h : edge I x y) : edge I y x := by
  unfold edge at *; rw [missing_symm]; exact h

theorem edge_degree {I : Matrix b} (P : PartialPlane I) (p : Fin 157) :
    wt (edge I p) = 156 - 12 * degree I p :=
  (sum_congr (edge_mark P p)).trans (missing_sum P p)

theorem wt_common {I : Matrix 143} (P : PartialPlane I) {v w : Fin 157}
    (ne : v ≠ w) (hv : degree I v = 11) (hw : degree I w = 11) :
    wt (fun x => edge I v x ∧ edge I w x) = 4 + 8 * missing I v w := by
  calc
    _ = dot (missing I v) (missing I w) := by
      apply sum_congr; intro x
      rcases missing_binary P v x with a|a <;> rcases missing_binary P w x with b|b <;>
        simp [mark,edge,a,b]
    _ = _ := common_missing P ne hv hw

theorem marked_clique {I : Matrix 143} (P : PartialPlane I)
    (htypes : ∀ x, degree I x = 11 ∨ degree I x = 13)
    (p : Fin 157) (hp : degree I p = 11) :
    ∃ D : Family, wt D = 13 ∧ (∀ x, D x → degree I x = 11) ∧
      ∀ x y, D x → D y → x ≠ y → edge I x y := by
  let U := edge I p
  have order : wt U = 24 := by rw [edge_degree P,hp]; decide
  have no_loop := edge_irrefl P
  have degU (v) (hv : U v) : degree I v = 11 := by
    rcases htypes v with h|h
    · exact h
    · have hzero := edge_degree P v
      rw [h] at hzero
      have mono : wt (fun x => p = x) ≤ wt (edge I v) :=
        wt_mono (fun _ e => e ▸ edge_flip hv)
      rw [wt_single] at mono; omega
  let H (v x : Fin 157) : Prop := U v ∧ U x ∧ v ≠ x ∧ ¬edge I v x
  let good (v x : Fin 157) : Prop := U x ∧ (v = x ∨ edge I v x)
  have good13 (v) (uv : U v) : wt (good v) = 13 := by
    have ne : p ≠ v := fun h => no_loop _ (h ▸ uv)
    have cnt := wt_common P ne hp (degU v uv)
    change missing I p v = 1 at uv
    rw [uv] at cnt
    calc
      _ = wt (fun x => (v = x) ∨ (edge I p x ∧ edge I v x)) := by
        apply wt_congr; intro x; change (U x ∧ (v = x ∨ edge I v x)) ↔ _
        constructor
        · intro ⟨ux,hh⟩; exact hh.elim Or.inl (fun ex => Or.inr ⟨ux,ex⟩)
        · intro h; rcases h with rfl|⟨ux,ex⟩
          · exact ⟨uv,Or.inl rfl⟩
          · exact ⟨ux,Or.inr ex⟩
      _ = _ := by
        rw [wt_disjoint (fun x (hh : v = x) (ee : edge I p x ∧ edge I v x) =>
            no_loop v (hh ▸ ee.2)),wt_single]
        omega
  have Hdeg (v) (uv : U v) : wt (H v) = 11 := by
    have rem := wt_outside (U := U) (A := good v) (fun _ hx => hx.1)
    rw [order,good13 v uv] at rem
    calc
      _ = wt (fun x => U x ∧ ¬good v x) := by
        apply wt_congr; intro x
        change (U v ∧ U x ∧ v ≠ x ∧ ¬edge I v x) ↔ (U x ∧ ¬(U x ∧ (v = x ∨ edge I v x)))
        simp only [uv,true_and]; by_cases ux : U x <;> simp [ux]
      _ = _ := rem
  have Hsymm {v x : Fin 157} (h : H v x) : H x v :=
    ⟨h.2.1,h.1,Ne.symm h.2.2.1,fun e => h.2.2.2 (edge_flip e)⟩
  have overlap3 {v w : Fin 157} (h : H v w) :
      wt (fun x => good v x ∧ good w x) ≤ 3 := by
    obtain ⟨uv,uw,vw,nonedge⟩ := h
    have cz := wt_common P vw (degU _ uv) (degU _ uw)
    have zero : missing I v w = 0 := (missing_binary P _ _).resolve_right nonedge
    rw [zero] at cz
    let A : Family := fun x => good v x ∧ good w x
    have outside : ¬ U p := no_loop p
    have sub : ∀ x, (p = x ∨ A x) → edge I v x ∧ edge I w x := by
      intro x hx
      rcases hx with rfl|⟨av,aw⟩
      · exact ⟨edge_flip uv,edge_flip uw⟩
      · obtain ⟨_,ev⟩ := av; obtain ⟨_,ew⟩ := aw
        rcases ev with rfl|ev <;> rcases ew with h|ew
        · exact False.elim (vw h.symm)
        · exact False.elim (nonedge (edge_flip ew))
        · exact False.elim (nonedge (h ▸ ev))
        · exact ⟨ev,ew⟩
    have bound := wt_mono sub
    rw [wt_disjoint (A := fun x => p = x) (B := A)
      (fun x eq hx => outside (eq ▸ hx.1.1)),wt_single] at bound
    change wt A ≤ 3; omega
  have tri {v w x : Fin 157} (vw : H v w) (vx : H v x) (wx : H w x) : False := by
    have bound := three_sets (A := good v) (B := good w) (C := good x) (U := U)
      (fun _ e => e.1) (fun _ e => e.1) (fun _ e => e.1)
    rw [good13 v vw.1,good13 w vw.2.1,good13 x vx.2.1,order] at bound
    have h1 := overlap3 vw; have h2 := overlap3 vx; have h3 := overlap3 wx
    omega
  obtain ⟨C,cnt,sub,indep⟩ :=
    independent_twelve U H order (fun h => h.2.1) Hsymm Hdeg tri
  refine ⟨fun x => p = x ∨ C x,?_,?_,?_⟩
  · rw [wt_disjoint (A := fun x => p = x) (B := C)
      (by intro x h cx; subst x; exact no_loop p (sub p cx)),wt_single,cnt]; decide
  · intro x hx; exact hx.elim (fun h => h ▸ hp) (fun e => degU _ (sub _ e))
  · intro x y hx hy ne
    rcases hx with rfl|cx <;> rcases hy with h|cy
    · exact False.elim (ne h)
    · exact sub y cy
    · exact h ▸ edge_flip (sub x cx)
    · exact Classical.byContradiction (fun he => indep x y cx cy ⟨sub _ cx,sub _ cy,ne,he⟩)

theorem summand_le {f : Fin n → Int} (nonneg : ∀ x, 0 ≤ f x) (k : Fin n) :
    f k ≤ sumF f := by
  have h : sumF (fun x => f k * spike k x) ≤ sumF f := by
    apply sum_mono; intro x
    by_cases he : k = x
    · subst x; simp [spike]
    · simpa [spike,he] using nonneg x
  simpa [sum_scale,sum_spike] using h

theorem edge_no_line {I : Matrix b} (P : PartialPlane I) {p q : Fin 157}
    (ne : p ≠ q) (e : edge I p q) (i : Fin b) (hp : I i p = 1) (hq : I i q = 1) : False := by
  have nonneg (j) : 0 ≤ I j p * I j q := by
    rcases P.binary j p with a|a <;> rcases P.binary j q with c|c <;> simp [a,c]
  have h := summand_le nonneg i
  rw [hp,hq] at h
  change 1*1 ≤ pencil I p q at h
  simp [edge,missing,spike,ne] at e
  omega

theorem clique_line {I : Matrix 143} (P : PartialPlane I) {D : Family} (count : wt D = 13)
    (degrees : ∀ x, D x → degree I x = 11)
    (clique : ∀ x y, D x → D y → x ≠ y → edge I x y) :
    ∃ L : Fin 157 → Int, (∀ x, L x = 0 ∨ L x = 1) ∧ sumF L = 13 ∧
      ∀ i, dot L (I i) = 1 := by
  let L : Fin 157 → Int := fun x => mark (D x)
  have binary (x) : L x = 0 ∨ L x = 1 := by by_cases h : D x <;> simp [L,mark,h]
  have atMost (i) : dot L (I i) ≤ 1 := by
    by_cases exists_pt : ∃ p, D p ∧ I i p = 1
    · obtain ⟨p,dp,ip⟩ := exists_pt
      have h : dot L (I i) ≤ sumF (spike p) := by
        apply sum_mono; intro x
        by_cases px : p = x
        · subst x; simp [L,mark,dp,ip,spike]
        by_cases dx : D x
        · have ix := (P.binary i x).resolve_right
            (edge_no_line P px (clique p x dp dx px) i ip)
          simp [L,mark,dx,ix,spike,px]
        · simp [L,mark,dx,spike,px]
      rwa [sum_spike] at h
    · have h : dot L (I i) = sumF (n := 157) (fun _ => 0) := by
        apply sum_congr; intro x
        by_cases dx : D x
        · have ix := (P.binary i x).resolve_right (fun ix => exists_pt ⟨x,dx,ix⟩)
          simp [L,mark,dx,ix]
        · simp [L,mark,dx]
      rw [h,sum_const]; decide
  have allInc : sumF (fun i => dot L (I i)) = 143 := by
    calc
      _ = sumF (fun x => L x * degree I x) := by
        unfold dot; rw [sum_swap]; apply sum_congr; intro x; exact sum_scale _ _
      _ = sumF (fun x => 11 * L x) := by
        apply sum_congr; intro x
        by_cases dx : D x
        · simp [L,mark,dx,degrees x dx]
        · simp [L,mark,dx]
      _ = _ := by rw [sum_scale]; change 11 * wt D = 143; rw [count]; decide
  refine ⟨L,binary,count,?_⟩
  intro i
  have zero : sumF (fun j => dot L (I j) + (-1)) = 0 := by rw [sum_add,allInc,sum_const]; decide
  have eq := zero_of_nonpos_sum_zero (fun j => show dot L (I j) + (-1) ≤ 0 by have := atMost j; omega) zero i
  omega

/-- The remaining projective-plane extension case at 143 lines. -/
theorem extension143 {I : Matrix 143} (P : PartialPlane I) :
    ∃ L : Fin 157 → Int, (∀ x, L x = 0 ∨ L x = 1) ∧ sumF L = 13 ∧
      ∀ i, dot L (I i) = 1 := by
  by_cases deg12 : ∃ p, degree I p = 12
  · obtain ⟨p,hp⟩ := deg12
    exact ⟨_,new_binary P p hp,new_size P p hp,new_meets_once P p hp⟩
  obtain ⟨types,count⟩ := boundary P deg12
  have count' : wt (fun x => degree I x = 11) = 91 := by
    calc
      _ = sumF (fun x => if degree I x = 11 then (1 : Int) else 0) := by
        apply sum_congr; intro x; by_cases h : degree I x = 11 <;> simp [mark,h]
      _ = 91 := count
  obtain ⟨p,hp⟩ := wt_pos (A := fun x => degree I x = 11) (by omega)
  obtain ⟨D,w,d,c⟩ := marked_clique P types p hp
  exact clique_line P w d c

/-- Every order-12 partial plane with between 143 and 157 lines extends to a
    full incidence matrix retaining every original row. -/
theorem complete_from_143 {I : Matrix b} (P : PartialPlane I) (lo : 143 ≤ b) (hi : b ≤ 157) :
    ∃ J : Matrix 157, PartialPlane J ∧ ∀ i, ∃ j, I i = J j := by
  by_cases h : b = 143
  · subst b
    obtain ⟨L,binL,sizeL,meetL⟩ := extension143 P
    obtain ⟨J,PJ,keep⟩ := reach_full (extend_matrix P binL sizeL meetL) (by decide) (by decide)
    exact ⟨J,PJ,fun i => keep i.succ⟩
  · exact reach_full P (by omega) hi

end
end Order12Extension

namespace Order12Extension
open Finset

theorem sumF_eq_sum (f : Fin n → Int) : sumF f = ∑ x, f x := by
  induction n with
  | zero => simp [sumF,List.finRange,total]
  | succ n h => rw [sum_succ, Fin.sum_univ_succ, h]

theorem indicators (A : Finset (Fin n)) :
    sumF (fun x => if x ∈ A then (1 : Int) else 0) = (A.card : Int) := by
  rw [sumF_eq_sum, Finset.sum_boole]; simp

def rowOf (A : Finset (Fin 157)) (x : Fin 157) : Int := if x ∈ A then 1 else 0

theorem dot_card (A B : Finset (Fin 157)) :
    dot (rowOf A) (rowOf B) = ((A ∩ B).card : Int) := by
  calc
    _ = sumF (fun x => if x ∈ A ∩ B then (1 : Int) else 0) := by
      apply sum_congr; intro x
      by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [rowOf,ha,hb]
    _ = _ := indicators _

theorem intersection_one {A B : Finset (Fin 157)} :
    (A ∩ B).card = 1 ↔ ∃! x, x ∈ A ∧ x ∈ B := by
  rw [Finset.card_eq_one]; constructor
  · rintro ⟨x,hx⟩
    have mem : x ∈ A ∩ B := hx ▸ Finset.mem_singleton_self _
    exact ⟨x, Finset.mem_inter.mp mem, fun y hy => Finset.eq_of_mem_singleton
      (hx ▸ Finset.mem_inter.mpr hy)⟩
  · rintro ⟨x,mem,unique⟩
    refine ⟨x,?_⟩; ext y
    simp only [Finset.mem_inter, Finset.mem_singleton]
    exact ⟨fun h => unique _ h,fun e => e ▸ mem⟩

theorem extend_finsets (S : Finset (Finset (Fin 157))) (lo : 143 ≤ S.card) (hi : S.card < 157)
    (size : ∀ a ∈ S, a.card = 13)
    (meets : ∀ a ∈ S, ∀ c ∈ S, a ≠ c → ∃! x, x ∈ a ∧ x ∈ c) :
    ∃ T : Finset (Finset (Fin 157)), S ⊆ T ∧ T.card = S.card + 1 ∧
      (∀ a ∈ T, a.card = 13) ∧ ∀ a ∈ T, ∀ c ∈ T, a ≠ c → ∃! x, x ∈ a ∧ x ∈ c := by
  classical
  let e := (Fintype.equivFin ↥S).symm
  let B (i) := (e i).val
  have Bin (i) : B i ∈ S := (e i).property
  have Binj : Function.Injective B := fun _ _ h => e.injective (Subtype.ext h)
  let I (i) := rowOf (B i)
  have P : PartialPlane I := by
    constructor
    · intro i x; by_cases hx : x ∈ B i <;> simp [I,rowOf,hx]
    · intro i; change sumF (fun x => if x ∈ B i then (1 : Int) else 0) = 13
      rw [indicators,size _ (Bin i)]; decide
    · intro i j; change dot (rowOf _) (rowOf _) = _
      rw [dot_card]
      by_cases eq : i = j
      · subst j; simp [spike,size _ (Bin i)]
      · have h := intersection_one.mpr (meets _ (Bin i) _ (Bin j) (fun he => eq (Binj he)))
        simp [spike,eq,h]
    · intro p q ne
      let C := Finset.univ.filter (fun i => p ∈ B i ∧ q ∈ B i)
      have single : C.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro i hi j hj
        have mi := (Finset.mem_filter.mp hi).2
        have mj := (Finset.mem_filter.mp hj).2
        apply Classical.byContradiction; intro contra
        have unique := meets _ (Bin i) _ (Bin j) (fun he => contra (Binj he))
        exact ne (unique.unique ⟨mi.1,mj.1⟩ ⟨mi.2,mj.2⟩)
      calc
        _ = sumF (fun i => if i ∈ C then (1 : Int) else 0) := by
          apply sum_congr; intro i
          by_cases hp : p ∈ B i <;> by_cases hq : q ∈ B i <;> simp [I,rowOf,C,hp,hq]
        _ = _ := indicators C
        _ ≤ _ := by omega
  have lower : 143 ≤ Fintype.card ↥S := by simpa using lo
  have upper : Fintype.card ↥S < 157 := by simpa using hi
  have oneMore {b : Nat} {J : Matrix b} (PJ : PartialPlane J) (l : 143 ≤ b) (h : b < 157) :
      ∃ L : Fin 157 → Int, (∀ x, L x = 0 ∨ L x = 1) ∧ sumF L = 13 ∧ ∀ i, dot L (J i) = 1 := by
    by_cases eq : b = 143
    · subst b; exact extension143 PJ
    · obtain ⟨L,bin,sz,hit,_⟩ := extension PJ (by omega) h
      exact ⟨L,bin,sz,hit⟩
  obtain ⟨L,binary,sz,meet⟩ := oneMore P lower upper
  let N := Finset.univ.filter (fun x => L x = 1)
  have repr : L = rowOf N := by
    funext x
    rcases binary x with hz|ho
    · simp [rowOf,N,hz]
    · simp [rowOf,N,ho]
  have sizeN : N.card = 13 := by
    rw [repr] at sz; change sumF (fun x => if x ∈ N then _ else _) = 13 at sz
    rw [indicators] at sz; omega
  have hits {a} (ha : a ∈ S) : (N ∩ a).card = 1 := by
    let i := e.symm ⟨a,ha⟩
    have val : B i = a := congrArg Subtype.val (e.apply_symm_apply ⟨a,ha⟩)
    have eq := meet i
    change dot L (rowOf (B i)) = 1 at eq
    rw [repr,dot_card,val] at eq; omega
  have fresh : N ∉ S := by
    intro hn; have one := hits hn; rw [Finset.inter_self] at one; omega
  refine ⟨insert N S,Finset.subset_insert _ _,Finset.card_insert_of_notMem fresh,?_,?_⟩
  · intro a ha; rcases Finset.mem_insert.mp ha with rfl|ha
    · exact sizeN
    · exact size a ha
  · intro a ha c hc ne
    rcases Finset.mem_insert.mp ha with rfl|ha <;> rcases Finset.mem_insert.mp hc with eq|hc
    · exact False.elim (ne eq.symm)
    · exact intersection_one.mp (hits hc)
    · subst c; apply intersection_one.mp; rw [Finset.inter_comm]; exact hits ha
    · exact meets a ha c hc ne

end Order12Extension

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_eq_12_R1.H2 := by
  exact Order12Extension.extend_finsets
