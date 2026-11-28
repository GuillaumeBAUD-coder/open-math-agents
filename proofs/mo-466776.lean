import OMAStatements.S_mo_466776
import Mathlib

/-! Proof of MathOverflow 466776, following the accepted answer. Three tiles carry the colour
pairs `{1,2}`, `{1,3}`, `{2,3}` on opposite sides. Any two of them tile with alternating
columns. In any tiling, the right/left colour is constant along rows and the top/bottom colour
along columns, so the tile at `(i, j)` is determined by a row colour and a column colour; a
finite check shows the three tiles cannot all occur.
Credit: Sudharsan Rajendiran -/

namespace OMA.P466776
open OMA.S_mo_466776

def T : Fin 3 → Fin 4 → ℕ := ![![1, 2, 1, 2], ![1, 3, 1, 3], ![2, 3, 2, 3]]

lemma opp_E (t : Fin 3) (r : Fin 4) : side (T t) r 1 = side (T t) r 3 := by
  revert t r; decide
lemma opp_N (t : Fin 3) (r : Fin 4) : side (T t) r 0 = side (T t) r 2 := by
  revert t r; decide

/-- The finite core: no choice of rotations for the three tiles makes all nine
row/column combinations realisable. -/
lemma core : ∀ r : Fin 3 → Fin 4, ¬ ∀ a b : Fin 3, ∃ t : Fin 3, ∃ s : Fin 4,
    side (T t) s 0 = side (T a) (r a) 0 ∧ side (T t) s 1 = side (T b) (r b) 1 := by
  decide +kernel

lemma not_all : ¬ Tiles T Finset.univ := by
  rintro ⟨g, -, hE, hN, huse⟩
  let E : ℤ × ℤ → ℕ := fun c => side (T (g c).1) (g c).2 1
  let N : ℤ × ℤ → ℕ := fun c => side (T (g c).1) (g c).2 0
  have rowstep : ∀ i j : ℤ, E (i + 1, j) = E (i, j) := fun i j => by
    simp only [E]; rw [hE i j, opp_E]
  have colstep : ∀ i j : ℤ, N (i, j + 1) = N (i, j) := fun i j => by
    simp only [N]; rw [hN i j, opp_N]
  have row : ∀ i j : ℤ, E (i, j) = E (0, j) := by
    intro i j
    induction i using Int.induction_on with
    | zero => rfl
    | succ k ih => rw [rowstep, ih]
    | pred k ih => rw [← ih, ← rowstep (-(k : ℤ) - 1) j]; ring_nf
  have col : ∀ i j : ℤ, N (i, j) = N (i, 0) := by
    intro i j
    induction j using Int.induction_on with
    | zero => rfl
    | succ k ih => rw [colstep, ih]
    | pred k ih => rw [← ih, ← colstep i (-(k : ℤ) - 1)]; ring_nf
  choose c hc using fun k : Fin 3 => huse k (Finset.mem_univ k)
  apply core (fun a => (g (c a)).2)
  intro a b
  refine ⟨(g ((c a).1, (c b).2)).1, (g ((c a).1, (c b).2)).2, ?_, ?_⟩
  · have h1 := col (c a).1 (c b).2
    have h2 := col (c a).1 (c a).2
    simp only [N] at h1 h2
    rw [h1, ← h2, hc a]
  · have h1 := row (c a).1 (c b).2
    have h2 := row (c b).1 (c b).2
    simp only [E] at h1 h2
    rw [h1, ← h2, hc b]

/-- Two tiles `p, q` (rotated by `rp, rq`) placed in alternating columns. -/
def stripes (p q : Fin 3) (rp rq : Fin 4) : ℤ × ℤ → Fin 3 × Fin 4 :=
  fun c => if Even c.1 then (p, rp) else (q, rq)

lemma tiles_pair (k : Fin 3) (p q : Fin 3) (rp rq : Fin 4)
    (hS : Finset.univ.erase k = {p, q}) (hpq : p ≠ q)
    (hp : side (T p) rp 1 = side (T p) rp 3) (hq : side (T q) rq 1 = side (T q) rq 3)
    (hm : side (T p) rp 1 = side (T q) rq 3) (hm' : side (T q) rq 1 = side (T p) rp 3) :
    Tiles T (Finset.univ.erase k) := by
  refine ⟨stripes p q rp rq, ?_, ?_, ?_, ?_⟩
  · intro c; rw [hS]; unfold stripes; split_ifs <;> simp
  · intro i j
    unfold stripes
    by_cases h : Even i
    · have : ¬ Even (i + 1) := by rw [Int.even_add_one]; exact not_not.mpr h
      simp [h, this, hm]
    · have : Even (i + 1) := by rw [Int.even_add_one]; exact h
      simp [h, this, hm']
  · intro i j
    unfold stripes
    by_cases h : Even i <;> simp [h, opp_N]
  · intro t ht
    rw [hS] at ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact ⟨(0, 0), by simp [stripes]⟩
    · rw [Finset.mem_singleton] at ht; subst ht
      exact ⟨(1, 0), by simp [stripes]⟩

lemma tiles_erase (k : Fin 3) : Tiles T (Finset.univ.erase k) := by
  fin_cases k
  · exact tiles_pair 0 1 2 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact tiles_pair 1 0 2 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact tiles_pair 2 0 1 1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end OMA.P466776

theorem OMA.solution : type_of% @OMA.S_mo_466776.main :=
  ⟨3, OMA.P466776.T, le_refl 3, OMA.P466776.not_all, OMA.P466776.tiles_erase⟩

