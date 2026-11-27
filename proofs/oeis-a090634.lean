import OMAStatements.S_oeis_a090634
import Mathlib

/-!
Putnam 2003 B2. One averaging step maps the list of values g(0), ..., g(m) to the list of
(g(i) + g(i+1))/2, so after j steps a list of j+1 values g(0), ..., g(j) becomes the single value
V_j(g) = Sum_t binomial(j,t) g(t) / 2^j (Pascal's rule). For g(k) = 1/(k+1),
binomial(j,t)/(t+1) = binomial(j+1,t+1)/(j+1), so F(j+1) = (2^(j+1) - 1)/((j+1) 2^j), which is
exactly 2 (1 - 1/2^(j+1))/(j+1); the denominators then agree.
-/

namespace R090634
open OMA.S_oeis_a090634

def L (m : ℕ) (g : ℕ → ℚ) : List ℚ := (List.range m).map g

theorem avg_L (m : ℕ) (g : ℕ → ℚ) :
    avg (L (m + 1) g) = L m (fun i => (g i + g (i + 1)) / 2) := by
  apply List.ext_getElem
  · simp [avg, L]
  · intro i h1 h2
    simp [avg, L]

def V (j : ℕ) (g : ℕ → ℚ) : ℚ := (∑ t ∈ Finset.range (j + 1), (j.choose t : ℚ) * g t) / 2 ^ j

theorem pascal (j : ℕ) (g : ℕ → ℚ) :
    ∑ t ∈ Finset.range (j + 1 + 1), ((j + 1).choose t : ℚ) * g t =
      ∑ t ∈ Finset.range (j + 1), (j.choose t : ℚ) * g t +
        ∑ t ∈ Finset.range (j + 1), (j.choose t : ℚ) * g (t + 1) := by
  have h3 : ∑ t ∈ Finset.range (j + 1), (j.choose t : ℚ) * g t =
      ∑ t ∈ Finset.range (j + 1), (j.choose (t + 1) : ℚ) * g (t + 1) + g 0 := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ, Nat.choose_succ_self]
    simp
  rw [Finset.sum_range_succ', h3]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right, Nat.cast_one, one_mul]
  ring

theorem iter (j : ℕ) : ∀ g : ℕ → ℚ, avg^[j] (L (j + 1) g) = [V j g] := by
  induction j with
  | zero => intro g; simp [L, V]
  | succ j ih =>
    intro g
    rw [Function.iterate_succ_apply, avg_L, ih]
    congr 1
    have e1 : ∑ t ∈ Finset.range (j + 1), (j.choose t : ℚ) * ((g t + g (t + 1)) / 2) =
        (∑ t ∈ Finset.range (j + 1), (j.choose t : ℚ) * g t +
          ∑ t ∈ Finset.range (j + 1), (j.choose t : ℚ) * g (t + 1)) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t _
      ring
    simp only [V]
    rw [e1, pascal, pow_succ]
    ring

theorem F_eq (j : ℕ) : F (j + 1) = V j (fun k => 1 / ((k : ℚ) + 1)) := by
  unfold F
  rw [Nat.add_sub_cancel, show start (j + 1) = L (j + 1) (fun k => 1 / ((k : ℚ) + 1)) from rfl,
    iter]
  simp

theorem V_h (j : ℕ) :
    V j (fun k => 1 / ((k : ℚ) + 1)) = 2 * (1 - 1 / 2 ^ (j + 1)) / ((j + 1 : ℕ) : ℚ) := by
  have hs : ∑ t ∈ Finset.range (j + 1), ((j + 1).choose (t + 1) : ℚ) = 2 ^ (j + 1) - 1 := by
    have h := Nat.sum_range_choose (j + 1)
    rw [Finset.sum_range_succ', Nat.choose_zero_right] at h
    have h' : ((∑ t ∈ Finset.range (j + 1), (j + 1).choose (t + 1) : ℕ) : ℚ) + 1 =
        2 ^ (j + 1) := by
      exact_mod_cast h
    push_cast at h'
    linarith
  have hterm : ∀ t : ℕ, (j.choose t : ℚ) * (1 / ((t : ℚ) + 1)) =
      ((j + 1).choose (t + 1) : ℚ) / ((j : ℚ) + 1) := by
    intro t
    have e := Nat.add_one_mul_choose_eq j t
    have e' : ((j : ℚ) + 1) * (j.choose t : ℚ) = ((j + 1).choose (t + 1) : ℚ) * ((t : ℚ) + 1) := by
      exact_mod_cast e
    field_simp
    linarith [e']
  simp only [V]
  rw [Finset.sum_congr rfl (fun t _ => hterm t), ← Finset.sum_div, hs]
  push_cast
  field_simp
  ring

theorem solve : ∀ n : ℕ, 1 ≤ n → a n = (2 * (1 - 1 / 2 ^ n) / (n : ℚ)).den := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  unfold a
  rw [F_eq, V_h]

end R090634

theorem OMA.solution : type_of% @OMA.S_oeis_a090634.main := R090634.solve
