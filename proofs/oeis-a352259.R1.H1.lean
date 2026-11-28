import OMAReductions.R_oeis_a352259_R1
import Mathlib

namespace OMA.A352259H1

def newt : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | f+1, D, g => if (g + D / g) / 2 < g then newt f D ((g + D / g) / 2) else g

def chk2 (n y z w s : ℕ) : Bool :=
  (decide (s*s < (y*z)^2 + 4*(n - w - 2*y^2 - 3*z^2)) &&
    decide ((y*z)^2 + 4*(n - w - 2*y^2 - 3*z^2) < (s+1)*(s+1))) ||
  (decide (s*s = (y*z)^2 + 4*(n - w - 2*y^2 - 3*z^2)) &&
    decide (w + ((s - y*z)/2)^2+2*y^2+3*z^2+((s - y*z)/2)*y*z ≠ n))

def chk (n y z w : ℕ) : Bool :=
  chk2 n y z w (newt 30 ((y*z)^2 + 4*(n - w - 2*y^2 - 3*z^2)) (y*z+1200))

theorem chk2_false (n w x y z s : ℕ) (e : w+x^2+2*y^2+3*z^2+x*y*z=n) :
    chk2 n y z w s = false := by
  have hD : (y*z)^2 + 4*(n - w - 2*y^2 - 3*z^2) = (2*x+y*z)*(2*x+y*z) := by
    have h : n - w - 2*y^2 - 3*z^2 = x^2 + x*y*z := by omega
    rw [h]; ring
  unfold chk2
  rw [hD]
  by_contra hc
  rw [Bool.not_eq_false, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hc
  simp only [decide_eq_true_eq] at hc
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a1 : s < 2*x+y*z := Nat.mul_self_lt_mul_self_iff.mp h1
    have a2 : 2*x+y*z < s+1 := Nat.mul_self_lt_mul_self_iff.mp h2
    omega
  · have a1 : s = 2*x+y*z := Nat.mul_self_inj.mp h1
    apply h2
    have a2 : (s - y*z)/2 = x := by omega
    rw [a2]; exact e

theorem key (n Y Z : ℕ) (hY : n < 2*Y^2) (hZ : n < 3*Z^2)
    (h : ∀ y < Y, ∀ z < Z, ∀ w < 2, chk n y z w = true) :
    ¬ ∃ w x y z : ℕ, w≤1 ∧ w+x^2+2*y^2+3*z^2+x*y*z=n := by
  rintro ⟨w, x, y, z, hw, e⟩
  have hy : y < Y := by
    by_contra hc
    push_neg at hc
    nlinarith [Nat.zero_le (x*y*z), Nat.zero_le (x^2), Nat.zero_le (z^2)]
  have hz : z < Z := by
    by_contra hc
    push_neg at hc
    nlinarith [Nat.zero_le (x*y*z), Nat.zero_le (x^2), Nat.zero_le (y^2)]
  have h1 := h y hy z hz w (by omega)
  unfold chk at h1
  rw [chk2_false n w x y z _ e] at h1
  exact Bool.false_ne_true h1

end OMA.A352259H1

open OMA.A352259H1 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
theorem OMA.solution : OMA.R_oeis_a352259_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact key 106 8 6 (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 744 20 16 (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 5469 53 43 (by norm_num) (by norm_num) (by decide +kernel)
  · exact key 331269 408 333 (by norm_num) (by norm_num) (by decide +kernel)
