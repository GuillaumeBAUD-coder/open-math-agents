import OMAStatements.S_oeis_a133058

-- Problem: A133058, the loop from index 638. a(638) = 1 is computed by the kernel. Then, with
-- m = 641 + 4t odd: a(639+4t) = 1 + (639+4t) + 1 = m (gcd 1), a(640+4t) = m + (m-1) + 1 = 2m
-- (gcd(m, m-1) = 1), a(641+4t) = 2m / m = 2 (gcd(2m, m) = m), a(642+4t) = 2 / 2 = 1 (642+4t even).

namespace OMA.A133058

open OMA.S_oeis_a133058

lemma step (n : ℕ) : a133058 (n + 2) = aStep133058 (a133058 (n + 1)) (n + 2) := rfl

set_option maxRecDepth 100000 in
lemma base0 : a133058 638 = 1 := by decide

lemma P (t : ℕ) : a133058 (638 + 4 * t) = 1 ∧ a133058 (639 + 4 * t) = 641 + 4 * t ∧
    a133058 (640 + 4 * t) = 2 * (641 + 4 * t) ∧ a133058 (641 + 4 * t) = 2 := by
  induction t with
  | zero =>
    have h0 := base0
    have h1 : a133058 639 = 641 := by
      rw [show 639 = 637 + 2 by rfl, step, h0]; unfold aStep133058; norm_num
    have h2 : a133058 640 = 2 * 641 := by
      rw [show 640 = 638 + 2 by rfl, step, h1]; unfold aStep133058; norm_num
    have h3 : a133058 641 = 2 := by
      rw [show 641 = 639 + 2 by rfl, step, h2]; unfold aStep133058; norm_num
    exact ⟨h0, h1, h2, h3⟩
  | succ t ih =>
    obtain ⟨-, -, -, h3⟩ := ih
    have h0 : a133058 (638 + 4 * (t + 1)) = 1 := by
      rw [show 638 + 4 * (t + 1) = (640 + 4 * t) + 2 by ring, step,
        show 640 + 4 * t + 1 = 641 + 4 * t by ring, h3]
      unfold aStep133058
      have hg : Nat.gcd 2 (640 + 4 * t + 2) = 2 :=
        Nat.gcd_eq_left ⟨321 + 2 * t, by ring⟩
      simp [hg]
    have h1 : a133058 (639 + 4 * (t + 1)) = 641 + 4 * (t + 1) := by
      rw [show 639 + 4 * (t + 1) = (641 + 4 * t) + 2 by ring, step,
        show 641 + 4 * t + 1 = 638 + 4 * (t + 1) by ring, h0]
      unfold aStep133058
      simp only [Nat.gcd_one_left, if_true]; ring
    have h2 : a133058 (640 + 4 * (t + 1)) = 2 * (641 + 4 * (t + 1)) := by
      rw [show 640 + 4 * (t + 1) = (642 + 4 * t) + 2 by ring, step,
        show 642 + 4 * t + 1 = 639 + 4 * (t + 1) by ring, h1]
      unfold aStep133058
      have hg : Nat.gcd (641 + 4 * (t + 1)) (642 + 4 * t + 2) = 1 := by
        rw [show 641 + 4 * (t + 1) = (642 + 4 * t + 2) + 1 by ring]
        simp
      simp only [hg, if_true]; ring
    have h3' : a133058 (641 + 4 * (t + 1)) = 2 := by
      rw [show 641 + 4 * (t + 1) = (643 + 4 * t) + 2 by ring, step,
        show 643 + 4 * t + 1 = 640 + 4 * (t + 1) by ring, h2]
      unfold aStep133058
      have hm : 643 + 4 * t + 2 = 641 + 4 * (t + 1) := by ring
      have hg : Nat.gcd (2 * (641 + 4 * (t + 1))) (643 + 4 * t + 2) = 641 + 4 * (t + 1) := by
        rw [hm]; exact Nat.gcd_mul_left_left 2 _
      have hne : (641 + 4 * (t + 1)) ≠ 1 := by omega
      simp only [hg, hne, if_false]
      exact Nat.mul_div_cancel _ (by omega)
    exact ⟨h0, h1, h2, h3'⟩

end OMA.A133058

theorem OMA.solution : type_of% @OMA.S_oeis_a133058.main := OMA.A133058.P
