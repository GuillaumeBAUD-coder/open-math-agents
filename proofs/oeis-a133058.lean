import OMAStatements.S_oeis_a133058

set_option maxRecDepth 100000 in
open OMA.S_oeis_a133058 in
theorem OMA.solution : type_of% @OMA.S_oeis_a133058.main := by
  have b : a133058 638 = 1 := by decide
  have st (n : ℕ) : a133058 (n+2) = aStep133058 (a133058 (n+1)) (n+2) := rfl
  have c (t : ℕ) (h : a133058 (638+4*t) = 1) : a133058 (639+4*t) = 641+4*t ∧
      a133058 (640+4*t) = 2*(641+4*t) ∧ a133058 (641+4*t) = 2 ∧ a133058 (638+4*(t+1)) = 1 := by
    have h1 : a133058 (639+4*t) = 641+4*t := by
      rw [show 639+4*t = 637+4*t+2 by ring, st, show 637+4*t+1 = 638+4*t by ring, h]
      simp only [aStep133058, Nat.gcd_one_left, if_true]
      ring
    have h2 : a133058 (640+4*t) = 2*(641+4*t) := by
      rw [show 640+4*t = 638+4*t+2 by ring, st, show 638+4*t+1 = 639+4*t by ring, h1]
      have g : Nat.gcd (641+4*t) (638+4*t+2) = 1 := by
        rw [show 641+4*t = 638+4*t+2+1 by ring]
        simp
      simp only [aStep133058, g, if_true]
      ring
    have h3 : a133058 (641+4*t) = 2 := by
      rw [show 641+4*t = 639+4*t+2 by ring, st, show 639+4*t+1 = 640+4*t by ring, h2,
        show 639+4*t+2 = 641+4*t by ring]
      simp only [aStep133058, Nat.gcd_mul_left_left, show 641+4*t ≠ 1 by omega, if_false]
      exact Nat.mul_div_cancel _ (by omega)
    refine ⟨h1, h2, h3, ?_⟩
    rw [show 638+4*(t+1) = 640+4*t+2 by ring, st, show 640+4*t+1 = 641+4*t by ring, h3]
    simp [aStep133058, show Nat.gcd 2 (640+4*t+2) = 2 from Nat.gcd_eq_left ⟨321+2*t, by ring⟩]
  have q (t : ℕ) : a133058 (638+4*t) = 1 := by
    induction t with
    | zero => exact b
    | succ t ih => exact (c t ih).2.2.2
  exact fun t => ⟨q t, (c t (q t)).1, (c t (q t)).2.1, (c t (q t)).2.2.1⟩
