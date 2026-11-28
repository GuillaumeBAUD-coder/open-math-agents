import OMAStatements.S_oeis_a113255

namespace OMA.Sol113255

lemma norm_pow {d : ℤ} (z : ℤ√d) (n : ℕ) : (z ^ n).norm = z.norm ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Zsqrtd.norm_mul, ih, pow_succ]

lemma key (m : ℤ) (f : ℕ → ℤ) (h0 : f 0 = -1) (h1 : f 1 = 4)
    (h2 : f 2 = -13 + 6 * (m - 1) + 3 * (m - 1) ^ 2) (h3 : f 3 = (-8 + m ^ 2) ^ 2)
    (hrec : ∀ n, f (n + 4) = m ^ 4 * f n + (2 * m) ^ 2 * f (n + 1) - 4 * f (n + 3)) :
    ∀ n : ℕ, IsSquare (f (2 * n + 1)) := by
  let z : ℤ√(4 - m ^ 2) := ⟨-2, 1⟩
  let w : ℕ → ℤ := fun k => (z ^ k).re
  have hw : ∀ k, w (k + 2) = -4 * w (k + 1) - m ^ 2 * w k := by
    intro k
    simp only [w, pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul, z]
    ring
  have w0 : w 0 = 1 := by simp [w]
  have w1 : w 1 = -2 := by simp [w, z]
  have w2 : w 2 = 8 - m ^ 2 := by rw [hw 0, w0, w1]; ring
  have w3 : w 3 = 6 * m ^ 2 - 32 := by rw [hw 1, w2, w1]; ring
  have w4 : w 4 = m ^ 4 - 32 * m ^ 2 + 128 := by rw [hw 2, w3, w2]; ring
  have closed : ∀ n, 4 * f n = m ^ (n + 1) * (1 - (-1) ^ n) + 2 * w (n + 1) := by
    have step : ∀ n, (4 * f n = m ^ (n + 1) * (1 - (-1) ^ n) + 2 * w (n + 1)) ∧
        (4 * f (n + 1) = m ^ (n + 2) * (1 - (-1) ^ (n + 1)) + 2 * w (n + 2)) ∧
        (4 * f (n + 2) = m ^ (n + 3) * (1 - (-1) ^ (n + 2)) + 2 * w (n + 3)) ∧
        (4 * f (n + 3) = m ^ (n + 4) * (1 - (-1) ^ (n + 3)) + 2 * w (n + 4)) := by
      intro n
      induction n with
      | zero =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [h0, w1]; ring
        · rw [h1, w2]; ring
        · rw [h2, w3]; ring
        · rw [h3, w4]; ring
      | succ n ih =>
        obtain ⟨e0, e1, e2, e3⟩ := ih
        refine ⟨e1, e2, e3, ?_⟩
        show 4 * f (n + 4) = m ^ (n + 5) * (1 - (-1) ^ (n + 4)) + 2 * w (n + 5)
        have r1 : w (n + 5) = -4 * w (n + 4) - m ^ 2 * w (n + 3) := hw (n + 3)
        have r2 : w (n + 3) = -4 * w (n + 2) - m ^ 2 * w (n + 1) := hw (n + 1)
        rw [hrec n]
        linear_combination m ^ 4 * e0 + 4 * m ^ 2 * e1 - 4 * e3 - 2 * r1 + 2 * m ^ 2 * r2
    exact fun n => (step n).1
  intro n
  set x := (z ^ (n + 1)).re
  set y := (z ^ (n + 1)).im
  have hnorm : m ^ (2 * n + 2) = x * x - (4 - m ^ 2) * y * y := by
    have := norm_pow z (n + 1)
    rw [Zsqrtd.norm_def] at this
    have hz : z.norm = m ^ 2 := by simp [Zsqrtd.norm_def, z]
    rw [hz, ← pow_mul] at this
    rw [show 2 * n + 2 = 2 * (n + 1) by ring, this]
  have hdbl : w (2 * n + 2) = x * x + (4 - m ^ 2) * y * y := by
    simp only [w]
    rw [show 2 * n + 2 = (n + 1) + (n + 1) by ring, pow_add, Zsqrtd.re_mul]
  have hc := closed (2 * n + 1)
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring, hdbl, hnorm] at hc
  have hodd : (-1 : ℤ) ^ (2 * n + 1) = -1 := by rw [pow_succ, pow_mul]; simp
  rw [hodd] at hc
  exact ⟨x, by linarith⟩

end OMA.Sol113255

theorem OMA.solution : type_of% @OMA.S_oeis_a113255.main := by
  intro m
  exact OMA.Sol113255.key (m : ℤ) (OMA.S_oeis_a113255.a m) rfl rfl rfl rfl (fun n => rfl)
