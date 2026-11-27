import OMAStatements.S_oeis_a067360

/-!
# Solution to oeis-a067360

We establish both identities for $a(n) = 17^n \sin(2n \arctan(1/4))$ by introducing the companion
sequence $b(n) = 17^n \cos(2n \arctan(1/4))$. Setting $\theta = \arctan(1/4)$, we have
$\tan \theta = 1/4$ and $\cos \theta > 0$, whence $\cos \theta = 4 \sin \theta$ and
$\sin^2 \theta = 1/17$. Double-angle formulas give $\sin(2\theta) = 8/17$ and
$\cos(2\theta) = 15/17$, yielding the coupled first-order system
$$a(n+1) = 15 a(n) + 8 b(n), \qquad b(n+1) = 15 b(n) - 8 a(n).$$
Eliminating $b$ gives $a(n+2) = 30 a(n+1) - 289 a(n)$, and induction over $\mathbb{C}$ shows
$b(n) \pm i a(n) = (15 \pm 8i)^n$, from which the closed form follows immediately.
-/

private noncomputable def bSeq (n : ℕ) : ℝ :=
  17 ^ n * Real.cos (2 * (n : ℝ) * Real.arctan (1 / 4))

private lemma sin_cos_two_arctan_quarter :
    Real.sin (2 * Real.arctan (1 / 4)) = 8 / 17 ∧
    Real.cos (2 * Real.arctan (1 / 4)) = 15 / 17 := by
  set θ : ℝ := Real.arctan (1 / 4)
  have htan : Real.tan θ = 1 / 4 := Real.tan_arctan (1 / 4)
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have hcos_ne : Real.cos θ ≠ 0 := ne_of_gt hcos_pos
  rw [Real.tan_eq_sin_div_cos, div_eq_iff hcos_ne] at htan
  have hsc : Real.cos θ = 4 * Real.sin θ := by linarith
  have hsq : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  constructor
  · rw [Real.sin_two_mul, hsc]
    nlinarith
  · rw [Real.cos_two_mul, hsc]
    nlinarith

private lemma ab_step (n : ℕ) :
    OMA.S_oeis_a067360.a (n + 1) = 15 * OMA.S_oeis_a067360.a n + 8 * bSeq n ∧
    bSeq (n + 1) = 15 * bSeq n - 8 * OMA.S_oeis_a067360.a n := by
  obtain ⟨hs2, hc2⟩ := sin_cos_two_arctan_quarter
  set θ : ℝ := Real.arctan (1 / 4)
  have hang : 2 * ((n + 1 : ℕ) : ℝ) * θ = 2 * (n : ℝ) * θ + 2 * θ := by
    push_cast
    ring
  constructor
  · simp only [OMA.S_oeis_a067360.a, bSeq, pow_succ]
    rw [hang, Real.sin_add, hs2, hc2]
    ring
  · simp only [OMA.S_oeis_a067360.a, bSeq, pow_succ]
    rw [hang, Real.cos_add, hs2, hc2]
    ring

private lemma complex_powers (n : ℕ) :
    ((bSeq n : ℝ) : ℂ) + ((OMA.S_oeis_a067360.a n : ℝ) : ℂ) * Complex.I =
      (15 + 8 * Complex.I) ^ n ∧
    ((bSeq n : ℝ) : ℂ) - ((OMA.S_oeis_a067360.a n : ℝ) : ℂ) * Complex.I =
      (15 - 8 * Complex.I) ^ n := by
  induction n with
  | zero =>
    simp [OMA.S_oeis_a067360.a, bSeq]
  | succ n ih =>
    obtain ⟨iha, ihb⟩ := ih
    obtain ⟨ha, hb⟩ := ab_step n
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    constructor
    · rw [pow_succ, ← iha, ha, hb]
      push_cast
      linear_combination -8 * ((OMA.S_oeis_a067360.a n : ℝ) : ℂ) * hI
    · rw [pow_succ, ← ihb, ha, hb]
      push_cast
      linear_combination -8 * ((OMA.S_oeis_a067360.a n : ℝ) : ℂ) * hI

theorem OMA.solution : type_of% @OMA.S_oeis_a067360.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
    have h1 := (ab_step (m + 1)).1
    have h0a := (ab_step m).1
    have h0b := (ab_step m).2
    have hsub1 : m + 2 - 1 = m + 1 := by omega
    have hsub2 : m + 2 - 2 = m := by omega
    rw [hsub1, hsub2]
    linarith
  · intro n _
    obtain ⟨hp, hm⟩ := complex_powers n
    rw [← hp, ← hm]
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination ((OMA.S_oeis_a067360.a n : ℝ) : ℂ) * hI
