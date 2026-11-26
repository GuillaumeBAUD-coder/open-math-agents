import FormalConjectures.OptimizationConstants.«7a»

/-!
# Irrational numbers have irrationality exponent at least 2

Dirichlet: an irrational `x` has infinitely many rationals `q` with `|x - q| < 1 / q.den ^ 2`
(Mathlib: `Real.exists_rat_abs_sub_lt_and_lt_of_irrational`). Their denominators are unbounded,
because for denominators up to `N` the distance from `x` to any fraction is bounded below by a
positive constant. So `LiouvilleWith 2 x` holds, hence `LiouvilleWith z x` for every `z < 2`.
-/

namespace OMA.C7a

lemma dist_lower {x : ℝ} (hx : Irrational x) :
    ∀ N : ℕ, ∃ ε > (0 : ℝ), ∀ d : ℕ, 1 ≤ d → d ≤ N → ∀ a : ℤ, ε ≤ |x - a / d| := by
  intro N
  induction N with
  | zero => exact ⟨1, one_pos, fun d h1 h2 _ => by omega⟩
  | succ N ih =>
    obtain ⟨ε, hε, hN⟩ := ih
    set y : ℝ := ((N + 1 : ℕ) : ℝ) * x
    have hd : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have hy : 0 < |y - round y| := by
      rw [abs_pos, sub_ne_zero]
      intro h
      have hyi : Irrational y := hx.natCast_mul (by omega)
      exact hyi.ne_int (round y) h
    refine ⟨min ε (|y - round y| / ((N + 1 : ℕ) : ℝ)), lt_min hε (div_pos hy hd), ?_⟩
    intro d h1 h2 a
    rcases Nat.lt_or_ge d (N + 1) with hlt | hge
    · exact (min_le_left _ _).trans (hN d h1 (by omega) a)
    · have hdeq : d = N + 1 := by omega
      subst hdeq
      refine (min_le_right _ _).trans ?_
      have key : |y - round y| ≤ |y - a| := round_le y a
      have e : x - (a : ℝ) / ((N + 1 : ℕ) : ℝ) = (y - a) / ((N + 1 : ℕ) : ℝ) := by
        simp only [y]
        field_simp
      rw [e, abs_div, abs_of_pos hd]
      exact div_le_div_of_nonneg_right key hd.le

lemma liouvilleWith_two {x : ℝ} (hx : Irrational x) : LiouvilleWith 2 x := by
  refine ⟨1, ?_⟩
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨ε, hε, hlow⟩ := dist_lower hx N
  obtain ⟨q0, hq0a, hq0b⟩ := exists_rat_btwn (show x - ε < x by linarith)
  obtain ⟨q, hq1, hq2⟩ := Real.exists_rat_abs_sub_lt_and_lt_of_irrational hx q0
  have hq0 : |x - q0| < ε := by
    rw [abs_lt]
    constructor <;> linarith
  have hcast : ((q.num : ℝ) / (q.den : ℝ)) = (q : ℝ) := (Rat.cast_def q).symm
  have hden : N < q.den := by
    by_contra hle
    rw [not_lt] at hle
    have := hlow q.den q.den_pos hle q.num
    rw [hcast] at this
    linarith
  refine ⟨q.den, hden.le, q.num, ?_, ?_⟩
  · rw [hcast]
    exact hx.ne_rat q
  · rw [hcast, Real.rpow_two]
    exact hq1

end OMA.C7a

theorem OMA.solution : type_of% @Constant7a.two_le_irrationalityExponent := by
  intro x hx
  rw [Constant7a.le_irrationalityExponent_iff]
  intro z hz
  have hz' : (z : ℝ) ≤ 2 := by
    have : z < 2 := by exact_mod_cast hz
    exact_mod_cast this.le
  exact (OMA.C7a.liouvilleWith_two hx).mono hz'
