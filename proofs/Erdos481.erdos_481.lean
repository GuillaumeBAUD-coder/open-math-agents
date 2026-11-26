import FormalConjectures.ErdosProblems.«481»

-- Problem: Erdős Problem 481
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/481.lean:57 (declaration Erdos481.erdos_481)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
namespace OMA

open Erdos481

noncomputable def S (L : List ℕ) : ℝ := (L.map fun x : ℕ => ((x : ℝ))⁻¹).sum

lemma mem_T {r : ℕ} (a b : Fin r → ℕ) (L : List ℕ) (x : ℕ) :
    x ∈ T a b L ↔ ∃ i, ∃ y ∈ L, a i * y + b i = x := by
  simp [T]

lemma S_T {r : ℕ} (a b : Fin r → ℕ) (L : List ℕ) :
    S (T a b L) = ∑ i, S (L.map (fun x => a i * x + b i)) := by
  simp only [S, T, List.flatMap]
  rw [Fin.sum_univ_def, List.map_flatten, List.sum_flatten, List.map_map, List.map_map]
  rfl

lemma S_upper (L : List ℕ) (N : ℕ) (hL : L.Nodup) (h : ∀ x ∈ L, 1 ≤ x ∧ x ≤ N) :
    S L ≤ 1 + Real.log N := by
  have hh := harmonic_le_one_add_log N
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
  refine le_trans ?_ hh
  rw [S, ← List.sum_toFinset _ hL]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [List.mem_toFinset] at hx
    simpa using h x hx
  · intros; positivity

lemma growth (ρ c α β : ℝ) (hρ : 1 < ρ) (hc : 0 < c) (h : ∀ n : ℕ, c * ρ ^ n ≤ α + β * n) :
    False := by
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hρ
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 hρ
  have h2 := (h0.const_mul α).add (h1.const_mul β)
  simp only [mul_zero, add_zero] at h2
  have := (h2.eventually (gt_mem_nhds hc)).exists_forall_of_atTop
  obtain ⟨N, hN⟩ := this
  have hN' := hN N le_rfl
  have hp : 0 < ρ ^ N := by positivity
  have := h N
  simp only [pow_one, pow_zero] at hN'
  rw [mul_one_div, mul_div_assoc', ← add_div, div_lt_iff₀ hp] at hN'
  linarith

lemma S_nil : S [] = 0 := by simp [S]

lemma S_cons (x : ℕ) (L : List ℕ) : S (x :: L) = (x : ℝ)⁻¹ + S L := by simp [S]

lemma S_nonneg (L : List ℕ) : 0 ≤ S L := by
  induction L with
  | nil => simp [S_nil]
  | cons x L ih => rw [S_cons]; positivity

lemma S_ge_mem (L : List ℕ) (x : ℕ) (hx : x ∈ L) : (x : ℝ)⁻¹ ≤ S L := by
  induction L with
  | nil => simp at hx
  | cons y L ih =>
    rw [S_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; linarith [S_nonneg L]
    · have := ih h; have : (0 : ℝ) ≤ (y : ℝ)⁻¹ := by positivity
      linarith

lemma point (m B a x b : ℝ) (hm : 0 < m) (hB : b ≤ B) (hb : 0 ≤ b) (ha : 1 ≤ a) (hx : m ≤ x) :
    m / (m + B) / a * x⁻¹ ≤ (a * x + b)⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hB0 : 0 ≤ B := by linarith
  have key : m * (a * x + b) ≤ (m + B) * a * x := by
    have h1 : m * b ≤ x * B := by nlinarith
    have h3 : 0 ≤ x * B := mul_nonneg hx0.le hB0
    have h2 : x * B ≤ x * B * a := by nlinarith
    nlinarith
  have hax : 0 < a * x + b := by nlinarith
  calc m / (m + B) / a * x⁻¹ = m / ((m + B) * a * x) := by field_simp
    _ ≤ 1 / (a * x + b) := by
      rw [div_le_div_iff₀ (by positivity) hax]; linarith
    _ = (a * x + b)⁻¹ := one_div _

lemma S_map_lower (m B a b : ℝ) (f : ℕ → ℕ) (hf : ∀ x : ℕ, ((f x : ℕ) : ℝ) = a * x + b)
    (hm : 0 < m) (hB : b ≤ B) (hb : 0 ≤ b) (ha : 1 ≤ a) (L : List ℕ) (hL : ∀ x ∈ L, m ≤ x) :
    m / (m + B) / a * S L ≤ S (L.map f) := by
  induction L with
  | nil => simp [S_nil]
  | cons y L ih =>
    rw [List.map_cons, S_cons, S_cons, mul_add, hf]
    have h1 := point m B a y b hm hB hb ha (hL y (by simp))
    have h2 := ih (fun x hx => hL x (by simp [hx]))
    linarith

lemma S_T_lower {r : ℕ} (a b : Fin r → ℕ) (ha : ∀ i, 0 < a i) (m B : ℝ) (hm : 0 < m)
    (hB : ∀ i, (b i : ℝ) ≤ B) (L : List ℕ) (hL : ∀ x ∈ L, m ≤ x) :
    m / (m + B) * (∑ i, (1 : ℝ) / a i) * S L ≤ S (T a b L) := by
  rw [S_T, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have := S_map_lower m B (a i) (b i) (fun x => a i * x + b i) (by intro x; push_cast; ring)
    hm (hB i) (by positivity) (by exact_mod_cast ha i) L hL
  calc m / (m + B) * (1 / (a i : ℝ)) * S L = m / (m + B) / a i * S L := by ring
    _ ≤ _ := this

lemma mem_iter_bound {r : ℕ} (a b : Fin r → ℕ) (ha : ∀ i, 0 < a i) (k : ℕ) :
    ∀ x ∈ (T a b)^[k] [1], 1 ≤ x ∧ x ≤ (∑ i, (a i + b i)) ^ k := by
  induction k with
  | zero => intro x hx; simp at hx; simp [hx]
  | succ k ih =>
    intro x hx
    rw [Function.iterate_succ_apply', mem_T] at hx
    obtain ⟨i, y, hy, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := ih y hy
    have hi : a i + b i ≤ ∑ j, (a j + b j) :=
      Finset.single_le_sum (f := fun j => a j + b j) (by intros; positivity) (Finset.mem_univ i)
    have hai := ha i
    constructor
    · nlinarith
    · rw [pow_succ]
      calc a i * y + b i ≤ (a i + b i) * y := by nlinarith
        _ ≤ (∑ j, (a j + b j)) * y := Nat.mul_le_mul_right _ hi
        _ ≤ (∑ j, (a j + b j)) * (∑ j, (a j + b j)) ^ k := Nat.mul_le_mul_left _ h2
        _ = _ := by ring

lemma mem_iter_ge {r : ℕ} (a b : Fin r → ℕ) (ha : ∀ i, 0 < a i)
    (hnid : ∀ i, ¬ (a i = 1 ∧ b i = 0)) (k : ℕ) :
    ∀ x ∈ (T a b)^[k] [1], k + 1 ≤ x := by
  induction k with
  | zero => intro x hx; simp at hx; simp [hx]
  | succ k ih =>
    intro x hx
    rw [Function.iterate_succ_apply', mem_T] at hx
    obtain ⟨i, y, hy, rfl⟩ := hx
    have h1 := ih y hy
    have hai := ha i
    have hn := hnid i
    by_cases h2 : 2 ≤ a i
    · nlinarith
    · have : a i = 1 := by omega
      have hb : 1 ≤ b i := by
        rcases Nat.eq_zero_or_pos (b i) with h | h
        · exact absurd ⟨this, h⟩ hn
        · exact h
      rw [this]; omega

lemma mem_iter_nonempty {r : ℕ} (a b : Fin r → ℕ) (i0 : Fin r) (k : ℕ) :
    ∃ x, x ∈ (T a b)^[k] [1] := by
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨a i0 * y + b i0, ?_⟩
    rw [Function.iterate_succ_apply', mem_T]
    exact ⟨i0, y, hy, rfl⟩

lemma id_case {r : ℕ} (a b : Fin r → ℕ) (i j : Fin r) (hi : a i = 1 ∧ b i = 0) (hij : i ≠ j) :
    ¬ (T a b (T a b [1])).Nodup := by
  intro h
  rw [T, List.nodup_flatMap] at h
  have : Std.Symm (Function.onFun List.Disjoint
      fun i => List.map (fun x => a i * x + b i) (T a b [1])) :=
    ⟨fun x y hxy => List.Disjoint.symm hxy⟩
  have hp := h.2.forall (List.mem_finRange i) (List.mem_finRange j) hij
  have h1 : (1 : ℕ) ∈ T a b [1] := by
    rw [mem_T]; exact ⟨i, 1, by simp, by simp [hi.1, hi.2]⟩
  have h2 : a j * 1 + b j ∈ T a b [1] := by
    rw [mem_T]; exact ⟨j, 1, by simp, rfl⟩
  apply hp (a := a j * 1 + b j)
  · rw [List.mem_map]; exact ⟨a j * 1 + b j, h2, by simp [hi.1, hi.2]⟩
  · rw [List.mem_map]; exact ⟨1, h1, rfl⟩

end OMA

theorem OMA.solution : type_of% @Erdos481.erdos_481 := by
  intro r a b ha hab
  by_contra hcon
  push Not at hcon
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp at hab; linarith
    · exact h
  have i0 : Fin r := ⟨0, hr⟩
  by_cases hid : ∃ i, a i = 1 ∧ b i = 0
  · obtain ⟨i, hi⟩ := hid
    have : ∃ j, j ≠ i := by
      by_contra hall
      push Not at hall
      rw [Fintype.sum_eq_single i (fun j hj => absurd (hall j) hj), hi.1] at hab
      simp at hab
    obtain ⟨j, hj⟩ := this
    exact OMA.id_case a b i j hi (Ne.symm hj) (hcon 2)
  push Not at hid
  have hnid : ∀ i, ¬ (a i = 1 ∧ b i = 0) := fun i h => hid i h.1 h.2
  set C := ∑ i, (1 : ℝ) / a i with hC
  set B : ℝ := ∑ i, (b i : ℝ) with hBdef
  have hB : ∀ i, (b i : ℝ) ≤ B := fun i =>
    Finset.single_le_sum (f := fun j => (b j : ℝ)) (by intros; positivity) (Finset.mem_univ i)
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (B / (C - 1))
  have hC1 : 0 < C - 1 := by linarith
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
  rw [div_lt_iff₀ hC1] at hm
  set ρ := (m : ℝ) / (m + B) * C with hρ
  have hρ1 : 1 < ρ := by
    rw [hρ, div_mul_eq_mul_div, one_lt_div (by positivity)]
    nlinarith
  set M := ∑ i, (a i + b i) with hM
  let s : ℕ → ℝ := fun n => OMA.S ((Erdos481.T a b)^[m + n] [1])
  have hstep : ∀ n, ρ * s n ≤ s (n + 1) := by
    intro n
    have := OMA.S_T_lower a b ha m B hm0 hB ((Erdos481.T a b)^[m + n] [1]) (by
      intro x hx
      have := OMA.mem_iter_ge a b ha hnid (m + n) x hx
      exact_mod_cast (show m ≤ x by omega))
    simp only [s, ← add_assoc, Function.iterate_succ_apply']
    exact this
  have hs0 : 0 < s 0 := by
    obtain ⟨x, hx⟩ := OMA.mem_iter_nonempty a b i0 (m + 0)
    have h1 := (OMA.mem_iter_bound a b ha (m + 0) x hx).1
    have := OMA.S_ge_mem _ x hx
    have : (0 : ℝ) < (x : ℝ)⁻¹ := by
      have : (1 : ℝ) ≤ x := by exact_mod_cast h1
      positivity
    simp only [s]; linarith
  have hgrow : ∀ n, s 0 * ρ ^ n ≤ s n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      have := hstep n
      nlinarith
  have hupper : ∀ n, s n ≤ (1 + m * Real.log M) + Real.log M * n := by
    intro n
    have := OMA.S_upper _ (M ^ (m + n)) (hcon (m + n)) (OMA.mem_iter_bound a b ha (m + n))
    simp only [s]
    push_cast at this
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  exact OMA.growth ρ (s 0) _ _ hρ1 hs0 (fun n => (hgrow n).trans (hupper n))
