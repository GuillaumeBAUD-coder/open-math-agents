import OMAStatements.S_oeis_a003285

namespace M5CF

open Matrix

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℤ

def tm (a : ℤ) : Mat2 := !![a, 1; 1, 0]

def tp (c : ℕ → ℤ) (s : ℕ) : ℕ → Mat2
  | 0 => 1
  | n + 1 => tm (c (s + n)) * tp c s n

lemma tp_add (c : ℕ → ℤ) (s n m : ℕ) :
    tp c s (n + m) = tp c (s + n) m * tp c s n := by
  induction m with
  | zero => simp [tp]
  | succ m ih =>
    change tm (c (s + (n + m))) * tp c s (n + m) =
      (tm (c ((s + n) + m)) * tp c (s + n) m) * tp c s n
    simp only [ih, Nat.add_assoc, Matrix.mul_assoc]

lemma tp_shift (c : ℕ → ℤ) (m : ℕ) (h : ∀ k, c (k + m) = c k)
    (s j : ℕ) : tp c (s + m) j = tp c s j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hc : c (s + m + j) = c (s + j) := by
      convert h (s + j) using 1 <;> congr 1 <;> omega
    simp only [tp, ih, hc]

lemma tp_trace_shift (c : ℕ → ℤ) (m : ℕ) (h : ∀ k, c (k + m) = c k)
    (s : ℕ) : (tp c (s + 1) m).trace = (tp c s m).trace := by
  cases m with
  | zero => rfl
  | succ j =>
    have hleft : tp c s (j + 1) = tp c (s + 1) j * tm (c s) := by
      calc
        tp c s (j + 1) = tp c s (1 + j) := by congr 1 <;> omega
        _ = tp c (s + 1) j * tp c s 1 := tp_add c s 1 j
        _ = tp c (s + 1) j * tm (c s) := by simp [tp]
    have hright : tp c (s + 1) (j + 1) = tm (c s) * tp c (s + 1) j := by
      simp only [tp]
      have hc : c (s + 1 + j) = c s := by
        convert h s using 1 <;> congr 1 <;> omega
      rw [hc]
    rw [hleft, hright, Matrix.trace_mul_comm]

lemma tp_trace_const (c : ℕ → ℤ) (m : ℕ) (h : ∀ k, c (k + m) = c k)
    (s : ℕ) : (tp c s m).trace = (tp c 0 m).trace := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [tp_trace_shift c m h s, ih]

lemma tp_det (c : ℕ → ℤ) (s m : ℕ) : (tp c s m).det = (-1 : ℤ) ^ m := by
  induction m with
  | zero => simp [tp]
  | succ m ih =>
    change (tm (c (s + m)) * tp c s m).det = (-1 : ℤ) ^ (m + 1)
    rw [Matrix.det_mul, ih, pow_succ]
    have ht : (tm (c (s + m))).det = (-1 : ℤ) := by simp [tm, Matrix.det_fin_two]
    rw [ht]
    ring

lemma action2 (A : Mat2) (v : Fin 2 → ℤ) :
    (A *ᵥ (A *ᵥ v)) 1 = A.trace * (A *ᵥ v) 1 - A.det * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.trace, Matrix.diag,
    Matrix.det_fin_two]
  ring

def vec (u : ℕ → ℤ) (s : ℕ) : Fin 2 → ℤ := ![u (s + 1), u s]

lemma vec_step (u c : ℕ → ℤ) (h : ∀ k, u (k + 2) = c k * u (k + 1) + u k)
    (s : ℕ) : vec u (s + 1) = tm (c s) *ᵥ vec u s := by
  funext i
  fin_cases i
  · simpa [vec, tm, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Nat.add_assoc] using h s
  · simp [vec, tm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma vec_prod (u c : ℕ → ℤ) (h : ∀ k, u (k + 2) = c k * u (k + 1) + u k)
    (s j : ℕ) : vec u (s + j) = tp c s j *ᵥ vec u s := by
  induction j with
  | zero => simp [tp]
  | succ j ih =>
    rw [Nat.add_succ, vec_step u c h, ih]
    simp only [tp, Matrix.mulVec_mulVec]

lemma periodic_linear (u c : ℕ → ℤ) (m : ℕ)
    (hu : ∀ k, u (k + 2) = c k * u (k + 1) + u k)
    (hc : ∀ k, c (k + m) = c k) :
    ∀ k, u (k + 2 * m) = (tp c 0 m).trace * u (k + m) - (-1 : ℤ) ^ m * u k := by
  intro k
  have h1 := vec_prod u c hu k m
  have h2 := vec_prod u c hu (k + m) m
  rw [tp_shift c m hc k m] at h2
  have h3 : vec u (k + 2 * m) = tp c k m *ᵥ (tp c k m *ᵥ vec u k) := by
    calc
      vec u (k + 2 * m) = vec u ((k + m) + m) := by congr 1 <;> omega
      _ = tp c k m *ᵥ vec u (k + m) := h2
      _ = tp c k m *ᵥ (tp c k m *ᵥ vec u k) := by rw [h1]
  have ha := action2 (tp c k m) (vec u k)
  rw [tp_trace_const c m hc k, tp_det] at ha
  have he := congrFun h3 1
  rw [ha] at he
  have hv : (tp c k m *ᵥ vec u k) 1 = u (k + m) := by
    rw [← h1]
    simp [vec]
  rw [hv] at he
  simpa [vec] using he
end M5CF

open M5CF OMA.S_oeis_a003285

theorem OMA.solution : type_of% @OMA.S_oeis_a003285.main := by
  classical
  intro d hd
  let x : ℝ := Real.sqrt d
  let m : ℕ := cfPeriod d
  let c : ℕ → ℤ := fun k => cfCoeff x (k + 2)
  let S : Set ℕ := {j : ℕ | 0 < j ∧ ∀ k : ℕ, 1 ≤ k →
    cfCoeff x (k + j) = cfCoeff x k}
  have hper : m = sInf S := rfl
  have hm : ∀ j, 1 ≤ j → cfCoeff x (j + m) = cfCoeff x j := by
    by_cases hs : S.Nonempty
    · rw [hper]
      exact (Nat.sInf_mem hs).2
    · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
      rw [hper, he, Nat.sInf_empty]
      intro j hj
      simp
  have hc : ∀ k, c (k + m) = c k := by
    intro k
    dsimp [c]
    have hk := hm (k + 2) (by omega)
    convert hk using 1 <;> congr 1 <;> omega
  refine ⟨(tp c 0 m).trace, ?_⟩
  constructor
  · exact periodic_linear (convDen x) c m (by intro k; rfl) hc
  · exact periodic_linear (convNum x) c m (by intro k; rfl) hc
