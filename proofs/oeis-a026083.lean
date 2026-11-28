import OMAStatements.S_oeis_a026083

-- Problem: A026083: a(n) = number of (s(0), s(1), ..., s(n)) such that every s(i) is an integer, s(0) = 0 = s(n), |s(i) - s(i-1)| = 1 for i = 1,2,3; |
-- Upstream: formal-conjectures statements/oeis-a026083.lean:0 (declaration OMA.S_oeis_a026083.main)
-- Credit: @m-miyawaki-m (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Proof sketch. With `P = x⁻¹ + 1 + x`, the paths counted by `a n` give
`a n = [x⁰] (x + x⁻¹)³ P^(n-3) = [x⁰] (P - 1)³ P^(n-3) = C n - 3 C (n-1) + 3 C (n-2) - C (n-3)`,
where `C j = [x⁰] P^j` are the central trinomial coefficients. These satisfy
`j C j = (2j-1) C (j-1) + 3 (j-1) C (j-2)` (from the Pascal rule and the derivative identity
`k T(m+1,k) = (m+1)(T(m,k-1) - T(m,k+1))`), and the target recurrence is the combination
`R(n) - 4R(n-1) + 6R(n-2) - 4R(n-3) + R(n-4)` of that one.
-/

namespace OMA.Sol_oeis_a026083

open OMA.S_oeis_a026083

/-- trinomial coefficients `T m k = [x^k] (x⁻¹ + 1 + x)^m`. -/
def T : ℕ → ℤ → ℤ
  | 0, k => if k = 0 then 1 else 0
  | m + 1, k => T m (k - 1) + T m k + T m (k + 1)

lemma T_succ (m : ℕ) (k : ℤ) : T (m + 1) k = T m (k - 1) + T m k + T m (k + 1) := rfl

lemma T_neg (m : ℕ) : ∀ k, T m (-k) = T m k := by
  induction m with
  | zero => intro k; simp [T]
  | succ m ih =>
    intro k
    rw [T_succ, T_succ, show -k - 1 = -(k + 1) by ring, show -k + 1 = -(k - 1) by ring,
      ih, ih, ih]
    ring

/-- derivative identity -/
lemma T_deriv (m : ℕ) : ∀ k : ℤ, k * T (m + 1) k = (m + 1) * (T m (k - 1) - T m (k + 1)) := by
  induction m with
  | zero =>
    intro k
    simp only [T]
    by_cases h0 : k = 0
    · subst h0; simp
    by_cases h1 : k = 1
    · subst h1; simp
    by_cases h2 : k = -1
    · subst h2; simp
    have : k - 1 ≠ 0 := by omega
    have : k + 1 ≠ 0 := by omega
    simp [*]
  | succ m ih =>
    intro k
    have h1 := ih (k - 1)
    have h2 := ih k
    have h3 := ih (k + 1)
    have p1 : T (m + 1) (k - 1) = T m (k - 2) + T m (k - 1) + T m k := by
      rw [T_succ]; ring_nf
    have p3 : T (m + 1) (k + 1) = T m k + T m (k + 1) + T m (k + 2) := by
      rw [T_succ]; ring_nf
    simp only [show k - 1 - 1 = k - 2 by ring, show k - 1 + 1 = k by ring,
      show k + 1 - 1 = k by ring, show k + 1 + 1 = k + 2 by ring] at h1 h3
    rw [T_succ (m + 1) k]
    push_cast
    linear_combination h1 + h2 + h3 - (↑m + 1) * p1 + (↑m + 1) * p3

/-- central trinomial coefficients -/
def C (j : ℕ) : ℤ := T j 0

lemma C_rec (m : ℕ) :
    ((m : ℤ) + 2) * C (m + 2) = (2 * m + 3) * C (m + 1) + 3 * (m + 1) * C m := by
  unfold C
  have e1 : T (m + 2) 0 = T (m + 1) (-1) + T (m + 1) 0 + T (m + 1) 1 := by
    rw [T_succ]; norm_num
  have e0 : T (m + 1) 0 = T m (-1) + T m 0 + T m 1 := by rw [T_succ]; norm_num
  have e2 : T (m + 1) 1 = T m 0 + T m 1 + T m 2 := by rw [T_succ]; norm_num
  have d := T_deriv m 1
  norm_num at d
  have s1 : T (m + 1) (-1) = T (m + 1) 1 := T_neg _ 1
  have s0 : T m (-1) = T m 1 := T_neg _ 1
  linear_combination (↑m + 2) * e1 + (↑m + 2) * s1 - (↑m + 1) * e0 - (↑m + 1) * s0
    + 2 * (↑m + 1) * e2 + 2 * d

/-- L3: the algebraic step. -/
theorem main_of_closed (ha : ∀ n, 3 ≤ n → (a n : ℤ) = C n - 3 * C (n - 1) + 3 * C (n - 2) - C (n - 3)) :
    ∀ n : ℕ, 7 ≤ n →
      (n : ℤ) * a n + (-3 * n + 5) * a (n - 1) + (-(n : ℤ) - 6) * a (n - 2) +
        3 * ((n : ℤ) - 5) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [ha _ (by omega), ha _ (by omega), ha _ (by omega), ha _ (by omega)]
  simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 6 - 1 = m + 5 by omega,
    show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega,
    show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 4 - 1 = m + 3 by omega,
    show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega]
  have r5 := C_rec (m + 5)
  have r4 := C_rec (m + 4)
  have r3 := C_rec (m + 3)
  have r2 := C_rec (m + 2)
  have r1 := C_rec (m + 1)
  push_cast at *
  linear_combination r5 - 4 * r4 + 6 * r3 - 4 * r2 + r1

/-! L1: counting. -/

/-- paths of length `m` from `k` to `0`, first `r` steps `±1`, later steps in `{-1,0,1}`. -/
def P (m : ℕ) (k : ℤ) (r : ℕ) : Set (Fin (m + 1) → ℤ) :=
  {s | s 0 = k ∧ s (Fin.last m) = 0 ∧ ∀ i : Fin m,
    (i.val < r → |s i.succ - s i.castSucc| = 1) ∧ (r ≤ i.val → |s i.succ - s i.castSucc| ≤ 1)}

lemma a_eq (n : ℕ) : a n = (P n 0 3).ncard := rfl

lemma mem_P_cons (m : ℕ) (k : ℤ) (r : ℕ) (t : Fin (m + 1) → ℤ) :
    (Fin.cons k t : Fin (m + 2) → ℤ) ∈ P (m + 1) k (r + 1) ↔
      |t 0 - k| = 1 ∧ t ∈ P m (t 0) r := by
  simp only [P, Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.succ_zero_eq_one,
    Fin.castSucc_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
  rw [show (Fin.last (m + 1)) = (Fin.last m).succ from (Fin.succ_last m).symm, Fin.cons_succ]
  constructor
  · rintro ⟨-, hl, ⟨h0, -⟩, hs⟩
    refine ⟨h0 (by omega), trivial, hl, fun i => ⟨fun h => (hs i).1 (by omega),
      fun h => (hs i).2 (by omega)⟩⟩
  · rintro ⟨h0, -, hl, hs⟩
    refine ⟨trivial, hl, ⟨fun _ => h0, fun h => by omega⟩, fun i => ⟨fun h => (hs i).1 (by omega),
      fun h => (hs i).2 (by omega)⟩⟩

lemma mem_P_cons0 (m : ℕ) (k : ℤ) (t : Fin (m + 1) → ℤ) :
    (Fin.cons k t : Fin (m + 2) → ℤ) ∈ P (m + 1) k 0 ↔
      |t 0 - k| ≤ 1 ∧ t ∈ P m (t 0) 0 := by
  simp only [P, Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.succ_zero_eq_one,
    Fin.castSucc_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
  rw [show (Fin.last (m + 1)) = (Fin.last m).succ from (Fin.succ_last m).symm, Fin.cons_succ]
  constructor
  · rintro ⟨-, hl, ⟨-, h0⟩, hs⟩
    exact ⟨h0 le_rfl, trivial, hl, fun i => ⟨fun h => by omega, fun _ => (hs i).2 (by omega)⟩⟩
  · rintro ⟨h0, -, hl, hs⟩
    exact ⟨trivial, hl, ⟨fun h => by omega, fun _ => h0⟩, fun i => ⟨fun h => by omega,
      fun _ => (hs i).2 (by omega)⟩⟩

/-- prepend a starting point. -/
def cz {m : ℕ} (k : ℤ) (t : Fin (m + 1) → ℤ) : Fin (m + 2) → ℤ := Fin.cons k t

lemma cz_inj {m : ℕ} (k : ℤ) : Function.Injective (cz (m := m) k) :=
  Fin.cons_right_injective (α := fun _ => ℤ) k

lemma P_zero (m : ℕ) (j : ℤ) (r : ℕ) {t : Fin (m + 1) → ℤ} (h : t ∈ P m j r) : t 0 = j := h.1

lemma disj {m : ℕ} (k j j' : ℤ) (r r' : ℕ) (h : j ≠ j') :
    Disjoint (cz k '' P m j r) (cz k '' P m j' r') := by
  rw [Set.disjoint_left]
  rintro _ ⟨t, ht, rfl⟩ ⟨u, hu, he⟩
  have := cz_inj k he
  subst this
  exact h ((P_zero _ _ _ ht).symm.trans (P_zero _ _ _ hu))

lemma eq_cz {m : ℕ} (k : ℤ) (s : Fin (m + 2) → ℤ) (h : s 0 = k) : s = cz k (Fin.tail s) := by
  rw [← h]; exact (Fin.cons_self_tail s).symm

lemma P_succ_succ (m : ℕ) (k : ℤ) (r : ℕ) :
    P (m + 1) k (r + 1) = cz k '' P m (k - 1) r ∪ cz k '' P m (k + 1) r := by
  ext s
  constructor
  · intro hs
    have e := eq_cz k s hs.1
    rw [e] at hs ⊢
    rw [cz, mem_P_cons] at hs
    obtain ⟨h0, ht⟩ := hs
    rcases abs_eq (zero_le_one) |>.1 h0 with h | h
    · right; refine ⟨_, ?_, rfl⟩; rwa [show k + 1 = Fin.tail s 0 by omega]
    · left; refine ⟨_, ?_, rfl⟩; rwa [show k - 1 = Fin.tail s 0 by omega]
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) <;> rw [cz, mem_P_cons] <;>
      refine ⟨?_, by rwa [P_zero _ _ _ ht]⟩ <;> rw [P_zero _ _ _ ht] <;> norm_num

lemma P_succ_zero (m : ℕ) (k : ℤ) :
    P (m + 1) k 0 = (cz k '' P m (k - 1) 0 ∪ cz k '' P m k 0) ∪ cz k '' P m (k + 1) 0 := by
  ext s
  constructor
  · intro hs
    have e := eq_cz k s hs.1
    rw [e] at hs ⊢
    rw [cz, mem_P_cons0] at hs
    obtain ⟨h0, ht⟩ := hs
    rw [abs_le] at h0
    rcases (show Fin.tail s 0 = k - 1 ∨ Fin.tail s 0 = k ∨ Fin.tail s 0 = k + 1 by omega)
      with h | h | h
    · left; left; exact ⟨_, h ▸ ht, rfl⟩
    · left; right; exact ⟨_, h ▸ ht, rfl⟩
    · right; exact ⟨_, h ▸ ht, rfl⟩
  · rintro ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩) <;> rw [cz, mem_P_cons0] <;>
      refine ⟨?_, by rwa [P_zero _ _ _ ht]⟩ <;> rw [P_zero _ _ _ ht] <;> norm_num

def N : ℕ → ℤ → ℕ → ℤ
  | 0, k, _ => if k = 0 then 1 else 0
  | m + 1, k, 0 => N m (k - 1) 0 + N m k 0 + N m (k + 1) 0
  | m + 1, k, r + 1 => N m (k - 1) r + N m (k + 1) r

lemma P_card (m : ℕ) : ∀ k r, (P m k r).Finite ∧ ((P m k r).ncard : ℤ) = N m k r := by
  induction m with
  | zero =>
    intro k r
    by_cases hk : k = 0
    · have : P 0 k r = {fun _ => 0} := by
        ext s
        simp only [P, Set.mem_ofPred_eq, Set.mem_singleton_iff, IsEmpty.forall_iff,
          and_true, Fin.last_zero]
        constructor
        · rintro ⟨-, h⟩; funext i; rw [Fin.fin_one_eq_zero i]; exact h
        · rintro rfl; exact ⟨hk.symm, rfl⟩
      rw [this]; simp [N, hk]
    · have : P 0 k r = ∅ := by
        ext s
        simp only [P, Set.mem_ofPred_eq, Set.mem_empty_iff_false, IsEmpty.forall_iff,
          and_true, Fin.last_zero, iff_false, not_and]
        intro h1 h2; exact hk (h1 ▸ h2)
      rw [this]; simp [N, hk]
  | succ m ih =>
    intro k r
    cases r with
    | zero =>
      rw [P_succ_zero]
      obtain ⟨f1, c1⟩ := ih (k - 1) 0
      obtain ⟨f2, c2⟩ := ih k 0
      obtain ⟨f3, c3⟩ := ih (k + 1) 0
      have F1 := f1.image (cz k); have F2 := f2.image (cz k); have F3 := f3.image (cz k)
      refine ⟨(F1.union F2).union F3, ?_⟩
      rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨disj _ _ _ _ _ (by omega),
          disj _ _ _ _ _ (by omega)⟩) (F1.union F2) F3,
        Set.ncard_union_eq (disj _ _ _ _ _ (by omega)) F1 F2,
        Set.ncard_image_of_injective _ (cz_inj k), Set.ncard_image_of_injective _ (cz_inj k),
        Set.ncard_image_of_injective _ (cz_inj k)]
      simp only [N]; push_cast; rw [c1, c2, c3]
    | succ r =>
      rw [P_succ_succ]
      obtain ⟨f1, c1⟩ := ih (k - 1) r
      obtain ⟨f3, c3⟩ := ih (k + 1) r
      have F1 := f1.image (cz k); have F3 := f3.image (cz k)
      refine ⟨F1.union F3, ?_⟩
      rw [Set.ncard_union_eq (disj _ _ _ _ _ (by omega)) F1 F3,
        Set.ncard_image_of_injective _ (cz_inj k), Set.ncard_image_of_injective _ (cz_inj k)]
      simp only [N]; push_cast; rw [c1, c3]

lemma N_zero (m : ℕ) : ∀ k, N m k 0 = T m k := by
  induction m with
  | zero => intro k; simp [N, T]
  | succ m ih => intro k; simp only [N, T_succ, ih]

lemma a_closed (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℤ) = C n - 3 * C (n - 1) + 3 * C (n - 2) - C (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [a_eq, (P_card _ 0 3).2]
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega, C, N, N_zero, T_succ]
  norm_num
  ring

end OMA.Sol_oeis_a026083

theorem OMA.solution : type_of% @OMA.S_oeis_a026083.main :=
  OMA.Sol_oeis_a026083.main_of_closed OMA.Sol_oeis_a026083.a_closed
