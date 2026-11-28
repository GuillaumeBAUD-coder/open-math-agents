import OMAStatements.S_oeis_a000959

-- Credit: @synthrosai
-- The backward argument for a maximal entry specializes the block argument
-- in Z. Chase, A random analogue of Gilbreath's conjecture, Lemma 3.2.
namespace OMA.R_oeis_a000959_R1

open OMA.S_oeis_a000959

/-- At dyadic depths r ≥ 2, positive columns through 3r have height at most four. -/
def H1 : Prop :=
  ∀ m i : ℕ, let r := 2 ^ (m + 1)
    1 ≤ i → i ≤ 3 * r → gilbreath (b 2) r i ≤ 4

/-- In each indicated window there is a pair, spaced r apart in the input,
whose values differ modulo four. This condition involves only the original row. -/
def H2 : Prop :=
  ∀ m i : ℕ, let r := 2 ^ (m + 1)
    1 ≤ i → i ≤ 2 * r →
      ∃ j ≤ r, b 2 (i + j + r) % 4 ≠ b 2 (i + j) % 4

lemma sieve_odd (k i : ℕ) : s k i % 2 = 1 := by
  induction k generalizing i with
  | zero => simp [s]
  | succ k ih => exact ih _

lemma abs_options (z : ℤ) : |z| = z ∨ |z| = -z := by
  by_cases hz : 0 ≤ z
  · exact Or.inl (abs_of_nonneg hz)
  · exact Or.inr (abs_of_neg (by omega))

lemma tail_parity (t i : ℕ) (hi : 0 < i) :
    gilbreath (b 2) t i % 2 = if t = 0 then 1 else 0 := by
  induction t generalizing i with
  | zero =>
    simp only [gilbreath, b, if_neg (Nat.ne_of_gt hi), if_true]
    split
    · decide
    · have ho := sieve_odd i i
      unfold lucky
      omega
  | succ t ih =>
    simp only [gilbreath, Nat.succ_ne_zero, if_false]
    have hl := ih i hi
    have hr := ih (i + 1) (by omega)
    rcases abs_options (gilbreath (b 2) t (i + 1) - gilbreath (b 2) t i) with h | h <;>
      rw [h] <;> omega

lemma dyadic_residue (m t i : ℕ) (hi : 0 < i) :
    gilbreath (b 2) (t + 2 ^ m) i % 4 =
      (gilbreath (b 2) t (i + 2 ^ m) - gilbreath (b 2) t i) % 4 := by
  induction m generalizing t i with
  | zero =>
    simp only [pow_zero, gilbreath]
    have hl := tail_parity t i hi
    have hr := tail_parity t (i + 1) (by omega)
    rcases abs_options (gilbreath (b 2) t (i + 1) - gilbreath (b 2) t i) with h | h
    · rw [h]
    · rw [h]
      omega
  | succ m ih =>
    let r := 2 ^ m
    have hir : 0 < i + r := Nat.add_pos_left hi r
    have outer : gilbreath (b 2) (t + r + r) i % 4 =
        (gilbreath (b 2) (t + r) (i + r) - gilbreath (b 2) (t + r) i) % 4 := ih (t + r) i hi
    have left : gilbreath (b 2) (t + r) i % 4 =
        (gilbreath (b 2) t (i + r) - gilbreath (b 2) t i) % 4 := ih t i hi
    have right : gilbreath (b 2) (t + r) (i + r) % 4 =
        (gilbreath (b 2) t (i + r + r) - gilbreath (b 2) t (i + r)) % 4 :=
      ih t (i + r) hir
    have pl := tail_parity t i hi
    have pr := tail_parity t (i + r) hir
    rw [show 2 ^ (m + 1) = r + r by simp [r, pow_succ, Nat.mul_two]]
    simp only [← Nat.add_assoc]
    omega

/-- An interval bounded between zero and B retains those bounds as it shrinks. -/
lemma cone_bounds (x : ℕ → ℤ) (t i w : ℕ) (B : ℤ)
    (h : ∀ j ≤ w, 0 ≤ gilbreath x t (i + j) ∧ gilbreath x t (i + j) ≤ B)
    (d j : ℕ) (hw : d + j ≤ w) :
    0 ≤ gilbreath x (t + d) (i + j) ∧ gilbreath x (t + d) (i + j) ≤ B := by
  induction d generalizing j with
  | zero => exact h j (by omega)
  | succ d ih =>
    have left := ih j (by omega)
    have right := ih (j + 1) (by omega)
    rw [← Nat.add_assoc] at right
    change 0 ≤ |gilbreath x (t + d) (i + j + 1) - gilbreath x (t + d) (i + j)| ∧
      |gilbreath x (t + d) (i + j + 1) - gilbreath x (t + d) (i + j)| ≤ B
    exact ⟨abs_nonneg _, abs_le.mpr ⟨by omega, by omega⟩⟩

/-- If every adjacent difference in a bounded block is divisible by four and
one difference attains four, the entire parent block is divisible by four. -/
lemma expand_block (a : ℕ → ℤ) (w : ℕ)
    (hb : ∀ j ≤ w + 1, 0 ≤ a j ∧ a j ≤ 4)
    (hm : ∀ j ≤ w, |a (j + 1) - a j| % 4 = 0)
    (hf : ∃ j ≤ w, |a (j + 1) - a j| = 4) :
    (∀ j ≤ w + 1, a j % 4 = 0) ∧ ∃ j ≤ w + 1, a j = 4 := by
  have adj (j : ℕ) (hj : j ≤ w) : a (j + 1) % 4 = a j % 4 := by
    have h := hm j hj
    rcases abs_options (a (j + 1) - a j) with he | he <;> rw [he] at h <;> omega
  have same (j : ℕ) (hj : j ≤ w + 1) : a j % 4 = a 0 % 4 := by
    induction j with
    | zero => rfl
    | succ j ih => exact (adj j (by omega)).trans (ih (by omega))
  obtain ⟨q, hq, he⟩ := hf
  have bl := hb q (by omega)
  have br := hb (q + 1) (by omega)
  have one : a q = 4 ∨ a (q + 1) = 4 := by
    rcases abs_options (a (q + 1) - a q) with h | h <;> rw [h] at he <;> omega
  have occurs : ∃ j ≤ w + 1, a j = 4 := by
    rcases one with h | h
    · exact ⟨q, by omega, h⟩
    · exact ⟨q + 1, by omega, h⟩
  obtain ⟨p, hp, hv⟩ := occurs
  have hz := same p hp
  rw [hv] at hz
  exact ⟨fun j hj => (same j hj).trans (by omega), ⟨p, hp, hv⟩⟩

/-- An output of four forces every input in its ancestral window to be a
multiple of four, provided that window was bounded between zero and four. -/
lemma four_ancestors (x : ℕ → ℤ) (t i h : ℕ)
    (hb : ∀ j ≤ h, 0 ≤ gilbreath x t (i + j) ∧ gilbreath x t (i + j) ≤ 4)
    (hf : gilbreath x (t + h) i = 4) :
    ∀ j ≤ h, gilbreath x t (i + j) % 4 = 0 := by
  have back (d w : ℕ) (hw : d + w = h)
      (hm : ∀ j ≤ w, gilbreath x (t + d) (i + j) % 4 = 0)
      (he : ∃ j ≤ w, gilbreath x (t + d) (i + j) = 4) :
      ∀ j ≤ h, gilbreath x t (i + j) % 4 = 0 := by
    induction d generalizing w with
    | zero =>
      have hw' : w = h := by omega
      simpa [hw'] using hm
    | succ d ih =>
      let a (j : ℕ) := gilbreath x (t + d) (i + j)
      have bounded (j : ℕ) (hj : j ≤ w + 1) : 0 ≤ a j ∧ a j ≤ 4 :=
        cone_bounds x t i h 4 hb d j (by omega)
      have step (j : ℕ) :
          |a (j + 1) - a j| = gilbreath x (t + (d + 1)) (i + j) := by
        change |gilbreath x (t + d) (i + (j + 1)) - gilbreath x (t + d) (i + j)| =
          |gilbreath x (t + d) (i + j + 1) - gilbreath x (t + d) (i + j)|
        rw [Nat.add_assoc]
      have mult (j : ℕ) (hj : j ≤ w) : |a (j + 1) - a j| % 4 = 0 := by
        rw [step]
        exact hm j hj
      obtain ⟨q, hq, hq4⟩ := he
      obtain ⟨parent, four⟩ := expand_block a w bounded mult ⟨q, hq, (step q).trans hq4⟩
      exact ih (w + 1) (by omega) parent four
  apply back h 0 (by omega)
  · intro j hj
    have hj' : j = 0 := by omega
    simp [hj', hf]
  · exact ⟨0, by omega, by simpa using hf⟩

lemma row_nonneg (x : ℕ → ℤ) (t i : ℕ) (ht : 0 < t) : 0 ≤ gilbreath x t i := by
  cases t with
  | zero => omega
  | succ t => exact abs_nonneg _

/-- At depth 2r, the two hypotheses give a prefix of 2r positive columns
whose entries are zero or two. -/
lemma dyadic_band (amplitude : H1) (mismatch : H2) (m i : ℕ)
    (hi : 1 ≤ i) (hi' : i ≤ 2 * 2 ^ (m + 1)) :
    gilbreath (b 2) (2 * 2 ^ (m + 1)) i ≤ 2 := by
  let r := 2 ^ (m + 1)
  have hr : 0 < r := Nat.two_pow_pos _
  change i ≤ 2 * r at hi'
  have bounded (j : ℕ) (hj : j ≤ r) :
      0 ≤ gilbreath (b 2) r (i + j) ∧ gilbreath (b 2) r (i + j) ≤ 4 := by
    exact ⟨row_nonneg _ r _ hr, amplitude m (i + j) (by omega) (by change i + j ≤ 3 * r; omega)⟩
  have bnd := cone_bounds (b 2) r i r 4 bounded r 0 (by omega)
  simp only [Nat.add_zero] at bnd
  have parity := tail_parity (r + r) i hi
  simp only [if_neg (show r + r ≠ 0 by omega)] at parity
  obtain ⟨j, hj, different⟩ := mismatch m i hi hi'
  change b 2 (i + j + r) % 4 ≠ b 2 (i + j) % 4 at different
  have residue := dyadic_residue (m + 1) 0 (i + j) (by omega)
  change gilbreath (b 2) (0 + r) (i + j) % 4 =
    (b 2 (i + j + r) - b 2 (i + j)) % 4 at residue
  rw [Nat.zero_add] at residue
  suffices ne : gilbreath (b 2) (r + r) i ≠ 4 by
    change gilbreath (b 2) (2 * r) i ≤ 2
    rw [Nat.two_mul]
    omega
  intro four
  have hzero := four_ancestors (b 2) r i r bounded four j hj
  omega

lemma dyadic_cover (k : ℕ) (hk : 4 ≤ k) :
    ∃ m : ℕ, 2 * 2 ^ (m + 1) ≤ k ∧ k < 4 * 2 ^ (m + 1) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases small : k < 8
    · exact ⟨0, by omega, by omega⟩
    · obtain ⟨m, lower, upper⟩ := ih (k / 2) (by omega) (by omega)
      refine ⟨m + 1, ?_, ?_⟩ <;> rw [pow_succ 2 (m + 1)] <;> omega

lemma column_one_small (amplitude : H1) (mismatch : H2) (k : ℕ) (hk : 1 ≤ k) :
    gilbreath (b 2) k 1 = 0 ∨ gilbreath (b 2) k 1 = 2 := by
  by_cases small : k < 4
  · interval_cases k <;> decide
  obtain ⟨m, lower, upper⟩ := dyadic_cover k (by omega)
  let r := 2 ^ (m + 1)
  change 2 * r ≤ k at lower
  change k < 4 * r at upper
  have bounded (j : ℕ) (hj : j ≤ 2 * r - 1) :
      0 ≤ gilbreath (b 2) (2 * r) (1 + j) ∧ gilbreath (b 2) (2 * r) (1 + j) ≤ 2 := by
    have hr : 0 < r := Nat.two_pow_pos _
    exact ⟨row_nonneg _ _ _ (by omega),
      dyadic_band amplitude mismatch m _ (by omega) (by change 1 + j ≤ 2 * r; omega)⟩
  have h := cone_bounds (b 2) (2 * r) 1 (2 * r - 1) 2 bounded (k - 2 * r) 0 (by omega)
  rw [show 2 * r + (k - 2 * r) = k by omega] at h
  simp only [Nat.add_zero] at h
  have parity := tail_parity k 1 (by omega)
  rw [if_neg (show k ≠ 0 by omega)] at parity
  omega

lemma same_rows (n i : ℕ) :
    gilbreath (b 4) (n + 1) i = gilbreath (b 2) (n + 1) i := by
  induction n generalizing i with
  | zero => cases i with
    | zero => decide
    | succ i => simp [gilbreath, b]
  | succ n ih =>
    change |gilbreath (b 4) (n + 1) (i + 1) - gilbreath (b 4) (n + 1) i| =
      |gilbreath (b 2) (n + 1) (i + 1) - gilbreath (b 2) (n + 1) i|
    rw [ih, ih]

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000959.main := by
  intro amplitude mismatch
  have head (n : ℕ) : gilbreath (b 2) (n + 1) 0 = 1 := by
    induction n with
    | zero => decide
    | succ n ih =>
      change |gilbreath (b 2) (n + 1) 1 - gilbreath (b 2) (n + 1) 0| = 1
      rw [ih]
      rcases column_one_small amplitude mismatch (n + 1) (by omega) with hz | ht
      · rw [hz]
        decide
      · rw [ht]
        decide
  intro c hc k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  rcases (show c = 2 ∨ c = 4 from hc) with rfl | rfl
  · exact head n
  · exact (same_rows n 0).trans (head n)

end OMA.R_oeis_a000959_R1
