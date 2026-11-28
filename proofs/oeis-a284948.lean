import OMAStatements.S_oeis_a284948

-- Problem: A284948: 1-limiting word of the morphism 0 -> 10, 1 -> 00.
-- Upstream: formal-conjectures :0 (declaration OMA.S_oeis_a284948.main)
-- Credit: @prasledi (the owner of the agent is credited as the solver)
-- Proof: both words are described by the parity of the 2-adic valuation.
-- f i = 0 for odd i and f (2q) = 1 - f q; then letter i of S(k) is f i (0 < i < 2^k)
-- and letter j of T(k) is f (j+1) (j < 2^k), so both sides equal f (n-1).

namespace OMA.P_oeis_a284948

open OMA.S_oeis_a284948

def f (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else if n % 2 = 1 then 0 else 1 - f (n / 2)
decreasing_by omega

lemma f_odd (q : ℕ) : f (2 * q + 1) = 0 := by
  rw [f]; simp

lemma f_even (q : ℕ) (hq : 0 < q) : f (2 * q) = 1 - f q := by
  rw [f]
  have h1 : ¬ (2 * q = 0) := by omega
  have h2 : ¬ (2 * q % 2 = 1) := by omega
  have h3 : 2 * q / 2 = q := by omega
  simp only [h1, h2, h3, dite_false, if_false]

lemma flatMap_two (g : ℕ → List ℕ) (hg : ∀ x, (g x).length = 2) :
    ∀ (l : List ℕ) (q r : ℕ), r < 2 →
      (l.flatMap g).getD (2 * q + r) 0 =
        if q < l.length then (g (l.getD q 0)).getD r 0 else 0
  | [], q, r, _ => by simp
  | a :: l, 0, r, hr => by
      rw [List.flatMap_cons, List.getD_append _ _ _ _ (by rw [hg]; omega)]
      simp
  | a :: l, q + 1, r, hr => by
      rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by rw [hg]; omega), hg]
      have e : 2 * (q + 1) + r - 2 = 2 * q + r := by omega
      rw [e, flatMap_two g hg l q r hr]
      simp

lemma len_two (g : ℕ → List ℕ) (hg : ∀ x, (g x).length = 2) :
    ∀ l : List ℕ, (l.flatMap g).length = 2 * l.length
  | [] => by simp
  | a :: l => by
      rw [List.flatMap_cons, List.length_append, hg, len_two g hg l, List.length_cons]
      ring

lemma morph_len (x : ℕ) : (morph x).length = 2 := by
  cases x <;> rfl

lemma pdMorph_len (x : ℕ) : (pdMorph x).length = 2 := by
  cases x <;> rfl

lemma iter_len : ∀ k, (iter k).length = 2 ^ k
  | 0 => rfl
  | k + 1 => by
      rw [iter, len_two morph morph_len, iter_len k, pow_succ]; ring

lemma pdIter_len : ∀ k, (pdIter k).length = 2 ^ k
  | 0 => rfl
  | k + 1 => by
      rw [pdIter, len_two pdMorph pdMorph_len, pdIter_len k, pow_succ]; ring

lemma f_le (n : ℕ) : f n ≤ 1 := by
  rw [f]; split_ifs <;> omega

lemma morph0 (x : ℕ) (hx : x ≤ 1) : (morph x).getD 0 0 = 1 - x := by
  interval_cases x <;> rfl

lemma morph1 (x : ℕ) : (morph x).getD 1 0 = 0 := by
  cases x <;> rfl

lemma pdMorph0 (x : ℕ) : (pdMorph x).getD 0 0 = 0 := by
  cases x <;> rfl

lemma pdMorph1 (x : ℕ) (hx : x ≤ 1) : (pdMorph x).getD 1 0 = 1 - x := by
  interval_cases x <;> rfl

lemma S_eq : ∀ k i, 0 < i → i < 2 ^ k → (iter k).getD i 0 = f i
  | 0, i, h0, h1 => by simp at h1; omega
  | k + 1, i, h0, h1 => by
      obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ∧ i = 2 * q + r := ⟨i / 2, i % 2, by omega, by omega⟩
      have hq : q < 2 ^ k := by rw [pow_succ] at h1; omega
      rw [iter, flatMap_two morph morph_len _ q r hr, iter_len, if_pos hq]
      interval_cases r
      · have hq0 : 0 < q := by omega
        rw [S_eq k q hq0 hq, morph0 _ (f_le q), Nat.add_zero, f_even q hq0]
      · rw [morph1, f_odd]

lemma T_eq : ∀ k j, j < 2 ^ k → (pdIter k).getD j 0 = f (j + 1)
  | 0, j, h1 => by
      have hj : j = 0 := by simp at h1; omega
      subst hj
      rw [show (0 : ℕ) + 1 = 2 * 0 + 1 from rfl, f_odd]
      rfl
  | k + 1, j, h1 => by
      obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ∧ j = 2 * q + r := ⟨j / 2, j % 2, by omega, by omega⟩
      have hq : q < 2 ^ k := by rw [pow_succ] at h1; omega
      rw [pdIter, flatMap_two pdMorph pdMorph_len _ q r hr, pdIter_len, if_pos hq]
      interval_cases r
      · rw [pdMorph0, Nat.add_zero, f_odd]
      · rw [T_eq k q hq, pdMorph1 _ (f_le _)]
        have e : 2 * q + 1 + 1 = 2 * (q + 1) := by ring
        rw [e, f_even (q + 1) (by omega)]

end OMA.P_oeis_a284948

open OMA.P_oeis_a284948 in
theorem OMA.solution : type_of% @OMA.S_oeis_a284948.main := by
  intro n hn
  have h2 : n - 1 < 2 ^ (2 * n + 1) := by
    have := Nat.lt_two_pow_self (n := 2 * n + 1)
    omega
  have h3 : n - 2 < 2 ^ (n - 2 + 1) := by
    have := Nat.lt_two_pow_self (n := n - 2 + 1)
    omega
  unfold OMA.S_oeis_a284948.a OMA.S_oeis_a284948.A096268
  rw [S_eq _ _ (by omega) h2, T_eq _ _ h3]
  congr 1
  omega
