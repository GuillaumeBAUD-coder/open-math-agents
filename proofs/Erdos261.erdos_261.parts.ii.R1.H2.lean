import OMAReductions.R_Erdos261_erdos_261_parts_ii_R1

/-! Soundness of the residual orbit. After `s` steps the state is `(n + 1 + s, ρ)` and
`n / 2^n = ∑_{taken a} a / 2^a + ρ / 2^(n + 1 + s)`, the taken levels lying strictly between `n`
and `n + 1 + s`. While nothing has been taken, `ρ = 2^(s + 1) n`, which is never `n + 1 + s` for
`s > 0`; so a hit `ρ = n + 1 + j` comes with at least one taken level, and adding the level
`n + 1 + j` itself gives a representation with at least two terms. -/

namespace OMA.E261

def step (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1 + 1, if p.1 + 1 < p.2 then 2 * (p.2 - p.1) else 2 * p.2)

theorem fst_iter (n s : ℕ) : (step^[s] (n + 1, 2 * n)).1 = n + 1 + s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    show (step^[s] (n + 1, 2 * n)).1 + 1 = n + 1 + (s + 1)
    omega

theorem inv (n s : ℕ) : ∃ S : Finset ℕ, (∀ k ∈ S, n < k ∧ k < n + 1 + s) ∧
    (n : ℚ) / 2 ^ n = ∑ k ∈ S, (k : ℚ) / 2 ^ k +
      ((step^[s] (n + 1, 2 * n)).2 : ℚ) / 2 ^ (n + 1 + s) ∧
    (S = ∅ → (step^[s] (n + 1, 2 * n)).2 = 2 ^ (s + 1) * n) := by
  induction s with
  | zero =>
    refine ⟨∅, by simp, ?_, fun _ => by simp⟩
    simp only [Finset.sum_empty, Function.iterate_zero, id_eq, zero_add, add_zero]
    push_cast
    rw [pow_succ]
    field_simp
  | succ s ih =>
    obtain ⟨S, hS, hsum, hemp⟩ := ih
    have hfst := fst_iter n s
    have hstep : step^[s + 1] (n + 1, 2 * n) = step (step^[s] (n + 1, 2 * n)) :=
      Function.iterate_succ_apply' _ _ _
    rw [hstep]
    generalize step^[s] (n + 1, 2 * n) = p at hsum hemp hfst
    obtain ⟨i, r⟩ := p
    simp only at hfst hsum hemp
    subst hfst
    have hpow : (2 : ℚ) ^ (n + 1 + (s + 1)) = 2 ^ (n + 1 + s) * 2 := by
      rw [← add_assoc, pow_succ]
    by_cases hc : n + 1 + s + 1 < r
    · have hval : (step (n + 1 + s, r)).2 = 2 * (r - (n + 1 + s)) := by
        show (if n + 1 + s + 1 < r then 2 * (r - (n + 1 + s)) else 2 * r) = _
        rw [if_pos hc]
      have hnot : n + 1 + s ∉ S := fun h => by have := (hS _ h).2; omega
      refine ⟨insert (n + 1 + s) S, ?_, ?_, ?_⟩
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · omega
        · have := hS k hk
          omega
      · rw [hval, Finset.sum_insert hnot, hsum, hpow]
        have hle : n + 1 + s ≤ r := by omega
        push_cast [Nat.cast_sub hle]
        field_simp
        ring
      · intro h
        exact absurd h (Finset.insert_ne_empty _ _)
    · have hval : (step (n + 1 + s, r)).2 = 2 * r := by
        show (if n + 1 + s + 1 < r then 2 * (r - (n + 1 + s)) else 2 * r) = _
        rw [if_neg hc]
      refine ⟨S, ?_, ?_, ?_⟩
      · intro k hk
        have := hS k hk
        omega
      · rw [hval, hsum, hpow]
        push_cast
        field_simp
      · intro h
        rw [hval, hemp h, pow_succ 2 (s + 1)]
        ring

theorem pow_gt (j : ℕ) (hj : 0 < j) : j + 2 < 2 ^ (j + 1) := by
  have h : j < 2 ^ j := Nat.lt_two_pow_self
  rw [pow_succ]
  omega

end OMA.E261

theorem OMA.solution : OMA.R_Erdos261_erdos_261_parts_ii_R1.H2 := by
  intro n j hn hj h
  have h' : (OMA.E261.step^[j] (n + 1, 2 * n)).2 = n + 1 + j := h
  obtain ⟨S, hS, hsum, hemp⟩ := OMA.E261.inv n j
  rw [h'] at hsum
  have hne : S ≠ ∅ := by
    intro hS0
    have h1 := hemp hS0
    rw [h'] at h1
    have h2 := OMA.E261.pow_gt j hj
    have h3 : (j + 2) * n < 2 ^ (j + 1) * n := Nat.mul_lt_mul_of_pos_right h2 hn
    nlinarith
  have hnot : n + 1 + j ∉ S := fun hm => by have := (hS _ hm).2; omega
  have hcard : 2 ≤ (insert (n + 1 + j) S).card := by
    rw [Finset.card_insert_of_notMem hnot]
    have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    omega
  refine ⟨(insert (n + 1 + j) S).card, hcard,
    fun k => (insert (n + 1 + j) S).orderEmbOfFin rfl k, ?_, ?_, ?_⟩
  · intro a b hab
    exact ((insert (n + 1 + j) S).orderEmbOfFin rfl).injective hab
  · intro k
    have hmem := (insert (n + 1 + j) S).orderEmbOfFin_mem rfl k
    show 1 ≤ (insert (n + 1 + j) S).orderEmbOfFin rfl k
    rcases Finset.mem_insert.mp hmem with h0 | h0
    · omega
    · have := hS _ h0
      omega
  · have hmap := Finset.sum_map Finset.univ
      ((insert (n + 1 + j) S).orderEmbOfFin rfl).toEmbedding (fun x : ℕ => (x : ℚ) / 2 ^ x)
    rw [Finset.map_orderEmbOfFin_univ] at hmap
    rw [hsum]
    have hins := Finset.sum_insert (f := fun x : ℕ => (x : ℚ) / 2 ^ x) hnot
    simp only [RelEmbedding.coe_toEmbedding] at hmap
    rw [← hmap, hins]
    push_cast
    ring
