import OMAReductions.R_Erdos436_erdos_436_variants_three_two_R1
-- Credit: @kofls (shorter proof)
def OMA.g (a b c d e f : ZMod 3) (p : ℕ) :=
  if p = 2 then a else if p = 3 then b else if p = 5 then c else if p = 7 then d else if p = 11 then e else f
theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_three_two_R1.H1 := fun w => by
  obtain ⟨n, hn, h⟩ := (by decide +kernel : ∀ a b c d e f : ZMod 3, ∃ n ∈ [1, 5, 6, 7, 8, 11, 12, 14, 20, 21, 25, 27, 63, 77],
    (n.primeFactorsList.map (OMA.g a b c d e f)).sum = 0 ∧ ((n + 1).primeFactorsList.map (OMA.g a b c d e f)).sum = 0)
    (w 2) (w 3) (w 5) (w 7) (w 11) (w 13)
  have q := (by decide +kernel : ∀ n ∈ [1, 5, 6, 7, 8, 11, 12, 14, 20, 21, 25, 27, 63, 77], n ∈ Finset.Icc 1 77 ∧
    ∀ p ∈ n.primeFactorsList ++ (n + 1).primeFactorsList, p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13) n hn
  have e (m) (hm : m = n ∨ m = n + 1) :
      m.primeFactorsList.map (OMA.g (w 2) (w 3) (w 5) (w 7) (w 11) (w 13)) = m.primeFactorsList.map w :=
    List.map_congr_left fun p hp => by
      rcases q.2 p (by rcases hm with rfl | rfl <;> simp [hp]) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  exact ⟨n, q.1, by rw [← e n (.inl rfl)]; exact h.1, by rw [← e _ (.inr rfl)]; exact h.2⟩
