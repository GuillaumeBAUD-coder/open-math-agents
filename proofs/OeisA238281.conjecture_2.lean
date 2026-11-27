import FormalConjectures.OEIS.«238281»
set_option maxRecDepth 4096 in
theorem OMA.disproof : ¬ (type_of% @OeisA238281.conjecture_2) := by
  intro all_lengths
  obtain ⟨k, hk, hlt, hprime, hequal⟩ := all_lengths 14 (by decide) (by decide)
  have ties : ∀ i : Fin 14, 0 < i.val →
      Nat.primeCounting (i.val * 14) - Nat.primeCounting ((i.val - 1) * 14) =
      Nat.primeCounting ((i.val + 1) * 14) - Nat.primeCounting (i.val * 14) →
      i.val = 4 ∨ i.val = 12 := by decide
  rcases ties ⟨k, hlt⟩ hk hequal with h | h <;> subst h <;> exact absurd hprime (by decide)
