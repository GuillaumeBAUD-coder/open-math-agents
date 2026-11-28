import OMAReductions.R_Erdos357_erdos_357_variants_monotone_parts_i_R1

/-! The two sets defining h n and f n coincide. A strictly monotone sequence is monotone. If a is
monotone with distinct interval sums and i < j, then a i ≤ a j, and a i ≠ a j because the
one-point intervals {i} and {j} have different sums. So a is strictly monotone. -/

theorem OMA.solution : OMA.R_Erdos357_erdos_357_variants_monotone_parts_i_R1.H2 := by
  intro n
  unfold Erdos357.h Erdos357.f
  congr 1
  ext k
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, hr, hm, hd⟩
    refine ⟨a, hr, ?_, hd⟩
    intro i j hij
    rcases (hm hij.le).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 : ({i} : Finset (Fin k)) ∈ {J : Finset (Fin k) | (J : Set (Fin k)).OrdConnected} := by
        simp [Set.ordConnected_singleton]
      have h2 : ({j} : Finset (Fin k)) ∈ {J : Finset (Fin k) | (J : Set (Fin k)).OrdConnected} := by
        simp [Set.ordConnected_singleton]
      have h3 := hd h1 h2 (by simp [h])
      exact hij.ne (Finset.singleton_inj.1 h3)
  · rintro ⟨a, hr, hs, hd⟩
    exact ⟨a, hr, hs.monotone, hd⟩
