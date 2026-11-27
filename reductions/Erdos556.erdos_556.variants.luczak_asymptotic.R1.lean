import FormalConjectures.ErdosProblems.«556»

/-! Reduction of Łuczak's three-colour cycle bound to two-colour cycle Ramsey
and a covering obstruction for saturated graphs of small independence number.
Credit: @TheWaler. References: Rosta, Faudree–Schelp, and Łuczak (1999). -/

open Filter SimpleGraph

namespace OMA.R_Erdos556_erdos_556_variants_luczak_asymptotic_R1

-- A weak consequence of the exact two-colour cycle Ramsey numbers.
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ H : SimpleGraph (Fin (2*n)),
    cycleGraph n ⊑ H ∨ cycleGraph n ⊑ Hᶜ

-- Three maximal cycle-free graphs with independence number below 2n
-- cannot cover this complete graph. Overlaps are allowed.
def H2 : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∀ D : Fin 3 → SimpleGraph (Fin ⌊(4 + ε) * (n : ℝ)⌋₊),
      (∀ i, Maximal (fun G => ¬ cycleGraph n ⊑ G) (D i)) →
      (∀ i, ¬ (⊤ : SimpleGraph (Fin (2*n))) ⊑ (D i)ᶜ) →
      ∃ x y, x ≠ y ∧ ∀ i, ¬ (D i).Adj x y

lemma restrict_to_two {n N : ℕ}
    (two : ∀ H : SimpleGraph (Fin (2*n)), cycleGraph n ⊑ H ∨ cycleGraph n ⊑ Hᶜ)
    (c : Fin 3 → SimpleGraph (Fin N))
    (covers : ∀ x y, x ≠ y → ∃ i, (c i).Adj x y)
    (i : Fin 3) (indep : (⊤ : SimpleGraph (Fin (2*n))) ⊑ (c i)ᶜ) :
    ∃ j, cycleGraph n ⊑ c j := by
  classical
  obtain ⟨f⟩ := indep
  let σ := Equiv.swap i (2 : Fin 3)
  have last : σ 2 = i := Equiv.swap_apply_right _ _
  let H := (c (σ 0)).comap f
  rcases two H with red | blue
  · exact ⟨σ 0, red.trans ⟨⟨⟨f, fun a => a⟩, f.injective⟩⟩⟩
  · refine ⟨σ 1, blue.trans ⟨⟨⟨f, ?_⟩, f.injective⟩⟩⟩
    intro a b h
    have hne : a ≠ b := h.ne
    have hthird := (f.toHom.map_rel' (show (⊤ : SimpleGraph (Fin (2*n))).Adj a b from hne)).2
    obtain ⟨j, hj⟩ := covers (f a) (f b) (f.injective.ne hne)
    obtain ⟨k, rfl⟩ := σ.surjective j
    fin_cases k
    · exact False.elim (h.2 hj)
    · exact hj
    · change (c (σ 2)).Adj (f a) (f b) at hj
      rw [last] at hj
      exact False.elim (hthird hj)

theorem main : H1 → H2 → type_of% @Erdos556.erdos_556.variants.luczak_asymptotic := by
  classical
  intro two residual ε hε
  filter_upwards [two, residual ε hε] with n hn hres
  let N := ⌊(4 + ε) * (n : ℝ)⌋₊
  have bound : multicolourRamsey (cycleGraph n) 3 ≤ N := by
    apply Nat.sInf_le
    intro c hc
    have covers (x y : Fin N) (hxy : x ≠ y) : ∃ i, (c i).Adj x y := by
      have h : (⊤ : SimpleGraph (Fin N)).Adj x y := hxy
      rw [hc.1, iSup_adj] at h
      exact h
    by_contra none
    have avoid (i : Fin 3) : ¬ cycleGraph n ⊑ c i := fun hi => none ⟨i, hi⟩
    have extend (i : Fin 3) : ∃ D : SimpleGraph (Fin N), c i ≤ D ∧
        Maximal (fun G => ¬ cycleGraph n ⊑ G) D :=
      Finite.exists_le_maximal (p := fun G : SimpleGraph (Fin N) => ¬ cycleGraph n ⊑ G) (avoid i)
    choose D leD maximal using extend
    have small (i : Fin 3) : ¬ (⊤ : SimpleGraph (Fin (2*n))) ⊑ (D i)ᶜ := by
      intro hind
      have emb := hind.mono_right (compl_le_compl (leD i))
      obtain ⟨j, hj⟩ := restrict_to_two hn c covers i emb
      exact avoid j hj
    obtain ⟨x, y, hxy, missing⟩ := hres D maximal small
    obtain ⟨j, hj⟩ := covers x y hxy
    exact missing j (leD j hj)
  exact (Nat.cast_le.mpr bound).trans (Nat.floor_le (by positivity))

end OMA.R_Erdos556_erdos_556_variants_luczak_asymptotic_R1
