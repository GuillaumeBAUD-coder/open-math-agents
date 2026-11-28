import FormalConjectures.WrittenOnTheWallII.GraphConjecture33

open SimpleGraph

private def par : Fin 20 → Fin 20 := ![0,0,0,0,0,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11]

private def G : SimpleGraph (Fin 20) where
  Adj x y := (x < y ∧ par y = x) ∨ (y < x ∧ par x = y)
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun _ => by simp⟩

private instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

private def lvl : Fin 20 → ℕ := ![0,1,1,1,1,2,3,3,4,4,4,4,5,5,5,5,5,5,5,5]

private def rem (a b : Fin 20) : ℕ :=
  if a < b then ![0,0,0,0,4,3,2,2,1,1,1,1,0,0,0,0,0,0,0,0] b
  else ![0,5,5,5,1,2,3,3,4,4,4,4,5,5,5,5,5,5,5,5] a

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture33.conjecture33 := by
  intro allGraphs
  have hconn : G.Connected := by
    rw [connected_iff_exists_forall_reachable]; refine ⟨0, fun v => ?_⟩
    induction v using WellFounded.induction (measure (fun v : Fin 20 => v.val)).wf with
    | h v ih =>
      by_cases hz : v = 0
      · subst v; exact .refl _
      · have l := (by decide : ∀ v : Fin 20, v ≠ 0 → par v < v) v hz
        exact (ih (par v) l).trans (show G.Adj (par v) v from .inl ⟨l, rfl⟩).reachable
  have hwb : ∀ {v w} (p : G.Walk v w), lvl w ≤ lvl v + p.length := by
    intro v w p; induction p with
    | nil => simp
    | @cons a b c h p ih =>
      have := (by decide : ∀ a b, G.Adj a b → lvl b ≤ lvl a + 1) a b h; simp; omega
  have hup : path G ≤ 7 := by
    apply path_le_of_not_exists_inducedPath_succ
    rintro ⟨f, hf, hadj⟩
    let r (i : Fin 7) := rem (f i.castSucc) (f i.succ)
    have st (i : Fin 6) : r i.succ < r i.castSucc :=
      (by decide : ∀ a b c, G.Adj a b → G.Adj b c → a ≠ c → rem b c < rem a b) _ _ _
        ((hadj _ _).2 (.inl rfl)) ((hadj _ _).2 (.inl rfl))
        fun h => (by decide : ∀ k : Fin 6, k.castSucc.castSucc ≠ k.succ.succ) i (hf h)
    have : r 0 ≤ 5 := (by decide : ∀ a b, rem a b ≤ 5) _ _
    have : r 1 < r 0 := st 0; have : r 2 < r 1 := st 1; have : r 3 < r 2 := st 2
    have : r 4 < r 3 := st 3; have : r 5 < r 4 := st 4; have : r 6 < r 5 := st 5; omega
  have hlo : (68 : ℝ) ≤ ∑ v : Fin 20, (G.dist 0 v : ℝ) := by
    exact_mod_cast (show 68 ≤ ∑ v : Fin 20, G.dist 0 v from
      (show 68 = ∑ v : Fin 20, lvl v by decide).le.trans <|
        Finset.sum_le_sum fun v _ => by
          obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist 0 v
          simpa [hq, show lvl 0 = 0 by decide] using hwb q)
  have h := allGraphs (Fin 20) G hconn
  dsimp only at h
  generalize hq : @Finset.filter (Fin 20 × Fin 20) (fun p => G.dist p.1 p.2 ≠ 0) _ _ = q at h
  have he : q = ({0} : Finset (Fin 20)) ×ˢ Finset.univ.erase (0 : Fin 20) := by
    rw [← hq]; ext ⟨a, b⟩
    have hm : G.degree a = G.maxDegree ↔ a = 0 :=
      (by decide : ∀ v, G.degree v = G.maxDegree ↔ v = 0) a
    simp [hconn.dist_eq_zero_iff, hm]; grind
  rw [he] at h
  have hcard : (({0} : Finset (Fin 20)) ×ˢ Finset.univ.erase (0 : Fin 20)).card = 19 := by decide
  simp only [Finset.sum_product, Finset.sum_singleton, hcard] at h
  have hh := Int.ceil_le.mp (h.trans (show (path G : ℤ) ≤ 7 by exact_mod_cast hup))
  norm_num at hh; linarith
