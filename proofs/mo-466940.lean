import OMAStatements.S_mo_466940

-- Problem: A concentration inequality derived from Freedman’s inequality
-- Upstream: formal-conjectures statements/mo-466940.lean:0 (declaration OMA.S_mo_466940.main)
-- Credit: @Ezekia1 (the owner of the agent is credited as the solver)
-- Disproof: one-point probability space, 32 increments identically -1, B = 1, delta = 1/2.
-- Every conditional expectation is -1, so the first event reads -32 ≤ -48 + 4 log 4, which is
-- false because log 4 ≤ 3. The event is empty and has probability 0 < 1/2.

open MeasureTheory

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_466940.main) := by
  rintro ⟨h1, -⟩
  have hlog : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  let F : Filtration ℕ (inferInstance : MeasurableSpace Unit) :=
    ⟨fun _ => inferInstance, fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  have h := h1 Unit inferInstance (Measure.dirac ()) inferInstance F
    (fun _ _ => (-1 : ℝ)) 32 1 (1 / 2) (fun _ => measurable_const) one_pos
    (by norm_num) (by norm_num) (fun t _ => Filter.Eventually.of_forall (fun _ => by norm_num))
  have hempty : OMA.S_mo_466940.firstEvent (Measure.dirac ()) F (fun _ _ => (-1 : ℝ)) 32 1 (1 / 2)
      = ∅ := by
    ext ω
    simp only [OMA.S_mo_466940.firstEvent, Set.mem_empty_iff_false, iff_false]
    have hc : ∀ t : ℕ, (Measure.dirac ())[fun _ : Unit => (-1 : ℝ) | F (t - 1)] = fun _ => -1 :=
      fun t => condExp_const (F.le (t - 1)) (-1 : ℝ)
    simp only [hc, Finset.sum_const, Nat.card_Icc]
    have h4 : (2 : ℝ) / (1 / 2) = 4 := by norm_num
    rw [h4]
    norm_num
    linarith
  rw [hempty] at h
  simp at h
  linarith
