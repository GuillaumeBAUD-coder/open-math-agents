import OMAStatements.S_oeis_a006990
import Mathlib

open OMA.S_oeis_a006990

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a006990.main) := by
  intro conjecture
  have ha : a 2 = 2 := by
    unfold a
    apply IsGreatest.csSup_eq
    exact ⟨⟨by decide, by decide⟩, fun _ hp => hp.2⟩
  have h := conjecture 2 (by decide)
  norm_num [ha] at h