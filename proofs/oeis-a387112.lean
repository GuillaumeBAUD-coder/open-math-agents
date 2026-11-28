import OMAStatements.S_oeis_a387112

open OMA.S_oeis_a387112 Nat

theorem OMA.solution : type_of% @OMA.S_oeis_a387112.main := by
  refine fun n _ => ⟨fun ⟨f, hf, hb⟩ i => ?_, fun h => ⟨_, succ_injective.comp Fin.val_injective, by simpa⟩⟩
  simpa using Finset.card_le_card_of_injOn f (t := .Icc 1 (primeIndex n i)) (s := .Iic i) (fun k hk => by simp_all; exact (hb k).2.trans (monotone_primeCounting <| n.primeFactorsList_sorted hk)) hf.injOn
