import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1

/-!
Finite intersections of two-sided finite-automaton nonhalting certificates.
Proof: Hanan Beer (@hananzlt).
The exact certificate interface and reduction are by Marcus Buffett (@marcusbuffett),
open-math-agents PR 5268. All upstream authors retain their attribution.
-/

open Turing Turing.BusyBeaver

namespace OMA.CertificateIntersection

abbrev Target := OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1.H2

theorem closure : Target := by
  classical
  intro I _ F M hcert hM
  choose n m x y L R S hL hR hstart hclose using hcert
  let X := ∀ i, Fin (n i)
  let Y := ∀ i, Fin (m i)
  let eX := Fintype.equivFin X
  let eY := Fintype.equivFin Y
  let LP (a : Fin 2) (u : Fin (Fintype.card X)) : Fin (Fintype.card X) :=
    eX (fun i => L i a (eX.symm u i))
  let RP (a : Fin 2) (v : Fin (Fintype.card Y)) : Fin (Fintype.card Y) :=
    eY (fun i => R i a (eY.symm v i))
  let SP (q : Fin 4) (a : Fin 2) (u : Fin (Fintype.card X))
      (v : Fin (Fintype.card Y)) : Bool :=
    decide (∀ i, S i q a (eX.symm u i) (eY.symm v i) = true)
  refine ⟨Fintype.card X, Fintype.card Y, eX x, eY y, LP, RP, SP, ?_, ?_, ?_, ?_⟩
  · simp only [LP, Equiv.symm_apply_apply]
    exact congrArg eX (funext hL)
  · simp only [RP, Equiv.symm_apply_apply]
    exact congrArg eY (funext hR)
  · simpa only [SP, Equiv.symm_apply_apply, decide_eq_true_eq] using hstart
  · intro q a s t u v h
    have hs : ∀ i, S i q a (L i s (eX.symm u i)) (R i t (eY.symm v i)) = true := by
      simpa only [SP, LP, RP, Equiv.symm_apply_apply, decide_eq_true_eq] using h
    have moves (i : I) := hclose i q a s t (eX.symm u i) (eY.symm v i) (hs i)
    obtain ⟨r, st, hm, hf⟩ := hM q a (fun i => by
      obtain ⟨r, w, d, he, _⟩ := moves i
      exact ⟨r, Stmt.write w d, he⟩)
    obtain ⟨w, d⟩ := st
    refine ⟨r, w, d, hm, ?_⟩
    have next (i : I) :
        (match d with
        | .left => S i r s (eX.symm u i) (R i w (R i t (eY.symm v i)))
        | .right => S i r t (L i w (L i s (eX.symm u i))) (eY.symm v i)) = true := by
      obtain ⟨r', w', d', he, hn⟩ := moves i
      have heq : r' = r ∧ w' = w ∧ d' = d := by
        simpa only [Option.some.injEq, Prod.mk.injEq, Stmt.write.injEq] using he.symm.trans (hf i)
      obtain ⟨rfl, rfl, rfl⟩ := heq
      cases d' <;> exact hn
    cases d <;>
      simpa only [SP, LP, RP, Equiv.symm_apply_apply, decide_eq_true_eq] using next

end OMA.CertificateIntersection

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1.H2 :=
  OMA.CertificateIntersection.closure
