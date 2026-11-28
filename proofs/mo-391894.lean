import OMAStatements.S_mo_391894

-- Problem: Positive integers m with 2m^2 - 1 = x^4 + y^4, |x - y| > 1
-- Upstream: statements/mo-391894.lean (declaration OMA.S_mo_391894.main)
-- Credit: @EmircanEsen

namespace OMA.Proof_mo_391894

private def pellPair : ℕ → ℕ × ℕ
  | 0 => (3, 10)
  | n + 1 =>
    let p := pellPair n
    (8 * p.1 + 3 * p.2 + 5, 21 * p.1 + 8 * p.2 + 15)

private lemma pellPair_eq (n : ℕ) :
    (pellPair n).2 ^ 2 = 7 * (pellPair n).1 ^ 2 + 10 * (pellPair n).1 + 7 := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [pellPair]
    have h1 : (21 * (pellPair n).1 + 8 * (pellPair n).2 + 15) ^ 2 =
        64 * (pellPair n).2 ^ 2 + 441 * (pellPair n).1 ^ 2 +
          336 * (pellPair n).1 * (pellPair n).2 + 630 * (pellPair n).1 +
          240 * (pellPair n).2 + 225 := by ring
    have h2 : 7 * (8 * (pellPair n).1 + 3 * (pellPair n).2 + 5) ^ 2 +
        10 * (8 * (pellPair n).1 + 3 * (pellPair n).2 + 5) + 7 =
        63 * (pellPair n).2 ^ 2 + 448 * (pellPair n).1 ^ 2 +
          336 * (pellPair n).1 * (pellPair n).2 + 640 * (pellPair n).1 +
          240 * (pellPair n).2 + 232 := by ring
    rw [h1, h2, ih]
    ring

private lemma pellPair_fst_strictMono : StrictMono (fun n => (pellPair n).1) := by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  simp only [pellPair]
  omega

private def seqM (n : ℕ) : ℕ :=
  let x := (pellPair n).1
  5 * x ^ 2 + 7 * x + 5

private lemma seqM_strictMono : StrictMono seqM := by
  intro a b hab
  have hx : (pellPair a).1 < (pellPair b).1 := pellPair_fst_strictMono hab
  dsimp only [seqM]
  nlinarith

private lemma seqM_mem (n : ℕ) :
    seqM n ∈ {m : ℕ | 0 < m ∧
      ∃ x y : ℕ, 2 * m ^ 2 = x ^ 4 + y ^ 4 + 1 ∧ (x + 1 < y ∨ y + 1 < x)} := by
  refine ⟨by dsimp only [seqM]; omega, (pellPair n).1, (pellPair n).2, ?_, Or.inl ?_⟩
  · have h := pellPair_eq n
    dsimp only [seqM]
    have h4 : (pellPair n).2 ^ 4 = ((pellPair n).2 ^ 2) ^ 2 := by ring
    rw [h4, h]
    ring
  · have h := pellPair_eq n
    nlinarith

end OMA.Proof_mo_391894

theorem OMA.solution : type_of% @OMA.S_mo_391894.main := by
  exact Set.infinite_of_injective_forall_mem
    OMA.Proof_mo_391894.seqM_strictMono.injective
    OMA.Proof_mo_391894.seqM_mem
