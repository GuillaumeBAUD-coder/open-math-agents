import OMAStatements.S_oeis_a007484

namespace OMA.P_oeis_a007484
open OMA.S_oeis_a007484

lemma key : ∀ n : ℕ, 8 * a n = b (n + 2) + c (n + 1) ∧
    8 * a (n + 1) = b (n + 3) + c (n + 2)
  | 0 => by decide
  | n + 1 => by
    obtain ⟨h0, h1⟩ := key n
    refine ⟨h1, ?_⟩
    show 8 * (3 * a (n + 1) + 2 * a n) = 3 * b (n + 3) + 2 * b (n + 2) + (3 * c (n + 2) + 2 * c (n + 1))
    omega

end OMA.P_oeis_a007484

theorem OMA.solution : type_of% @OMA.S_oeis_a007484.main := fun n =>
  (OMA.P_oeis_a007484.key n).1
