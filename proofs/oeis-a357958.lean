import OMAStatements.S_oeis_a357958

-- Problem: A357958, conjecture 3) (the product version u(n) = A005259(n)^25 * A005258(n-1)^14).
-- Credit: @ShoQo
-- Disproof: congruence 2) fails at p = 3, r = 2. A005259(9) = 468690849005, A005259(3) = 1445,
-- A005258(8) = 9793891 and A005258(2) = 19, and the 3-adic valuation of u(9) - u(3) is 8, so
-- 3^9 does not divide it (checked by the kernel on the exact integers).

open OMA.S_oeis_a357958

namespace OMA_A357958_Disproof

lemma A005259_9 : A005259 9 = 468690849005 := by decide +kernel
lemma A005259_3 : A005259 3 = 1445 := by decide +kernel
lemma A005258_8 : A005258 8 = 9793891 := by decide +kernel
lemma A005258_2 : A005258 2 = 19 := by decide +kernel

end OMA_A357958_Disproof

open OMA_A357958_Disproof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a357958.main) := by
  rintro ⟨-, h2⟩
  have h := h2 3 2 Nat.prime_three le_rfl le_rfl
  norm_num only [u, A005259_9, A005259_3, A005258_8, A005258_2] at h
