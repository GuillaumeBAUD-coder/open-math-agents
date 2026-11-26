import FormalConjectures.Wikipedia.WallSunSun
import Mathlib.Tactic

-- Problem: Infinitude of Wall–Sun–Sun primes — exists quadraticAlgebra of isQuadraticExtension
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/WallSunSun.lean (declaration Algebra.exists_quadraticAlgebra_of_isQuadraticExtension)
-- Credit: @florynepierson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @Algebra.exists_quadraticAlgebra_of_isQuadraticExtension := by
  intro K L _ _ _ _
  exact Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra
