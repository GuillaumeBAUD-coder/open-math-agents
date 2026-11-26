import FormalConjectures.ErdosProblems.«723»

/-!
# Erdős Problem 723, variant: every prime power is the order of a projective plane

Problem: Erdős Problem 723: The prime power conjecture. — prime power is projplane order
Upstream: formal-conjectures FormalConjectures/ErdosProblems/723.lean:45
(declaration Erdos723.erdos_723.variants.prime_power_is_projplane_order)

Construction: the classical plane PG(2, q) over the Galois field with q = p ^ k elements.
Mathlib already provides the projective plane structure on the projectivization of K ^ 3
(Configuration.ofField: points and lines are both the projectivization, incidence is
orthogonality for the dot product, joins and meets are cross products). What remains is to
compute its order by counting points:
order ^ 2 + order + 1 = card points = 1 + q + q ^ 2, hence order = q.
-/

/-- The order of the projective plane over a finite field K is the cardinality of K. -/
lemma OMA.order_ofField (K : Type) [Field K] [Finite K] [DecidableEq K]
    [Fintype (Projectivization K (Fin 3 → K))] :
    Configuration.ProjectivePlane.order (Projectivization K (Fin 3 → K))
      (Projectivization K (Fin 3 → K)) = Nat.card K := by
  have h1 := Configuration.ProjectivePlane.card_points (Projectivization K (Fin 3 → K))
    (Projectivization K (Fin 3 → K))
  have h2 := Projectivization.card_of_finrank K (Fin 3 → K) (Module.finrank_fin_fun K)
  rw [Nat.card_eq_fintype_card, h1] at h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h2
  generalize Configuration.ProjectivePlane.order (Projectivization K (Fin 3 → K))
    (Projectivization K (Fin 3 → K)) = o at h2 ⊢
  generalize Nat.card K = q at h2 ⊢
  rcases lt_trichotomy o q with h | h | h
  · nlinarith
  · exact h
  · nlinarith

theorem OMA.solution : type_of% @Erdos723.erdos_723.variants.prime_power_is_projplane_order := by
  intro n hn
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  have : Fact p.Prime := ⟨Nat.prime_iff.mpr hp⟩
  classical
  have : Finite (GaloisField p k) :=
    Nat.finite_of_card_ne_zero (by rw [GaloisField.card p k hk.ne']; exact pow_ne_zero _ hp.ne_zero)
  have : Fintype (Projectivization (GaloisField p k) (Fin 3 → GaloisField p k)) :=
    Fintype.ofFinite _
  refine ⟨Projectivization (GaloisField p k) (Fin 3 → GaloisField p k),
    Projectivization (GaloisField p k) (Fin 3 → GaloisField p k),
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [OMA.order_ofField, GaloisField.card p k hk.ne']
