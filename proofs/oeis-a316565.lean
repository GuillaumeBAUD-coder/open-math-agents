import OMAStatements.S_oeis_a316565

-- Problem: A316565, max element order in GL(2, Z/p) is p^2 - 1 (powers lie in span(1, T); GF(p^2) via leftMulMatrix).
-- Credit: @bnb9001

namespace OMA_A316565_Proof

open Matrix OMA.S_oeis_a316565

theorem cayley_hamilton_two {R : Type*} [CommRing R] (T : Matrix (Fin 2) (Fin 2) R) :
    T * T = T.trace • T - T.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

theorem order_le (p : ℕ) [hp : Fact p.Prime] (g : GL (Fin 2) (ZMod p)) :
    orderOf g ≤ p * p - 1 := by
  classical
  set T : Matrix (Fin 2) (Fin 2) (ZMod p) := (g : Matrix (Fin 2) (Fin 2) (ZMod p))
  set S : Finset (Matrix (Fin 2) (Fin 2) (ZMod p)) :=
    (Finset.univ : Finset (ZMod p × ZMod p)).image
      (fun ab => ab.1 • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) + ab.2 • T)
  have hpow : ∀ i : ℕ, T ^ i ∈ S := by
    intro i
    induction i with
    | zero => exact Finset.mem_image.mpr ⟨(1, 0), Finset.mem_univ _, by simp⟩
    | succ i ih =>
      obtain ⟨⟨x, y⟩, -, hxy⟩ := Finset.mem_image.mp ih
      refine Finset.mem_image.mpr ⟨(-(y * T.det), x + y * T.trace), Finset.mem_univ _, ?_⟩
      simp only at hxy ⊢
      rw [pow_succ, ← hxy, add_mul, smul_mul_assoc, smul_mul_assoc, Matrix.one_mul,
        cayley_hamilton_two]
      module
  have hunit : IsUnit T := (g : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ).isUnit
  have hne : ∀ i : ℕ, T ^ i ≠ 0 := fun i => (hunit.pow i).ne_zero
  have h0 : (0 : Matrix (Fin 2) (Fin 2) (ZMod p)) ∈ S :=
    Finset.mem_image.mpr ⟨(0, 0), Finset.mem_univ _, by simp⟩
  have hle : orderOf T ≤ (S.erase 0).card :=
    Finset.le_card_of_inj_on_range (T ^ ·)
      (fun i _ => Finset.mem_erase.mpr ⟨hne i, hpow i⟩) pow_injOn_Iio_orderOf
  have hS : S.card ≤ p * p := by
    calc S.card ≤ (Finset.univ : Finset (ZMod p × ZMod p)).card := Finset.card_image_le
      _ = p * p := by simp [ZMod.card]
  rw [Finset.card_erase_of_mem h0] at hle
  have : orderOf g = orderOf T := (orderOf_units (y := g)).symm
  omega

theorem exists_order (p : ℕ) [hp : Fact p.Prime] :
    ∃ g : GL (Fin 2) (ZMod p), orderOf g = p * p - 1 := by
  classical
  let K := GaloisField p 2
  have hfr : Module.finrank (ZMod p) K = 2 := GaloisField.finrank p (by norm_num)
  let b : Module.Basis (Fin 2) (ZMod p) K := Module.finBasisOfFinrankEq _ _ hfr
  let φ := Algebra.leftMulMatrix b
  have hφ : Function.Injective φ := Algebra.leftMulMatrix_injective b
  let ψ : Kˣ →* GL (Fin 2) (ZMod p) := Units.map φ.toMonoidHom
  have hψ : Function.Injective ψ := by
    intro x y hxy
    apply Units.ext
    apply hφ
    have := congrArg (fun u : GL (Fin 2) (ZMod p) => (u : Matrix (Fin 2) (Fin 2) (ZMod p))) hxy
    simpa [ψ] using this
  haveI : Finite K := inferInstance
  obtain ⟨x, hx⟩ := Monoid.exists_orderOf_eq_exponent (G := Kˣ) (Monoid.ExponentExists.of_finite)
  rw [IsCyclic.exponent_eq_card] at hx
  have hcard : Nat.card Kˣ = p * p - 1 := by
    rw [Nat.card_units, GaloisField.card p 2 (by norm_num), sq]
  refine ⟨ψ x, ?_⟩
  rw [orderOf_injective ψ hψ x, hx, hcard]

end OMA_A316565_Proof

open Matrix OMA.S_oeis_a316565 OMA_A316565_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a316565.main := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hpp : (p - 1) * (p + 1) = p * p - 1 := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
    rw [show (q + 1) * (q + 1) = q * (q + 2) + 1 by ring]
    simp only [Nat.add_sub_cancel]
  rw [hpp]
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hg⟩ := exists_order p
    exact ⟨g, hg⟩
  · rintro k ⟨g, rfl⟩
    exact order_le p g
