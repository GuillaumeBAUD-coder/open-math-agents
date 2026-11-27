import FormalConjectures.ErdosProblems.«964»

-- Credit: @marcusbuffett
/-! Eberhard, *Ratios of consecutive values of the divisor function*,
arXiv:2505.00727. The almost-prime input (Corollary 2.1) is independent of
the elementary construction synchronizing the three possible divisor ratios. -/
namespace OMA.R_Erdos964_erdos_964_variants_eberhard_R1

open Finset
open scoped ArithmeticFunction.sigma

/-- Two of three admissible forms are simultaneously prescribed multiples
of products of two distinct primes above any fixed threshold. -/
def H1 : Prop :=
  ∀ A r : Fin 3 → ℕ, ((∀ i, 0 < A i ∧ 0 < r i ∧ (r i).Coprime (A i)) ∧ StrictMono A ∧
     (∀ i j, i ≠ j → (r i).Coprime (r j) ∧
       (r i).Coprime (if A i > A j then A i - A j else A j - A i))) →
    ∀ T : ℕ, ∃ i j : Fin 3, i < j ∧
      {x : ℕ | ∀ l ∈ ({i,j} : Finset (Fin 3)), ∃ p s : ℕ,
        p.Prime ∧ s.Prime ∧ p ≠ s ∧ T < p ∧ T < s ∧
        A l*x+1 = r l*(p*s)}.Infinite

/-- Eberhard's choice of coefficients. For each possible winning pair the
scaled forms are consecutive and the fixed parts already have ratio q. -/
def H2 : Prop :=
  ∀ q : ℚ, 0 < q → ∃ A r : Fin 3 → ℕ, ∃ U V : Fin 3 → Fin 3 → ℕ,
    ((∀ i, 0 < A i ∧ 0 < r i ∧ (r i).Coprime (A i)) ∧ StrictMono A ∧
     (∀ i j, i ≠ j → (r i).Coprime (r j) ∧
       (r i).Coprime (if A i > A j then A i - A j else A j - A i))) ∧
    ∀ i j, i < j → 0 < U i j ∧ 0 < V i j ∧
      (∀ x : ℕ, U i j * (A i*x+1) = V i j * (A j*x+1)+1) ∧
      (((U i j * r i).divisors.card : ℚ) / (V i j * r j).divisors.card) = q

lemma four_divisors {m p s : ℕ} (hm : 0 < m) (hp : p.Prime) (hs : s.Prime)
    (hps : p ≠ s) (hmp : m < p) (hms : m < s) :
    (m*(p*s)).divisors.card = m.divisors.card * 4 := by
  have comp : m.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmp)).symm
  have coms : m.Coprime s :=
    (hs.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hms)).symm
  rw [(comp.mul_right coms).card_divisors_mul,
      ((Nat.coprime_primes hp hs).mpr hps).card_divisors_mul]
  simp [hp.divisors,hs.divisors,hp.ne_one.symm,hs.ne_one.symm]

theorem main : H1 → H2 → type_of% @Erdos964.erdos_964.variants.eberhard := by
  classical
  intro sieve build q hq
  obtain ⟨A,r,U,V,admissible,scales⟩ := build q hq
  let bound := fun ij : Fin 3 × Fin 3 => max (U ij.1 ij.2 * r ij.1) (V ij.1 ij.2 * r ij.2)
  let T := univ.sup bound
  obtain ⟨i,j,hij,hInf⟩ := sieve A r admissible T
  obtain ⟨hu,hv,adjacent,ratio⟩ := scales i j hij
  have hAi := (admissible.1 i).1
  have hAj := (admissible.1 j).1
  have hui := Nat.mul_pos hu (admissible.1 i).2.1
  have hvj := Nat.mul_pos hv (admissible.1 j).2.1
  have hbound : bound (i,j) ≤ T := le_sup (mem_univ _)
  have hU : U i j * r i ≤ T := (le_max_left _ _).trans hbound
  have hV : V i j * r j ≤ T := (le_max_right _ _).trans hbound
  let f := fun x : ℕ => V i j * (A j*x+1)
  have hf : Function.Injective f := by
    intro x y he
    exact Nat.eq_of_mul_eq_mul_left hAj (Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left hv he))
  apply (hInf.image hf.injOn).mono
  rintro n ⟨x,hx,rfl⟩
  obtain ⟨p,s,hp,hs,hps,htp,hts,hi⟩ := hx i (by simp)
  obtain ⟨P,S,hP,hS,hPS,htP,htS,hj⟩ := hx j (by simp)
  have succ : f x + 1 = (U i j*r i)*(p*s) := by
    dsimp [f]
    rw [← adjacent, hi, mul_assoc]
  have curr : f x = (V i j*r j)*(P*S) := by
    dsimp [f]
    rw [hj,mul_assoc]
  refine ⟨Nat.mul_pos hv (Nat.succ_pos _), ?_⟩
  have hrat : (((U i j * r i).divisors.card : ℝ) / (V i j * r j).divisors.card) = q := by
    rw [← ratio]
    push_cast
    rfl
  rw [Erdos964.tauRatio, ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply,
      succ, curr, four_divisors hui hp hs hps (hU.trans_lt htp) (hU.trans_lt hts),
      four_divisors hvj hP hS hPS (hV.trans_lt htP) (hV.trans_lt htS), ← hrat]
  push_cast
  ring

end OMA.R_Erdos964_erdos_964_variants_eberhard_R1
