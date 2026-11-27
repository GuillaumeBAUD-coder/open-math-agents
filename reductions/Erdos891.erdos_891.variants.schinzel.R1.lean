import FormalConjectures.ErdosProblems.«891»
import Mathlib

/-! Schinzel's argument, via the finiteness of solutions to a diagonal cubic
Thue equation. Splitting prime exponents modulo three gives the finite
set of coefficients required for the smooth-gap argument.
The identification of omega with the size of primeFactors follows @rorcores. -/

namespace OMA.R_Erdos891_erdos_891_variants_schinzel_R1
open Finset Filter
open scoped ArithmeticFunction.omega

private lemma multiple (n d : ℕ) (hd : 0 < d) : ∃ x ∈ Ico n (n+d), d ∣ x := by
  by_cases hz : n % d = 0
  · exact ⟨n, mem_Ico.mpr ⟨le_rfl, by omega⟩, Nat.dvd_of_mod_eq_zero hz⟩
  · refine ⟨d*(n/d+1), mem_Ico.mpr ?_, dvd_mul_right _ _⟩
    have := Nat.mod_add_div n d
    have := Nat.mod_lt n hd
    rw [Nat.mul_add, Nat.mul_one]
    omega

def H1 : Prop :=
  ∀ a b d : ℕ, 0 < d → ∀ᶠ m : ℕ in atTop,
    ∀ x y : ℕ, m = a*x^3 → m+d ≠ b*y^3

def H2 : Prop :=
  ∀ S : Finset ℕ, ∃ A : Finset ℕ, ∀ m : ℕ, 0 < m → m.primeFactors ⊆ S →
    ∃ a ∈ A, ∃ x : ℕ, m = a*x^3

theorem main : H1 → H2 → type_of% @Erdos891.erdos_891.variants.schinzel := by
  classical
  intro thue cores k hk
  have isolated (S : Finset ℕ) (L : ℕ) :
      ∀ᶠ n : ℕ in atTop, ∀ x ∈ Ico n (n+L), ∀ y ∈ Ico n (n+L),
        x.primeFactors ⊆ S → y.primeFactors ⊆ S → x = y := by
    obtain ⟨A,hA⟩ := cores S
    have h : ∀ᶠ m : ℕ in atTop, ∀ a ∈ A, ∀ b ∈ A, ∀ d ∈ Icc 1 L,
        ∀ u v : ℕ, m = a*u^3 → m+d ≠ b*v^3 := by
      exact (eventually_all_finset A).2 fun a _ => (eventually_all_finset A).2 fun b _ =>
        (eventually_all_finset _).2 fun d hd => thue a b d (mem_Icc.mp hd).1
    obtain ⟨N,hN⟩ := eventually_atTop.mp h
    filter_upwards [eventually_ge_atTop (N+1)] with n hn
    have excl (x y : ℕ) (hxn : n ≤ x) (hyL : y < n+L) (hxy : x < y)
        (hx : x.primeFactors ⊆ S) (hy : y.primeFactors ⊆ S) : False := by
      obtain ⟨a,ha,u,hu⟩ := hA x (by omega) hx
      obtain ⟨b,hb,v,hv⟩ := hA y (by omega) hy
      apply hN x (by omega) a ha b hb (y-x) (mem_Icc.mpr ⟨by omega,by omega⟩) u v hu
      rwa [Nat.add_sub_of_le hxy.le]
    intro x hx y hy hs ht
    obtain ⟨hx₁,hx₂⟩ := mem_Ico.mp hx
    obtain ⟨hy₁,hy₂⟩ := mem_Ico.mp hy
    rcases lt_trichotomy x y with h | h | h
    · exact (excl x y hx₁ hy₂ h hs ht).elim
    · exact h
    · exact (excl y x hy₁ hx₂ h ht hs).elim
  let p := Nat.nth Nat.Prime
  let P := ∏ i ∈ range (k-1), p i
  let S := (range (k-1)).image p
  let u := p (k-1)
  let v := p k
  have hp (i : ℕ) : (p i).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i
  have inc : StrictMono p := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have huv : u < v := inc (show k-1 < k by omega)
  have hS (i : ℕ) (hi : k-1 ≤ i) : p i ∉ S := by
    rintro he
    obtain ⟨j,hj,h⟩ := mem_image.mp he
    have := inc.injective h
    simp only [mem_range] at hj
    omega
  have cardS : S.card = k-1 := by
    rw [show S = (range (k-1)).image p by rfl, card_image_of_injective _ inc.injective, card_range]
  have hP : 0 < P := prod_pos (fun i _ => (hp i).pos)
  have fits (r : ℕ) (hr : r.Prime) (hnew : r ∉ S) (x : ℕ) (hx : 0 < x)
      (hd : P*r ∣ x) (hw : ω x ≤ k) : x.primeFactors = insert r S := by
    have sub : insert r S ⊆ x.primeFactors := by
      intro q hq
      apply Nat.mem_primeFactors.mpr
      rcases mem_insert.mp hq with rfl | hq
      · exact ⟨hr, dvd_trans (dvd_mul_left _ _) hd, hx.ne'⟩
      · obtain ⟨i,hi,rfl⟩ := mem_image.mp hq
        exact ⟨hp i, dvd_trans (dvd_prod_of_mem p hi) (dvd_trans (dvd_mul_right _ _) hd), hx.ne'⟩
    have hω : ω x = x.primeFactors.card := by
      rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]
    exact (eq_of_subset_of_card_le sub (by rw [card_insert_of_notMem hnew, cardS]; omega)).symm
  let T := insert u (insert v S)
  change ∀ᶠ n : ℕ in atTop, ∃ m ∈ Ico n (n+P*v), k < ω m
  filter_upwards [isolated T (P*v), eventually_ge_atTop (1 : ℕ)] with n hIso hn
  obtain ⟨x,hx,dx⟩ := multiple n (P*u) (Nat.mul_pos hP (hp _).pos)
  obtain ⟨y,hy,dy⟩ := multiple n (P*v) (Nat.mul_pos hP (hp _).pos)
  have hx' : x ∈ Ico n (n+P*v) := mem_Ico.mpr
    ⟨(mem_Ico.mp hx).1, (mem_Ico.mp hx).2.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_left P huv.le) n)⟩
  by_contra! h
  have ex := fits u (hp _) (hS _ le_rfl) x (lt_of_lt_of_le hn (mem_Ico.mp hx).1) dx (h x hx')
  have ey := fits v (hp _) (hS _ (by omega)) y (lt_of_lt_of_le hn (mem_Ico.mp hy).1) dy (h y hy)
  have same : x = y := hIso x hx' y hy (by rw [ex]; exact insert_subset_insert _ (subset_insert _ _))
    (by rw [ey]; exact subset_insert _ _)
  have hu : u ∈ y.primeFactors := by rw [← same, ex]; exact mem_insert_self _ _
  rw [ey, mem_insert] at hu
  exact hu.elim (ne_of_lt huv) (hS _ le_rfl)

end OMA.R_Erdos891_erdos_891_variants_schinzel_R1
