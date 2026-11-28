import OMAReductions.R_Erdos713_erdos_713_parts_i_R1_H1_R1_H2_R1_H1_R1

/-!
Füredi's lower bound for complete bipartite graphs with one side of size two,
split into its arithmetic and its algebraic part.

Let t be at least two and m = t-1. For a prime q congruent to 1 modulo m,
Füredi (New asymptotics for bipartite Turán numbers, JCTA 75 (1996)) takes the
subgroup of order m of the multiplicative group of the field with q elements,
lets it act on the nonzero pairs (x,y) by scaling, and joins two orbits when
the bilinear form a*x+b*y of their representatives lies in the subgroup. This
graph has (q^2-1)/m vertices, all degrees at least q-1, and two vertices never
have t common neighbours. This is H2.

H1 says that primes congruent to 1 modulo m can be chosen immediately below
each large integer with relative error tending to zero, a consequence of the
prime number theorem for arithmetic progressions.

Given both, for large n take the prime q below the integer square root of m*n.
The graph of H2 has at most n vertices, so after padding with isolated vertices
ex(n) is at least (q^2-1)(q-1)/(2m), and q is asymptotic to sqrt(m*n). This
gives ex(n) ≥ (1-o(1)) (sqrt(m)/2) n^(3/2).
-/

open SimpleGraph Filter Asymptotics Finset
open scoped Topology Classical

namespace E713Furedi

theorem active (m : ℕ) (v) : ¬(completeBipartiteGraph (Fin 2) (Fin (m+1))).IsIsolated v := by
  apply exists_adj_iff_not_isIsolated.mp
  cases v with
  | inl i => exact ⟨Sum.inr 0,Or.inl ⟨rfl,rfl⟩⟩
  | inr j => exact ⟨Sum.inl 0,Or.inr ⟨rfl,rfl⟩⟩

/-- The counting part: a host with m*w+1 = q^2 vertices-times-m and minimum degree q-1. -/
theorem count (m w q e : ℕ) (q1 : 1 ≤ q) (size : m*w = q^2-1) (deg : w*(q-1) ≤ 2*e) :
    q^3 ≤ 2*m*e+2*q^2 := by
  obtain ⟨d,rfl⟩ : ∃ d, q = d+1 := ⟨q-1,by omega⟩
  have sq : m*w+1 = (d+1)^2 := by
    have : 1 ≤ (d+1)^2 := Nat.one_le_pow _ _ (by omega)
    omega
  simp only [Nat.add_sub_cancel] at deg
  have h := Nat.mul_le_mul_left m deg
  nlinarith

/-- The analytic part: interpolation between the orders where the construction exists. -/
theorem interpolate (m : ℕ) (m1 : 1 ≤ m) (f p : ℕ → ℕ)
    (dense : Tendsto (fun k : ℕ => (p k : ℝ)/k) atTop (𝓝 1))
    (bound : ∀ᶠ n : ℕ in atTop, (p (Nat.sqrt (m*n)))^3 ≤ 2*m*f n+2*(p (Nat.sqrt (m*n)))^2)
    (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (1-ε)*(Real.sqrt (m:ℝ)/2)*(n:ℝ)^(3/2:ℝ) ≤ (f n : ℝ) := by
  let r (n : ℕ) : ℝ := Real.sqrt ((m*n : ℕ) : ℝ)
  let q (n : ℕ) : ℕ := p (Nat.sqrt (m*n))
  have topmul : Tendsto (fun n : ℕ => m*n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n m1) tendsto_id
  have top : Tendsto (fun n : ℕ => Nat.sqrt (m*n)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b*b)] with n hn
    exact Nat.le_sqrt.mpr (hn.trans (Nat.le_mul_of_pos_left n m1))
  have near : Tendsto (fun n => (q n:ℝ)/r n) atTop (𝓝 1) := by
    have prod := (dense.comp top).mul (E713Interpolation.sqrt_floor_ratio.comp topmul)
    rw [one_mul] at prod
    apply prod.congr'
    filter_upwards [top.eventually (eventually_ge_atTop (1:ℕ))] with n hn
    change ((q n:ℝ)/(Nat.sqrt (m*n):ℝ))*((Nat.sqrt (m*n):ℝ)/r n) = _
    have h : (Nat.sqrt (m*n):ℝ) ≠ 0 := by exact_mod_cast (show Nat.sqrt (m*n) ≠ 0 by omega)
    field_simp
  have inv : Tendsto (fun n => (r n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp topmul))
  have low : Tendsto (fun n => ((q n:ℝ)/r n)^3-2*((q n:ℝ)/r n)^2*(r n)⁻¹) atTop (𝓝 1) := by
    simpa using (near.pow 3).sub (((tendsto_const_nhds (x:=(2:ℝ))).mul (near.pow 2)).mul inv)
  filter_upwards [low.eventually (eventually_ge_nhds (show 1-ε < 1 by linarith)),bound,
    eventually_ge_atTop 1] with n hlow hb hn
  have npos : (0:ℝ) < n := by exact_mod_cast hn
  have mpos : (0:ℝ) < m := by exact_mod_cast m1
  have rpos : 0 < r n := Real.sqrt_pos.mpr (by push_cast; positivity)
  have real : (q n:ℝ)^3 ≤ 2*m*f n+2*(q n:ℝ)^2 := by exact_mod_cast hb
  have e1 : (((q n:ℝ)/r n)^3-2*((q n:ℝ)/r n)^2*(r n)⁻¹)*(r n)^3 = (q n:ℝ)^3-2*(q n:ℝ)^2 := by
    field_simp
  have scaled := mul_le_mul_of_nonneg_right hlow (show 0 ≤ (r n)^3 by positivity)
  rw [e1] at scaled
  have rsq : (r n)^2 = m*n := by
    change Real.sqrt ((m*n : ℕ) : ℝ)^2 = _
    rw [Real.sq_sqrt (by positivity)]
    push_cast
    rfl
  have rmul : r n = Real.sqrt m*Real.sqrt n := by
    change Real.sqrt ((m*n : ℕ) : ℝ) = _
    rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg m)]
  have power : (n:ℝ)^(3/2:ℝ) = n*Real.sqrt n := by
    rw [show (3/2:ℝ) = 1+(1/2:ℝ) by norm_num,Real.rpow_add npos,Real.rpow_one,← Real.sqrt_eq_rpow]
  have cube : (r n)^3 = m*n*(Real.sqrt m*Real.sqrt n) := by
    rw [show (r n)^3 = (r n)^2*r n by ring,rsq,← rmul]
  have key : 2*(m:ℝ)*((1-ε)*(Real.sqrt (m:ℝ)/2)*(n:ℝ)^(3/2:ℝ)) ≤ 2*(m:ℝ)*(f n:ℝ) := by
    calc _ = (1-ε)*(r n)^3 := by rw [cube,power]; ring
         _ ≤ _ := by linarith
  exact le_of_mul_le_mul_left key (by positivity)

end E713Furedi

namespace OMA.R_Erdos713_erdos_713_parts_i_R1_H1_R1_H2_R1_H1_R1_H2_R1

/-- Primes congruent to one modulo m can be chosen immediately below each large integer with
relative error tending to zero. -/
def H1 : Prop := ∀ m : ℕ, 1 ≤ m → ∃ p : ℕ → ℕ, (∀ᶠ k in atTop, (p k).Prime ∧ p k ≤ k ∧ m ∣ p k-1) ∧
    Tendsto (fun k : ℕ => (p k : ℝ)/k) atTop (𝓝 1)

/-- Füredi's graphs: for a prime q congruent to one modulo t-1 there is a graph on (q^2-1)/(t-1)
vertices with minimum degree at least q-1 in which no two vertices have t common neighbours. -/
def H2 : Prop := ∀ t q : ℕ, 2 ≤ t → q.Prime → t-1 ∣ q-1 →
    ∃ (W : Type) (_ : Fintype W) (X : SimpleGraph W), (t-1)*Fintype.card W = q^2-1 ∧
      (completeBipartiteGraph (Fin 2) (Fin t)).Free X ∧ Fintype.card W*(q-1) ≤ 2*X.edgeFinset.card

theorem main : H1 → H2 → OMA.R_Erdos713_erdos_713_parts_i_R1_H1_R1_H2_R1_H1_R1.H2 := by
  intro primes build t ht ε he
  obtain ⟨m,rfl⟩ : ∃ m, t = m+1 := ⟨t-1,by omega⟩
  have m1 : 1 ≤ m := by omega
  obtain ⟨p,prim,dense⟩ := primes m m1
  have top : Tendsto (fun n : ℕ => Nat.sqrt (m*n)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b*b)] with n hn
    exact Nat.le_sqrt.mpr (hn.trans (Nat.le_mul_of_pos_left n m1))
  have bound : ∀ᶠ n : ℕ in atTop, (p (Nat.sqrt (m*n)))^3 ≤
      2*m*extremalNumber n (completeBipartiteGraph (Fin 2) (Fin (m+1)))+2*(p (Nat.sqrt (m*n)))^2 := by
    filter_upwards [top.eventually prim] with n ⟨hp,hle,hdiv⟩
    obtain ⟨W,_,X,card,free,edges⟩ := build (m+1) _ ht hp (by simpa using hdiv)
    simp only [Nat.add_sub_cancel] at card
    have small : (p (Nat.sqrt (m*n)))^2 ≤ m*n :=
      (Nat.pow_le_pow_left hle 2).trans (by simpa [pow_two] using Nat.sqrt_le (m*n))
    have fit : Fintype.card W ≤ n := Nat.le_of_mul_le_mul_left (by omega) m1
    have pad := E713Amplify.padding _ (E713Furedi.active m) X free n fit
    have h := E713Furedi.count m _ _ _ hp.one_le card edges
    exact h.trans (by gcongr)
  have h := E713Furedi.interpolate m m1 _ p dense bound ε he
  simpa using h

end OMA.R_Erdos713_erdos_713_parts_i_R1_H1_R1_H2_R1_H1_R1_H2_R1
