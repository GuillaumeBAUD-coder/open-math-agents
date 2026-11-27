import OMAReductions.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1
import Mathlib

/-! The prescribed prime powers are removed on a single arithmetic progression.
At a prime dividing the progression modulus the constant terms are units.
At every other prime the progression can be sent to zero, so the seven new
forms have no fixed prime divisor. Their determinants are nonzero by the
distinctness of the original slopes. The remaining sieve input is the
fixed-coefficient seven-dimensional statement of Hildebrand, Lemma 2. -/
-- Credit: @marcusbuffett
namespace OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1
open Filter Finset Real

/-- The fixed-coefficient almost-prime sieve for admissible, pairwise
nonproportional linear forms. There are no prescribed valuations. -/
def H1 : Prop := ∀ A D : Fin 7 → ℕ, (∀ i, 0 < A i) → (∀ i, 0 < D i) →
  (∀ i j, i ≠ j → A i * D j ≠ A j * D i) →
  (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬ p ∣ A i*t+D i) →
  ∀ B : ℕ, ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop, ∃ U : Finset ℕ,
    x/(log x)^7 ≤ C*U.card ∧ ∀ t∈U, 0<t ∧ (t:ℝ)≤x ∧
      (∀ i, 1<A i*t+D i ∧ Squarefree (A i*t+D i) ∧ ∀ p∈(A i*t+D i).primeFactors,B<p) ∧
      (∑ i,(A i*t+D i).primeFactors.card)≤27

/-- Simultaneous congruences at the seven prescribed primes, including the
cross-conditions that a prime prescribed to one form misses the other six. -/
def H2 : Prop := ∀ a q e : Fin 7 → ℕ, StrictMono a → (∀ i, 0<a i) →
  Function.Injective q → (∀ i,(q i).Prime) → (∀ i j,a i<q j) →
  ∃ r : ℕ, ∀ i, q i ^ e i ∣ a i*r+1 ∧ ∀ j, ¬ q j ∣ (a i*r+1)/(q i^e i)

lemma shift_target (m r p : ℕ) (hp : p.Prime) (h : ¬ p∣m) :
    ∃ t : ℕ,p∣m*t+r := by
  letI : Fact p.Prime := ⟨hp⟩
  have nz : (m : ZMod p) ≠ 0 := fun h₀ => h ((ZMod.natCast_eq_zero_iff ..).mp h₀)
  let t : ZMod p := -(r : ZMod p)/m
  refine ⟨t.val,(ZMod.natCast_eq_zero_iff ..).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  dsimp [t]
  field_simp <;> ring

theorem main : H1 → H2 → OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1.H1 := by
  classical
  intro sieve crt a q e mono pos inj prime sep B
  obtain ⟨r,hr⟩ := crt a q e mono pos inj prime sep
  let d i := q i^e i
  let m := ∏ i,q i^(e i+1)
  let A i := (a i*m)/(d i)
  let D i := (a i*r+1)/(d i)
  have dp i : 0<d i := pow_pos (prime i).pos _
  have mp : 0 < m := Finset.prod_pos fun i _ => pow_pos (prime i).pos _
  have dm i : d i ∣ m :=
    (pow_dvd_pow (q i) (Nat.le_succ _)).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  have slope i : d i * A i=a i*m :=
    Nat.mul_div_cancel' ((dm i).trans (dvd_mul_left _ _))
  have const i : d i * D i=a i*r+1 := Nat.mul_div_cancel' (hr i).1
  have eqn i t : d i * (A i*t+D i) = a i*(m*t+r)+1 := by
    rw [mul_add,←mul_assoc,slope,const]; ring
  have apos i : 0<A i := by
    by_contra! h
    have h₀ : A i=0 := by omega
    have h' := slope i
    rw [h₀,mul_zero] at h'
    exact (Nat.mul_pos (pos i) mp).ne' h'.symm
  have dpos i : 0<D i := by
    by_contra! h
    have h₀ : D i=0 := by omega
    have h' := const i
    rw [h₀,mul_zero] at h'
    omega
  have det (i j : Fin 7) (ij : i≠j) : A i*D j ≠ A j*D i := by
    intro same
    have h : (d i*A i)*(d j*D j)=(d j*A j)*(d i*D i) := by
      calc
        _ = (d i*d j)*(A i*D j) := by ring
        _ = _ := by rw [same]; ring
    rw [slope,slope,const,const] at h
    have hh : m*a i=m*a j := by nlinarith
    exact ij (mono.injective (Nat.eq_of_mul_eq_mul_left mp hh))
  have admiss (p : ℕ) (hp : p.Prime) : ∃ t : ℕ,∀ i,¬p∣A i*t+D i := by
    by_cases h : p∣m
    · obtain ⟨j,_,hj⟩ := (hp.prime.dvd_finsetProd_iff (fun i => q i^(e i+1))).mp h
      have eq := (Nat.prime_dvd_prime_iff_eq hp (prime j)).mp (hp.dvd_of_dvd_pow hj)
      subst p
      exact ⟨0, fun i => by simpa [D] using (hr i).2 j⟩
    · obtain ⟨t,ht⟩ := shift_target m r p hp h
      refine ⟨t,?_⟩
      intro i bad
      have h₁ : p∣a i*(m*t+r)+1 := eqn i t ▸ bad.mul_left (d i)
      have h₂ := ht.mul_left (a i)
      exact hp.not_dvd_one ((Nat.dvd_add_right h₂).mp h₁)
  obtain ⟨C,cp,hU⟩ := sieve A D apos dpos det admiss B
  let k : ℝ := 2*(m:ℝ)
  have kp : 0<k := by dsimp [k]; positivity
  have k₁ : 1 ≤ k := by
    have hm : (1:ℝ) ≤ m := by exact_mod_cast mp
    dsimp [k]
    linarith
  have tend : Tendsto (fun x : ℝ => x/k) atTop atTop := (tendsto_div_const_atTop_of_pos kp).mpr tendsto_id
  refine ⟨k*C,mul_pos kp cp,?_⟩
  filter_upwards [tend.eventually hU,tend.eventually (eventually_gt_atTop (1:ℝ)),
    eventually_ge_atTop (2*(r:ℝ))] with x hx hy hrx
  obtain ⟨U,estimate,good⟩ := hx
  let f t := m*t+r
  have injf : Function.Injective f := by
    intro t t' h
    exact Nat.eq_of_mul_eq_mul_left mp (Nat.add_right_cancel h)
  refine ⟨U.image f,?_,?_⟩
  · rw [card_image_of_injective _ injf]
    have xpos : 0<x := (div_pos_iff_of_pos_right kp).mp (by linarith : 0<x/k)
    have le : x/k≤x := (div_le_iff₀ kp).mpr (by nlinarith)
    have lp : 0<log (x/k) := log_pos hy
    have powle := pow_le_pow_left₀ lp.le (log_le_log (by linarith) le) 7
    calc
      x/(log x)^7 = k*((x/k)/(log x)^7) := by field_simp <;> ring
      _ ≤ k*((x/k)/(log (x/k))^7) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by linarith) (pow_pos lp _) powle) kp.le
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left estimate kp.le
  · intro n hn
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨tp,tx,values,tot⟩ := good t ht
    have quotient i : (a i*f t+1)/q i^e i=A i*t+D i := by
      change (a i*(m*t+r)+1)/d i=_
      rw [←eqn,Nat.mul_div_cancel_left _ (dp i)]
    refine ⟨Nat.add_pos_left (Nat.mul_pos mp tp) _,?_,?_,?_⟩
    · change ((m*t+r : ℕ) : ℝ)≤x
      push_cast
      have bound := (le_div_iff₀ kp).mp tx
      dsimp [k] at bound
      nlinarith
    · intro i
      refine ⟨⟨_,(eqn i t).symm⟩,?_⟩
      simpa only [quotient] using values i
    · simpa only [quotient] using tot

end OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1
