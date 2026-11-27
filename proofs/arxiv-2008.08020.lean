import OMAStatements.S_arxiv_2008_08020
import Mathlib

/-!
# Proof of Vielhaber's Conjecture 23

Credit: @rleshner
Source: https://arxiv.org/abs/2008.08020

Two sequences approaching zero have exact secant slopes 1 and 9/8.
Appending their continued fractions to an even-length rational prefix
transports them to the given rational point. The numerical binary codes
of the prefixed strings differ from those of the tails by a common
positive affine transformation. Differentiability at the rational would
give a derivative at zero of the composite with the smooth prefix map,
contradicting the two slopes.
-/

open OMA.S_arxiv_2008_08020 Filter
open scoped Topology

/-- Euclid's algorithm, taking two quotients at a time. A terminating
single quotient A is written as the pair (A-1,1). -/
private theorem rationalPrefix (p : ℕ) : ∀ q : ℕ, p<q →
    ∃ ds : List (ℕ × ℕ), cf ds 0 = (p:ℝ)/q := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro q hpq
    by_cases hp0 : p = 0
    · subst p; exact ⟨[],by simp [cf]⟩
    have hp := Nat.pos_of_ne_zero hp0
    let a := q/p
    let c := q%p
    have hqa : c + p*a = q := Nat.mod_add_div q p
    have hcl : c < p := Nat.mod_lt q hp
    have ha : 0 < a := Nat.div_pos hpq.le hp
    have hpr : 0 < (p:ℝ) := by exact_mod_cast hp
    have hqr : 0 < (q:ℝ) := by exact_mod_cast (hp.trans hpq)
    have hqr' : (c:ℝ)+(p:ℝ)*a=q := by exact_mod_cast hqa
    by_cases hc0 : c = 0
    · have ha2 : 2 ≤ a := by
        by_contra! hab
        have : a=1 := by omega
        simp [hc0,this] at hqa
        omega
      have hcast : ((a-2 : ℕ):ℝ)+1+1 = a := by
        exact_mod_cast (by omega : a-2+1+1=a)
      refine ⟨[(a-2,0)],?_⟩
      simp only [cf, Nat.cast_zero,zero_add,add_zero,div_one,hcast]
      have hapos : (0:ℝ)<a := by exact_mod_cast ha
      field_simp
      simpa [hc0, mul_comm] using hqr'.symm
    · have hc : 0<c := Nat.pos_of_ne_zero hc0
      let b := p/c
      let d := p%c
      have hpb : d+c*b=p := Nat.mod_add_div p c
      have hdl : d<c := Nat.mod_lt p hc
      have hb : 0<b := Nat.div_pos hcl.le hc
      obtain ⟨ds, hds⟩ := ih d (hdl.trans hcl) c hdl
      have hcasta : ((a-1 : ℕ):ℝ)+1=a := by exact_mod_cast (by omega : a-1+1=a)
      have hcastb : ((b-1 : ℕ):ℝ)+1=b := by exact_mod_cast (by omega : b-1+1=b)
      have hcr : 0<(c:ℝ) := by exact_mod_cast hc
      have hpb' : (d:ℝ)+(c:ℝ)*b=p := by exact_mod_cast hpb
      have h1 : (b:ℝ)+(d:ℝ)/c=(p:ℝ)/c := by field_simp; linarith
      have h2 : (a:ℝ)+(c:ℝ)/p=(q:ℝ)/p := by field_simp; linarith
      refine ⟨(a-1,b-1)::ds,?_⟩
      simp only [cf,hds,hcasta,hcastb,h1,one_div_div,h2]

private theorem cf_append (front tail : List (ℕ × ℕ)) (x : ℝ) :
    cf (front++tail) x = cf front (cf tail x) := by
  induction front with
  | nil => rfl
  | cons p ds ih => rcases p with ⟨a,b⟩; simp [cf,ih]

private theorem code_append (front tail : List (ℕ × ℕ)) (y : ℝ) :
    code (front++tail) y = code front (code tail y) := by
  induction front with
  | nil => rfl
  | cons p ds ih => rcases p with ⟨a,b⟩; simp [code,ih]

private theorem code_affine (ds : List (ℕ × ℕ)) :
    ∃ L : ℝ, 0<L ∧ ∀ y : ℝ, code ds y = code ds 0 + L*y := by
  induction ds with
  | nil => exact ⟨1,by norm_num,by simp [code]⟩
  | cons p ds ih =>
    obtain ⟨a,b⟩ := p
    obtain ⟨L,hL,haff⟩ := ih
    have hd (d : ℕ) : (0:ℝ)<denom d := by dsimp [denom]; positivity
    refine ⟨L / denom (b+1) / denom (a+1),div_pos (div_pos hL (hd _)) (hd _),?_⟩
    intro y
    simp only [code]
    rw [haff y]
    ring

private theorem cf_nonneg (ds : List (ℕ × ℕ)) : 0 ≤ cf ds 0 := by
  induction ds with
  | nil => rfl
  | cons p ds ih => rcases p with ⟨a,b⟩; simp only [cf]; positivity

private theorem cf_smooth (ds : List (ℕ × ℕ)) : DifferentiableAt ℝ (cf ds) 0 := by
  induction ds with
  | nil => exact differentiableAt_id
  | cons p ds ih =>
    rcases p with ⟨a,b⟩
    have h := cf_nonneg ds
    change DifferentiableAt ℝ (fun x : ℝ => 1 / ((a:ℝ)+1+1/((b:ℝ)+1+cf ds x))) 0
    fun_prop (disch := positivity)

/-- A derivative fixes the slope along every nonzero sequence tending to zero. -/
private theorem slopeAlong {g : ℝ → ℝ} (hg : DifferentiableAt ℝ g 0)
    {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0)) (hne : ∀ k, 0 < u k)
    {v : ℝ} (hv : ∀ k, g (u k) = g 0 + v * u k) : deriv g 0 = v := by
  have hnear : Tendsto u atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hu, .of_forall fun k => (hne k).ne'⟩
  have hs := hg.hasDerivAt.tendsto_slope.comp hnear
  have heq : slope g 0 ∘ u = fun _ : ℕ => v := by
    funext k
    simp only [Function.comp_apply,slope_def_field,sub_zero,hv]
    field_simp [(hne k).ne']
    ring
  rw [heq] at hs
  exact tendsto_nhds_unique hs tendsto_const_nhds

private theorem seedPair (a j v : ℕ) (hj : Nat.log 2 (a+1) = j)
    (hv : 3*2^j - 1 - (a+1) = v) :
    cf [(a,0)] 0 = 1/((a:ℝ)+2) ∧
    code [(a,0)] 0 = (v:ℝ)/(2*((2:ℝ)^j)^2) := by
  constructor
  · simp [cf]; ring_nf
  · have h0 : bitsII 1 = 0 := by decide
    simp only [code, Nat.zero_add, h0, Nat.cast_zero, add_zero, zero_div]
    simp only [bitsI, denom, hj, hv, Nat.cast_pow, Nat.cast_ofNat]
    rw [pow_succ, Nat.mul_comm 2 j, pow_mul]; ring

private theorem seed1 (k : ℕ) : ∃ ds, cf ds 0 = (1/2:ℝ)^(k+1) ∧ code ds 0 = (1/2:ℝ)^(k+1) := by
  let a := 2*2^k-2
  have hk : 0 < (2:ℕ)^k := by positivity
  have ha : a+2 = 2*2^k := by dsimp [a]; omega
  have hl : Nat.log 2 (a+1) = k := Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [pow_succ]; omega)
  have ⟨hc,hb⟩ := seedPair a k (2^k) hl (by omega)
  have hr : (a:ℝ)+2 = 2*(2:ℝ)^k := by exact_mod_cast ha
  refine ⟨[(a,0)], ?_, ?_⟩
  · rw [hc, hr, div_pow, one_pow, pow_succ]; ring
  · rw [hb, Nat.cast_pow, Nat.cast_ofNat, div_pow, one_pow, pow_succ]; field_simp; exact pow_succ _ _
private theorem seed2 (k : ℕ) : ∃ ds, cf ds 0 = (1/3:ℝ)*(1/2:ℝ)^(k+1) ∧ code ds 0 = (9/8:ℝ)*((1/3:ℝ)*(1/2:ℝ)^(k+1)) := by
  let a := 6*2^k-2
  have hk : 0 < (2:ℕ)^k := by positivity
  have ha : a+2 = 6*2^k := by dsimp [a]; omega
  have h4 : (2:ℕ)^(k+2) = 2^k*4 := by rw [pow_add]; norm_num
  have hl : Nat.log 2 (a+1) = k+2 := Nat.log_eq_of_pow_le_of_lt_pow (by rw [h4]; omega) (by rw [pow_succ,h4]; omega)
  have ⟨hc,hb⟩ := seedPair a (k+2) (6*2^k) hl (by rw [h4]; omega)
  have hr : (a:ℝ)+2 = 6*(2:ℝ)^k := by exact_mod_cast ha
  refine ⟨[(a,0)], ?_, ?_⟩
  · rw [hc, hr, div_pow, one_pow, pow_succ]; ring
  · rw [hb]; push_cast; rw [div_pow, one_pow, pow_succ (n := k), pow_add]; field_simp; ring

private theorem notDifferentiableAtPrefix (F : ℝ → ℝ) (hF : Encodes F)
    (ds : List (ℕ × ℕ)) : ¬ DifferentiableAt ℝ F (cf ds 0) := by
  intro h
  let g : ℝ → ℝ := F ∘ cf ds
  have hg : DifferentiableAt ℝ g 0 := h.comp 0 (cf_smooth ds)
  obtain ⟨L,hL,hline⟩ := code_affine ds
  have evaluate (tail : List (ℕ × ℕ)) : g (cf tail 0) = g 0 + L*code tail 0 := by
    change F (cf ds (cf tail 0)) = F (cf ds 0) + _
    rw [← cf_append,hF,hF,code_append,hline (code tail 0)]
  let u : ℕ → ℝ := fun k => (1/2:ℝ)^(k+1)
  have hu : Tendsto u atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num)
    simpa [u,pow_succ] using hpow.mul_const (1/2:ℝ)
  have hpos (k : ℕ) : 0<u k := by dsimp [u]; positivity
  have hfirst : deriv g 0 = L := by
    apply slopeAlong hg hu hpos
    intro k
    obtain ⟨tail,ht,hc⟩ := seed1 k
    simpa [ht,hc,u] using evaluate tail
  have hlim : Tendsto (fun k => (1/3:ℝ)*u k) atTop (𝓝 0) := by
    simpa using hu.const_mul (1/3:ℝ)
  have hsecond : deriv g 0 = L*(9/8) := by
    apply slopeAlong hg hlim (fun k => mul_pos (by norm_num) (hpos k))
    intro k
    obtain ⟨tail,ht,hc⟩ := seed2 k
    simpa [ht,hc,u,mul_assoc] using evaluate tail
  linarith

theorem OMA.solution : type_of% @OMA.S_arxiv_2008_08020.main := by
  intro F hF p q _ hpq
  obtain ⟨ds,heq⟩ := rationalPrefix p q hpq
  rw [← heq]
  exact notDifferentiableAtPrefix F hF ds
