import OMAStatements.S_oeis_a167138
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Tactic

namespace OMA.LogMoments

open PowerSeries OMA.S_oeis_a167138
open scoped PowerSeries

lemma deriv_log_unit : derivative ℂ (log ℂ) * (1+X) = 1 := by
  rw [mul_add, mul_one, deriv_log]
  ext n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_mk]
  | succ n =>
    rw [map_add, show (X : PowerSeries ℂ) = X^1 by simp, coeff_mul_X_pow]
    simp [pow_succ]

lemma subst_const {g : PowerSeries ℂ} (hg : g.constantCoeff=0) (f : PowerSeries ℂ) :
    coeff 0 (f.subst g) = coeff 0 f := by
  rw [coeff_subst' (.of_constantCoeff_zero' hg), finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [coeff_zero_eq_constantCoeff_apply,map_pow,hg,zero_pow hd,smul_zero]

lemma euler_coeff (f : PowerSeries ℂ) (n : ℕ) :
    coeff n (derivative ℂ f * (1+X)) =
      coeff (n+1) f * (n+1) + coeff n f * n := by
  rw [mul_add,mul_one,map_add,coeff_derivative]
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    rw [show (X : PowerSeries ℂ) = X^1 by simp, coeff_mul_X_pow, coeff_derivative]
    simp

lemma exp_log : (exp ℂ).subst (log ℂ) = 1+X := by
  let F := (exp ℂ).subst (log ℂ)
  have h : derivative ℂ F * (1+X) = F := by
    dsimp [F]
    rw [derivative_subst HasSubst.log,derivative_exp,mul_assoc,deriv_log_unit,mul_one]
  have c0 : coeff 0 F = 1 := by
    dsimp [F]
    rw [subst_const constantCoeff_log,coeff_exp]
    norm_num
  have c1 : coeff 1 F = 1 := by
    have ht := congrArg (coeff 0) h
    rw [euler_coeff] at ht
    simpa [c0] using ht
  have c2 (n : ℕ) : coeff (n+2) F = 0 := by
    induction n with
    | zero =>
      have ht := congrArg (coeff 1) h
      rw [euler_coeff] at ht
      norm_num at ht
      exact ht
    | succ n ih =>
      have ht := congrArg (coeff (n+2)) h
      rw [euler_coeff,ih,zero_mul,add_zero,mul_eq_zero] at ht
      exact ht.resolve_right (by exact_mod_cast Nat.succ_ne_zero (n+2))
  ext n
  change coeff n F = _
  rcases n with _ | _ | n
  · simpa using c0
  · simpa using c1
  · simpa [coeff_X, show n+2 ≠ 1 by omega] using c2 n

def atom (k n : ℕ) : ℂ := (k:ℂ)^n

lemma transform_atom (k : ℕ) :
    transform (atom k) = (1+PowerSeries.X)^k := by
  have h : egf (atom k) = exp ℂ ^ k := by
    ext n
    rw [exp_pow_eq_rescale_exp, coeff_rescale, coeff_exp, egf, coeff_mk]
    simp [atom, div_eq_mul_inv]
  rw [transform,h,subst_pow HasSubst.log,exp_log]

-- A finite integer combination of atoms k^n. Multiplication in the monoid algebra
-- sends a pair of atoms indexed by k and j to the atom indexed by k*j.
noncomputable def moment (n : ℕ) : MonoidAlgebra ℤ ℕ →ₐ[ℤ] ℂ :=
  MonoidAlgebra.lift ℤ ℂ ℕ
    { toFun := fun k => (k:ℂ)^n
      map_one' := by simp
      map_mul' := by intros; simp [mul_pow] }

noncomputable def moments (v : MonoidAlgebra ℤ ℕ) (n : ℕ) : ℂ := moment n v

lemma add_model (v w : MonoidAlgebra ℤ ℕ) :
    transform (moments (v+w)) = transform (moments v) + transform (moments w) := by
  have he : egf (moments (v+w)) = egf (moments v) + egf (moments w) := by
    ext n
    simp [moments,egf,add_div]
  simp only [transform,he,subst_add HasSubst.log]

lemma single_model (k : ℕ) (c : ℤ) :
    transform (moments (MonoidAlgebra.single k c)) =
    (c : PowerSeries ℂ) * (1+X)^k := by
  have he : egf (moments (MonoidAlgebra.single k c)) = (c : ℂ) • egf (atom k) := by
    ext n
    rw [map_smul]
    simp [moments,moment,MonoidAlgebra.lift_single,atom,egf,zsmul_eq_mul, mul_div_assoc]
  rw [transform,he,subst_smul HasSubst.log]
  change (c : ℂ) • transform (atom k) = _
  rw [transform_atom, Algebra.smul_def]
  simp

lemma zero_model : transform (moments 0) = 0 := by
  simpa using single_model 0 0

lemma poly_model (p : Polynomial ℤ) :
    ∃ v : MonoidAlgebra ℤ ℕ, transform (moments v) =
      p.eval₂ (Int.castRingHom (PowerSeries ℂ)) (1+X) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨v,hv⟩ := hp
    obtain ⟨w,hw⟩ := hq
    exact ⟨v+w, by rw [add_model,hv,hw,Polynomial.eval₂_add]⟩
  | monomial n c =>
    exact ⟨MonoidAlgebra.single n c, by simp [single_model,Polynomial.eval₂_monomial]⟩

lemma model_integral (v : MonoidAlgebra ℤ ℕ) : integralSeries (transform (moments v)) := by
  induction v using MonoidAlgebra.induction_linear with
  | zero => intro n; exact ⟨0, by rw [zero_model]; simp⟩
  | add v w hv hw =>
    intro n
    obtain ⟨a,ha⟩ := hv n
    obtain ⟨b,hb⟩ := hw n
    exact ⟨a+b, by rw [add_model,map_add,ha,hb]; simp⟩
  | single k c =>
    intro n
    refine ⟨c*(k.choose n), ?_⟩
    rw [single_model,← zsmul_eq_mul, map_zsmul]
    have he : (1+X : PowerSeries ℂ)^k = (((1 + Polynomial.X : Polynomial ℂ)^k : Polynomial ℂ) : PowerSeries ℂ) := by simp
    rw [he,Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
    simp [zsmul_eq_mul]

def agree (N : ℕ) (F G : PowerSeries ℂ) : Prop := ∀ j < N, coeff j F = coeff j G

lemma agree_subst {N : ℕ} {F G u : PowerSeries ℂ} (hu : u.constantCoeff=0) (h : agree N F G) :
    agree N (F.subst u) (G.subst u) := by
  have horder := nat_le_order (F-G) N (fun j hj => by rw [map_sub,h j hj,sub_self])
  have hbound := horder.trans (le_order_subst_left' (φ:=F-G) hu)
  intro j hj
  have hz := coeff_of_lt_order j (lt_of_lt_of_le (by exact_mod_cast hj) hbound)
  have hsub : (F-G).subst u = F.subst u - G.subst u := by
    rw [← coe_substAlgHom (.of_constantCoeff_zero' hu),map_sub]
  simpa [hsub,sub_eq_zero] using hz

lemma agree_log {N : ℕ} {F G : PowerSeries ℂ} :
    agree N (F.subst (log ℂ)) (G.subst (log ℂ)) ↔ agree N F G := by
  refine ⟨?_,agree_subst constantCoeff_log⟩
  intro h
  have unit : IsUnit ((log ℂ).coeff 1) := by simp
  let u := (log ℂ).substInvOfIsUnit unit
  have h' := agree_subst (u:=u) (by simp [u]) h
  have hu : HasSubst u := HasSubst.substInvOfIsUnit _ _
  have he : (log ℂ).subst u = X := subst_substInvOfIsUnit_right _ constantCoeff_log unit
  simpa only [subst_comp_subst_apply HasSubst.log hu, he, X_subst] using h'

lemma agree_moments (N : ℕ) (L K : ℕ → ℂ) :
    agree N (transform L) (transform K) ↔ ∀ j < N, L j = K j := by
  rw [transform,transform,agree_log]
  simp only [agree,egf,coeff_mk]
  have hfact (n : ℕ) : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  simp [div_left_inj' (hfact _)]

lemma eval_integer_polynomial (p : Polynomial ℤ) :
    p.eval₂ (Int.castRingHom (PowerSeries ℂ)) X =
      ((p.map (Int.castRingHom ℂ) : Polynomial ℂ) : PowerSeries ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.eval₂_add,hp,hq]
  | monomial n c =>
    simp only [Polynomial.eval₂_monomial, Int.coe_castRingHom, Polynomial.map_monomial, Polynomial.coe_monomial]
    rw [show (c : PowerSeries ℂ) = C (c : ℂ) by simp]
    ext j
    rw [coeff_C_mul_X_pow, coeff_monomial]

-- Truncating an integral series and translating the polynomial by X-1 expresses
-- every finite prefix of its moments as a combination of the atoms.
lemma approximate (L : ℕ → ℂ) (h : integralSeries (transform L)) (N : ℕ) :
    ∃ v, ∀ j < N, L j = moments v j := by
  choose z hz using h
  let p := trunc N (mk z)
  obtain ⟨v,hv⟩ := poly_model (p.comp (Polynomial.X-1))
  refine ⟨v,(agree_moments N L _).mp ?_⟩
  rw [hv,Polynomial.eval₂_comp]
  simp only [Polynomial.eval₂_sub,Polynomial.eval₂_X,Polynomial.eval₂_one,add_sub_cancel_left]
  rw [eval_integer_polynomial]
  intro j hj
  simpa [p,Polynomial.coeff_coe,Polynomial.coeff_map,coeff_trunc,hj] using hz j

end OMA.LogMoments

open OMA.LogMoments OMA.S_oeis_a167138

theorem OMA.solution : type_of% @OMA.S_oeis_a167138.main := by
  intro L h m _ n
  obtain ⟨v,hv⟩ := approximate L h (n+1)
  have hx : agree (n+1) (transform (fun j => L j ^m)) (transform (moments (v^m))) := by
    apply (agree_moments _ _ _).mpr
    intro j hj
    simp [hv j hj,moments]
  rw [hx n (by omega)]
  exact model_integral _ n
