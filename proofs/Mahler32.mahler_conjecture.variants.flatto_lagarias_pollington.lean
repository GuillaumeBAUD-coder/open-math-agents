import FormalConjectures.Wikipedia.Mahler32
/-! Fractional parts in an interval narrower than 1/p have a locally contracting inverse. -/
open Filter Finset Mahler32
namespace FractionalPowers

lemma small_int {x : ℝ} (hz : ∃ z : ℤ, x = z) (hx : |x| < 1) : x = 0 := by
  obtain ⟨z,rfl⟩ := hz
  obtain ⟨hl,hu⟩ := abs_lt.mp hx
  have hl' : (-1:ℤ) < z := by exact_mod_cast hl
  have hu' : z < 1 := by exact_mod_cast hu
  exact_mod_cast (show z=0 by omega)

lemma collide (f : ℕ → ℝ) (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n < 1)
    {ρ ε : ℝ} (hρ : 0 < ρ) (hr : ρ < 1) (he : 0 < ε)
    (back : ∀ i j, |f (i+1)-f (j+1)| < ε →
      |f i-f j| = ρ*|f (i+1)-f (j+1)|) : ∃ i j, i < j ∧ f i = f j := by
  classical
  by_contra! hinj
  obtain ⟨K,hK⟩ := exists_nat_gt (1/ε)
  let g := fun (v : Fin (K+1) × Fin (K+1)) =>
    if v.1 = v.2 then (1:ℝ) else |f v.1 - f v.2|
  have hg (v) : 0 < g v := by
    dsimp [g]; split
    · norm_num
    · rename_i hn
      apply abs_pos.mpr
      apply sub_ne_zero.mpr
      rcases lt_or_gt_of_ne hn with h | h
      · exact hinj _ _ h
      · exact (hinj _ _ h).symm
  let δ := univ.inf' (univ_nonempty : (univ : Finset (Fin (K+1) × Fin (K+1))).Nonempty) g
  have hd : 0 < δ := (lt_inf'_iff _).mpr (fun i _ => hg i)
  obtain ⟨t,ht⟩ := exists_pow_lt_of_lt_one (div_pos hd he) hr
  let bin := fun i : Fin (K+1) => ⌊f (i.val+t)/ε⌋₊
  have hbin (i) : bin i < K := by
    apply (Nat.floor_lt (div_nonneg (h0 _) he.le)).mpr
    exact ((div_lt_div_iff_of_pos_right he).mpr (h1 _)).trans hK
  obtain ⟨i,j,hij,hij'⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i => (⟨bin i,hbin i⟩ : Fin K)) (by simp)
  have eqbin : bin i = bin j := congrArg Fin.val hij'
  have close : |f (i.val+t)-f (j.val+t)| < ε := by
    have H (i : Fin (K+1)) : (bin i : ℝ)*ε ≤ f (i.val+t) ∧ f (i.val+t) < ((bin i : ℝ)+1)*ε :=
      ⟨(le_div_iff₀ he).mp (Nat.floor_le (div_nonneg (h0 _) he.le)),
       (div_lt_iff₀ he).mp (Nat.lt_floor_add_one _)⟩
    have hi := H i
    have hj := H j
    rw [eqbin] at hi
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  have pull (t i j : ℕ) (h : |f (i+t)-f (j+t)| < ε) :
      |f i-f j| ≤ ρ^t*|f (i+t)-f (j+t)| := by
    induction t generalizing i j with
    | zero => simp
    | succ t ih =>
      have hh := back (i+t) (j+t) (by simpa [Nat.add_assoc] using h)
      have hsmall : |f (i+t)-f (j+t)| < ε := by
        rw [hh]
        exact (mul_le_of_le_one_left (abs_nonneg _) hr.le).trans_lt (by simpa [Nat.add_assoc] using h)
      calc
        _ ≤ _ := ih _ _ hsmall
        _ = _ := by rw [hh,pow_succ]; simp [Nat.add_assoc,mul_assoc]
  have hb := pull t i j close
  have hlow : δ ≤ |f i-f j| := by simpa [g,hij] using (inf'_le g (mem_univ (i,j)))
  have hh := (lt_div_iff₀ he).mp ht
  exact (not_lt_of_ge hlow) (hb.trans_lt ((mul_lt_mul_of_pos_left close (pow_pos hρ _)).trans hh))

lemma aperiodic {p q : ℕ} (hq : 1 < q) (hp : q < p) (hc : p.Coprime q)
    {θ : ℝ} (hθ : 0 < θ) {i j : ℕ} (hij : i < j)
    (h : ∀ k : ℕ, Int.fract (θ*((p:ℝ)/q)^(j+k)) = Int.fract (θ*((p:ℝ)/q)^(i+k))) : False := by
  let r := (p:ℝ)/q
  have hqR : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hr : 1 < r := (one_lt_div hqR).mpr (by exact_mod_cast hp)
  obtain ⟨z,hz⟩ := Int.fract_eq_fract.mp (h 0)
  change θ*r^(j+0)-θ*r^(i+0)=(z:ℝ) at hz
  simp only [Nat.add_zero] at hz
  have hpos : 0 < z := by
    have hj := mul_lt_mul_of_pos_left (pow_lt_pow_right₀ hr hij) hθ
    exact_mod_cast (show (0:ℝ) < z by linarith)
  let k := z.natAbs
  obtain ⟨w,hw⟩ := Int.fract_eq_fract.mp (h k)
  change θ*r^(j+k)-θ*r^(i+k)=(w:ℝ) at hw
  rw [pow_add,pow_add,← mul_assoc,← mul_assoc,← sub_mul,hz] at hw
  change (z:ℝ)*((p:ℝ)/q)^k=(w:ℝ) at hw
  rw [div_pow,← mul_div_assoc,div_eq_iff (pow_ne_zero _ hqR.ne')] at hw
  have he : z*(p:ℤ)^k=w*(q:ℤ)^k := by exact_mod_cast hw
  have hd : q^k ∣ p^k*z.natAbs := by
    have hZ : (q:ℤ)^k ∣ z*(p:ℤ)^k := he ▸ dvd_mul_left _ _
    have hh := Int.natAbs_dvd_natAbs.mpr hZ
    simpa [Int.natAbs_mul,Int.natAbs_pow,Nat.mul_comm] using hh
  have hk := Nat.le_of_dvd (Int.natAbs_pos.mpr hpos.ne') ((hc.symm.pow k k).dvd_of_dvd_mul_left hd)
  exact (Nat.not_le_of_lt (Nat.lt_pow_self (n := k) hq)) hk

lemma width_bound {p q : ℕ} (hq : 1 < q) (hp : q < p) (hc : p.Coprime q)
    {θ : ℝ} (hθ : 0 < θ) {l u : ℝ}
    (thin : (p:ℝ)*(u-l)<1)
    (band : ∀ n : ℕ, Int.fract (θ*((p:ℝ)/q)^n) ∈ Set.Icc l u) : False := by
  let r := (p:ℝ)/q
  let f := fun n : ℕ => Int.fract (θ*r^n)
  have hqR : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hpR : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hr : (q:ℝ) < p := by exact_mod_cast hp
  have hb (i j : ℕ) : |f i-f j| ≤ u-l := by
    obtain ⟨h1,h2⟩ := band i
    obtain ⟨h3,h4⟩ := band j
    dsimp [f,r]; exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩
  have hstep (n : ℕ) : ∃ z : ℤ, (p:ℝ)*f n - q*f (n+1) = z := by
    refine ⟨(q:ℤ)*⌊θ*r^(n+1)⌋-(p:ℤ)*⌊θ*r^n⌋,?_⟩
    simp only [f,Int.fract,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
    have hh : (q:ℝ)*r=p := by dsimp [r]; field_simp
    rw [pow_succ]
    linear_combination -(θ*r^n)*hh
  have hd (i j : ℕ) : ∃ z : ℤ,
      (p:ℝ)*(f i-f j)-q*(f (i+1)-f (j+1))=z := by
    obtain ⟨x,hx⟩ := hstep i
    obtain ⟨y,hy⟩ := hstep j
    exact ⟨x-y,by push_cast; linarith⟩
  let ε := (1-(p:ℝ)*(u-l))/q
  have he : 0 < ε := div_pos (by linarith) hqR
  have heq : (q:ℝ)*ε = 1-(p:ℝ)*(u-l) := by dsimp [ε]; field_simp
  have back (i j : ℕ) (hh : |f (i+1)-f (j+1)| < ε) :
      |f i-f j| = ((q:ℝ)/p) * |f (i+1)-f (j+1)| := by
    have ha := abs_sub ((p:ℝ)*(f i-f j)) ((q:ℝ)*(f (i+1)-f (j+1)))
    rw [abs_mul,abs_mul,abs_of_pos hpR,abs_of_pos hqR] at ha
    have hL := mul_le_mul_of_nonneg_left (hb i j) hpR.le
    have hR := mul_lt_mul_of_pos_left hh hqR
    have hz := small_int (hd i j) (ha.trans_lt (by linarith only [hL,hR,heq]))
    have hh' := congrArg abs (sub_eq_zero.mp hz)
    rw [abs_mul,abs_mul,abs_of_pos hpR,abs_of_pos hqR] at hh'
    field_simp; linarith
  obtain ⟨i,j,hij,heij⟩ := collide f (fun _ => Int.fract_nonneg _) (fun _ => Int.fract_lt_one _)
    (div_pos hqR hpR) ((div_lt_one hpR).mpr hr) he back
  have eq (k : ℕ) : f (j+k) = f (i+k) := by
    induction k with
    | zero => simpa using heij.symm
    | succ k ih =>
      have ht := hd (j+k) (i+k)
      rw [ih,sub_self,mul_zero,zero_sub] at ht
      have hgap := abs_nonneg (f 0-f 0) |>.trans (hb 0 0)
      have hh := mul_le_mul_of_nonneg_left (hb (j+k+1) (i+k+1)) hqR.le
      have ht' := small_int ht (by rw [abs_neg,abs_mul,abs_of_pos hqR]; linarith [mul_le_mul_of_nonneg_right hr.le hgap])
      exact sub_eq_zero.mp ((mul_eq_zero.mp (neg_eq_zero.mp ht')).resolve_left hqR.ne')
  exact aperiodic hq hp hc hθ hij eq
end FractionalPowers

theorem OMA.solution : type_of% @Mahler32.mahler_conjecture.variants.flatto_lagarias_pollington := by
  intro p q hq hc hp
  let r := (p:ℝ)/q
  have hpR : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hqR : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  rw [Mahler32.Ω]
  apply le_csInf
  · exact ⟨_,1,by norm_num,rfl⟩
  rintro _ ⟨θ,hθ,rfl⟩
  let f := fun n : ℕ => Int.fract (θ*r^n)
  let u := limsup f atTop
  let l := liminf f atTop
  change 1/(p:ℝ) ≤ u-l
  by_contra! hn
  let δ := (1/(p:ℝ)-(u-l))/4
  have hd : 0 < δ := by dsimp [δ]; linarith
  have hu : ∀ᶠ n in atTop, f n < u+δ := eventually_lt_of_limsup_lt
    (show u<u+δ by linarith) (isBoundedUnder_of ⟨1,fun _ => (Int.fract_lt_one _).le⟩)
  have hl : ∀ᶠ n in atTop, l-δ < f n := eventually_lt_of_lt_liminf
    (show l-δ<l by linarith) (isBoundedUnder_of ⟨0,fun _ => Int.fract_nonneg _⟩)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hl.and hu)
  apply FractionalPowers.width_bound hq hp hc (θ := θ*r^N) (l := l-δ) (u := u+δ)
  · exact mul_pos hθ (pow_pos (div_pos hpR hqR) _)
  · have hh : (u+δ)-(l-δ) < 1/(p:ℝ) := by dsimp [δ]; linarith
    linarith [(lt_div_iff₀ hpR).mp hh]
  · intro n
    have hh := hN (N+n) (by omega)
    change Int.fract (θ*r^N*r^n) ∈ _
    rw [mul_assoc,← pow_add]
    exact ⟨hh.1.le,hh.2.le⟩
