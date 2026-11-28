import OMAReductions.R_OeisA280831_conjecture_R1

/-!
# Binary forms for the 1680-conjecture

Gauss reduction for determinants 3 and 22 converts modular square roots
to restricted four-square representations when the input is 7 modulo 8.

Credit: @MrSeizy. The squarefree descent uses the parity argument from
@ivillar's merged H1 proof, adapted there from @amurthy04.
-/

namespace OMA.R_OeisA280831_conjecture_R1_H2_R1

private theorem reduce_form (d n : ℤ) (hd : 0 < d)
    (a b c x y : ℤ) (ha : 0 < a) (hdet : a*c = b^2+d)
    (hrep : n = a*x^2+2*b*x*y+c*y^2) :
    ∃ A B C X Y : ℤ, 0 < A ∧ -A ≤ 2*B ∧ 2*B ≤ A ∧ A ≤ C ∧
      A*C = B^2+d ∧ n = A*X^2+2*B*X*Y+C*Y^2 := by
  let k := (b + a/2) / a
  let B := b - a*k
  let C := c - 2*b*k + a*k^2
  have hr : B = (b + a/2) % a - a/2 := by
    dsimp [B,k]
    have := Int.mul_ediv_add_emod (b+a/2) a
    omega
  have hr₀ := Int.emod_nonneg (b+a/2) (by omega : a ≠ 0)
  have hr₁ := Int.emod_lt_of_pos (b+a/2) ha
  have hB₁ : -a ≤ 2*B := by omega
  have hB₂ : 2*B ≤ a := by omega
  have hD : a*C = B^2+d := by dsimp [B,C]; linear_combination hdet
  have hC : 0 < C := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le h, sq_nonneg B]
  have hN : n = a*(x+k*y)^2 + 2*B*(x+k*y)*y + C*y^2 := by
    dsimp [B,C]
    linear_combination hrep
  by_cases h : a ≤ C
  · exact ⟨a,B,C,x+k*y,y,ha,hB₁,hB₂,h,hD,hN⟩
  · exact reduce_form d n hd C B a y (x+k*y) hC (by rw [mul_comm]; exact hD)
      (by linear_combination hN)
termination_by a.toNat
decreasing_by exact (Int.toNat_lt_toNat ha).mpr (lt_of_not_ge h)

private theorem sq_mod_eight (x : ℤ) :
    x^2 % 8 = 0 ∨ x^2 % 8 = 1 ∨ x^2 % 8 = 4 := by
  simp only [pow_two]
  rw [Int.mul_emod x x]
  have h₁ := Int.emod_nonneg x (by decide : (8 : ℤ) ≠ 0)
  have h₂ := Int.emod_lt_of_pos x (by decide : (0 : ℤ) < 8)
  interval_cases x % 8 <;> decide

private theorem reduced_rep (d n : ℤ) (hd : d = 3 ∨ d = 22) (hn : n%8=7)
    (a b c x y : ℤ) (ha : 0<a) (hl : -a ≤ 2*b) (hu : 2*b ≤ a)
    (hc : a≤c) (hdet : a*c=b^2+d) (hrep : n=a*x^2+2*b*x*y+c*y^2) :
    ∃ u v : ℤ, n=u^2+d*v^2 := by
  have hbound : 3*a^2 ≤ 4*d := by
    nlinarith [mul_nonneg (show 0 ≤ a+2*b by omega) (show 0 ≤ a-2*b by omega),
      mul_nonneg ha.le (sub_nonneg.mpr hc)]
  have ha5 : a ≤ 5 := by
    by_contra! h
    rcases hd with rfl | rfl <;> nlinarith [mul_nonneg (show 0 ≤ a-6 by omega) (show 0 ≤ a+6 by omega)]
  have hb₁ : -2 ≤ b := by omega
  have hb₂ : b ≤ 2 := by omega
  have classes : (a=1 ∧ b=0 ∧ c=d) ∨ (a=2 ∧ c=2) ∨
      (a=2 ∧ b=0 ∧ c=11) := by
    rcases hd with rfl | rfl <;> interval_cases a <;> interval_cases b <;>
      try norm_num at hdet ⊢ <;> omega
  rcases classes with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact ⟨x,y,by linear_combination hrep⟩
  · have he : n = 2 * (x^2+b*x*y+y^2) := by linear_combination hrep
    omega
  · have he : n = 2*x^2 + 11*y^2 := by linear_combination hrep
    rcases sq_mod_eight x with h|h|h <;> rcases sq_mod_eight y with j|j|j <;> omega

private theorem combine_roots (d : ℤ) (n : ℕ) (hn : Squarefree n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → IsSquare (d : ZMod p)) :
    IsSquare (d : ZMod n) := by
  induction n using Nat.recOnMul with
  | zero => exact (hn.ne_zero rfl).elim
  | one => exact ⟨0, Subsingleton.elim _ _⟩
  | prime p hp => exact h p hp dvd_rfl
  | mul a b ia ib =>
    obtain ⟨r,hr⟩ := ia hn.of_mul_left (fun p hp hv => h p hp (dvd_mul_of_dvd_left hv b))
    obtain ⟨s,hs⟩ := ib hn.of_mul_right (fun p hp hv => h p hp (dvd_mul_of_dvd_right hv a))
    let e := ZMod.chineseRemainder (Nat.coprime_of_squarefree_mul hn)
    refine ⟨e.symm (r,s), e.injective ?_⟩
    rw [map_mul, e.apply_symm_apply, map_intCast]
    exact Prod.ext hr hs

private theorem prime_recip {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p%4=3) (hq : q%4=3) (hne : p ≠ q) (h : IsSquare (p : ZMod q)) :
    IsSquare (-(q : ZMod p)) := by
  have hq0 := ZMod.prime_ne_zero p q hne
  have hp0 := ZMod.prime_ne_zero q p hne.symm
  have hleg := (legendreSym.eq_one_iff' q hp0).mpr h
  have hrec := legendreSym.quadratic_reciprocity_three_mod_four (p:=q) (q:=p) hq hp
  have hneg := legendreSym.at_neg (p:=p) (a:=(q:ℤ)) (by omega : p≠2)
  have hchar := ZMod.χ₄_nat_three_mod_four hp
  have hz : (((-(q : ℤ)) : ℤ) : ZMod p) ≠ 0 := by simpa using hq0
  have hs := (legendreSym.eq_one_iff p hz).mp (by rw [hneg,hchar,hrec,hleg]; norm_num)
  simpa using hs

private theorem prime_classes {p : ℕ} (hp : p.Prime) (h7 : p%8=7)
    (h3 : ¬ IsSquare (-3 : ZMod p)) (h22 : ¬ IsSquare (-22 : ZMod p)) :
    p%3=2 ∧ p%11 ∈ ([2,6,7,8,10] : List ℕ) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h4 : p%4=3 := by omega
  have hP3 : ¬IsSquare (p : ZMod 3) := fun h => h3 (by
    simpa using prime_recip h4 (by decide : 3%4=3) (by omega) h)
  have hP11 : ¬IsSquare (p : ZMod 11) := by
    intro h
    have hh := prime_recip h4 (by decide : 11%4=3) (by omega) h
    have htwo := (ZMod.exists_sq_eq_two_iff (p:=p) (by omega)).mpr (Or.inr h7)
    apply h22
    rw [show (-22 : ZMod p) = 2 * (-11) by ring]
    exact htwo.mul (by simpa using hh)
  have h₃ : IsSquare ((p%3 : ℕ) : ZMod 3) ↔ IsSquare (p : ZMod 3) := by simp
  have h₁₁ : IsSquare ((p%11 : ℕ) : ZMod 11) ↔ IsSquare (p : ZMod 11) := by simp
  constructor
  · by_contra hz
    apply hP3
    apply h₃.mp
    have hh : p%3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases p%3 <;> first | decide +kernel | omega
  · by_contra hz
    apply hP11
    apply h₁₁.mp
    have hh : p%11 < 11 := Nat.mod_lt _ (by decide)
    interval_cases p%11 <;> first | decide +kernel | simp_all

private theorem from_root (n d : ℕ) (h7 : n%8=7) (hd : d=3 ∨ d=22)
    (hs : IsSquare (-(d : ZMod n))) : OeisA280831.A n := by
  obtain ⟨s,hs⟩ := hs
  obtain ⟨r, rfl⟩ := ZMod.intCast_surjective s
  have hdiv : (n : ℤ) ∣ r^2+d := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    linear_combination -hs
  obtain ⟨c,hc⟩ := hdiv
  have hd' : (d : ℤ) = 3 ∨ (d : ℤ) = 22 := by exact_mod_cast hd
  have hn' : (n : ℤ)%8=7 := by exact_mod_cast h7
  obtain ⟨a,b,c',x,y,ha,hl,hu,hle,hD,hN⟩ := reduce_form d n (by omega)
    n r c 1 0 (by omega) hc.symm (by ring)
  obtain ⟨u,v,h⟩ := reduced_rep d n hd' hn' a b c' x y ha hl hu hle hD hN
  have hn : n = u.natAbs^2 + d*v.natAbs^2 := by
    exact_mod_cast (show (n:ℤ) = (u.natAbs:ℤ)^2 + (d:ℤ)*(v.natAbs:ℤ)^2 by
      simpa only [Int.natAbs_pow_two] using h)
  rcases hd with rfl | rfl
  · exact ⟨v.natAbs,v.natAbs,v.natAbs,u.natAbs,by rw [hn]; ring,41*v.natAbs^2,by ring⟩
  · exact ⟨3*v.natAbs,2*v.natAbs,3*v.natAbs,u.natAbs,by rw [hn]; ring,201*v.natAbs^2,by ring⟩

/-- The five remaining prime classes modulo 264. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p%264 ∈ ([95,167,215,239,263] : List ℕ) → OeisA280831.A p

/-- Squarefree composite inputs with a prime obstruction for each binary form. -/
def H2 : Prop :=
  ∀ n : ℕ, Squarefree n → ¬ n.Prime → n%8=7 →
    (∃ p : ℕ, p.Prime ∧ p ∣ n ∧ ¬ IsSquare (-3 : ZMod p)) →
    (∃ q : ℕ, q.Prime ∧ q ∣ n ∧ ¬ IsSquare (-22 : ZMod q)) → OeisA280831.A n

theorem squarefree_case (h₁ : H1) (h₂ : H2) (n : ℕ) (hs : Squarefree n)
    (hn : n%8=7) : OeisA280831.A n := by
  classical
  by_cases h3 : IsSquare (-3 : ZMod n)
  · exact from_root n 3 hn (Or.inl rfl) (by simpa using h3)
  by_cases h22 : IsSquare (-22 : ZMod n)
  · exact from_root n 22 hn (Or.inr rfl) (by simpa using h22)
  by_cases hp : n.Prime
  · obtain ⟨hn3,hn11⟩ := prime_classes hp hn h3 h22
    have table : ∀ r : Fin 264, r.val%8=7 → r.val%3=2 →
        r.val%11 ∈ ([2,6,7,8,10] : List ℕ) →
        r.val ∈ ([95,167,215,239,263] : List ℕ) := by decide +kernel
    apply h₁ n hp
    apply table ⟨n%264, Nat.mod_lt _ (by decide)⟩
    · simpa only [Nat.mod_mod_of_dvd n (by decide : 8 ∣ 264)] using hn
    · simpa only [Nat.mod_mod_of_dvd n (by decide : 3 ∣ 264)] using hn3
    · simpa only [Nat.mod_mod_of_dvd n (by decide : 11 ∣ 264)] using hn11
  · apply h₂ n hs hp hn
    · by_contra! h
      apply h3
      simpa using combine_roots (-3) n hs (by simpa using h)
    · by_contra! h
      apply h22
      simpa using combine_roots (-22) n hs (by simpa using h)

theorem main : H1 → H2 → OMA.R_OeisA280831_conjecture_R1.H2 := by
  intro h₁ h₂ n h7
  obtain ⟨m,s,hm,hs⟩ := Nat.sq_mul_squarefree n
  have odd : s%2=1 := by
    by_contra h
    have he : s=2*(s/2) := by omega
    have h4 : n=4*((s/2)^2*m) := calc
      n = s^2*m := hm.symm
      _ = (2*(s/2))^2*m := by rw [← he]
      _ = _ := by ring
    omega
  have hsq : s^2%8=1 := by
    have : s%8=1 ∨ s%8=3 ∨ s%8=5 ∨ s%8=7 := by omega
    rcases this with h|h|h|h <;> simp [Nat.pow_mod,h]
  have h7m : m%8=7 := by
    rw [← hm, Nat.mul_mod, hsq, one_mul, Nat.mod_mod] at h7
    exact h7
  obtain ⟨x,y,z,w,hsum,r,hr⟩ := squarefree_case h₁ h₂ m hs h7m
  refine ⟨s*x,s*y,s*z,s*w,?_,s^2*r,?_⟩
  · rw [← hm,hsum]; ring
  · calc
      (s*x)^4 + 1680*(s*y)^3*(s*z) = s^4*(x^4+1680*y^3*z) := by ring
      _ = _ := by rw [hr]; ring

end OMA.R_OeisA280831_conjecture_R1_H2_R1
