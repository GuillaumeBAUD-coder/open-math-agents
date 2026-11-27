import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1

/-!
# Odd parameters in the normalized shared-divisor problem

Mixed parity is impossible in a positive pair with integral square quotient.
For two even components, shift each up by one. The shifted components are odd,
and replacing the larger root of the quotient quadratic by its Vieta partner
strictly decreases the smaller shifted component. The only odd base pair is
(1,1), which corresponds to zero components.
-/

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1

theorem odd_shifted_eq_one (x : ℕ) :
    ∀ y q : ℕ, Odd x → Odd y → x ≤ y →
      ((x : ℤ) + y - 2)^2 = (q : ℤ)*x*y → x = 1 ∧ y = 1 := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro y q hx hy hxy he
    have hxpos : 0 < x := by obtain ⟨k, hk⟩ := hx; omega
    have hypos : (0 : ℤ) < y := by exact_mod_cast (show 0 < y by omega)
    by_cases h1 : x = 1
    · subst x
      have hdiv : (y : ℤ) ∣ 1 := ⟨(q : ℤ) - y + 2, by
        push_cast at he
        linear_combination he⟩
      exact ⟨rfl, by exact_mod_cast (Int.eq_one_of_dvd_one hypos.le hdiv)⟩
    have hx3 : (3 : ℤ) ≤ x := by
      obtain ⟨k, hk⟩ := hx
      exact_mod_cast (show 3 ≤ x by omega)
    let z : ℤ := ((q : ℤ)-2)*x+4-y
    have hzprod : (y : ℤ)*z = ((x : ℤ)-2)^2 := by
      dsimp [z]
      linear_combination -he
    have hzpos : 0 < z := by
      by_contra hz
      have hn := mul_nonpos_of_nonneg_of_nonpos hypos.le (le_of_not_gt hz)
      rw [hzprod] at hn
      have hp : 0 < ((x : ℤ)-2)^2 := pow_pos (by omega) _
      linarith
    have hxz : z < x := by
      have hsq : ((x : ℤ)-2)^2 < (x : ℤ)*x := by linarith [show (x : ℤ) ≥ 3 from hx3]
      have hxy' : (x : ℤ) ≤ y := by exact_mod_cast hxy
      have hb := hsq.trans_le (mul_le_mul_of_nonneg_left hxy' (by positivity : (0 : ℤ) ≤ x))
      have hzle : (y : ℤ)*z < y*x := by rw [hzprod, mul_comm (y : ℤ) x]; exact hb
      exact lt_of_mul_lt_mul_left hzle hypos.le
    have hroot : ((x : ℤ)+z-2)^2 = (q : ℤ)*x*z := by
      dsimp only [z]
      linear_combination he
    let t := z.toNat
    have ht : (t : ℤ) = z := Int.toNat_of_nonneg hzpos.le
    have htz : t < x := by exact_mod_cast (show (t : ℤ) < x by rwa [ht])
    have htodd : Odd t := by
      obtain ⟨i, hi⟩ := hx
      obtain ⟨j, hj⟩ := hy
      have hpx := congrArg (fun a : ℤ => a % 2) hzprod
      rw [← ht, Int.mul_emod, pow_two, Int.mul_emod ((x : ℤ)-2) ((x : ℤ)-2)] at hpx
      have hxx : (x : ℤ) % 2 = 1 := by exact_mod_cast (show x % 2 = 1 by omega)
      have hyy : (y : ℤ) % 2 = 1 := by exact_mod_cast (show y % 2 = 1 by omega)
      have hsub : ((x : ℤ)-2) % 2 = 1 := by omega
      rw [hyy, hsub] at hpx
      simp at hpx
      have : t % 2 = 1 := by exact_mod_cast hpx
      exact ⟨t/2, by omega⟩
    have htroot : ((t : ℤ)+x-2)^2 = (q : ℤ)*t*x := by
      rw [ht]
      linear_combination hroot
    exact (h1 (ih t htz x q htodd hx htz.le htroot).2).elim

theorem odd_components {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (hd : (a+1)*(b+1) ∣ (a+b)^2) : Odd a ∧ Odd b := by
  obtain ⟨q, hq⟩ := hd
  have mixed {x y : ℕ} (hex : Even x) (hoy : Odd y)
      (he : (x+y)^2 = (x+1)*(y+1)*q) : False := by
    have ho : Odd ((x+y)^2) := (hex.add_odd hoy).pow
    obtain ⟨k, hk⟩ := hoy
    have hev : Even ((x+y)^2) := ⟨(x+1)*(k+1)*q, by
      rw [he, hk]
      ring⟩
    obtain ⟨u, hu⟩ := ho
    obtain ⟨v, hv⟩ := hev
    omega
  rcases Nat.even_or_odd a with hae | hao
  · rcases Nat.even_or_odd b with hbe | hbo
    · have hsa : Odd (a+1) := by obtain ⟨k,hk⟩ := hae; exact ⟨k, by omega⟩
      have hsb : Odd (b+1) := by obtain ⟨k,hk⟩ := hbe; exact ⟨k, by omega⟩
      have hq' : (((a+1 : ℕ) : ℤ)+(b+1 : ℕ)-2)^2 =
          (q : ℤ)*(a+1 : ℕ)*(b+1 : ℕ) := by
        push_cast
        have hqz : ((a : ℤ)+b)^2 = (a+1)*(b+1)*q := by exact_mod_cast hq
        linear_combination hqz
      have h := (odd_shifted_eq_one (a+1) (b+1) q hsa hsb (by omega) hq').1
      omega
    · exact (mixed hae hbo hq).elim
  · rcases Nat.even_or_odd b with hbe | hbo
    · exact (mixed hbe hao (by simpa only [add_comm b a, mul_comm (b+1) (a+1)] using hq)).elim
    · exact ⟨hao,hbo⟩

/-- The smaller coprime component is one. -/
def H1 : Prop :=
  ∀ g y z : ℕ, 1 < g → 3 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →
    (g+1)*(y*z+1) ∣ (g+y*z)^2 →
    (g*y+1)*(z+1) ∣ (g*y+z)^2 → g = z

/-- Both coprime components are nontrivial, in increasing order. -/
def H2 : Prop :=
  ∀ g x y z : ℕ, 1 < g → 3 ≤ x → x < y →
    Odd g → Odd x → Odd y → Odd z → g*y ≤ x*z → Nat.Coprime x y →
    (g*x+1)*(y*z+1) ∣ (g*x+y*z)^2 →
    (g*y+1)*(x*z+1) ∣ (g*y+x*z)^2 → g = z

theorem main : H1 → H2 → OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1.H2 := by
  intro hone hlarge g x y z hg hx hy hz hne hsort₁ hsort₂ hcop hdiv₁ hdiv₂
  have go : ∀ x y : ℕ, 0 < x → 0 < y → x < y →
      g*x ≤ y*z → g*y ≤ x*z → Nat.Coprime x y →
      (g*x+1)*(y*z+1) ∣ (g*x+y*z)^2 →
      (g*y+1)*(x*z+1) ∣ (g*y+x*z)^2 → g = z := by
    intro u v hu hv huv h₁ h₂ cop du dv
    have odd₁ := odd_components (mul_pos (by omega : 0 < g) hu) h₁ du
    have odd₂ := odd_components (mul_pos (by omega : 0 < g) hv) h₂ dv
    have og := Nat.Odd.of_mul_left odd₁.1
    have ou := Nat.Odd.of_mul_right odd₁.1
    have ov := Nat.Odd.of_mul_right odd₂.1
    have oz := Nat.Odd.of_mul_right odd₁.2
    by_cases huone : u = 1
    · subst u
      have hvthree : 3 ≤ v := by obtain ⟨k,hk⟩ := ov; omega
      exact hone g v z hg hvthree og ov oz (by simpa using h₂)
        (by simpa using du) (by simpa using dv)
    · have huthree : 3 ≤ u := by obtain ⟨k,hk⟩ := ou; omega
      exact hlarge g u v z hg huthree huv og ou ov oz h₂ cop du dv
  rcases lt_or_gt_of_ne hne with h | h
  · exact go x y hx hy h hsort₁ hsort₂ hcop hdiv₁ hdiv₂
  · exact go y x hy hx h hsort₂ hsort₁ hcop.symm hdiv₂ hdiv₁

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1
