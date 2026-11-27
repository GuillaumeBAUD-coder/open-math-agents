import OMAReductions.R_OeisA287616_conjecture_R1
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The two middle-coordinate improvements from Cao, Guo, Qiu, Feng and Gao
(arXiv:2606.26035, Lemma 9) are verified, together with the normalization
of parity pattern (even, even, odd) by the same norm-preserving move.
The remaining mixed-parity and all-odd cases are separated.
-/

namespace OMA.R_OeisA287616_conjecture_R1_H2_R1

private theorem primitive_from_scaled_inverse {n x y z d : ℕ} {u v w a b c : ℤ}
    (hd : d = 2 ∨ d = 3 ∨ d = 4)
    (hn : 15 * x ^ 2 + 5 * y ^ 2 + 3 * z ^ 2 = 120 * n + 23)
    (hprim : Int.gcd u (Int.gcd v w) = 1)
    (hx : x = a.natAbs) (hy : y = b.natAbs) (hz : z = c.natAbs)
    (hback : ∀ p : ℤ, p ∣ a → p ∣ b → p ∣ c →
      p ∣ (d : ℤ) * u ∧ p ∣ (d : ℤ) * v ∧ p ∣ (d : ℤ) * w) :
    x.gcd (y.gcd z) = 1 := by
  refine Nat.eq_one_iff_not_exists_prime_dvd.mpr ?_
  intro p hp hpg
  have px := Nat.dvd_trans hpg (Nat.gcd_dvd_left x (y.gcd z))
  have pyz := Nat.dvd_trans hpg (Nat.gcd_dvd_right x (y.gcd z))
  have py := Nat.dvd_trans pyz (Nat.gcd_dvd_left y z)
  have pz := Nat.dvd_trans pyz (Nat.gcd_dvd_right y z)
  have pq : p ∣ 120 * n + 23 := by
    rw [← hn]
    have dx : p ∣ 15 * x ^ 2 := by
      simpa only [pow_two] using dvd_mul_of_dvd_right (dvd_mul_of_dvd_left px x) 15
    have dy : p ∣ 5 * y ^ 2 := by
      simpa only [pow_two] using dvd_mul_of_dvd_right (dvd_mul_of_dvd_left py y) 5
    have dz : p ∣ 3 * z ^ 2 := by
      simpa only [pow_two] using dvd_mul_of_dvd_right (dvd_mul_of_dvd_left pz z) 3
    exact Nat.dvd_add (Nat.dvd_add dx dy) dz
  have hp2 : p ≠ 2 := fun he => (by omega : ¬ 2 ∣ 120 * n + 23) (he ▸ pq)
  have hp3 : p ≠ 3 := fun he => (by omega : ¬ 3 ∣ 120 * n + 23) (he ▸ pq)
  have hpd : ¬ (p : ℤ) ∣ (d : ℤ) := by
    intro h
    have hn : p ∣ d := by exact_mod_cast h
    rcases hd with rfl | rfl | rfl
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hn)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hn)
    · have htwo : p ∣ 2 := (hp.dvd_mul.1 (show p ∣ 2 * 2 from hn)).elim id id
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp htwo)
  have pin : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have ha : (p : ℤ) ∣ a := by
    exact Int.ofNat_dvd_left.mpr (by simpa only [hx] using px)
  have hb : (p : ℤ) ∣ b := by
    exact Int.ofNat_dvd_left.mpr (by simpa only [hy] using py)
  have hc : (p : ℤ) ∣ c := by
    exact Int.ofNat_dvd_left.mpr (by simpa only [hz] using pz)
  obtain ⟨hu, hv, hw⟩ := hback p ha hb hc
  have h := Int.dvd_gcd ((pin.dvd_mul.1 hu).resolve_left hpd)
    (Int.dvd_coe_gcd ((pin.dvd_mul.1 hv).resolve_left hpd) ((pin.dvd_mul.1 hw).resolve_left hpd))
  rw [hprim] at h
  exact hp.not_dvd_one h

private theorem pair_uv (u v w : ℕ) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (he : (u : ℤ) % 2 = ((v : ℤ) * s) % 2)
    (n : ℕ) (hn : 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23)
    (hprim : u.gcd (v.gcd w) = 1) :
    let a := ((u : ℤ) + (v : ℤ) * s) / 2
    let b := (3 * (u : ℤ) - (v : ℤ) * s) / 2
    15 * a.natAbs ^ 2 + 5 * b.natAbs ^ 2 + 3 * w ^ 2 = 120 * n + 23 ∧
      a.natAbs.gcd (b.natAbs.gcd w) = 1 := by
  dsimp
  let U : ℤ := u
  let V : ℤ := v
  let W : ℤ := w
  let a := (U + V * s) / 2
  let b := (3 * U - V * s) / 2
  have ha : 2 * a = U + V * s := by dsimp [a, U, V]; omega
  have hb : 2 * b = 3 * U - V * s := by dsimp [b, U, V]; omega
  have hn' : 15 * U ^ 2 + 5 * V ^ 2 + 3 * W ^ 2 = 120 * (n : ℤ) + 23 := by
    dsimp [U, V, W]; exact_mod_cast hn
  have hsq : s ^ 2 = 1 := hs.elim (fun h => by simp [h]) (fun h => by simp [h])
  have hn'' : 15 * a ^ 2 + 5 * b ^ 2 + 3 * W ^ 2 = 120 * (n : ℤ) + 23 := by
    have hscaled : 4 * (15 * a ^ 2 + 5 * b ^ 2 + 3 * W ^ 2 - (120 * (n : ℤ) + 23)) = 0 := by
      linear_combination 15 * (2 * a + (U + V * s)) * ha +
        5 * (2 * b + (3 * U - V * s)) * hb + 4 * hn' + 20 * V ^ 2 * hsq
    omega
  have hnat : 15 * a.natAbs ^ 2 + 5 * b.natAbs ^ 2 + 3 * w ^ 2 = 120 * n + 23 := by
    have hcast (x : ℤ) : (x.natAbs : ℤ) ^ 2 = x ^ 2 := by simp
    exact_mod_cast (show 15 * (a.natAbs : ℤ) ^ 2 + 5 * (b.natAbs : ℤ) ^ 2 + 3 * (w : ℤ) ^ 2 =
      120 * (n : ℤ) + 23 by simpa only [hcast] using hn'')
  have hprim' : Int.gcd U (Int.gcd V W) = 1 := by simpa [U, V, W] using hprim
  refine ⟨hnat, primitive_from_scaled_inverse (d := 2) (a := a) (b := b) (c := W)
    (Or.inl rfl) hnat hprim' rfl rfl rfl ?_⟩
  intro p hpa hpb hpc
  have h1 : 2 * U = a + b := by omega
  have h2 : 2 * (V * s) = 3 * a - b := by omega
  refine ⟨h1 ▸ dvd_add hpa hpb, ?_, dvd_mul_of_dvd_right hpc 2⟩
  have hps : p ∣ 2 * (V * s) := h2 ▸ dvd_sub (dvd_mul_of_dvd_right hpa 3) hpb
  rcases hs with h | h
  · simpa [h] using hps
  · simpa [h] using hps


private theorem natAbs_odd {z : ℤ} (hz : z % 2 = 1) : z.natAbs % 2 = 1 := by
  rcases le_total 0 z with hp | hn
  · have he := Int.natAbs_of_nonneg hp
    omega
  · have he := Int.ofNat_natAbs_of_nonpos hn
    omega

private theorem sq_mod_eight (x : ℕ) :
    x ^ 2 % 8 = if x % 2 = 1 then 1 else if x % 4 = 2 then 4 else 0 := by
  rw [Nat.pow_mod, show x % 2 = (x % 8) % 2 by omega,
    show x % 4 = (x % 8) % 4 by omega]
  have he : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨
      x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by omega
  rcases he with he | he | he | he | he | he | he | he <;> rw [he] <;> decide

set_option maxHeartbeats 4000000 in
private theorem odd_third_of_even_first {n u v w : ℕ}
    (hn : 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23)
    (hu : u % 2 = 0) : v % 2 = 0 ∧ w % 2 = 1 ∧ (u + v) % 4 = 2 := by
  have h8 : (15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2) % 8 = 7 := by rw [hn]; omega
  have U := sq_mod_eight u
  have V := sq_mod_eight v
  have W := sq_mod_eight w
  simp only [hu, Nat.zero_ne_one, if_false] at U
  by_cases hu4 : u % 4 = 2 <;> simp only [hu4, if_true, if_false] at U <;>
    by_cases hv : v % 2 = 1 <;> simp only [hv, if_true, if_false] at V <;>
    by_cases hv4 : v % 4 = 2 <;> (try simp only [hv4, if_true, if_false] at V) <;>
    by_cases hw : w % 2 = 1 <;> simp only [hw, if_true, if_false] at W <;>
    by_cases hw4 : w % 4 = 2 <;> (try simp only [hw4, if_true, if_false] at W) <;> omega

private theorem oddify_third {n u v w : ℕ}
    (hn : 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23)
    (hprim : u.gcd (v.gcd w) = 1) (hu : u % 2 = 0) :
    ∃ x y z : ℕ, 15 * x ^ 2 + 5 * y ^ 2 + 3 * z ^ 2 = 120 * n + 23 ∧
      x.gcd (y.gcd z) = 1 ∧ x % 2 = 1 ∧ y % 2 = 1 ∧ z % 2 = 1 := by
  obtain ⟨hv, hw, hs⟩ := odd_third_of_even_first hn hu
  have he : (u : ℤ) % 2 = ((v : ℤ) * 1) % 2 := by omega
  obtain ⟨hq, hp⟩ := pair_uv u v w 1 (Or.inl rfl) he n hn hprim
  refine ⟨_, _, w, hq, hp, natAbs_odd ?_, natAbs_odd ?_, hw⟩ <;>
    simp only [mul_one] <;> omega

private theorem repair_middle {n u v w : ℕ}
    (hn : 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23)
    (hprim : u.gcd (v.gcd w) = 1) (hu : u % 2 = 1) (hv : v % 6 = 5)
    (hmove : u % 4 ≠ v % 4 ∨ 3 * u < v) :
    ∃ x y : ℕ, 15 * x ^ 2 + 5 * y ^ 2 + 3 * w ^ 2 = 120 * n + 23 ∧
      x.gcd (y.gcd w) = 1 ∧ x % 2 = 1 ∧ y % 6 = 1 := by
  by_cases he : u % 4 ≠ v % 4
  · have hpar : (u : ℤ) % 2 = ((v : ℤ) * (-1)) % 2 := by omega
    obtain ⟨hq, hp⟩ := pair_uv u v w (-1) (Or.inr rfl) hpar n hn hprim
    refine ⟨_, _, hq, hp, natAbs_odd ?_, ?_⟩
    · simp only [mul_neg, mul_one]
      omega
    · have heq := Int.natAbs_of_nonneg (show 0 ≤ (3 * (u : ℤ) - v * (-1)) / 2 by omega)
      omega
  · have hlt : 3 * u < v := hmove.resolve_left he
    have hpar : (u : ℤ) % 2 = ((v : ℤ) * 1) % 2 := by omega
    obtain ⟨hq, hp⟩ := pair_uv u v w 1 (Or.inl rfl) hpar n hn hprim
    refine ⟨_, _, hq, hp, natAbs_odd ?_, ?_⟩
    · simp only [mul_one]
      omega
    · have heq := Int.ofNat_natAbs_of_nonpos (show (3 * (u : ℤ) - v * 1) / 2 ≤ 0 by omega)
      omega

def H1 : Prop :=
  let allOdd (u v w : ℕ) := u % 2 = 1 ∧ v % 2 = 1 ∧ w % 2 = 1
  let rank (n u v w : ℕ) :=
    let badV := if allOdd u v w ∧ v % 6 = 1 then 0 else 1
    let badW := if allOdd u v w ∧ w % 10 = 1 then 0 else 1
    let regretV := if allOdd u v w ∧ u % 4 ≠ v % 4 then 0 else badV
    let regretW := if (u + w) % 3 = 0 then 0 else badW
    let evenPenalty := if allOdd u v w then 0 else 2
    (5 * (badV + badW) + regretV + regretW + evenPenalty) *
      (3 * (120 * n + 23) + 1) + u + v + w
  ∀ n u v w : ℕ,
    15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23 →
    u.gcd (v.gcd w) = 1 →
    u % 2 = 1 → ¬ allOdd u v w →
    ¬ (u % 2 = 1 ∧ v % 6 = 1 ∧ w % 10 = 1) →
    ∃ u' v' w' : ℕ,
      15 * u' ^ 2 + 5 * v' ^ 2 + 3 * w' ^ 2 = 120 * n + 23 ∧
      u'.gcd (v'.gcd w') = 1 ∧ rank n u' v' w' < rank n u v w

def H2 : Prop :=
  let allOdd (u v w : ℕ) := u % 2 = 1 ∧ v % 2 = 1 ∧ w % 2 = 1
  let rank (n u v w : ℕ) :=
    let badV := if allOdd u v w ∧ v % 6 = 1 then 0 else 1
    let badW := if allOdd u v w ∧ w % 10 = 1 then 0 else 1
    let regretV := if allOdd u v w ∧ u % 4 ≠ v % 4 then 0 else badV
    let regretW := if (u + w) % 3 = 0 then 0 else badW
    let evenPenalty := if allOdd u v w then 0 else 2
    (5 * (badV + badW) + regretV + regretW + evenPenalty) *
      (3 * (120 * n + 23) + 1) + u + v + w
  ∀ n u v w : ℕ,
    15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23 →
    u.gcd (v.gcd w) = 1 →
    allOdd u v w → ¬ (v % 6 = 5 ∧ (u % 4 ≠ v % 4 ∨ 3 * u < v)) →
    ¬ (u % 2 = 1 ∧ v % 6 = 1 ∧ w % 10 = 1) →
    ∃ u' v' w' : ℕ,
      15 * u' ^ 2 + 5 * v' ^ 2 + 3 * w' ^ 2 = 120 * n + 23 ∧
      u'.gcd (v'.gcd w') = 1 ∧ rank n u' v' w' < rank n u v w


private theorem scaled_drop {n u v w x y z S T : ℕ}
    (h : 15 * x ^ 2 + 5 * y ^ 2 + 3 * z ^ 2 = 120 * n + 23) (hle : S < T) :
    S * (3 * (120 * n + 23) + 1) + x + y + z <
      T * (3 * (120 * n + 23) + 1) + u + v + w := by
  have hx := Nat.le_self_pow (by decide : 2 ≠ 0) x
  have hy := Nat.le_self_pow (by decide : 2 ≠ 0) y
  have hz := Nat.le_self_pow (by decide : 2 ≠ 0) z
  have hsum : x + y + z < 3 * (120 * n + 23) + 1 := by omega
  have hscale := Nat.mul_le_mul_right (3 * (120 * n + 23) + 1) (show S + 1 ≤ T by omega)
  rw [Nat.add_mul, Nat.one_mul] at hscale
  omega

theorem main : H1 → H2 → OMA.R_OeisA287616_conjecture_R1.H2 := by
  intro hMixed hResidual n u v w hn hp hb
  by_cases hu : u % 2 = 0
  · obtain ⟨x, y, z, hq, hprim, hx, hy, hz⟩ := oddify_third hn hp hu
    refine ⟨x, y, z, hq, hprim, scaled_drop hq ?_⟩
    simp only [hu, hx, hy, hz, Nat.zero_ne_one, false_and, true_and, and_true, if_true, if_false]
    split_ifs <;> omega
  · have huOdd : u % 2 = 1 := by omega
    by_cases hodd : u % 2 = 1 ∧ v % 2 = 1 ∧ w % 2 = 1
    · by_cases hV : v % 6 = 5 ∧ (u % 4 ≠ v % 4 ∨ 3 * u < v)
      · obtain ⟨x, y, hq, hprim, hx, hy⟩ := repair_middle hn hp huOdd hV.1 hV.2
        have hyOdd : y % 2 = 1 := by omega
        have hvBad : v % 6 ≠ 1 := by omega
        refine ⟨x, y, w, hq, hprim, scaled_drop hq ?_⟩
        simp only [huOdd, hodd.2.1, hodd.2.2, hx, hyOdd, hy, hvBad,
          true_and, and_true, and_false, if_true, if_false]
        split_ifs <;> omega
      · exact hResidual n u v w hn hp hodd hV hb
    · exact hMixed n u v w hn hp huOdd hodd hb

end OMA.R_OeisA287616_conjecture_R1_H2_R1
