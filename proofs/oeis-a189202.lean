import OMAStatements.S_oeis_a189202
import Mathlib

open OMA.S_oeis_a189202

namespace OMA.A189202

lemma separated_digits {b k x y : ℕ} (hb : 1 < b) (hy : 0 < y)
    (hlen : (b.digits x).length ≤ k) (hdiv : b^k ∣ y) :
    ds b (x+y) = ds b x + ds b y := by
  obtain ⟨z,rfl⟩ := hdiv
  have hz : 0 < z := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hy
  have h := Nat.digits_append_zeroes_append_digits (b := b) (n := x) (m := z)
    (k := k-(b.digits x).length) hb hz
  rw [Nat.add_sub_of_le hlen] at h
  simp [ds, ← h, Nat.digits_base_pow_mul hb hz]

lemma denominator_dvd (n x : ℕ) (hn : 2 ≤ n) : n-1 ∣ ds n (x*(n-1)) := by
  by_cases h : n = 2
  · simp [h]
  have hm : n % (n-1) = 1 := by
    rw [Nat.mod_eq_sub_mod (by omega : n-1 ≤ n), Nat.mod_eq_of_lt (by omega)]
    omega
  exact (Nat.dvd_iff_dvd_digits_sum (n-1) n hm _).mp (dvd_mul_left _ _)

lemma even_of_same_remainder {x y : ℕ} (h : x%2 = y%2) : Even (x+y) := by
  rw [Nat.even_iff]
  omega

lemma exists_admissible (n : ℕ) (hn : 2 ≤ n) : ∃ m, admissible n m := by
  let M (i : ℕ) := (2*n)^i
  let x (i : ℕ) := M i * (n-1)
  let y (i : ℕ) := 2*M i * (n-1)
  let r (a : ℕ) : Fin 2 := ⟨a%2, by omega⟩
  let color (i : ℕ) := (r (ds 2 (x i)), r (ds n (y i)/(n-1)))
  -- Infinitely many blocks share both parities, so the second can start beyond
  -- all digits of the first in both bases.
  obtain ⟨v,hv⟩ := Finite.exists_infinite_fiber color
  have hf : (color ⁻¹' {v}).Infinite := Set.infinite_coe_iff.mp hv
  obtain ⟨i,hi⟩ := hf.nonempty
  obtain ⟨j,hj,hfar⟩ := hf.exists_gt ((Nat.digits 2 (x i)).length + (Nat.digits n (y i)).length)
  change color i = v at hi
  change color j = v at hj
  have equalColor := hi.trans hj.symm
  have hx : ds 2 (x i) % 2 = ds 2 (x j) % 2 :=
    congrArg (fun t : Fin 2 × Fin 2 => t.1.val) equalColor
  have hy : ds n (y i)/(n-1) % 2 = ds n (y j)/(n-1) % 2 :=
    congrArg (fun t : Fin 2 × Fin 2 => t.2.val) equalColor
  have hn' : 0 < n-1 := by omega
  have hm (e : ℕ) : 0 < M e := by dsimp [M]; positivity
  have dx : 2^j ∣ x j := by
    use n^j*(n-1)
    simp [x,M,mul_pow,mul_assoc]
  have dy : n^j ∣ y j := by
    use 2*2^j*(n-1)
    dsimp [y,M]
    rw [mul_pow]
    ring
  have ex := separated_digits (b := 2) (k := j) (x := x i) (y := x j)
    (by decide) (Nat.mul_pos (hm j) hn') (by omega) dx
  have ey := separated_digits (b := n) (k := j) (x := y i) (y := y j)
    (by omega) (Nat.mul_pos (Nat.mul_pos (by decide) (hm j)) hn') (by omega) dy
  refine ⟨M i + M j, by exact Nat.add_pos_left (hm i) _, ?_, ?_⟩
  · rw [Nat.add_mul]
    change Even (ds 2 (x i+x j))
    rw [ex]
    exact even_of_same_remainder hx
  · rw [Nat.mul_add, Nat.add_mul]
    change Even (ds n (y i+y j)/(n-1))
    rw [ey, Nat.add_div_of_dvd_right (denominator_dvd n (2*M i) hn)]
    exact even_of_same_remainder hy

end OMA.A189202

theorem OMA.solution : type_of% @OMA.S_oeis_a189202.main := by
  intro n hn
  classical
  have h := OMA.A189202.exists_admissible n hn
  rw [term, dif_pos h]
  exact (Nat.find_spec h).1
