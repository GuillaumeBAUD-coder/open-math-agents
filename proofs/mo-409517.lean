import OMAStatements.S_mo_409517
import Mathlib

open Finset OMA.S_mo_409517

private theorem weight_step {p : ℕ} (hp : 1 < p) (n : ℕ) :
    weight p n = n % p + weight p (n / p) := by
  by_cases hn : n = 0
  · simp [hn, weight]
  · simp [weight, Nat.digits_eq_cons_digits_div hp hn]

private theorem a_step {p : ℕ} (hp : 1 < p) (n : ℕ) :
    a p n = (1 + (weight p n : ℤ)) * a p (n / p) := by
  by_cases hn : n = 0
  · simp [hn, a, weight, digitProduct]
  · simp [a, weight, Nat.digits_eq_cons_digits_div hp hn, digitProduct]

private def term (p n k : ℕ) (f : ℕ → ℤ) : ℤ :=
  if p ∣ n.choose k then 0 else
    (-1 : ℤ) ^ (weight p n + weight p k) * a p k * f (weight p k)

private def transform (p n : ℕ) (f : ℕ → ℤ) := ∑ k ∈ range (n+1), term p n k f

private theorem parity_sign (u v : ℕ) :
    (if Even ((u : ℤ) - v) then (1 : ℤ) else -1) = (-1 : ℤ)^(u+v) := by
  rw [neg_one_pow_eq_ite]
  congr 1
  simp [Int.even_iff, Nat.even_iff]
  omega

private theorem b_eq_transform (p n : ℕ) : b p n = transform p n (fun _ => 1) := by
  simp [b, transform, term, parity_sign]

private inductive PosPoly : (ℕ → ℤ) → Prop
  | const (c : ℕ) : PosPoly (fun _ => (c : ℤ))
  | var : PosPoly (fun x => (x : ℤ))
  | add {f g} : PosPoly f → PosPoly g → PosPoly (fun x => f x + g x)
  | mul {f g} : PosPoly f → PosPoly g → PosPoly (fun x => f x * g x)

private theorem PosPoly.nonneg {f : ℕ → ℤ} (h : PosPoly f) (x : ℕ) : 0 ≤ f x := by
  induction h with
  | const => positivity
  | var => positivity
  | add _ _ ih jh => exact add_nonneg ih jh
  | mul _ _ ih jh => exact mul_nonneg ih jh

private theorem PosPoly.shift {f : ℕ → ℤ} (h : PosPoly f) (i : ℕ) :
    PosPoly (fun x => f (x+i)) := by
  induction h with
  | const c => exact .const c
  | var => simpa using PosPoly.var.add (.const i)
  | add _ _ ih jh => exact ih.add jh
  | mul _ _ ih jh => exact ih.mul jh

private theorem PosPoly.diff {f : ℕ → ℤ} (h : PosPoly f) :
    PosPoly (fun x => f (x+1)-f x) := by
  induction h with
  | const c => simpa using PosPoly.const 0
  | var => simpa using PosPoly.const 1
  | add hf hg ih jh =>
    convert ih.add jh using 1
    ext x
    dsimp
    ring
  | mul hf hg ih jh =>
    convert (ih.mul (hg.shift 1)).add (hf.mul jh) using 1
    ext x
    dsimp
    ring

private def alt (d : ℕ) (f : ℕ → ℤ) (x : ℕ) :=
  ∑ j ∈ range (d+1), (-1 : ℤ)^(d+j) * f (x+j)

private theorem alt_succ (d : ℕ) (f : ℕ → ℤ) (x : ℕ) :
    alt (d+1) f x = f (x+(d+1))-alt d f x := by
  rw [alt, sum_range_succ, alt]
  simp only [show d+1+(d+1) = 2*(d+1) by omega, pow_mul]
  norm_num
  simp only [show ∀ j, d+1+j = d+j+1 by omega, pow_succ, mul_neg_one, neg_mul,
    sum_neg_distrib]
  ring

private theorem alt_nonneg {f : ℕ → ℤ} (hf : PosPoly f) (d : ℕ) : PosPoly (alt d f) := by
  induction d using Nat.twoStepInduction with
  | zero =>
    convert hf using 1
    ext x
    simp [alt]
  | one =>
    convert hf.diff using 1
    ext x
    rw [show 1 = 0+1 by rfl, alt_succ]
    simp [alt]
  | more d ih _ =>
    convert ((hf.diff.shift (d+1)).add ih) using 1
    ext x
    rw [alt_succ, alt_succ]
    rw [show x + (d+1) + 1 = x+(d+1+1) by omega]
    ring

private theorem positive_step {f : ℕ → ℤ} (hf : PosPoly f) (h0 : 0 < f 0) (d : ℕ) :
    0 < alt d (fun x => (1+(x:ℤ))*f x) 0 := by
  let g := fun x : ℕ => (1+(x:ℤ))*f x
  have hg : PosPoly g := ((PosPoly.const 1).add PosPoly.var).mul hf
  induction d using Nat.twoStepInduction with
  | zero => simpa [alt] using h0
  | one =>
    have hh := hf.diff.nonneg 0
    change 0 ≤ f 1 - f 0 at hh
    rw [show 1 = 0+1 by rfl, alt_succ]
    simp [alt]
    omega
  | more d ih _ =>
    have hh := hg.diff.nonneg (d+1)
    change 0 ≤ g (d+1+1)-g (d+1) at hh
    change 0 < alt (d+1+1) g 0
    change 0 < alt d g 0 at ih
    rw [alt_succ, alt_succ]
    simp only [zero_add]
    omega

private theorem blocks (f : ℕ → ℤ) (p t : ℕ) :
    ∑ k ∈ range (t*p), f k = ∑ u ∈ range t, ∑ j ∈ range p, f (u*p+j) := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

private theorem support {p n k : ℕ} (hp : p.Prime) :
    p ∣ n.choose k ↔ n % p < k % p ∨ p ∣ (n/p).choose (k/p) := by
  let : Fact p.Prime := ⟨hp⟩
  rw [Choose.choose_modEq_choose_mod_mul_choose_div_nat.dvd_iff (dvd_refl p), hp.dvd_mul]
  by_cases h : n%p < k%p
  · simp [h, Nat.choose_eq_zero_of_lt h]
  · have hc := Nat.Prime.coprime_choose_of_lt hp (Nat.mod_lt n hp.pos) (by omega : k%p ≤ n%p)
    simp [h, (Nat.Prime.coprime_iff_not_dvd hp).mp hc]


private theorem reduce {p : ℕ} (hp : p.Prime) (n : ℕ) (f : ℕ → ℤ) :
    transform p n f = transform p (n/p)
      (alt (n%p) (fun x => (1+(x:ℤ))*f x)) := by
  unfold transform
  have hn := Nat.lt_mul_div_succ n hp.pos
  rw [Nat.mul_comm p] at hn
  have pad : ∑ k ∈ range (n+1), term p n k f =
      ∑ k ∈ range ((n/p+1)*p), term p n k f := by
    apply sum_subset (range_mono (by omega))
    intro k _ hk
    simp only [mem_range] at hk
    simp [term, Nat.choose_eq_zero_of_lt (by omega : n < k)]
  rw [pad, blocks]
  apply sum_congr rfl
  intro u _
  have dlt := Nat.mod_lt n hp.pos
  have divmod (j : ℕ) (hj : j < p) :
       (u*p+j)/p = u ∧ (u*p+j)%p = j := by
    rw [Nat.mul_comm u p, Nat.mul_add_div hp.pos, Nat.mul_add_mod,
      Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, Nat.add_zero]
    exact ⟨rfl,rfl⟩
  have cut : ∑ j ∈ range (n%p+1), term p n (u*p+j) f =
      ∑ j ∈ range p, term p n (u*p+j) f := by
    apply sum_subset (range_mono (by omega))
    intro j hj hj'
    simp only [mem_range] at hj hj'
    have hdvd : p ∣ n.choose (u*p+j) := (support hp).mpr
      (Or.inl (by rw [(divmod j hj).2]; omega))
    simp [term, hdvd]
  rw [← cut]
  by_cases ht : p ∣ (n/p).choose u
  · have hz (j) (hj : j ∈ range (n%p+1)) : term p n (u*p+j) f = 0 := by
      have hj' := mem_range.mp hj
      have hdvd : p ∣ n.choose (u*p+j) := (support hp).mpr
        (Or.inr (by simpa only [(divmod j (by omega)).1] using ht))
      simp [term, hdvd]
    rw [sum_eq_zero hz]
    simp [term, ht]
  · simp only [term, ht, if_false, alt, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    obtain ⟨hdiv,hmod⟩ := divmod j (by omega)
    have hnondvd : ¬ p ∣ n.choose (u*p+j) := by
      rw [support hp, hdiv, hmod]
      omega
    simp only [hnondvd, if_false]
    rw [a_step hp.one_lt (u*p+j), weight_step hp.one_lt (u*p+j), hdiv,hmod,
      weight_step hp.one_lt n]
    rw [show n%p+weight p (n/p)+(j+weight p u) =
        (weight p (n/p)+weight p u)+(n%p+j) by omega, pow_add, add_comm j (weight p u)]
    ring

private theorem pos_transform {p : ℕ} (hp : p.Prime) (n : ℕ) (f : ℕ → ℤ)
    (hf : PosPoly f) (h0 : 0 < f 0) : 0 < transform p n f := by
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hn : n = 0
    · simpa [hn,transform,term,a,weight,digitProduct,hp.not_dvd_one] using h0
    · rw [reduce hp]
      exact ih _ (Nat.div_lt_self (by omega) hp.one_lt) _
        (alt_nonneg (((PosPoly.const 1).add PosPoly.var).mul hf) _)
        (positive_step hf h0 _)

theorem OMA.solution : type_of% @OMA.S_mo_409517.main := by
  intro p n hp
  rw [b_eq_transform]
  exact pos_transform hp n (fun _ => 1) (PosPoly.const 1) (by decide)
