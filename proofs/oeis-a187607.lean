import OMAStatements.S_oeis_a187607

/-!
In one coordinate each move is -1 or +2. A coordinate path through three
squares is determined by its two successive moves and its smallest
coordinate. Three move patterns have span 2, and the fourth has span 4.
The two coordinates vary independently and the three squares are distinct.
-/

namespace QuasiBishopTours

open OMA.S_oeis_a187607 Finset

private def step {n : ℕ} (x y : Fin n) : Prop :=
  (y : ℕ) + 1 = x ∨ (x : ℕ) + 2 = y

private def valid {n : ℕ} (p : Fin 3 → Fin n) : Prop :=
  step (p 0) (p 1) ∧ step (p 1) (p 2)

private instance {n : ℕ} : DecidablePred (@valid n) := fun _ => by
  unfold valid step
  infer_instance

private def paths (n : ℕ) := Finset.univ.filter (@valid n)

private abbrev Code (n : ℕ) :=
  Fin (n-2) ⊕ (Fin (n-2) ⊕ (Fin (n-2) ⊕ Fin (n-4)))

private def decode {n : ℕ} : Code n → (Fin 3 → Fin n)
  | .inl i => ![⟨(i : ℕ)+2, by omega⟩, ⟨(i : ℕ)+1, by omega⟩, ⟨i, by omega⟩]
  | .inr (.inl i) => ![⟨(i : ℕ)+1, by omega⟩, ⟨i, by omega⟩, ⟨(i : ℕ)+2, by omega⟩]
  | .inr (.inr (.inl i)) => ![⟨i, by omega⟩, ⟨(i : ℕ)+2, by omega⟩, ⟨(i : ℕ)+1, by omega⟩]
  | .inr (.inr (.inr i)) => ![⟨i, by omega⟩, ⟨(i : ℕ)+2, by omega⟩, ⟨(i : ℕ)+4, by omega⟩]

private theorem decode_valid {n : ℕ} (c : Code n) : valid (decode c) := by
  rcases c with i | i | i | i <;> simp [decode, valid, step]

private theorem decode_injective {n : ℕ} : Function.Injective (@decode n) := by
  intro u v h
  have h0 := congrArg (fun f : Fin 3 → Fin n => (f 0 : ℕ)) h
  have h1 := congrArg (fun f : Fin 3 → Fin n => (f 1 : ℕ)) h
  have h2 := congrArg (fun f : Fin 3 → Fin n => (f 2 : ℕ)) h
  rcases u with i | i | i | i <;> rcases v with j | j | j | j <;>
    simp [decode] at h0 h1 h2 ⊢ <;> first | apply Fin.ext; omega | omega

private theorem decode_surjective {n : ℕ} (p : Fin 3 → Fin n) (hp : valid p) :
    ∃ c : Code n, decode c = p := by
  have h0 := (p 0).isLt
  have h1 := (p 1).isLt
  have h2 := (p 2).isLt
  rcases hp with ⟨h | h, h' | h'⟩
  · refine ⟨.inl ⟨(p 2).val, by omega⟩, ?_⟩
    funext i; fin_cases i <;> apply Fin.ext <;> simp [decode] <;> omega
  · refine ⟨.inr (.inl ⟨(p 1).val, by omega⟩), ?_⟩
    funext i; fin_cases i <;> apply Fin.ext <;> simp [decode] <;> omega
  · refine ⟨.inr (.inr (.inl ⟨(p 0).val, by omega⟩)), ?_⟩
    funext i; fin_cases i <;> apply Fin.ext <;> simp [decode] <;> omega
  · refine ⟨.inr (.inr (.inr ⟨(p 0).val, by omega⟩)), ?_⟩
    funext i; fin_cases i <;> apply Fin.ext <;> simp [decode] <;> omega

private theorem path_count (n : ℕ) : (paths n).card = 3*(n-2)+(n-4) := by
  have H : (univ : Finset (Code n)).card = (paths n).card := by
    apply Finset.card_bij (fun c _ => decode c)
    · intro c _; exact mem_filter.mpr ⟨mem_univ _, decode_valid c⟩
    · intro u _ v _ e; exact decode_injective e
    · intro p hp
      obtain ⟨c, hc⟩ := decode_surjective p (mem_filter.mp hp).2
      exact ⟨c, mem_univ _, hc⟩
  rw [← H]
  simp [Code]
  omega

private theorem valid_injective {n : ℕ} {p : Fin 3 → Fin n} (hp : valid p) :
    Function.Injective p := by
  obtain ⟨c, rfl⟩ := decode_surjective p hp
  intro i j h
  have e := congrArg Fin.val h
  rcases c with x | x | x | x <;> fin_cases i <;> fin_cases j <;>
    simp [decode] at e ⊢

private theorem move_iff {n : ℕ} (u v : Fin n × Fin n) :
    toZ v - toZ u ∈ moves ↔ step u.1 v.1 ∧ step u.2 v.2 := by
  simp [OMA.S_oeis_a187607.toZ, moves, Prod.ext_iff, step]
  omega

private theorem tour_iff {n : ℕ} (p : Fin 3 → Fin n × Fin n) :
    IsTour n 3 p ↔ valid (fun i => (p i).1) ∧ valid (fun i => (p i).2) := by
  constructor
  · rintro ⟨_, hm⟩
    have u := (move_iff _ _).mp (hm 0 1 (by decide))
    have v := (move_iff _ _).mp (hm 1 2 (by decide))
    exact ⟨⟨u.1, v.1⟩, ⟨u.2, v.2⟩⟩
  · rintro ⟨hx, hy⟩
    refine ⟨fun i j e => valid_injective hx (congrArg Prod.fst e), ?_⟩
    have m₁ := (move_iff (p 0) (p 1)).mpr ⟨hx.1, hy.1⟩
    have m₂ := (move_iff (p 1) (p 2)).mpr ⟨hx.2, hy.2⟩
    intro i j h
    fin_cases i <;> fin_cases j <;> first | exact m₁ | exact m₂ | norm_num at h

private theorem count (n : ℕ) : a n = (3*(n-2)+(n-4))^2 := by
  rw [← path_count, pow_two, ← Finset.card_product]
  apply Finset.card_bij (fun p _ => ((fun i => (p i).1), (fun i => (p i).2)))
  · intro p hp
    simpa [paths] using (tour_iff p).mp (mem_filter.mp hp).2
  · intro p _ q _ h
    funext i
    exact Prod.ext (congrFun (congrArg Prod.fst h) i) (congrFun (congrArg Prod.snd h) i)
  · rintro ⟨x,y⟩ h
    obtain ⟨hx,hy⟩ := mem_product.mp h
    refine ⟨fun i => (x i, y i), mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
    exact (tour_iff _).mpr ⟨(mem_filter.mp hx).2, (mem_filter.mp hy).2⟩


private theorem quadratic (n : ℕ) (hn : 3 < n) :
    (a n : ℤ) = 16*n^2 - 80*n + 100 := by
  obtain ⟨k, rfl⟩ : ∃ k, n=k+4 := ⟨n-4, by omega⟩
  rw [count, show k+4-2 = k+2 by omega, show k+4-4 = k by omega]
  push_cast
  ring

private theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 3*a (n-1) - 3*a (n-2) + a (n-3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n=k+7 := ⟨n-7, by omega⟩
  simp only [show k+7-1=k+6 by omega, show k+7-2=k+5 by omega,
    show k+7-3=k+4 by omega]
  rw [quadratic _ (by omega), quadratic _ (by omega),
    quadratic _ (by omega), quadratic _ (by omega)]
  push_cast
  ring

open PowerSeries in
private theorem generating :
    mk (fun n => (a n : ℤ)) * (1-X)^3 = X^3 * (9+9*X+19*X^2-5*X^3) := by
  let F := mk (fun n => (a n : ℤ))
  change F * _ = _
  suffices H : F - (3:ℕ) • (F*X^1) + (3:ℕ) • (F*X^2) - F*X^3 =
      (9:ℕ) • (X^3 : PowerSeries ℤ) + (9:ℕ) • X^4 + (19:ℕ) • X^5 - (5:ℕ) • X^6 by
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at H
    linear_combination H
  ext n
  simp only [map_add, map_sub, map_nsmul]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, coeff_mul_X_pow', coeff_X_pow, F, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | k
  all_goals try (solve | norm_num [count])
  simp [show 1 ≤ k+7 by omega, show 2 ≤ k+7 by omega, show 3 ≤ k+7 by omega,
    show k+7 ≠ 3 by omega, show k+7 ≠ 4 by omega,
    show k+7 ≠ 5 by omega, show k+7 ≠ 6 by omega]
  rw [quadratic _ (by omega), quadratic _ (by omega),
    quadratic _ (by omega), quadratic _ (by omega)]
  push_cast
  ring

theorem result : type_of% @OMA.S_oeis_a187607.main := ⟨quadratic, generating, recurrence⟩

end QuasiBishopTours

theorem OMA.solution : type_of% @OMA.S_oeis_a187607.main := QuasiBishopTours.result
