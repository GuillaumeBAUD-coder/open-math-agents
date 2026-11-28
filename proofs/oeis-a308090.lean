import OMAStatements.S_oeis_a308090

-- Credit: @mjsechrest2
theorem OMA.solution : type_of% @OMA.S_oeis_a308090.main := by
  intro n hn ha
  by_contra hnp
  obtain ⟨d, hd, h2, hlt⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hnp
  have hf : d ∣ n.factorial := Nat.dvd_factorial (by omega) (by omega)
  have hc : d ∣ Nat.gcd (2 ^ n + n.factorial) (3 ^ n + n.factorial) :=
    (ha ▸ hd).trans (Nat.gcd_dvd_left _ _)
  have := Nat.dvd_one.mp (((by decide : Nat.Coprime 2 3).pow n n) ▸ Nat.dvd_gcd
    ((Nat.dvd_add_iff_left hf).2 (hc.trans (Nat.gcd_dvd_left _ _)))
    ((Nat.dvd_add_iff_left hf).2 (hc.trans (Nat.gcd_dvd_right _ _))))
  omega
