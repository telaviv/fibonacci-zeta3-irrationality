import FibZeta.Defs

/-!
# Root types depend only on the order (PROOF §3.1, "the type depends only on d")

For a primitive `d`-th root of unity `ζ ∈ ℂ`, the order of `w(ζ) = −ζ²` and the predicate
`α_k(ζ) = 1` are the same as for the chosen root `zetaC d = exp(2πi/d)`.  Proof: `ζ = (zetaC d)^j`
with `j` odd and coprime to `2d`; then `−ζ² = (−ζ_d²)^j` and `α_k(ζ) = α_k(ζ_d)^j`, and raising to a
power coprime to the order (which divides `2d`) preserves the order.
-/

namespace FibZeta

theorem zetaC_primitive {d : ℕ} (hd : 0 < d) : IsPrimitiveRoot (zetaC d) d := by
  unfold zetaC
  exact Complex.isPrimitiveRoot_exp d hd.ne'

/-- Every primitive `d`-th root is `(zetaC d)^j` with `j` coprime to `2d`. -/
theorem exists_coprime_pow {d : ℕ} (hd : 0 < d) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d) :
    ∃ j : ℕ, Nat.Coprime j (2 * d) ∧ ζ = zetaC d ^ j := by
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨i, -, hij⟩ := (zetaC_primitive hd).eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hcop : i.Coprime d := ((zetaC_primitive hd).pow_iff_coprime hd i).mp (hij ▸ hζ)
  rcases Nat.even_or_odd i with hev | hodd
  · -- `i` even forces `d` odd; use `i + d`
    have hdodd : Odd d := by
      rcases Nat.even_or_odd d with hd2 | hd2
      · exfalso
        have h2 : 2 ∣ Nat.gcd i d := Nat.dvd_gcd (even_iff_two_dvd.mp hev) (even_iff_two_dvd.mp hd2)
        rw [hcop] at h2; omega
      · exact hd2
    refine ⟨i + d, Nat.Coprime.mul_right ?_ ?_, ?_⟩
    · exact Nat.coprime_two_right.mpr (hev.add_odd hdodd)
    · exact Nat.coprime_add_self_left.mpr hcop
    · rw [pow_add, (zetaC_primitive hd).pow_eq_one, mul_one, hij]
  · exact ⟨i, Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hodd) hcop, hij.symm⟩

theorem orderOf_pow_of_coprime_two_mul {x : ℂ} {d j : ℕ} (hx : x ^ (2 * d) = 1)
    (hj : j.Coprime (2 * d)) : orderOf (x ^ j) = orderOf x :=
  Nat.Coprime.orderOf_pow (hj.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hx)).symm

theorem pow_eq_one_iff_of_coprime_two_mul {x : ℂ} {d j : ℕ} (hx : x ^ (2 * d) = 1)
    (hj : j.Coprime (2 * d)) : x ^ j = 1 ↔ x = 1 := by
  rw [← orderOf_eq_one_iff (x := x ^ j), orderOf_pow_of_coprime_two_mul hx hj, orderOf_eq_one_iff]

theorem odd_of_coprime_two_mul {j d : ℕ} (hj : j.Coprime (2 * d)) : Odd j :=
  Nat.coprime_two_right.mp (hj.coprime_dvd_right (dvd_mul_right 2 d))

/-- `e(ζ) = e(d)` for every primitive `d`-th root `ζ`. -/
theorem orderOf_neg_sq_of_primitive {d : ℕ} (hd : 0 < d) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d) :
    orderOf (-ζ ^ 2) = eW d := by
  obtain ⟨j, hj, rfl⟩ := exists_coprime_pow hd hζ
  have hjodd := odd_of_coprime_two_mul hj
  have hrw : -(zetaC d ^ j) ^ 2 = (-(zetaC d) ^ 2) ^ j := by
    rw [hjodd.neg_pow, ← pow_mul, ← pow_mul, mul_comm]
  have hx : (-(zetaC d) ^ 2) ^ (2 * d) = 1 := by
    rw [(even_two_mul d).neg_pow, ← pow_mul, show 2 * (2 * d) = d * 4 by ring, pow_mul,
      (zetaC_primitive hd).pow_eq_one, one_pow]
  rw [hrw, orderOf_pow_of_coprime_two_mul hx hj]
  rfl

/-- `α_k(ζ) = 1` iff `α_k(ζ_d) = 1`, for every primitive `d`-th root `ζ`. -/
theorem alpha_eq_one_iff_of_primitive {d : ℕ} (hd : 0 < d) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (k : ℕ) : (-ζ) * (-ζ ^ 2) ^ k = 1 ↔ IsAlphaRoot d k := by
  obtain ⟨j, hj, rfl⟩ := exists_coprime_pow hd hζ
  have hjodd := odd_of_coprime_two_mul hj
  have hrw : (-(zetaC d ^ j)) * (-(zetaC d ^ j) ^ 2) ^ k =
      ((-zetaC d) * (-(zetaC d) ^ 2) ^ k) ^ j := by
    have e1 : -(zetaC d ^ j) = (-zetaC d) ^ j := (hjodd.neg_pow _).symm
    have e2 : -(zetaC d ^ j) ^ 2 = (-(zetaC d) ^ 2) ^ j := by
      rw [hjodd.neg_pow, ← pow_mul, ← pow_mul, mul_comm]
    rw [e1, e2, ← pow_mul, mul_comm j k, pow_mul, ← mul_pow]
  have hx : ((-zetaC d) * (-(zetaC d) ^ 2) ^ k) ^ (2 * d) = 1 := by
    have h1 : (-zetaC d) ^ (2 * d) = 1 := by
      rw [(even_two_mul d).neg_pow, mul_comm, pow_mul, (zetaC_primitive hd).pow_eq_one, one_pow]
    have h2 : (-(zetaC d) ^ 2) ^ (2 * d) = 1 := by
      rw [(even_two_mul d).neg_pow, ← pow_mul, show 2 * (2 * d) = d * 4 by ring, pow_mul,
        (zetaC_primitive hd).pow_eq_one, one_pow]
    rw [mul_pow, h1, one_mul, ← pow_mul, mul_comm, pow_mul, h2, one_pow]
  rw [hrw, pow_eq_one_iff_of_coprime_two_mul hx hj]
  rfl

end FibZeta
