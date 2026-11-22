import PrimeEndpoint
import Mathlib.NumberTheory.Primorial

open scoped BigOperators
open ArithmeticFunction

namespace Goldbach.PrimePowerError
noncomputable section

/-- A composite prime power has a prime base and exponent at least two. -/
private theorem power_witness {n : ℕ} (hn : IsPrimePow n) (hc : ¬ n.Prime) :
    n.minFac.Prime ∧ ∃ k : ℕ, 2 ≤ k ∧ n.minFac ^ k = n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  rw [Nat.pow_minFac hk.ne', hp.minFac_eq]
  refine ⟨hp, k, ?_, rfl⟩
  by_contra! hk'
  have hk1 : k = 1 := by omega
  exact hc (by simpa [hk1] using hp)

/-- In a set of multiplicative width strictly less than two, fixing a prime
    base determines at most one positive power belonging to the set. -/
private theorem one_power {p k l : ℕ} (hp : 2 ≤ p)
    (hkl : p ^ k < 2 * p ^ l) (hlk : p ^ l < 2 * p ^ k) : k = l := by
  have step {i j : ℕ} (h : i < j) : 2 * p ^ i ≤ p ^ j := calc
    _ ≤ p * p ^ i := Nat.mul_le_mul_right _ hp
    _ = p ^ (i+1) := (pow_succ' _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) h
  rcases lt_trichotomy k l with h | h | h
  · exact False.elim (not_lt_of_ge (step h) hlk)
  · exact h
  · exact False.elim (not_lt_of_ge (step h) hkl)

theorem theta_le (B : ℕ) :
    (∑ p in (Finset.range (B+1)).filter Nat.Prime, Real.log (p : ℝ)) ≤
      (B : ℝ) * Real.log 4 := by
  have hpos : (0 : ℝ) < (primorial B : ℝ) := by exact_mod_cast primorial_pos B
  have hle : (primorial B : ℝ) ≤ (4 : ℝ) ^ B := by exact_mod_cast primorial_le_4_pow B
  calc
    _ = Real.log (primorial B : ℝ) := by
      rw [primorial, Nat.cast_prod, Real.log_prod]
      intro n hn
      exact_mod_cast (Finset.mem_filter.mp hn).2.ne_zero
    _ ≤ Real.log ((4 : ℝ)^B) := Real.log_le_log hpos hle
    _ = _ := Real.log_pow _ _

/-- Prime-only sum differs from its von Mangoldt counterpart by at most
    W·B·log 4 if bad prime powers have prime base ≤ B. -/
theorem pollution_of_base_bound (S : Finset ℕ) (w : ℕ → ℝ) (W : ℝ) (B : ℕ)
    (hW : 0 ≤ W) (hw : ∀ n ∈ S, |w n| ≤ W)
    (hRatio : ∀ n ∈ S, ∀ m ∈ S, n < 2*m)
    (hB : ∀ n ∈ S, IsPrimePow n → ¬ n.Prime → n.minFac ≤ B) :
    |(∑ n in S, vonMangoldt n * w n) -
       ∑ p in S.filter Nat.Prime, Real.log (p : ℝ) * w p| ≤
       W * ((B : ℝ) * Real.log 4) := by
  classical
  let bad := S.filter (fun n => IsPrimePow n ∧ ¬ n.Prime)
  have hbad {n : ℕ} (hn : n ∈ bad) : n ∈ S ∧ IsPrimePow n ∧ ¬ n.Prime :=
    Finset.mem_filter.mp hn
  have huniq : Set.InjOn Nat.minFac (↑bad : Set ℕ) := by
    intro n hn m hm he
    obtain ⟨hp,k,_,hpk⟩ := power_witness (hbad hn).2.1 (hbad hn).2.2
    obtain ⟨_,l,_,hpl⟩ := power_witness (hbad hm).2.1 (hbad hm).2.2
    rw [← he] at hpl
    have keq : k = l := one_power hp.two_le
      (by rw [hpk,hpl]; exact hRatio _ (hbad hn).1 _ (hbad hm).1)
      (by rw [hpl,hpk]; exact hRatio _ (hbad hm).1 _ (hbad hn).1)
    exact hpk.symm.trans (keq ▸ hpl)
  have hsub : bad.image Nat.minFac ⊆ (Finset.range (B+1)).filter Nat.Prime := by
    intro p hp
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hp
    have hn' := hbad hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le
      (hB n hn'.1 hn'.2.1 hn'.2.2)), (power_witness hn'.2.1 hn'.2.2).1⟩
  have hremove :
      (∑ n in S, vonMangoldt n * w n) -
      (∑ p in S.filter Nat.Prime, Real.log (p : ℝ) * w p) =
      ∑ n in bad, vonMangoldt n * w n := by
    simp only [bad, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : n.Prime
    · simp [hp, vonMangoldt_apply_prime hp]
    · by_cases hpp : IsPrimePow n
      · simp [hp,hpp]
      · simp [hp,hpp,vonMangoldt_eq_zero_iff.mpr hpp]
  rw [hremove]
  calc
    _ ≤ ∑ n in bad, |vonMangoldt n * w n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n in bad, W * Real.log (n.minFac : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hv := (vonMangoldt_nonneg (n:=n))
      rw [abs_mul, abs_of_nonneg hv, mul_comm]
      have hv' : vonMangoldt n = Real.log (n.minFac : ℝ) := by
        rw [vonMangoldt_apply, if_pos (hbad hn).2.1]
      rw [← hv']
      exact mul_le_mul_of_nonneg_right (hw n (hbad hn).1) hv
    _ = W * ∑ p in bad.image Nat.minFac, Real.log (p : ℝ) := by
      rw [Finset.sum_image huniq, Finset.mul_sum]
    _ ≤ W * ((B : ℝ) * Real.log 4) := by
      apply mul_le_mul_of_nonneg_left _ hW
      apply le_trans _ (theta_le B)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
        Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))

/-- Explicit prime-power pollution bound in the balanced window, for each X. -/
theorem pollution (X : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ n ∈ S, |w n| ≤ W)
    (hX : ∀ n ∈ S, n ≤ X) (hRatio : ∀ n ∈ S, ∀ m ∈ S, n < 2*m) :
    |(∑ n in S, vonMangoldt n * w n) -
       ∑ p in S.filter Nat.Prime, Real.log (p : ℝ) * w p| ≤
       W * ((Nat.sqrt X : ℝ) * Real.log 4) := by
  apply pollution_of_base_bound S w W (Nat.sqrt X) hW hw hRatio
  intro n hn hpp hc
  obtain ⟨hp,k,hk,hpk⟩ := power_witness hpp hc
  apply Nat.le_sqrt'.mpr
  calc
    _ ≤ n.minFac ^ k := Nat.pow_le_pow_right hp.pos hk
    _ = n := hpk
    _ ≤ X := hX n hn

private theorem exponent_plus_one_le (e : ℕ) : e + 1 ≤ 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ]
    omega

/-- The number of divisors of a rough number is small even when the cutoff
    depends on the target: the exponent-wise bound holds at every prime. -/
theorem divisor_count_pow_le (m r : ℕ) (hm : m ≠ 0)
    (hrough : ∀ p ∈ m.primeFactors, 2^r ≤ p) : m.divisors.card ^ r ≤ m := by
  rw [Nat.card_divisors hm, ← Finset.prod_pow]
  calc
    _ ≤ ∏ p in m.primeFactors, p ^ m.factorization p := by
      apply Finset.prod_le_prod' 
      intro p hp
      have h := Nat.pow_le_pow_left (exponent_plus_one_le (m.factorization p)) r
      calc
        _ ≤ (2 ^ m.factorization p) ^ r := h
        _ = (2 ^ r) ^ m.factorization p := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ _ := Nat.pow_le_pow_left (hrough p hp) _
    _ = m := Nat.factorization_prod_pow_eq_self hm

/-- If each prime divisor of m is at least y and m ≤ y^K, the prime
    factorization has total exponent at most K, and m has at most 2^K divisors. -/
theorem rough_divisor_budget (m K : ℕ) (y : ℝ) (hm : m ≠ 0) (hy : 1 < y)
    (hsize : (m : ℝ) ≤ y ^ K) (hbase : ∀ p ∈ m.primeFactors, y ≤ (p : ℝ)) :
    m.divisors.card ≤ 2 ^ K := by
  let e := ∑ p in m.primeFactors, m.factorization p
  have hval : (∏ p in m.primeFactors, p ^ m.factorization p) = m :=
    Nat.factorization_prod_pow_eq_self hm
  have he : y ^ e ≤ (m : ℝ) := calc
    _ = ∏ p in m.primeFactors, y ^ m.factorization p :=
      (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ ≤ ∏ p in m.primeFactors, (p : ℝ) ^ m.factorization p := by
      apply Finset.prod_le_prod (fun p _ => pow_nonneg (by linarith) _)
      exact fun p hp => pow_le_pow_left (by linarith) (hbase p hp) _
    _ = _ := by exact_mod_cast hval
  have heK : e ≤ K := (pow_le_pow_iff_right hy).mp (he.trans hsize)
  rw [Nat.card_divisors hm]
  calc
    _ ≤ ∏ p in m.primeFactors, 2 ^ m.factorization p :=
      Finset.prod_le_prod' fun p _ => exponent_plus_one_le _
    _ = 2^e := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := Nat.pow_le_pow_right (by decide) heK

/-- The precise signed truncated divisor weight in Section 5. The balanced
    support restriction is carried by the outer finset. -/
def sieveWeight (N : ℕ) (y t : ℝ) (n : ℕ) : ℝ :=
  if n.Coprime N ∧ y < ((N-n).minFac : ℝ) then
    ∑ d in (N-n).divisors.filter (fun d : ℕ => t < (d : ℝ)),
      (ArithmeticFunction.moebius d : ℝ)
  else 0

theorem sieveWeight_bound (N r n : ℕ) (y t : ℝ) (hr : 0 < r)
    (hy : ((2^r : ℕ) : ℝ) ≤ y) (hn : n < N) :
    |sieveWeight N y t n| ≤ (N : ℝ) ^ (r : ℝ)⁻¹ := by
  classical
  let m := N-n
  have hm : m ≠ 0 := by dsimp [m]; omega
  unfold sieveWeight
  split_ifs with h
  · have hrough (p : ℕ) (hp : p ∈ m.primeFactors) : 2^r ≤ p := by
      have hmin : m.minFac ≤ p := Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le
        (Nat.dvd_of_mem_primeFactors hp)
      have hl : ((2^r : ℕ) : ℝ) < m.minFac := lt_of_le_of_lt hy h.2
      have hcast : 2^r < m.minFac := by exact_mod_cast hl
      exact hcast.le.trans hmin
    have hle : m.divisors.card ^ r ≤ N := (divisor_count_pow_le m r hm hrough).trans (Nat.sub_le _ _)
    let T := m.divisors.filter (fun d : ℕ => t < (d : ℝ))
    calc
      _ ≤ ∑ d in T, |(ArithmeticFunction.moebius d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d in T, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=d))
      _ = (T.card : ℝ) := by simp
      _ ≤ (m.divisors.card : ℝ) := by
        exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _) : T.card ≤ m.divisors.card)
      _ ≤ _ := by
        apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
          (show (0:ℝ)<r by exact_mod_cast hr)).mpr
        rw [Real.rpow_natCast]
        exact_mod_cast hle
  · simpa using Real.rpow_nonneg (show (0 : ℝ) ≤ N by positivity) ((r : ℝ)⁻¹)

/-- In the power-rough regime y^K ≥ N this controls every truncated
    Möbius tail at once; its bound has no logarithmic dependence on N. -/
theorem sieveWeight_budget (N K n : ℕ) (y t : ℝ) (hy : 1 < y)
    (hsize : (N : ℝ) ≤ y ^ K) (hn : n < N) :
    |sieveWeight N y t n| ≤ (2 : ℝ)^K := by
  classical
  let m := N-n
  have hm : m ≠ 0 := by dsimp [m]; omega
  unfold sieveWeight
  split_ifs with h
  · have hbase (p : ℕ) (hp : p ∈ m.primeFactors) : y ≤ (p : ℝ) := by
      have hmin : m.minFac ≤ p := Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le
        (Nat.dvd_of_mem_primeFactors hp)
      exact h.2.le.trans (by exact_mod_cast hmin)
    have hmN : (m : ℝ) ≤ N := by exact_mod_cast (Nat.sub_le N n)
    have hcard := rough_divisor_budget m K y hm hy (hmN.trans hsize) hbase
    let T := m.divisors.filter (fun d : ℕ => t < (d : ℝ))
    calc
      _ ≤ ∑ d in T, |(ArithmeticFunction.moebius d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d in T, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=d))
      _ = (T.card : ℝ) := by simp
      _ ≤ _ := by
        have : T.card ≤ 2^K := (Finset.card_le_card (Finset.filter_subset _ _)).trans hcard
        exact_mod_cast this
  · simp

/-- Integer points of the support window specified in the paper. -/
def middle (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (N-2)).filter (fun n => N ≤ 3*n ∧ 3*n < 2*N)

/-- Uniform endpoint-to-prime comparison for the paper's actual signed sieve.
    For r = 3 and y ≥ 8 the right side is O(N^(5/6)). This estimates the
    prime-power contamination, not the value of the prime correlation itself. -/
theorem sieve_endpoint_prime_error (N r q : ℕ) [Fact q.Prime]
    (y t c : ℝ) (linear : DirichletCharacter ℂ q → ℝ) (hN : 4 ≤ N)
    (hq : (N-2)*(N-2) < q) (hc : 0 < c) (hr : 0 < r)
    (hy : ((2^r : ℕ) : ℝ) ≤ y) :
    let S := middle N
    let X := N-2
    let w := sieveWeight N y t
    let coeff := FourierWindow.dirichletCoeff S c ((q-1 : ℕ) : ℝ) w
      (id : DirichletCharacter ℂ q → _)
    |PaperFourier.endpoint X (PrimeEndpoint.centeredSpectralRamp q X vonMangoldt coeff linear) +
       coeff 1 * (X : ℝ) * ((X : ℝ)+1) * Real.log (1 + 1 / (X : ℝ)) -
       ∑ p in S.filter Nat.Prime, Real.log (p : ℝ) * w p| ≤
       (N : ℝ) ^ (r : ℝ)⁻¹ * ((Nat.sqrt X : ℝ) * Real.log 4) := by
  dsimp only
  have hRange (n : ℕ) (hn : n ∈ middle N) : 2 ≤ n ∧ n ≤ N-2 := by
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  have hRatio (n : ℕ) (hn : n ∈ middle N) (m : ℕ) (hm : m ∈ middle N) : n < 2*m := by
    have ha := (Finset.mem_filter.mp hn).2.2
    have hb := (Finset.mem_filter.mp hm).2.1
    omega
  have hE := PrimeEndpoint.vonMangoldt_endpoint (q:=q) (middle N) c (sieveWeight N y t)
    linear (by omega) hq hc hRange hRatio
  dsimp only at hE
  rw [← hE]
  apply pollution (N-2) (middle N) (sieveWeight N y t)
    ((N : ℝ) ^ (r : ℝ)⁻¹) (Real.rpow_nonneg (by positivity) _) _ 
    (fun n hn => (hRange n hn).2) hRatio
  intro n hn
  exact sieveWeight_bound N r n y t hr hy (by have := (hRange n hn).2; omega)

/-- In the actual regime y ≥ N^(1/K), the signed endpoint minus the sum
    over genuine primes is O_K(√N) for *every* target and *every* cutoff t. -/
theorem sieve_endpoint_sqrt (N K q : ℕ) [Fact q.Prime]
    (y t c : ℝ) (linear : DirichletCharacter ℂ q → ℝ) (hN : 4 ≤ N)
    (hq : (N-2)*(N-2) < q) (hc : 0 < c) (hy : 1 < y)
    (hsize : (N : ℝ) ≤ y ^ K) :
    let S := middle N
    let X := N-2
    let w := sieveWeight N y t
    let coeff := FourierWindow.dirichletCoeff S c ((q-1 : ℕ) : ℝ) w
      (id : DirichletCharacter ℂ q → _)
    |PaperFourier.endpoint X (PrimeEndpoint.centeredSpectralRamp q X vonMangoldt coeff linear) +
       coeff 1 * (X : ℝ) * ((X : ℝ)+1) * Real.log (1 + 1 / (X : ℝ)) -
       ∑ p in S.filter Nat.Prime, Real.log (p : ℝ) * w p| ≤
       (2 : ℝ)^K * ((Nat.sqrt X : ℝ) * Real.log 4) := by
  dsimp only
  have hRange (n : ℕ) (hn : n ∈ middle N) : 2 ≤ n ∧ n ≤ N-2 :=
    Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  have hRatio (n : ℕ) (hn : n ∈ middle N) (m : ℕ) (hm : m ∈ middle N) : n < 2*m := by
    have ha := (Finset.mem_filter.mp hn).2.2
    have hb := (Finset.mem_filter.mp hm).2.1
    omega
  have hE := PrimeEndpoint.vonMangoldt_endpoint (q:=q) (middle N) c (sieveWeight N y t)
    linear (by omega) hq hc hRange hRatio
  dsimp only at hE
  rw [← hE]
  apply pollution (N-2) (middle N) (sieveWeight N y t) ((2 : ℝ)^K) (by positivity) _
    (fun n hn => (hRange n hn).2) hRatio
  intro n hn
  exact sieveWeight_budget N K n y t hy hsize (by have := (hRange n hn).2; omega)

#print axioms theta_le
#print axioms rough_divisor_budget
#print axioms sieveWeight_budget
#print axioms sieve_endpoint_sqrt
#print axioms pollution_of_base_bound
#print axioms pollution
#print axioms divisor_count_pow_le
#print axioms sieveWeight_bound
#print axioms sieve_endpoint_prime_error

end
end Goldbach.PrimePowerError
