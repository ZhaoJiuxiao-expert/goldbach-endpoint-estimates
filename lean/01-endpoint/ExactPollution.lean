import SingleEndpoint

open scoped BigOperators
open ArithmeticFunction
namespace FixedEven.Cubic
noncomputable section

/-- Selected integers that are powers of a prime with exponent at least two. -/
def exceptionalPowers (N z : ℕ) : Finset ℕ := by
  classical
  exact (selected N z).filter (fun n => IsPrimePow n ∧ ¬n.Prime)

/-- Exact proper-prime-power correction for the given target and cutoff. -/
def powerCorrection (N z : ℕ) : ℝ :=
  ∑ n ∈ exceptionalPowers N z, Real.log (n.minFac : ℝ)

/-- The finite correction is exactly the logarithm of a positive integer. -/
theorem powerCorrection_eq_log_product (N z : ℕ) :
    powerCorrection N z = Real.log (↑(∏ n ∈ exceptionalPowers N z, n.minFac) : ℝ) := by
  classical
  rw [powerCorrection,Nat.cast_prod,Real.log_prod]
  intro n _
  exact_mod_cast (Nat.minFac_pos n).ne'

/-- Every term in the correction can be generated from a prime base at most
floor sqrt(N-2) by taking powers with exponent at least two. -/
theorem correction_power_support {N z n : ℕ} (hN : 4096 ≤ N) (hz : 8 ≤ z)
    (hn : n ∈ exceptionalPowers N z) :
    n.minFac.Prime ∧ n.minFac ≤ Nat.sqrt (N-2) ∧
    ∃ k : ℕ, 2 ≤ k ∧ n.minFac^k = n := by
  classical
  obtain ⟨hs,hp,hc⟩ := Finset.mem_filter.mp hn
  have hbound := ((screen_spec hN hz).1 n (Finset.mem_filter.mp hs).1).2
  obtain ⟨p,k,hpp,hkp,hpk⟩ := (isPrimePow_nat_iff n).mp hp
  have hk : 2 ≤ k := by
    by_contra! h
    have hk1 : k = 1 := by omega
    exact hc (by rw [← hpk,hk1,pow_one]; exact hpp)
  have hmin : n.minFac = p := by rw [← hpk,Nat.pow_minFac hkp.ne',hpp.minFac_eq]
  rw [hmin]
  exact ⟨hpp,Nat.le_sqrt'.mpr ((Nat.pow_le_pow_right hpp.pos hk).trans (hpk.trans_le hbound)),
    k,hk,hpk⟩

/-- For the exact cubic cutoff the finite sum can be obtained just by testing
the reflected integers of proper prime powers on the specified support. -/
theorem mem_correction_iff {N z n : ℕ} (hN : 4096 ≤ N) (hz : 8 ≤ z)
    (hwindow : 2*N < 3*z^3) :
    n ∈ exceptionalPowers N z ↔ n ∈ screen N z ∧ IsPrimePow n ∧ ¬n.Prime ∧ (N-n).Prime := by
  classical
  have hzz : z-1+1 = z := by omega
  have hcut : N / (z-1+1) ≤ N/z := by rw [hzz]
  by_cases hs : n ∈ screen N z
  · obtain ⟨hm,ht,hr⟩ := (screen_spec hN hz).2.2 n hs
    have hh := (Finset.mem_filter.mp hs).2.1
    have hsz : N-n < (z-1+1)^3 := by rw [hzz]; omega
    have hmu := tail_eq_mu (by omega) (Nat.sub_le N n) ht hcut hr
    simp [exceptionalPowers,selected,hs,hmu,rough_mu_neg_iff_prime hm hr hsz,
      and_assoc,and_comm,and_left_comm]
  · simp [exceptionalPowers,selected,hs]

/-- The exact correction lies between zero and the uniform tolerance for
every target and sieve cutoff in range, even before imposing a cubic cutoff. -/
theorem correction_bounds {N z : ℕ} (hN : 4096 ≤ N) (hz : 8 ≤ z) :
    0 ≤ powerCorrection N z ∧
    powerCorrection N z ≤ (Nat.sqrt (N-2) : ℝ)*Real.log 4 := by
  classical
  let A := exceptionalPowers N z
  have hs {n : ℕ} (hn : n ∈ A) : n ∈ screen N z :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
  obtain ⟨hx,hr,_⟩ := screen_spec hN hz
  have hp := Goldbach.PrimePowerError.pollution (N-2) A (fun _ => 1) 1
    (by norm_num) (by simp) (fun n hn => (hx n (hs hn)).2)
    (fun n hn m hm => hr n (hs hn) m (hs hm))
  have hem : A.filter Nat.Prime = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro n hn
    obtain ⟨hA,hpr⟩ := Finset.mem_filter.mp hn
    exact (Finset.mem_filter.mp hA).2.2 hpr
  have hsum : (∑ n ∈ A, vonMangoldt n) = powerCorrection N z := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [vonMangoldt_apply,if_pos (Finset.mem_filter.mp hn).2.1]
  have hpos : 0 ≤ ∑ n ∈ A, vonMangoldt n := Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg
  simp only [mul_one,hem,Finset.sum_empty,sub_zero,abs_of_nonneg hpos,one_mul] at hp
  exact ⟨hsum ▸ hpos,hsum ▸ hp⟩

/-- A finite exact formula isolates the sole correction without evaluating
any sum over possible Goldbach pairs to obtain the correction itself. -/
theorem observable_eq_prime_mass_add_correction {N z q : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hwindow : 2*N < 3*z^3)
    (hq : (N-2)*(N-2) < q) (c : ℝ) (hc : 0 < c)
    (linear : DirichletCharacter ℂ q → ℝ) :
    mangoldtObservable N z c linear =
      (∑ p ∈ genuine (screen N z) N, Real.log p) + powerCorrection N z := by
  classical
  have hzz : z-1+1 = z := by omega
  have hcut : N / (z-1+1) ≤ N/z := by rw [hzz]
  have hs : detected (screen N z) N (N/z) = genuine (screen N z) N := by
    apply detected_eq_genuine_of_cube (screen N z) hcut (screen_spec hN hz).2.2
    intro n hn
    have hh := (Finset.mem_filter.mp hn).2.1
    rw [hzz]
    omega
  have heq : (selected N z).filter Nat.Prime = genuine (screen N z) N := by
    rw [← hs]
    ext n
    simp [selected,detected,and_assoc,and_left_comm,and_comm]
  rw [mangoldtObservable_eq_sum hN hz hq c hc linear,← heq]
  simp only [powerCorrection,exceptionalPowers,Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · simp [hp,vonMangoldt_apply_prime hp]
  · by_cases hh : IsPrimePow n <;> simp [hp,hh,vonMangoldt_apply]

/-- Crossing the negative of the actual finite correction suffices. This
can be strictly weaker than crossing the uniform square-root bound. -/
theorem representation_of_single_below_correction {N z q : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hwindow : 2*N < 3*z^3)
    (hq : (N-2)*(N-2) < q) (c : ℝ) (hc : 0 < c)
    (linear : DirichletCharacter ℂ q → ℝ)
    (hneg : singleEndpoint N z c linear < -powerCorrection N z) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p+r=N := by
  have hx := neg_single_le_observable (z:=z) (by omega : 4 ≤ N) hq c hc linear
  rw [observable_eq_prime_mass_add_correction hN hz hwindow hq c hc linear] at hx
  have hg : (genuine (screen N z) N).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.sum_empty] at hx
    linarith
  obtain ⟨p,hp⟩ := hg
  obtain ⟨hs,hp',hr⟩ := Finset.mem_filter.mp hp
  have hle := ((screen_spec hN hz).1 p hs).2
  exact ⟨p,N-p,hp',hr,by omega⟩

#print axioms correction_power_support
#print axioms powerCorrection_eq_log_product
#print axioms mem_correction_iff
#print axioms correction_bounds
#print axioms observable_eq_prime_mass_add_correction
#print axioms representation_of_single_below_correction
end
end FixedEven.Cubic
