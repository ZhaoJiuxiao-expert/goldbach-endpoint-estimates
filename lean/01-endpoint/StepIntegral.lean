import PrimePowerError
import Mathlib.Analysis.SpecialFunctions.Integrals

open scoped BigOperators Interval
open MeasureTheory Set ArithmeticFunction

namespace Goldbach.StepIntegral
noncomputable section
open PrimePowerError

/-- With the target and the prime cutoff fixed, the divisor cutoff enters
    through finitely many strict half-line indicators. -/
theorem measurable_sieveWeight (N n : ℕ) (y : ℝ) :
    Measurable (fun t : ℝ => sieveWeight N y t n) := by
  classical
  unfold sieveWeight
  by_cases h : n.Coprime N ∧ y < ((N-n).minFac : ℝ)
  · simp only [if_pos h, Finset.sum_filter]
    apply Finset.measurable_sum
    intro d _
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const
  · simp [h]

/-- A bounded measurable step sum times the logarithmic integration density
    is genuinely interval integrable on a positive interval. -/
private theorem integrable_div (f : ℝ → ℝ) (M a b : ℝ) (hf : Measurable f)
    (hM : 0 ≤ M) (hbound : ∀ t, |f t| ≤ M) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t => f t / t) volume a b := by
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume a b :=
    intervalIntegrable_inv_iff.mpr (.inr (not_mem_uIcc_of_lt ha hb))
  apply (hinv.const_mul M).mono_fun (hf.div measurable_id).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hM, abs_inv]
  simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right (hbound t) (abs_nonneg t)

/-- Reconstructed (principal-corrected) endpoint, as a function of cutoff t. -/
def endpointAt (N q : ℕ) [Fact q.Prime] (y c : ℝ)
    (linear : DirichletCharacter ℂ q → ℝ) (t : ℝ) : ℝ :=
  let X := N-2
  let coeff := FourierWindow.dirichletCoeff (middle N) c ((q-1 : ℕ) : ℝ)
    (sieveWeight N y t) (id : DirichletCharacter ℂ q → _)
  PaperFourier.endpoint X (PrimeEndpoint.centeredSpectralRamp q X vonMangoldt coeff linear) +
    coeff 1 * (X : ℝ) * ((X : ℝ)+1) * Real.log (1 + 1 / (X : ℝ))

def primeAt (N : ℕ) (y t : ℝ) : ℝ :=
  ∑ p in (middle N).filter Nat.Prime, Real.log (p : ℝ) * sieveWeight N y t p

/-- The corrected endpoint and the corresponding prime-only sum are both
    integrable in the real cutoff against dt/t. The conclusion compares two
    separate integrals, including the intermediate signed cancellation. -/
theorem integrated_sieve_endpoint_error (N K q : ℕ) [Fact q.Prime] (y c a b : ℝ)
    (linear : DirichletCharacter ℂ q → ℝ) (hN : 4 ≤ N) (hq : (N-2)*(N-2) < q)
    (hc : 0 < c) (hy : 1 < y) (hsize : (N : ℝ) ≤ y ^ K) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => endpointAt N q y c linear t / t) volume a b ∧
    IntervalIntegrable (fun t => primeAt N y t / t) volume a b ∧
    |(∫ t in a..b, endpointAt N q y c linear t / t) - ∫ t in a..b, primeAt N y t / t| ≤
      ((2 : ℝ)^K * ((Nat.sqrt (N-2) : ℝ) * Real.log 4)) * Real.log (b/a) := by
  let S := middle N
  let E := endpointAt N q y c linear
  let P := primeAt N y
  let B := (2 : ℝ)^K * ((Nat.sqrt (N-2) : ℝ) * Real.log 4)
  have hb := ha.trans_le hab
  have hRange (n : ℕ) (hn : n ∈ S) : 2 ≤ n ∧ n ≤ N-2 :=
    Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  have hRatio (n : ℕ) (hn : n ∈ S) (m : ℕ) (hm : m ∈ S) : n < 2*m := by
    have ha' := (Finset.mem_filter.mp hn).2.2
    have hb' := (Finset.mem_filter.mp hm).2.1
    omega
  have hrecon (t : ℝ) : E t = ∑ n in S, vonMangoldt n * sieveWeight N y t n :=
    (PrimeEndpoint.vonMangoldt_endpoint (q:=q) S c (sieveWeight N y t) linear
      (by omega) hq hc hRange hRatio).symm
  have integ (T : Finset ℕ) (hT : T ⊆ S) (coeff : ℕ → ℝ) :
      IntervalIntegrable (fun t : ℝ => (∑ n in T, coeff n * sieveWeight N y t n) / t)
        volume a b := by
    let f := fun n t => coeff n * (sieveWeight N y t n / t)
    have hi (n : ℕ) (hn : n ∈ T) : IntervalIntegrable (f n) volume a b := by
      apply IntervalIntegrable.const_mul
      apply integrable_div _ ((2:ℝ)^K) _ _ (measurable_sieveWeight N n y) (by positivity) _ ha hb
      intro t
      exact sieveWeight_budget N K n y t hy hsize (by have := (hRange n (hT hn)).2; omega)
    have H := IntervalIntegrable.sum T hi
    convert H using 1
    funext t
    simp only [Finset.sum_div, Finset.sum_apply, f, mul_div_assoc]
  have hE : IntervalIntegrable (fun t => E t / t) volume a b := by
    simpa only [hrecon] using integ S (fun _ h => h) vonMangoldt
  have hP : IntervalIntegrable (fun t => P t / t) volume a b :=
    integ (S.filter Nat.Prime) (Finset.filter_subset _ _) (fun n => Real.log (n:ℝ))
  refine ⟨hE,hP,?_⟩
  change |(∫ t in a..b, E t / t) - ∫ t in a..b, P t / t| ≤ B * Real.log (b/a)
  rw [← intervalIntegral.integral_sub hE hP]
  have hmajor : IntervalIntegrable (fun t : ℝ => B * t⁻¹) volume a b :=
    (intervalIntegrable_inv_iff.mpr (Or.inr (not_mem_uIcc_of_lt ha hb))).const_mul B
  calc
    _ ≤ ∫ t in a..b, |E t / t - P t / t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, B * t⁻¹ := by
      apply intervalIntegral.integral_mono_on hab (hE.sub hP).abs hmajor
      intro t ht
      have htpos := ha.trans_le ht.1
      have H : |E t - P t| ≤ B := sieve_endpoint_sqrt N K q y t c linear hN hq hc hy hsize
      rw [← sub_div, abs_div, abs_of_pos htpos, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right H (inv_nonneg.mpr htpos.le)
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]

#print axioms measurable_sieveWeight
#print axioms integrated_sieve_endpoint_error

end
end Goldbach.StepIntegral
