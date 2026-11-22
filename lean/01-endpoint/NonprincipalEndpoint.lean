import PrimeEndpoint
import PrincipalMass

open scoped BigOperators
namespace Goldbach.NonprincipalEndpoint
noncomputable section
open FourierWindow PrimeCharacter PrimeEndpoint
attribute [local instance] allCharacters

/-- The half-open balanced window from Section 5; integer tests include exact endpoints. -/
def window (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun n => N ≤ 3 * n ∧ 3 * n < 2 * N

def samples (B : Finset ℕ) (w : ℕ → ℝ) : Finset ℕ := by
  classical
  exact B.filter fun n => ArithmeticFunction.vonMangoldt n ≠ 0 ∧ w n ≠ 0

def reservoir (B : Finset ℕ) : Finset ℕ :=
  B.filter fun n => 6 ∣ n

theorem zero_of_six_dvd {n : ℕ} (hn : 6 ∣ n) :
    ArithmeticFunction.vonMangoldt n = 0 := by
  have h6 : ¬ IsPrimePow (6 : ℕ) := by decide
  rw [ArithmeticFunction.vonMangoldt_apply, if_neg (fun h => h6 (h.dvd hn (by decide)))]

theorem reservoir_nonempty {N : ℕ} (hN : 18 ≤ N) :
    (reservoir (window N)).Nonempty := by
  refine ⟨6 * ((N + 17) / 18), ?_⟩
  simp only [reservoir, window, Finset.mem_filter, Finset.mem_range]
  exact ⟨⟨by omega, by omega, by omega⟩, dvd_mul_right _ _⟩

/-- The original arithmetic sum lives on the sampled positions. -/
theorem sum_samples (B : Finset ℕ) (w : ℕ → ℝ) :
    (∑ n in B, ArithmeticFunction.vonMangoldt n * w n) =
      ∑ n in samples B w, ArithmeticFunction.vonMangoldt n * w n := by
  classical
  rw [samples, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : ArithmeticFunction.vonMangoldt n = 0 <;> by_cases hw : w n = 0 <;> simp [h, hw]

def balancedWeight (P T : Finset ℕ) (w : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  if n ∈ T then -(c + ∑ j in P, w j) / (T.card : ℝ) else w n

private theorem reservoir_identities (P T : Finset ℕ) (w : ℕ → ℝ) (c : ℝ)
    (hd : Disjoint P T) (hT : T.Nonempty)
    (hz : ∀ n ∈ T, ArithmeticFunction.vonMangoldt n = 0) :
    let u := balancedWeight P T w c
    (∑ n in P ∪ T, u n) = -c ∧
    (∑ n in P ∪ T, ArithmeticFunction.vonMangoldt n * u n) =
      (∑ n in P, ArithmeticFunction.vonMangoldt n * w n) ∧
    (∑ n in P ∪ T, u n * u n) =
      (∑ n in P, w n * w n) + (c + ∑ n in P, w n) ^ 2 / (T.card : ℝ) := by
  classical
  let u := balancedWeight P T w c
  let d := -(c + ∑ j in P, w j) / (T.card : ℝ)
  have hp (n : ℕ) (hn : n ∈ P) : u n = w n := by
    simp [u, balancedWeight, Finset.disjoint_left.mp hd hn]
  have ht (n : ℕ) (hn : n ∈ T) : u n = d := by simp [u, balancedWeight, hn, d]
  have hM : (T.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hT).ne'
  change (∑ n in P ∪ T, u n) = -c ∧ _ ∧ _
  simp only [Finset.sum_union hd]
  constructor
  · rw [Finset.sum_congr rfl hp, Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul]
    dsimp [d]
    field_simp
  constructor
  · rw [Finset.sum_congr rfl (fun n hn => congrArg (fun z => ArithmeticFunction.vonMangoldt n * z) (hp n hn))]
    have hzero : (∑ n in T, ArithmeticFunction.vonMangoldt n * u n) = 0 := Finset.sum_eq_zero (fun n hn => by rw [hz n hn, zero_mul])
    rw [hzero, add_zero]
  · rw [Finset.sum_congr rfl (fun n hn => congrArg (fun z : ℝ => z * z) (hp n hn)),
        Finset.sum_congr rfl (fun n hn => congrArg (fun z : ℝ => z * z) (ht n hn)),
        Finset.sum_const, nsmul_eq_mul]
    dsimp [d]
    field_simp
    ring

/-- Unconditional finite reduction. The principal character has zero spectral mass.
    The price in total mass is explicit and distributed over silent composite positions. -/
theorem balanced_nonprincipal_endpoint {q N : ℕ} [Fact (Nat.Prime q)]
    (w : ℕ → ℝ) (c : ℝ) (linear : DirichletCharacter ℂ q → ℝ)
    (hN : 18 ≤ N) (hq : (N-2) * (N-2) < q) (hc : 0 < c) :
    let B := window N
    let P := samples B w
    let T := reservoir B
    ∃ coeff : DirichletCharacter ℂ q → ℝ,
      (∀ χ, 0 ≤ coeff χ) ∧ coeff 1 = 0 ∧
      (∑ χ, coeff χ) = c + ((∑ n in P, w n * w n) +
        (c + ∑ n in P, w n)^2 / (T.card : ℝ)) / c ∧
      (∑ n in B, ArithmeticFunction.vonMangoldt n * w n) =
      PaperFourier.endpoint (N-2)
        (centeredSpectralRamp q (N-2) ArithmeticFunction.vonMangoldt coeff linear) := by
  classical
  let B := window N
  let P := samples B w
  let T := reservoir B
  let u := balancedWeight P T w c
  let S := P ∪ T
  let coeff := dirichletCoeff S c ((q-1 : ℕ) : ℝ) u (id : DirichletCharacter ℂ q → _)
  have hT : T.Nonempty := reservoir_nonempty hN
  have hz (n : ℕ) (hn : n ∈ T) : ArithmeticFunction.vonMangoldt n = 0 :=
    zero_of_six_dvd (Finset.mem_filter.mp hn).2
  have hd : Disjoint P T := by
    refine Finset.disjoint_left.mpr ?_
    intro n hnP hnT
    have hP : n ∈ B ∧ (ArithmeticFunction.vonMangoldt n ≠ 0 ∧ w n ≠ 0) :=
      Finset.mem_filter.mp (show n ∈ B.filter (fun k => ArithmeticFunction.vonMangoldt k ≠ 0 ∧ w k ≠ 0) from hnP)
    exact hP.2.1 (hz n hnT)
  have hsum := reservoir_identities P T w c hd hT hz
  have hWindow (n : ℕ) (hn : n ∈ S) : N ≤ 3*n ∧ 3*n < 2*N := by
    have hb : n ∈ B := by
      obtain hp | ht := Finset.mem_union.mp hn
      · exact (Finset.mem_filter.mp hp).1
      · exact (Finset.mem_filter.mp ht).1
    exact (Finset.mem_filter.mp hb).2
  have hRange (n : ℕ) (hn : n ∈ S) : 2 ≤ n ∧ n ≤ N-2 := by
    have := hWindow n hn
    omega
  have hRatio (a : ℕ) (ha : a ∈ S) (b : ℕ) (hb : b ∈ S) : a < 2*b := by
    have := (hWindow a ha).2
    have := (hWindow b hb).1
    omega
  have hX : 2 ≤ N-2 := by omega
  have hp : Nat.Prime q := Fact.out
  have hh : 0 < q-1 := by have := hp.two_le; omega
  have hF := dirichlet_window_coefficients S c ((q-1 : ℕ) : ℝ) u
    (id : DirichletCharacter ℂ q → _) hX hq hc (by exact_mod_cast hh) hRange hRatio
    (fun a b ha hb => by simpa using orthogonality a b ha hb)
  have h0 : coeff 1 = 0 := by
    change dirichletCoeff S _ _ _ _ 1 = 0
    rw [principal_mass S c u hX hq hRange, hsum.1]
    simp
  refine ⟨coeff, hF.1, h0, ?_, ?_⟩
  · exact hF.2.2.trans (by rw [hsum.2.2])
  · have h := vonMangoldt_endpoint S c u linear hX hq hc hRange hRatio
    change (∑ n in S, ArithmeticFunction.vonMangoldt n * u n) =
      PaperFourier.endpoint (N-2) _ + coeff 1 * _ * _ * _ at h
    rw [h0, zero_mul, zero_mul, zero_mul, add_zero, hsum.2.1] at h
    exact (sum_samples B w).trans h

/-- Explicit reservoir size: each full block of eighteen in N gives a new
    multiple of six in the window of length N/3. -/
theorem reservoir_card (N : ℕ) : N / 18 ≤ (reservoir (window N)).card := by
  let f := fun i : ℕ => 6 * ((N + 17) / 18 + i)
  have hfi : Function.Injective f := by
    intro i j h
    dsimp [f] at h
    omega
  have hsub : (Finset.range (N / 18)).image f ⊆ reservoir (window N) := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have h := Finset.mem_range.mp hi
    simp only [reservoir, window, Finset.mem_filter, Finset.mem_range, f]
    exact ⟨⟨by omega, by omega, by omega⟩, dvd_mul_right _ _⟩
  have h := Finset.card_le_card hsub
  simpa [Finset.card_image_of_injective _ hfi] using h

/-- Relative overhead when c² is the energy in sampled positions. -/
theorem reservoir_overhead (P T : Finset ℕ) (w : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c) (hV : ∑ n in P, w n*w n = c*c) (hT : T.Nonempty) :
    (c + ∑ n in P, w n)^2 / ((T.card : ℝ)*c) ≤
      (2*c) * (1 + P.card) / (T.card : ℝ) := by
  have hcard : 0 < (T.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hT
  have hCS : (∑ n in P, w n)^2 ≤ (P.card : ℝ)*(c*c) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq P (fun _ => (1:ℝ)) w
    simpa [sq, hV] using h
  have hsq : (c + ∑ n in P, w n)^2 ≤ 2*(1+(P.card : ℝ))*(c*c) := by
    nlinarith [sq_nonneg (c - ∑ n in P, w n)]
  apply (div_le_iff₀ (mul_pos hcard hc)).2
  calc
    _ ≤ 2*(1+(P.card : ℝ))*(c*c) := hsq
    _ = _ := by field_simp; ring

/-- Uniform bound on the logarithmic correction in the *original* (unmodified)
    spectrum. At the balanced parameter c = √V, it costs at most 8c. -/
theorem principal_correction_le_eight {q X : ℕ} [Fact (Nat.Prime q)]
    (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) (hX : 2 ≤ X) (hq : X*X < q)
    (hRange : ∀ n ∈ S, 2 ≤ n ∧ n ≤ X) (hc : 0 < c)
    (hV : ∑ n in S, w n * w n = c*c) :
    let a₀ := dirichletCoeff S c ((q-1 : ℕ) : ℝ) w (id : DirichletCharacter ℂ q → _) 1
    let correction := a₀ * (X : ℝ) * ((X : ℝ) + 1) * Real.log (1 + 1/(X : ℝ))
    0 ≤ correction ∧ correction ≤ 8*c := by
  classical
  let x : ℝ := X
  let h : ℝ := (q-1 : ℕ)
  let s := ∑ n in S, w n
  let a₀ := dirichletCoeff S c ((q-1 : ℕ) : ℝ) w (id : DirichletCharacter ℂ q → _) 1
  change 0 ≤ a₀*x*(x+1)*Real.log (1+1/x) ∧ a₀*x*(x+1)*Real.log (1+1/x) ≤ 8*c
  have hx1 : (1:ℝ) ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ X by omega)
  have hx : 0 < x := by linarith
  have hxh : x*x ≤ h := by
    change (X : ℝ)*(X : ℝ) ≤ ((q-1 : ℕ) : ℝ)
    exact_mod_cast (show X*X ≤ q-1 by omega)
  have hh : 0 < h := lt_of_lt_of_le (mul_pos hx hx) hxh
  have hKnat : S.card ≤ X := by
    have hh := Finset.card_le_card (show S ⊆ Finset.Icc 1 X from
      fun n hn => Finset.mem_Icc.mpr ⟨(by have := (hRange n hn).1; omega), (hRange n hn).2⟩)
    simpa [Nat.card_Icc] using hh
  have hK : (S.card : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hKnat
  have hCS : s*s ≤ (S.card : ℝ)*(c*c) := by
    simpa [s, sq, hV] using (Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) w)
  have hsq : (c+s)^2 ≤ 2*(1+x)*(c*c) := by
    nlinarith [sq_nonneg (c-s), mul_nonneg (sub_nonneg.mpr hK) (mul_self_nonneg c)]
  have hformula : a₀ = (c+s)^2 / (c*h) := principal_mass S c w hX hq hRange
  have hpos : 0 ≤ a₀ := by rw [hformula]; positivity
  have ha : a₀ ≤ 2*c*(1+x)/h := by
    rw [hformula]
    apply (div_le_iff₀ (mul_pos hc hh)).2
    calc
      _ ≤ 2*(1+x)*(c*c) := hsq
      _ = _ := by field_simp; ring
  have hlog : Real.log (1+1/x) ≤ 1/x := by
    have h₁ : 0 < 1+1/x := by positivity
    linarith [Real.log_le_sub_one_of_pos h₁]
  have hlower : 0 ≤ Real.log (1+1/x) := Real.log_nonneg (by linarith [one_div_pos.mpr hx])
  constructor
  · positivity
  calc
    _ ≤ a₀*x*(x+1)*(1/x) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = a₀*(x+1) := by field_simp; ring
    _ ≤ (2*c*(1+x)/h)*(x+1) := mul_le_mul_of_nonneg_right ha (by positivity)
    _ = (2*c*((1+x)*(1+x)))/h := by ring
    _ ≤ 8*c := by
      apply (div_le_iff₀ hh).2
      have hprod : (1+x)*(1+x) ≤ (2*x)*(2*x) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      have hs : (1+x)*(1+x) ≤ 4*h := by nlinarith [hprod,hxh]
      nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hs)]

#print axioms principal_correction_le_eight
#print axioms reservoir_card
#print axioms reservoir_overhead
#print axioms zero_of_six_dvd
#print axioms reservoir_nonempty
#print axioms sum_samples
#print axioms balanced_nonprincipal_endpoint

end
end Goldbach.NonprincipalEndpoint
