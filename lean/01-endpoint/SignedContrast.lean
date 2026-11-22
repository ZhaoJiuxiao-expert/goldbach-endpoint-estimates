import SingleEndpoint

open scoped BigOperators
open ArithmeticFunction
open Goldbach.PrimePowerError (middle sieveWeight)
namespace FixedEven.Cubic
noncomputable section

def DistinctSemiprime (m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ m = p*q

/-- Below the cube of the least allowed factor, the positive Möbius sign
identifies exactly products of two distinct primes. -/
theorem rough_mu_pos_iff_distinctSemiprime {m y : ℕ} (hm : 1 < m) (hr : Rough y m)
    (hsize : m < (y+1)^3) : moebius m = 1 ↔ DistinctSemiprime m := by
  classical
  constructor
  · intro hmu
    have hsf : Squarefree m := moebius_ne_zero_iff_squarefree.mp (by omega)
    have hprod := Nat.prod_primeFactors_of_squarefree hsf
    have hc : m.primeFactors.card = cardFactors m := by
      rw [← Nat.toFinset_factors, List.toFinset_card_of_nodup hsf.nodup_primeFactorsList]
      rfl
    have hbound : (y+1)^m.primeFactors.card ≤ m := by
      calc
        _ = ∏ _p ∈ m.primeFactors, (y+1) := by simp
        _ ≤ ∏ p ∈ m.primeFactors, p := Finset.prod_le_prod' fun p hp =>
          hr p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
        _ = m := hprod
    have hlt : m.primeFactors.card < 3 := by
      by_contra! hh
      have := Nat.pow_le_pow_right (by omega : 0 < y+1) hh
      omega
    have hnz : m.primeFactors.card ≠ 0 := by
      intro h
      have he := Finset.card_eq_zero.mp h
      simp [he] at hprod
      omega
    rw [moebius_apply_of_squarefree hsf, ← hc] at hmu
    have htwo : m.primeFactors.card = 2 := by
      interval_cases m.primeFactors.card <;> norm_num at *
    obtain ⟨p,q,hpq,hset⟩ := Finset.card_eq_two.mp htwo
    have hpr : p ∈ m.primeFactors := by simp [hset]
    have hqr : q ∈ m.primeFactors := by simp [hset]
    exact ⟨p,q,Nat.prime_of_mem_primeFactors hpr,Nat.prime_of_mem_primeFactors hqr,hpq,by
      simpa [hset,hpq] using hprod.symm⟩
  · rintro ⟨p,q,hp,hq,hd,rfl⟩
    rw [isMultiplicative_moebius.map_mul_of_coprime ((Nat.coprime_primes hp hq).mpr hd),
      moebius_apply_prime hp, moebius_apply_prime hq]
    norm_num

def semiprimePartners (N z : ℕ) : Finset ℕ := by
  classical
  exact (screen N z).filter fun n => n.Prime ∧ DistinctSemiprime (N-n)

/-- On the original Section 5 window, the signed weight distinguishes
two different prime factors (+1), one prime (-1) and all other cases (0). -/
theorem signed_weight_split {N z n : ℕ} (hN : 4096 ≤ N) (hz : 8 ≤ z)
    (hwindow : 2*N < 3*z^3) (hn : n ∈ middle N) :
    let w := sieveWeight N ((z-1 : ℕ) : ℝ) ((N/z : ℕ) : ℝ)
    letI := Classical.propDecidable
    w n = (if n ∈ screen N z ∧ DistinctSemiprime (N-n) then (1:ℝ) else 0) -
      (if n ∈ screen N z ∧ (N-n).Prime then 1 else 0) := by
  classical
  dsimp only
  have hh := (Finset.mem_filter.mp hn).2
  have hr : Rough (z-1) (N-n) ↔ z-1 < (N-n).minFac := by
    refine ⟨fun h => h _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _), ?_⟩
    intro h p hp hd
    exact h.trans_le (Nat.minFac_le_of_dvd hp.two_le hd)
  have hc : n ∈ screen N z ↔ n.Coprime N ∧ ((z-1 : ℕ) : ℝ) < ((N-n).minFac : ℝ) := by
    change n ∈ (Finset.Icc 2 (N-2)).filter _ ↔ _
    rw [Finset.mem_filter]
    simp only [(Finset.mem_filter.mp hn).1, hh.1, hh.2, true_and, hr, Nat.cast_lt]
  unfold sieveWeight
  by_cases hs : n ∈ screen N z
  · obtain ⟨h1,h2,hrough⟩ := (screen_spec hN hz).2.2 n hs
    have hzz : z-1+1 = z := by omega
    have hsize : N-n < (z-1+1)^3 := by rw [hzz]; omega
    have ht := tail_eq_mu (by omega : 0<N-n) (Nat.sub_le N n) h2
      (y:=z-1) (by simp [hzz]) hrough
    have hpos := rough_mu_pos_iff_distinctSemiprime h1 hrough hsize
    have hneg := rough_mu_neg_iff_prime h1 hrough hsize
    rw [if_pos (hc.mp hs)]
    have htail : (∑ d ∈ (N-n).divisors.filter (fun d : ℕ => ((N/z : ℕ) : ℝ) < (d : ℝ)),
        (moebius d : ℝ)) = (tail (N-n) (N/z) : ℝ) := by simp [tail]
    rw [htail, ht]
    simp only [hs,true_and,← hpos,← hneg]
    rcases moebius_eq_or (N-n) with hm|hm|hm <;> norm_num [hm]
  · rw [if_neg (mt hc.mpr hs)]
    simp [hs]

private theorem sum_as_indicator {T A : Finset ℕ} (h : T ⊆ A) :
    (∑ p ∈ T, Real.log p) = ∑ p ∈ A, if p ∈ T then Real.log p else 0 := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter]
  exact ⟨fun hn => ⟨h hn,hn⟩,And.right⟩

/-- The signed endpoint measures the difference of the two positive prime
masses, up to pollution from higher powers on its von Mangoldt coordinate. -/
theorem single_endpoint_contrast {q N z : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hwindow : 2*N < 3*z^3)
    (hq : (N-2)*(N-2) < q) (c : ℝ) (hc : 0 < c) (linear : DirichletCharacter ℂ q → ℝ) :
    |singleEndpoint N z c linear - ((∑ p ∈ semiprimePartners N z, Real.log p) -
       ∑ p ∈ genuine (screen N z) N, Real.log p)| ≤ (Nat.sqrt (N-2) : ℝ)*Real.log 4 := by
  classical
  let w := sieveWeight N ((z-1 : ℕ) : ℝ) ((N/z : ℕ) : ℝ)
  let A := (middle N).filter Nat.Prime
  have hRange (n : ℕ) (hn : n ∈ middle N) : 2 ≤ n ∧ n ≤ N-2 :=
    Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  have hRatio (n : ℕ) (hn : n ∈ middle N) (m : ℕ) (hm : m ∈ middle N) :
      n < 2*m := by
    have h1 := (Finset.mem_filter.mp hn).2.2
    have h2 := (Finset.mem_filter.mp hm).2.1
    omega
  have he : singleEndpoint N z c linear = ∑ n ∈ middle N, vonMangoldt n * w n :=
    (Goldbach.PrimeEndpoint.vonMangoldt_endpoint (middle N) c w linear
      (by omega) hq hc hRange hRatio).symm
  have hw (n : ℕ) (hn : n ∈ middle N) : |w n| ≤ 1 := by
    change |sieveWeight N _ _ n| ≤ 1
    rw [signed_weight_split hN hz hwindow hn]
    split_ifs <;> norm_num
  have hsub {n : ℕ} (hs : n ∈ screen N z) (hp : n.Prime) : n ∈ A := by
    have hh := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hh.1,hh.2.1,hh.2.2.1⟩,hp⟩
  have hplus : semiprimePartners N z ⊆ A := fun _ hn =>
    hsub (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2.1
  have hminus : genuine (screen N z) N ⊆ A := fun _ hn =>
    hsub (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2.1
  have hmass : (∑ p ∈ A, Real.log p * w p) =
      (∑ p ∈ semiprimePartners N z, Real.log p) - ∑ p ∈ genuine (screen N z) N, Real.log p := by
    rw [sum_as_indicator hplus,sum_as_indicator hminus,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hm,hp'⟩ := Finset.mem_filter.mp hp
    change Real.log p * sieveWeight N _ _ p = _
    rw [signed_weight_split hN hz hwindow hm]
    simp only [semiprimePartners,genuine,Finset.mem_filter,hp',true_and,mul_sub,mul_ite,
      mul_one,mul_zero]
  have h := Goldbach.PrimePowerError.pollution (N-2) (middle N) w 1 (by norm_num) hw
    (fun n hn => (hRange n hn).2) hRatio
  simpa only [one_mul,he,←hmass] using h

#print axioms rough_mu_pos_iff_distinctSemiprime
#print axioms signed_weight_split
#print axioms single_endpoint_contrast
end
end FixedEven.Cubic
