import Rigidity.Proofs.S2.FiniteClusterPolynomialMoment
import Rigidity.Proofs.S2.InfluenceIntegrability

/-!
# Moments of single-bond density influences

The finite-cluster moment estimate controls each resampling influence uniformly in the bond,
the counting cube, and the moment order.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

/-- A finite sum of nonnegative terms is controlled by the sum of their integer powers. -/
theorem sum_pow_le_card_pow_mul_sum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (r : ℕ) (hr : 1 ≤ r) :
    (∑ i ∈ s, f i) ^ r ≤ (s.card : ℝ) ^ r * ∑ i ∈ s, f i ^ r := by
  have hcard : (1 : ℝ) ≤ s.card := by exact_mod_cast (Finset.one_le_card.mpr hs)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s (f := f) hr' hf
  have hcoeff : (s.card : ℝ) ^ ((r : ℝ) - 1) ≤ (s.card : ℝ) ^ (r : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hcard (by linarith)
  have hsum : 0 ≤ ∑ i ∈ s, f i ^ r := Finset.sum_nonneg fun i hi => pow_nonneg (hf i hi) _
  have h' := h.trans (mul_le_mul_of_nonneg_right hcoeff (by simpa only [Real.rpow_natCast] using hsum))
  simpa only [Real.rpow_natCast] using h'


/-- Single-bond density-count influences have uniform factorial moment bounds in the plane. -/
theorem planar_density_influence_polynomial_moment (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2) (e : Bond 2) (r : ℕ),
      1 ≤ r →
      Integrable (fun q : Configuration 2 × Configuration 2 =>
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r)
        ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)) ∧
      (∫ q : Configuration 2 × Configuration 2,
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r
        ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))) ≤
          (4 : ℝ) ^ (r + 1) * (((2 * r).factorial : ℝ) / a ^ (2 * r)) * C := by
  classical
  obtain ⟨a, C, ha, hC, hmoment⟩ := planar_finiteComponent_polynomial_moment p hp
  refine ⟨a, C, ha, hC, fun m k e r hr => ?_⟩
  refine ⟨integrable_count_influence_pow p m k e r, ?_⟩
  let μ := latticeBondLaw 2 p
  let ν := μ.prod μ
  let S : Finset (Vertex 2 × Fin 2) := e.val.toFinset ×ˢ Finset.univ
  let F (i : Vertex 2 × Fin 2) (q : Configuration 2 × Configuration 2) : ℝ :=
    if i.2 = 0 then (finiteComponentVertices q.1 i.1).card
    else (finiteComponentVertices (resampleBond q.1 q.2 e) i.1).card
  let K : ℝ := ((2 * r).factorial : ℝ) / a ^ (2 * r)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hEpos : 0 < e.val.toFinset.card := by
    rw [Sym2.card_toFinset]
    split_ifs <;> omega
  have hEmax : e.val.toFinset.card ≤ 2 := by
    rw [Sym2.card_toFinset]
    split_ifs <;> omega
  have hSpos : 0 < S.card := by
    dsimp [S]
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    omega
  have hSmax : S.card ≤ 4 := by
    dsimp [S]
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    omega
  have hS : S.Nonempty := Finset.card_pos.mp hSpos
  have hFnonneg (i : Vertex 2 × Fin 2) (q : Configuration 2 × Configuration 2) :
      0 ≤ F i q := by dsimp [F]; split_ifs <;> positivity
  have hFint (i : Vertex 2 × Fin 2) : Integrable (fun q => F i q ^ r) ν := by
    have hbase := (hmoment r i.1).1
    by_cases hi : i.2 = 0
    · have hP : MeasurePreserving (fun q : Configuration 2 × Configuration 2 => q.1) ν μ :=
        measurePreserving_fst
      simpa only [F, hi, if_pos, Function.comp_def] using hP.integrable_comp_of_integrable hbase
    · have hP : MeasurePreserving (fun q : Configuration 2 × Configuration 2 =>
          resampleBond q.1 q.2 e) ν μ := measurePreserving_resampleBond 2 p e
      simpa only [F, hi, if_false, Function.comp_def] using hP.integrable_comp_of_integrable hbase
  have hFbound (i : Vertex 2 × Fin 2) : (∫ q, F i q ^ r ∂ν) ≤ K * C := by
    have hbase := (hmoment r i.1).1
    have hmap (T : Configuration 2 × Configuration 2 → Configuration 2)
        (hP : MeasurePreserving T ν μ) :
        (∫ q, ((finiteComponentVertices (T q) i.1).card : ℝ) ^ r ∂ν) =
          ∫ ω, ((finiteComponentVertices ω i.1).card : ℝ) ^ r ∂μ := by
      have hm : AEStronglyMeasurable
          (fun ω : Configuration 2 => ((finiteComponentVertices ω i.1).card : ℝ) ^ r)
          (Measure.map T ν) := by rw [hP.map_eq]; exact hbase.aestronglyMeasurable
      have heq := integral_map hP.measurable.aemeasurable hm
      rw [hP.map_eq] at heq
      exact heq.symm
    by_cases hi : i.2 = 0
    · simpa only [F, hi, if_pos] using
        (hmap (fun q => q.1) measurePreserving_fst).le.trans (hmoment r i.1).2
    · simpa only [F, hi, if_false] using
        (hmap (fun q => resampleBond q.1 q.2 e) (measurePreserving_resampleBond 2 p e)).le.trans
          (hmoment r i.1).2
  have hpoint (q : Configuration 2 × Configuration 2) :
      |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
        (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ≤
          ∑ i ∈ S, F i q := by
    have h := abs_infiniteClusterCount_resampleBond_le m k q.1 q.2 e
    simpa only [S, F, Finset.sum_product, Fin.sum_univ_two, Fin.isValue, ↓reduceIte,
      zero_ne_one, one_ne_zero] using h
  have hpointPow (q : Configuration 2 × Configuration 2) :
      |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
        (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r ≤
          (4 : ℝ) ^ r * ∑ i ∈ S, F i q ^ r := by
    calc
      _ ≤ (∑ i ∈ S, F i q) ^ r := pow_le_pow_left₀ (abs_nonneg _) (hpoint q) r
      _ ≤ (S.card : ℝ) ^ r * ∑ i ∈ S, F i q ^ r :=
        sum_pow_le_card_pow_mul_sum S hS (fun i => F i q) (fun i _ => hFnonneg i q) r hr
      _ ≤ (4 : ℝ) ^ r * ∑ i ∈ S, F i q ^ r := by
        apply mul_le_mul_of_nonneg_right
        · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hSmax) r
        · exact Finset.sum_nonneg fun i _ => pow_nonneg (hFnonneg i q) _
  have hsumInt : Integrable (fun q => ∑ i ∈ S, F i q ^ r) ν :=
    integrable_finsetSum S (fun i _ => hFint i)
  have hmajInt : Integrable (fun q => (4 : ℝ) ^ r * ∑ i ∈ S, F i q ^ r) ν :=
    hsumInt.const_mul _
  have hsumBound : (∑ i ∈ S, ∫ q, F i q ^ r ∂ν) ≤ (S.card : ℝ) * (K * C) := by
    calc
      _ ≤ ∑ _i ∈ S, K * C := Finset.sum_le_sum fun i _ => hFbound i
      _ = _ := by simp
  have hIC : 0 ≤ K * C := mul_nonneg hK hC.le
  calc
    _ ≤ ∫ q, (4 : ℝ) ^ r * ∑ i ∈ S, F i q ^ r ∂ν :=
      integral_mono (integrable_count_influence_pow p m k e r) hmajInt hpointPow
    _ = (4 : ℝ) ^ r * ∑ i ∈ S, ∫ q, F i q ^ r ∂ν := by
      rw [integral_const_mul, integral_finsetSum S (fun i _ => hFint i)]
    _ ≤ (4 : ℝ) ^ r * ((S.card : ℝ) * (K * C)) :=
      mul_le_mul_of_nonneg_left hsumBound (by positivity)
    _ ≤ (4 : ℝ) ^ r * (4 * (K * C)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hSmax) hIC) (by positivity)
    _ = _ := by dsimp [K]; rw [pow_succ]; ring

end Rigidity.Proofs.S2
