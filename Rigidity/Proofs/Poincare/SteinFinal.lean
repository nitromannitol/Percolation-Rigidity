import Rigidity.Proofs.Poincare.SteinBound

/-!
# The weighted Littlewood-Paley bound for the heat flow of `ℤ²`, `1 < p ≤ 2`

The conclusion of the lattice form of Armstrong, Kuusi and Mourrat, Proposition D.2, Step 2
(`k = 1`, `α = 0`), with the weights of Remark D.6 and the constant tracked in `q = p/(p-1)`:
for `g` supported in a finite set `S`, `T ≥ 0`, `0 ≤ a ≤ 1/6`, `a max(√T, 1) ≤ 1`,

  `Σ_x coshW(x) (∫_0^T Σ_i (v_s(x + e_i) - v_s(x))² ds)^{p/2} ≤ 2 (C q)^p Σ_x coshW |g|^p`,

`v_s = heatF S g s` (`exists_steinSigned`). With `p` the dual exponent of `q ≥ 2`, the constant
is `O(q)`, as in Dario's use of Armstrong, Kuusi and Mourrat, Proposition D.1 (`A √q` there, `A q`
here; both below the `A q^{3/2}` of Dario's Proposition 2.19).
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare

/-- The pointwise weighted AM-GM step. -/
theorem pointwise_amgm {ω g M I c KM KI p : ℝ} (hω : 0 < ω) (hg : 0 ≤ g) (hM : 0 ≤ M)
    (hI : 0 ≤ I) (hc : 0 ≤ c) (hKM : 0 < KM) (hKI : 0 < KI) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (h : g ≤ c * M ^ (2 - p) * I) :
    ω * g ^ (p / 2) ≤ c ^ (p / 2) * KM ^ ((2 - p) / 2) * KI ^ (p / 2) *
      ((2 - p) / 2 * (ω * M ^ p / KM) + p / 2 * (ω * I / KI)) := by
  have hw1 : 0 ≤ (2 - p) / 2 := by linarith
  have hw2 : 0 ≤ p / 2 := by linarith
  have h1 : g ^ (p / 2) ≤ (c * M ^ (2 - p) * I) ^ (p / 2) := Real.rpow_le_rpow hg h hw2
  have h2 : (c * M ^ (2 - p) * I) ^ (p / 2) = c ^ (p / 2) * (M ^ p) ^ ((2 - p) / 2) *
      I ^ (p / 2) := by
    rw [Real.mul_rpow (by positivity) hI, Real.mul_rpow hc (Real.rpow_nonneg hM _),
      ← Real.rpow_mul hM, ← Real.rpow_mul hM]
    congr 3
    ring
  have h3 : ω = ω ^ ((2 - p) / 2) * ω ^ (p / 2) := by
    rw [← Real.rpow_add hω, show (2 - p) / 2 + p / 2 = 1 by ring, Real.rpow_one]
  have hA : 0 ≤ ω * M ^ p / KM := by have := Real.rpow_nonneg hM p; positivity
  have hB : 0 ≤ ω * I / KI := by positivity
  have amgm := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 hA hB (by ring)
  have e1 : (ω * M ^ p) ^ ((2 - p) / 2) =
      KM ^ ((2 - p) / 2) * (ω * M ^ p / KM) ^ ((2 - p) / 2) := by
    rw [← Real.mul_rpow hKM.le hA]
    congr 1
    field_simp
  have e2 : (ω * I) ^ (p / 2) = KI ^ (p / 2) * (ω * I / KI) ^ (p / 2) := by
    rw [← Real.mul_rpow hKI.le hB]
    congr 1
    field_simp
  have hMp := Real.rpow_nonneg hM p
  calc ω * g ^ (p / 2) ≤ ω * (c ^ (p / 2) * (M ^ p) ^ ((2 - p) / 2) * I ^ (p / 2)) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hω.le
    _ = c ^ (p / 2) * ((ω * M ^ p) ^ ((2 - p) / 2) * (ω * I) ^ (p / 2)) := by
        rw [Real.mul_rpow hω.le hMp, Real.mul_rpow hω.le hI]
        conv_lhs => rw [h3]
        ring
    _ = c ^ (p / 2) * KM ^ ((2 - p) / 2) * KI ^ (p / 2) *
          ((ω * M ^ p / KM) ^ ((2 - p) / 2) * (ω * I / KI) ^ (p / 2)) := by
        rw [e1, e2]; ring
    _ ≤ c ^ (p / 2) * KM ^ ((2 - p) / 2) * KI ^ (p / 2) *
          ((2 - p) / 2 * (ω * M ^ p / KM) + p / 2 * (ω * I / KI)) :=
        mul_le_mul_of_nonneg_left amgm (by positivity)

/-- **Stein's weighted square function bound** for `f ≥ 0`, with explicit constants. -/
theorem exists_steinWeighted : ∃ C : ℝ, 1 ≤ C ∧ ∀ p a T : ℝ, 1 < p → p ≤ 2 → 0 ≤ a →
    a ≤ 1 / 6 → a * max (Real.sqrt T) 1 ≤ 1 → 0 ≤ T → ∀ (S : Finset (Vertex 2))
    (f : Vertex 2 → ℝ), (∀ y, 0 ≤ f y) → (∀ y ∉ S, f y = 0) →
      ∑' x, ENNReal.ofReal (coshW a x * gam S f T x ^ (p / 2)) ≤
        ENNReal.ofReal ((2 / (p * (p - 1))) ^ (p / 2) *
          (3 * (3 * C * Real.exp a) ^ p * (18 * 2 ^ (p - 1) * p / (p - 1))) ^ ((2 - p) / 2) *
          (4 * (Real.cosh a - 1) * T * Real.exp (4 * T * (Real.cosh a - 1)) + 1) ^ (p / 2) *
          ∑ y ∈ S, coshW a y * f y ^ p) := by
  obtain ⟨C₀, hC₀, hmax₀⟩ := exists_heat_le_boxMax
  set C := max C₀ 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hC0 : 0 < C := by linarith
  have hmax : ∀ T a : ℝ, 0 ≤ T → 0 ≤ a → a ≤ 1 / 6 → a * max (Real.sqrt T) 1 ≤ 1 →
      ∀ s : ℝ, 0 ≤ s → s ≤ T → ∀ G : Vertex 2 → ℝ, (∀ z, 0 ≤ G z) → Summable G →
        ∀ x : Vertex 2, ∑' y, ENNReal.ofReal (openHeat (allOpen 2) s x y *
          Real.exp (a * (|(((y - x) 0 : ℤ) : ℝ)| + |(((y - x) 1 : ℤ) : ℝ)|)) * G y) ≤
            ENNReal.ofReal (C * boxMax G x) := by
    intro T a hT ha0 ha6 haT s hs hsT G hG hGs x
    refine (hmax₀ T a hT ha0 ha6 haT s hs hsT G hG hGs x).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (boxMax_nonneg hG hGs x)
  refine ⟨C, hC1, fun p a T hp1 hp2 ha0 ha6 haT hT S f hf hfS => ?_⟩
  have hp0 : 0 < p := by linarith
  set W := ∑ y ∈ S, coshW a y * f y ^ p with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun y _ => mul_nonneg (coshW_pos a y).le
    (Real.rpow_nonneg (hf y) _)
  set M := steinMajorant C a p f with hMdef
  have hM0 : ∀ x, 0 ≤ M x := steinMajorant_nonneg hf hfS hC0.le a p
  set KM := 3 * (3 * C * Real.exp a) ^ p * (18 * 2 ^ (p - 1) * p / (p - 1)) with hKM
  set KI := 4 * (Real.cosh a - 1) * T * Real.exp (4 * T * (Real.cosh a - 1)) + 1 with hKI
  set c := 2 / (p * (p - 1)) with hc
  have hcosh : 0 ≤ Real.cosh a - 1 := by linarith [Real.one_le_cosh a]
  have hKMpos : 0 < KM := by
    have : 0 < p - 1 := by linarith
    positivity
  have hKIpos : 0 < KI := by
    have : 0 ≤ 4 * (Real.cosh a - 1) * T * Real.exp (4 * T * (Real.cosh a - 1)) := by positivity
    linarith
  have hc0 : 0 ≤ c := by
    have : 0 < p * (p - 1) := by nlinarith
    positivity
  -- the majorant dominates the flow at `x` and its forward neighbours
  have hdom : ∀ s ∈ Set.Icc 0 T, ∀ y, heatF S f s y ≤
      C * coshW a y ^ (-(1 / p)) * boxMax (wf a p f) y := by
    intro s hs y
    have h := heatF_le_boxMax hmax hC0 hf hfS hp1.le hT ha0 ha6 haT hs.1 hs.2 y
    have hω := coshW_pos a y
    have e : heatF S f s y = coshW a y ^ (-(1 / p)) * (coshW a y ^ (1 / p) * heatF S f s y) := by
      rw [← mul_assoc, ← Real.rpow_add hω, neg_add_cancel, Real.rpow_zero, one_mul]
    rw [e]
    calc coshW a y ^ (-(1 / p)) * (coshW a y ^ (1 / p) * heatF S f s y)
        ≤ coshW a y ^ (-(1 / p)) * (C * boxMax (wf a p f) y) :=
          mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hω.le _)
      _ = C * coshW a y ^ (-(1 / p)) * boxMax (wf a p f) y := by ring
  have hbm := fun z => boxMax_nonneg (wf_nonneg hf a p) (summable_wf hfS a p) z
  have hexp1 : 1 ≤ Real.exp a := Real.one_le_exp ha0
  have hvx : ∀ x, ∀ s ∈ Set.Icc 0 T, heatF S f s x ≤ M x := by
    intro x s hs
    refine (hdom s hs x).trans ?_
    simp only [hMdef, steinMajorant]
    have hr := Real.rpow_nonneg (coshW_pos a x).le (-(1 / p))
    have := hbm (x + unit 0); have := hbm (x + unit 1); have := hbm x
    have hCr : 0 ≤ C * coshW a x ^ (-(1 / p)) := by positivity
    calc C * coshW a x ^ (-(1 / p)) * boxMax (wf a p f) x
        ≤ C * coshW a x ^ (-(1 / p)) * (Real.exp a * (boxMax (wf a p f) x +
            boxMax (wf a p f) (x + unit 0) + boxMax (wf a p f) (x + unit 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ hCr
          nlinarith
      _ = _ := by ring
  have hvi : ∀ x, ∀ s ∈ Set.Icc 0 T, ∀ i, heatF S f s (x + unit i) ≤ M x := by
    intro x s hs i
    refine (hdom s hs (x + unit i)).trans ?_
    simp only [hMdef, steinMajorant]
    have hr := rpow_neg_coshW_add_unit_le ha0 hp1.le x i
    have := hbm (x + unit 0); have := hbm (x + unit 1); have := hbm x
    have hr0 := Real.rpow_nonneg (coshW_pos a x).le (-(1 / p))
    have hbi : boxMax (wf a p f) (x + unit i) ≤ boxMax (wf a p f) x +
        boxMax (wf a p f) (x + unit 0) + boxMax (wf a p f) (x + unit 1) := by
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> linarith
    calc C * coshW a (x + unit i) ^ (-(1 / p)) * boxMax (wf a p f) (x + unit i)
        ≤ C * (Real.exp a * coshW a x ^ (-(1 / p))) * boxMax (wf a p f) (x + unit i) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hC0.le) (hbm _)
      _ ≤ C * (Real.exp a * coshW a x ^ (-(1 / p))) * (boxMax (wf a p f) x +
            boxMax (wf a p f) (x + unit 0) + boxMax (wf a p f) (x + unit 1)) :=
          mul_le_mul_of_nonneg_left hbi
            (mul_nonneg hC0.le (mul_nonneg (Real.exp_pos a).le hr0))
      _ = _ := by ring
  -- the pointwise bound
  have hpt : ∀ x, coshW a x * gam S f T x ^ (p / 2) ≤ c ^ (p / 2) * KM ^ ((2 - p) / 2) *
      KI ^ (p / 2) * ((2 - p) / 2 * (coshW a x * M x ^ p / KM) +
        p / 2 * (coshW a x * ipos S f p T x / KI)) := by
    intro x
    exact pointwise_amgm (coshW_pos a x) (gam_nonneg hT x) (hM0 x)
      (ipos_nonneg hf hp1 hp2 hT x) hc0 hKMpos hKIpos hp1 hp2
      (gam_le_mul_ipos hf hp1 hp2 hT (hM0 x) x (hvx x) (hvi x))
  have hMsum := tsum_ofReal_coshW_mul_steinMajorant_le hf hfS hC0.le (a := a) hp1
  have hIsum := tsum_ofReal_coshW_mul_ipos_le hf hfS hp1 hp2 ha0 hT
  set K := c ^ (p / 2) * KM ^ ((2 - p) / 2) * KI ^ (p / 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have hw1 : 0 ≤ (2 - p) / 2 := by linarith
  have hw2 : 0 ≤ p / 2 := by linarith
  have hA := fun x => mul_nonneg (coshW_pos a x).le (Real.rpow_nonneg (hM0 x) p)
  have hB := fun x => mul_nonneg (coshW_pos a x).le (ipos_nonneg (S := S) hf hp1 hp2 hT x)
  calc ∑' x, ENNReal.ofReal (coshW a x * gam S f T x ^ (p / 2))
      ≤ ∑' x, (ENNReal.ofReal K * (ENNReal.ofReal ((2 - p) / 2 / KM) *
          ENNReal.ofReal (coshW a x * M x ^ p) + ENNReal.ofReal (p / 2 / KI) *
          ENNReal.ofReal (coshW a x * ipos S f p T x))) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by have := hA x; positivity) (by have := hB x; positivity),
          ← ENNReal.ofReal_mul hK0]
        refine ENNReal.ofReal_le_ofReal ((hpt x).trans (le_of_eq ?_))
        ring
    _ = ENNReal.ofReal K * (ENNReal.ofReal ((2 - p) / 2 / KM) *
          ∑' x, ENNReal.ofReal (coshW a x * M x ^ p) + ENNReal.ofReal (p / 2 / KI) *
          ∑' x, ENNReal.ofReal (coshW a x * ipos S f p T x)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left,
          ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal ((2 - p) / 2 / KM) * ENNReal.ofReal (KM * W) +
          ENNReal.ofReal (p / 2 / KI) * ENNReal.ofReal (KI * W)) := by
        gcongr
    _ = ENNReal.ofReal (K * W) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hK0]
        congr 1
        field_simp
        ring

end Rigidity.Poincare
