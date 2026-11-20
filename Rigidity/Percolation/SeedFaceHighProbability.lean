import Rigidity.Percolation.SeedFaceTrialProbability

/-!
# High-probability outward seed creation

A supercritical base field and an independent positive sprinkling connect a
large centered seed to a fully open outward trial with arbitrarily high
probability.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External Filter
open scoped Topology

/-- With positive percolation probability in the base layer and positive
sprinkling density, a centered seed connects to an outward open trial with
probability arbitrarily close to one on all sufficiently large cube faces. -/
theorem exists_seed_eventually_faceSuccess {d : ℕ} (q r : unitInterval)
    (hq : (q : ℝ) < 1) (hθ : 0 < LatticeProb.Percolation.theta d q)
    (hr : 0 < (r : ℝ)) (i : Fin d) (η : ℝ) (hη : 0 < η) :
    ∃ M : ℕ, 0 < M ∧ ∀ᶠ n in atTop,
      1 - η < (bondPairLaw d q r).real (seedReachableFaceSuccess
        (centeredBondCube (M + n)) (centeredBondCubeFinset M)
        (centeredCubeOrthantFace (M + n) i (fun _ => true)) (2 * M + 1) i (M + n)) := by
  let δ : ℝ := min (η / 3) (1 / 3)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ ≤ 1 / 3 := min_le_right _ _
  have hδη : 3 * δ ≤ η := by
    have h := min_le_left (η / 3) (1 / 3)
    dsimp only [δ]
    linarith
  obtain ⟨M, hMpos, hM⟩ := exists_seed_eventually_few_orthantFace_contacts q hq hθ i δ hδ
  let k := 2 * M + 1
  have hk : 0 < k := by dsimp [k]; omega
  let a : ℝ := (r : ℝ) ^ ((k ^ d + 1) ^ 2)
  have ha : 0 < a := pow_pos hr _
  have ha1 : a ≤ 1 := pow_le_one₀ r.property.1 r.property.2
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr ha1)
    (show 1 - a < 1 by linarith)
  obtain ⟨m, hm⟩ := (hlim.eventually (eventually_lt_nhds hδ)).exists
  refine ⟨M, hMpos, ?_⟩
  filter_upwards [hM (m * k ^ d)] with n hn
  have hface : ∀ x ∈ centeredCubeOrthantFace (M + n) i (fun _ => true),
      x i = ((M + n : ℕ) : ℤ) := by
    intro x hx
    have h := ((mem_centeredCubeOrthantFace _ _ _ _).mp hx).2.1
    simpa only [↓reduceIte] using h
  have hb := measureReal_seedReachableFaceSuccess_lower (m := m) hk q r
    (centeredBondCube (M + n)) (centeredBondCubeFinset M)
    (centeredCubeOrthantFace (M + n) i (fun _ => true)) i (M + n) hface
  have hpow : 0 ≤ (1 - a) ^ m := pow_nonneg (sub_nonneg.mpr ha1) _
  have hprob : 0 ≤ (latticeBondLaw d q).real (fewSeedContacts
      (centeredBondCube (M + n)) (centeredBondCubeFinset M)
      (centeredCubeOrthantFace (M + n) i (fun _ => true)) (m * k ^ d)) := measureReal_nonneg
  have hprod : 0 ≤ (δ - (1 - a) ^ m) * (1 - δ) :=
    mul_nonneg (le_of_lt (sub_pos.mpr hm)) (by linarith)
  have hprod' : 0 ≤ (1 - (1 - a) ^ m) *
      (δ - (latticeBondLaw d q).real (fewSeedContacts
        (centeredBondCube (M + n)) (centeredBondCubeFinset M)
        (centeredCubeOrthantFace (M + n) i (fun _ => true)) (m * k ^ d))) :=
    mul_nonneg (by linarith) (le_of_lt (sub_pos.mpr hn))
  change 1 - η < (bondPairLaw d q r).real (seedReachableFaceSuccess
    (centeredBondCube (M + n)) (centeredBondCubeFinset M)
    (centeredCubeOrthantFace (M + n) i (fun _ => true)) k i (M + n))
  change (1 - (1 - a) ^ m) * (1 - (latticeBondLaw d q).real (fewSeedContacts
    (centeredBondCube (M + n)) (centeredBondCubeFinset M)
    (centeredCubeOrthantFace (M + n) i (fun _ => true)) (m * k ^ d))) ≤ _ at hb
  nlinarith

end Rigidity.Percolation
