import Rigidity.Proofs.Corrector.GeneralStepTwoCapped
import Rigidity.Proofs.Corrector.GeneralStepTwoSiteGrad

/-!
# The finite-range weight of the Step 2 sum on `ℤᵈ`

At scale `R` with cap `n = ⌊log₃ R⌋` (`capScale`), the finite-range weight at `u` is

`W_R(u) = Σ_{v ∈ B(u, R)} 1{u ∈ B(v, 3κ cs(v))} d T_R(v)⁹`, with
`T_R(v) = Σ_{z ∈ B(v, 3κ cs(v))} (1 + 2d (J_R(z) + 1))`

(`finiteWeight`, `finiteBallSum`), with `cs` the side of the partition into good cubes capped at
scale `n` (`cappedSide`) and `J_R(z)` the local gradient bound at the site `z` (`siteGrad`). It is
at most `(2R + 1)ᵈ d ((6κR + 1)ᵈ (1 + 2d (6R + 1)))⁹` (`finiteWeight_le`), measurable, and local:
it depends only on the bonds inside `B(u, (3κ + 9)R + 1)` (`finiteWeight_eq_of_localBonds`). It
dominates the weight of the Step 2 sum (`stepTwoWeight_le_finiteWeight`) when no edge with its tail
outside `B(u, R)` has `u` in its box (`FarGood`), the capped sides are the sides on `B(u, R)`
(`SideGood`) and the local gradient bounds dominate the plane gradient bound on `B(u, R + 3κR)`
(`GradGood`).

This ports the planar file `DarioStepTwoFiniteWeight`: the boxes are the `ℓ^∞` boxes of `ℤᵈ`, the
sides are those of the partition into good cubes of `ℤᵈ` (`partSide`, `cappedSide`), the bound
`5 + 4J` of the plane gradient becomes `1 + 2d (J + 1)` (`planeGrad_le_siteGrad`), and the factor
`2` of the two edges with a given tail in the plane becomes `d`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External
open Rigidity.Poincare.GeneralDim (supBox mem_supBox card_supBox)
open scoped Classical ENNReal

variable {d : ℕ}

private theorem supBox_mono {x : Vertex d} {r r' : ℕ} (h : r ≤ r') :
    supBox x r ⊆ supBox x r' := fun z hz =>
  mem_supBox.2 fun i => (mem_supBox.1 hz i).trans (by exact_mod_cast h)

/-- The cap scale `⌊log₃ R⌋`. -/
def capScale (R : ℕ) : ℕ := Nat.log 3 R

theorem three_pow_capScale_le {R : ℕ} (hR : 1 ≤ R) : 3 ^ capScale R ≤ R :=
  Nat.pow_log_le_self 3 (by omega)

theorem mem_supBox_trans {u v z : Vertex d} {r₁ r₂ : ℕ} (hz : z ∈ supBox v r₁)
    (hv : v ∈ supBox u r₂) : z ∈ supBox u (r₁ + r₂) := by
  rw [mem_supBox] at *
  intro i
  have t := abs_sub_le (z i) (v i) (u i)
  have := hz i
  have := hv i
  push_cast
  linarith

theorem supBox_subset_of_mem {u v : Vertex d} {r₁ r₂ : ℕ} (hv : v ∈ supBox u r₂) :
    (↑(supBox v r₁) : Set (Vertex d)) ⊆ ↑(supBox u (r₁ + r₂)) := fun _ hz =>
  Finset.mem_coe.2 (mem_supBox_trans (Finset.mem_coe.1 hz) hv)

theorem cap_le_aux₁ {κ R a : ℕ} (ha : a ≤ R) : 8 * a + R ≤ (3 * κ + 9) * R + 1 := by
  nlinarith

theorem cap_le_aux₂ {κ R a : ℕ} (ha : a ≤ R) :
    2 * R + 1 + (3 * κ * a + R) ≤ (3 * κ + 9) * R + 1 := by
  nlinarith

theorem cap_le_aux₃ {κ R c : ℕ} (hc : c ≤ R) : 3 * κ * c + R ≤ R + 3 * κ * R := by
  nlinarith

/-- `T_R(v)`, over the fixed box of radius `3κ 3ⁿ`. -/
noncomputable def finiteBallSum (κ R : ℕ) (ω : Configuration d) (v : Vertex d) : ℝ :=
  ∑ z ∈ supBox v (3 * κ * 3 ^ capScale R),
    if z ∈ supBox v (3 * κ * cappedSide (capScale R) ω v) then
      1 + 2 * d * (siteGrad R ω z + 1) else 0

/-- **The finite-range weight.** -/
noncomputable def finiteWeight (κ R : ℕ) (ω : Configuration d) (u : Vertex d) : ℝ :=
  ∑ v ∈ supBox u R, if u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v) then
    d * finiteBallSum κ R ω v ^ 9 else 0

theorem finiteBallSum_eq (κ R : ℕ) (ω : Configuration d) (v : Vertex d) :
    finiteBallSum κ R ω v =
      ∑ z ∈ supBox v (3 * κ * cappedSide (capScale R) ω v),
        (1 + 2 * d * (siteGrad R ω z + 1)) := by
  unfold finiteBallSum
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext z
  simp only [Finset.mem_filter, and_iff_right_iff_imp]
  intro hz
  refine supBox_mono ?_ hz
  exact Nat.mul_le_mul_left _ (cappedSide_le _ _ _)

theorem finiteBallSum_nonneg {κ R : ℕ} (hR : 1 ≤ R) (ω : Configuration d) (v : Vertex d) :
    0 ≤ finiteBallSum κ R ω v :=
  Finset.sum_nonneg fun z _ => by
    split_ifs
    · have := siteGrad_nonneg hR ω z; positivity
    · exact le_rfl

theorem finiteBallSum_le {κ R : ℕ} (hR : 1 ≤ R) (ω : Configuration d) (v : Vertex d) :
    finiteBallSum κ R ω v ≤ (6 * κ * R + 1) ^ d * (1 + 2 * d * (6 * R + 1)) := by
  unfold finiteBallSum
  have hn := three_pow_capScale_le hR
  calc _ ≤ ∑ _z ∈ supBox v (3 * κ * 3 ^ capScale R), ((1 : ℝ) + 2 * d * (6 * R + 1)) :=
        Finset.sum_le_sum fun z _ => by
          split_ifs
          · have := siteGrad_le hR ω z
            have : (0 : ℝ) ≤ 2 * d := by positivity
            nlinarith
          · positivity
    _ = ((2 * (3 * κ * 3 ^ capScale R) + 1) ^ d : ℕ) * ((1 : ℝ) + 2 * d * (6 * R + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, card_supBox]
    _ ≤ (6 * κ * R + 1) ^ d * (1 + 2 * d * (6 * R + 1)) := by
        gcongr
        have : 2 * (3 * κ * 3 ^ capScale R) + 1 ≤ 6 * κ * R + 1 := by
          have := Nat.mul_le_mul_left (3 * κ) hn
          have e : 6 * κ * R = 2 * (3 * κ * R) := by ring
          omega
        exact_mod_cast pow_le_pow_left₀ (Nat.zero_le _) this d

theorem finiteWeight_nonneg {κ R : ℕ} (hR : 1 ≤ R) (ω : Configuration d) (u : Vertex d) :
    0 ≤ finiteWeight κ R ω u :=
  Finset.sum_nonneg fun v _ => by
    split_ifs
    · have := finiteBallSum_nonneg (κ := κ) hR ω v; positivity
    · exact le_rfl

/-- **The finite-range weight is bounded**:
`W_R(u) ≤ (2R + 1)ᵈ d ((6κR + 1)ᵈ (1 + 2d (6R + 1)))⁹`. -/
theorem finiteWeight_le {κ R : ℕ} (hR : 1 ≤ R) (ω : Configuration d) (u : Vertex d) :
    finiteWeight κ R ω u ≤
      (2 * R + 1) ^ d * (d * ((6 * κ * R + 1) ^ d * (1 + 2 * d * (6 * R + 1))) ^ 9) := by
  unfold finiteWeight
  calc _ ≤ ∑ _v ∈ supBox u R,
        ((d : ℝ) * ((6 * κ * R + 1) ^ d * (1 + 2 * d * (6 * (R : ℝ) + 1))) ^ 9) :=
        Finset.sum_le_sum fun v _ => by
          split_ifs
          · have h1 := finiteBallSum_le (κ := κ) hR ω v
            have h0 := finiteBallSum_nonneg (κ := κ) hR ω v
            gcongr
          · positivity
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, card_supBox]
        push_cast
        ring

theorem measurable_finiteBallSum (κ R : ℕ) (v : Vertex d) :
    Measurable fun ω => finiteBallSum κ R ω v := by
  unfold finiteBallSum
  refine Finset.measurable_sum _ fun z _ => Measurable.ite ?_
    (((measurable_siteGrad R z).add_const 1).const_mul (2 * d) |>.const_add 1) measurable_const
  have : {ω : Configuration d | z ∈ supBox v (3 * κ * cappedSide (capScale R) ω v)} =
      (fun ω => cappedSide (capScale R) ω v) ⁻¹'
        {m | z ∈ supBox v (3 * κ * m)} := rfl
  rw [this]
  exact measurable_cappedSide _ v (Set.to_countable _).measurableSet

theorem measurable_finiteWeight (κ R : ℕ) (u : Vertex d) :
    Measurable fun ω => finiteWeight κ R ω u := by
  unfold finiteWeight
  refine Finset.measurable_sum _ fun v _ => Measurable.ite ?_
    (((measurable_finiteBallSum κ R v).pow_const 9).const_mul d) measurable_const
  have : {ω : Configuration d | u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v)} =
      (fun ω => cappedSide (capScale R) ω v) ⁻¹'
        {m | u ∈ supBox v (3 * κ * m)} := rfl
  rw [this]
  exact measurable_cappedSide _ v (Set.to_countable _).measurableSet

/-- **Locality of the finite-range weight.** -/
theorem finiteWeight_eq_of_localBonds {ω ω' : Configuration d} {κ R : ℕ} (hR : 1 ≤ R)
    {u : Vertex d}
    (h : ∀ e ∈ localBonds (↑(supBox u ((3 * κ + 9) * R + 1)) : Set (Vertex d)), ω e = ω' e) :
    finiteWeight κ R ω' u = finiteWeight κ R ω u := by
  have hn := three_pow_capScale_le hR
  have hcap : ∀ v ∈ supBox u R, cappedSide (capScale R) ω' v = cappedSide (capScale R) ω v := by
    intro v hv
    refine cappedSide_eq_of_localBonds fun e he => h e (localBonds_mono ?_ he)
    refine (localRegion_capCube_subset _ v).trans ((supBox_subset_of_mem hv).trans ?_)
    intro z hz
    exact Finset.mem_coe.2 (supBox_mono (cap_le_aux₁ hn) (Finset.mem_coe.1 hz))
  have hsite : ∀ v ∈ supBox u R, ∀ z ∈ supBox v (3 * κ * 3 ^ capScale R),
      siteGrad R ω' z = siteGrad R ω z := by
    intro v hv z hz
    refine siteGrad_eq_of_localBonds fun e he => h e (localBonds_mono ?_ he)
    refine (supBox_subset_of_mem (mem_supBox_trans hz hv)).trans ?_
    intro y hy
    exact Finset.mem_coe.2 (supBox_mono (cap_le_aux₂ hn) (Finset.mem_coe.1 hy))
  have hball : ∀ v ∈ supBox u R, finiteBallSum κ R ω' v = finiteBallSum κ R ω v := by
    intro v hv
    unfold finiteBallSum
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [hcap v hv, hsite v hv z hz]
  unfold finiteWeight
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [hcap v hv, hball v hv]

/-- No edge with its tail outside `B(u, R)` has `u` in its box. -/
def FarGood (κ R : ℕ) (ω : Configuration d) (u : Vertex d) : Prop :=
  ∀ v, u ∈ supBox v (3 * κ * partSide ω v) → v ∈ supBox u R

/-- The capped sides are the sides on `B(u, R)`. -/
def SideGood (R : ℕ) (ω : Configuration d) (u : Vertex d) : Prop :=
  ∀ v ∈ supBox u R, partSide ω v = cappedSide (capScale R) ω v

section Grad

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The local gradient bounds dominate the plane gradient bound on `B(u, R + 3κR)`. -/
def GradGood (κ R : ℕ) (i : Fin d) (ω : Configuration d) (u : Vertex d) : Prop :=
  ∀ z ∈ supBox u (R + 3 * κ * R), planeGrad hG hGv i ω z ≤ 1 + 2 * d * (siteGrad R ω z + 1)

/-- **The finite-range weight dominates the weight on the good events.** -/
theorem stepTwoWeight_le_finiteWeight {ω : Configuration d} (hP : PartitionEvent ω)
    {κ R : ℕ} (hR : 1 ≤ R) {i : Fin d} {u : Vertex d} (hfar : FarGood κ R ω u)
    (hside : SideGood R ω u) (hgrad : GradGood hG hGv κ R i ω u) :
    stepTwoWeight hG hGv κ i ω u ≤ ENNReal.ofReal (finiteWeight κ R ω u) := by
  have hn := three_pow_capScale_le hR
  set g : Vertex d → ℝ := fun z => 1 + 2 * d * (siteGrad R ω z + 1) with hg
  have hg1 : ∀ z, 1 ≤ g z := fun z => by
    have := siteGrad_nonneg hR ω z
    have h2 : 0 ≤ 2 * (d : ℝ) * (siteGrad R ω z + 1) := by positivity
    simp only [hg]; linarith
  have hedge : ∀ v (k : Fin d), (if u ∈ stepTwoBox κ ω (v, k) then
      ENNReal.ofReal (stepTwoFactor hG hGv κ i ω (v, k)) else 0) ≤
      if v ∈ supBox u R ∧ u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v) then
        ENNReal.ofReal (finiteBallSum κ R ω v ^ 9) else 0 := by
    intro v k
    split_ifs with hu hc
    · refine ENNReal.ofReal_le_ofReal ?_
      have hu' := mem_supBox_of_mem_stepTwoBox hP hu
      have hvu := hfar v hu'
      have hs := hside v hvu
      have hb := stepTwoFactor_le_of_bound hG hGv hP (a := (v, k)) hg1 fun z hz => by
        refine hgrad z (supBox_mono ?_ (mem_supBox_trans hz hvu))
        rw [show (v, k).1 = v from rfl, hs]
        exact cap_le_aux₃ ((cappedSide_le _ ω v).trans hn)
      refine hb.trans (le_of_eq ?_)
      rw [finiteBallSum_eq, ← hs]
    · exfalso
      have hu' := mem_supBox_of_mem_stepTwoBox hP hu
      have hvu := hfar v hu'
      have hs := hside v hvu
      rw [show (v, k).1 = v from rfl, hs] at hu'
      exact hc ⟨hvu, hu'⟩
    · positivity
    · exact le_rfl
  unfold stepTwoWeight
  rw [ENNReal.tsum_prod (f := fun v k => if u ∈ stepTwoBox κ ω (v, k) then
    ENNReal.ofReal (stepTwoFactor hG hGv κ i ω (v, k)) else 0)]
  calc ∑' v, ∑' k : Fin d, (if u ∈ stepTwoBox κ ω (v, k) then
        ENNReal.ofReal (stepTwoFactor hG hGv κ i ω (v, k)) else 0)
      ≤ ∑' v, (if v ∈ supBox u R ∧ u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v) then
          (d : ℝ≥0∞) * ENNReal.ofReal (finiteBallSum κ R ω v ^ 9) else 0) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        rw [tsum_fintype]
        calc ∑ k : Fin d, (if u ∈ stepTwoBox κ ω (v, k) then
              ENNReal.ofReal (stepTwoFactor hG hGv κ i ω (v, k)) else 0)
            ≤ ∑ _k : Fin d, (if v ∈ supBox u R ∧
                u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v) then
              ENNReal.ofReal (finiteBallSum κ R ω v ^ 9) else 0) :=
              Finset.sum_le_sum fun k _ => hedge v k
          _ = _ := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              split_ifs <;> simp
    _ = ENNReal.ofReal (finiteWeight κ R ω u) := by
        rw [tsum_eq_sum (s := supBox u R) fun v hv => by rw [if_neg fun h => hv h.1]]
        unfold finiteWeight
        rw [ENNReal.ofReal_sum_of_nonneg fun v _ => by
          split_ifs
          · have := finiteBallSum_nonneg (κ := κ) hR ω v; positivity
          · exact le_rfl]
        refine Finset.sum_congr rfl fun v hv => ?_
        by_cases hc : u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v)
        · rw [if_pos ⟨hv, hc⟩, if_pos hc, ENNReal.ofReal_mul (by positivity)]
          simp
        · rw [if_neg fun h => hc h.2, if_neg hc, ENNReal.ofReal_zero]

end Grad

end Rigidity.Corrector.GeneralDim
