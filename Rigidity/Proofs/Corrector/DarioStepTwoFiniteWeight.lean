import Rigidity.Proofs.Corrector.DarioStepTwoSiteGrad

/-!
# The finite-range weight of the Step 2 sum

At scale `R` with cap `n = ⌊log₃ R⌋` (`capScale`), the finite-range weight at `u` is

`W_R(u) = Σ_{v ∈ B(u, R)} 1{u ∈ B(v, 3κ cs(v))} 2 T_R(v)⁹`, with
`T_R(v) = Σ_{z ∈ B(v, 3κ cs(v))} (5 + 4 J_R(z))`

(`finiteWeight`, `finiteBallSum`), with `cs` the side of the planar partition capped at scale `n`
(`cappedSide`) and `J_R(z)` the local gradient bound at the site `z` (`siteGrad`). It is at most
`(2R + 1)² 2 ((6κR + 1)² (5 + 24R))⁹` (`finiteWeight_le`), measurable, and local: it depends only
on the bonds inside `B(u, (3κ + 9)R + 1)` (`finiteWeight_eq_of_localBonds`). It dominates the
weight of the Step 2 sum (`stepTwoWeight_le_finiteWeight`) when no edge outside `B(u, R)` has `u` in
its box (`FarGood`), the capped sides are the sides on `B(u, R)` (`SideGood`) and the local
gradient bounds dominate the plane gradient bound on `B(u, R + 3κR)` (`GradGood`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

/-- The cap scale `⌊log₃ R⌋`. -/
def capScale (R : ℕ) : ℕ := Nat.log 3 R

theorem three_pow_capScale_le {R : ℕ} (hR : 1 ≤ R) : 3 ^ capScale R ≤ R :=
  Nat.pow_log_le_self 3 (by omega)

/-- `T_R(v)`, over the fixed box of radius `3κ 3ⁿ`. -/
noncomputable def finiteBallSum (κ R : ℕ) (ω : Configuration 2) (v : Vertex 2) : ℝ :=
  ∑ z ∈ supBox v (3 * κ * 3 ^ capScale R),
    if z ∈ supBox v (3 * κ * cappedSide (capScale R) ω v) then 5 + 4 * siteGrad R ω z else 0

/-- **The finite-range weight.** -/
noncomputable def finiteWeight (κ R : ℕ) (ω : Configuration 2) (u : Vertex 2) : ℝ :=
  ∑ v ∈ supBox u R, if u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v) then
    2 * finiteBallSum κ R ω v ^ 9 else 0

theorem finiteBallSum_eq (κ R : ℕ) (ω : Configuration 2) (v : Vertex 2) :
    finiteBallSum κ R ω v =
      ∑ z ∈ supBox v (3 * κ * cappedSide (capScale R) ω v), (5 + 4 * siteGrad R ω z) := by
  unfold finiteBallSum
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext z
  simp only [Finset.mem_filter, and_iff_right_iff_imp]
  intro hz
  refine supBox_mono ?_ hz
  exact Nat.mul_le_mul_left _ (cappedSide_le _ _ _)

theorem finiteBallSum_nonneg {κ R : ℕ} (hR : 1 ≤ R) (ω : Configuration 2) (v : Vertex 2) :
    0 ≤ finiteBallSum κ R ω v :=
  Finset.sum_nonneg fun z _ => by
    split_ifs
    · have := siteGrad_nonneg hR ω z; linarith
    · exact le_rfl

theorem finiteBallSum_le {κ R : ℕ} (hR : 1 ≤ R) (ω : Configuration 2) (v : Vertex 2) :
    finiteBallSum κ R ω v ≤ (6 * κ * R + 1) ^ 2 * (5 + 24 * R) := by
  unfold finiteBallSum
  have hn := three_pow_capScale_le hR
  calc _ ≤ ∑ _z ∈ supBox v (3 * κ * 3 ^ capScale R), ((5 : ℝ) + 24 * R) :=
        Finset.sum_le_sum fun z _ => by
          split_ifs
          · have := siteGrad_le hR ω z; linarith
          · positivity
    _ = ((2 * (3 * κ * 3 ^ capScale R) + 1) ^ 2 : ℕ) * ((5 : ℝ) + 24 * R) := by
        rw [Finset.sum_const, nsmul_eq_mul, card_supBox]
    _ ≤ (6 * κ * R + 1) ^ 2 * (5 + 24 * R) := by
        gcongr
        have : 2 * (3 * κ * 3 ^ capScale R) + 1 ≤ 6 * κ * R + 1 := by
          have := Nat.mul_le_mul_left (3 * κ) hn
          have e : 6 * κ * R = 2 * (3 * κ * R) := by ring
          omega
        exact_mod_cast pow_le_pow_left₀ (Nat.zero_le _) this 2

theorem finiteWeight_nonneg {κ R : ℕ} (hR : 1 ≤ R) (ω : Configuration 2) (u : Vertex 2) :
    0 ≤ finiteWeight κ R ω u :=
  Finset.sum_nonneg fun v _ => by
    split_ifs
    · have := finiteBallSum_nonneg (κ := κ) hR ω v; positivity
    · exact le_rfl

/-- **The finite-range weight is bounded.** -/
theorem finiteWeight_le {κ R : ℕ} (hR : 1 ≤ R) (ω : Configuration 2) (u : Vertex 2) :
    finiteWeight κ R ω u ≤ (2 * R + 1) ^ 2 * (2 * ((6 * κ * R + 1) ^ 2 * (5 + 24 * R)) ^ 9) := by
  unfold finiteWeight
  calc _ ≤ ∑ _v ∈ supBox u R, (2 * ((6 * κ * R + 1) ^ 2 * (5 + 24 * (R : ℝ))) ^ 9) :=
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

theorem measurable_finiteBallSum (κ R : ℕ) (v : Vertex 2) :
    Measurable fun ω => finiteBallSum κ R ω v := by
  unfold finiteBallSum
  refine Finset.measurable_sum _ fun z _ => Measurable.ite ?_
    ((measurable_siteGrad R z).const_mul 4 |>.const_add 5) measurable_const
  have : {ω : Configuration 2 | z ∈ supBox v (3 * κ * cappedSide (capScale R) ω v)} =
      (fun ω => cappedSide (capScale R) ω v) ⁻¹'
        {m | z ∈ supBox v (3 * κ * m)} := rfl
  rw [this]
  exact measurable_cappedSide _ v (Set.to_countable _).measurableSet

theorem measurable_finiteWeight (κ R : ℕ) (u : Vertex 2) :
    Measurable fun ω => finiteWeight κ R ω u := by
  unfold finiteWeight
  refine Finset.measurable_sum _ fun v _ => Measurable.ite ?_
    (((measurable_finiteBallSum κ R v).pow_const 9).const_mul 2) measurable_const
  have : {ω : Configuration 2 | u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v)} =
      (fun ω => cappedSide (capScale R) ω v) ⁻¹'
        {m | u ∈ supBox v (3 * κ * m)} := rfl
  rw [this]
  exact measurable_cappedSide _ v (Set.to_countable _).measurableSet


theorem mem_supBox_trans {u v z : Vertex 2} {r₁ r₂ : ℕ} (hz : z ∈ supBox v r₁)
    (hv : v ∈ supBox u r₂) : z ∈ supBox u (r₁ + r₂) := by
  rw [mem_supBox] at *
  intro i
  have t := abs_sub_le (z i) (v i) (u i)
  have := hz i
  have := hv i
  push_cast
  linarith

theorem supBox_subset_of_mem {u v : Vertex 2} {r₁ r₂ : ℕ} (hv : v ∈ supBox u r₂) :
    (↑(supBox v r₁) : Set (Vertex 2)) ⊆ ↑(supBox u (r₁ + r₂)) := fun _ hz =>
  Finset.mem_coe.2 (mem_supBox_trans (Finset.mem_coe.1 hz) hv)

private theorem cap_le_aux₁ {κ R a : ℕ} (ha : a ≤ R) : 8 * a + R ≤ (3 * κ + 9) * R + 1 := by
  nlinarith

private theorem cap_le_aux₂ {κ R a : ℕ} (ha : a ≤ R) :
    2 * R + 1 + (3 * κ * a + R) ≤ (3 * κ + 9) * R + 1 := by
  nlinarith

private theorem cap_le_aux₃ {κ R c : ℕ} (hc : c ≤ R) : 3 * κ * c + R ≤ R + 3 * κ * R := by
  nlinarith

/-- **Locality of the finite-range weight.** -/
theorem finiteWeight_eq_of_localBonds {ω ω' : Configuration 2} {κ R : ℕ} (hR : 1 ≤ R)
    {u : Vertex 2}
    (h : ∀ e ∈ localBonds (↑(supBox u ((3 * κ + 9) * R + 1)) : Set (Vertex 2)), ω e = ω' e) :
    finiteWeight κ R ω' u = finiteWeight κ R ω u := by
  have hn := three_pow_capScale_le hR
  have hcap : ∀ v ∈ supBox u R, cappedSide (capScale R) ω' v = cappedSide (capScale R) ω v := by
    intro v hv
    refine cappedSide_eq_of_localBonds fun e he => h e (localBonds_mono ?_ he)
    refine (planarLocalRegion_capCube_subset _ v).trans ((supBox_subset_of_mem hv).trans ?_)
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
def FarGood (κ R : ℕ) (ω : Configuration 2) (u : Vertex 2) : Prop :=
  ∀ v, u ∈ supBox v (3 * κ * planarSide ω v) → v ∈ supBox u R

/-- The capped sides are the sides on `B(u, R)`. -/
def SideGood (R : ℕ) (ω : Configuration 2) (u : Vertex 2) : Prop :=
  ∀ v ∈ supBox u R, planarSide ω v = cappedSide (capScale R) ω v

section Grad

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The local gradient bounds dominate the plane gradient bound on `B(u, R + 3κR)`. -/
def GradGood (κ R : ℕ) (i : Fin 2) (ω : Configuration 2) (u : Vertex 2) : Prop :=
  ∀ z ∈ supBox u (R + 3 * κ * R), planeGrad hG hGv i ω z ≤ 5 + 4 * siteGrad R ω z

/-- **The finite-range weight dominates the weight on the good events.** -/
theorem stepTwoWeight_le_finiteWeight {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {κ R : ℕ} (hR : 1 ≤ R) {i : Fin 2} {u : Vertex 2} (hfar : FarGood κ R ω u)
    (hside : SideGood R ω u) (hgrad : GradGood hG hGv κ R i ω u) :
    stepTwoWeight hG hGv κ i ω u ≤ ENNReal.ofReal (finiteWeight κ R ω u) := by
  have hn := three_pow_capScale_le hR
  set g : Vertex 2 → ℝ := fun z => 5 + 4 * siteGrad R ω z with hg
  have hg1 : ∀ z, 1 ≤ g z := fun z => by
    have := siteGrad_nonneg hR ω z; simp only [hg]; linarith
  -- each edge at `v`
  have hedge : ∀ v (k : Fin 2), (if u ∈ stepTwoBox κ ω (v, k) then
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
  calc ∑' v, ∑' k : Fin 2, (if u ∈ stepTwoBox κ ω (v, k) then
        ENNReal.ofReal (stepTwoFactor hG hGv κ i ω (v, k)) else 0)
      ≤ ∑' v, (if v ∈ supBox u R ∧ u ∈ supBox v (3 * κ * cappedSide (capScale R) ω v) then
          2 * ENNReal.ofReal (finiteBallSum κ R ω v ^ 9) else 0) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        rw [tsum_fintype]
        calc ∑ k : Fin 2, (if u ∈ stepTwoBox κ ω (v, k) then
              ENNReal.ofReal (stepTwoFactor hG hGv κ i ω (v, k)) else 0)
            ≤ ∑ _k : Fin 2, (if v ∈ supBox u R ∧
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
        · rw [if_pos ⟨hv, hc⟩, if_pos hc, ENNReal.ofReal_mul (by norm_num)]
          simp
        · rw [if_neg fun h => hc h.2, if_neg hc, ENNReal.ofReal_zero]

end Grad

end Rigidity.Corrector
