import Rigidity.Proofs.Corrector.GeneralStepTwoCapped
import Rigidity.Proofs.Corrector.GeneralStepTwoSiteGrad

/-!
# The finite-range weight of the Step 2 sum on `ℤᵈ`

At scale `R` with cap `n = ⌊log₃ R⌋` (`capScale`), the capped side of the edge `a = (v, k)` is
`cm(a) = max(cs(v), cs♭(a, v))` (`cappedEdgeSide`), with `cs` the side of the partition into good
cubes capped at scale `n` (`cappedSide`) and `cs♭(a, ·)` the same side for the configuration with
the bond of `a` closed. The finite-range weight at `u` is

`W_R(u) = Σ_{v ∈ B(u, R)} Σ_{k < d} 1{u ∈ B(v, 3κ cm(v, k))} T_R(v, k)⁹`, with
`T_R(a) = Σ_{z ∈ B(v, 3κ cm(a))} (1 + 2d (J_R(z) + 1))`

(`finiteWeight`, `finiteBallSum`), with `J_R(z)` the local gradient bound at the site `z`
(`siteGrad`). It is at most `(2R + 1)ᵈ d ((6κR + 1)ᵈ (1 + 2d (6R + 1)))⁹` (`finiteWeight_le`),
measurable, and local: it depends only on the bonds inside `B(u, (3κ + 9)R + 1)`
(`finiteWeight_eq_of_localBonds`). It dominates the weight of the Step 2 sum, whose box at the edge
`a` has radius at most `3κ max(s(v), s♭(a, v))` (`stepTwoWeight_le_finiteWeight`), when no edge with
its tail outside `B(u, R)` has `u` in the box of radius `3κ s(v)` or `3κ s♭(a, v)` (`FarGood`,
`FarGoodFlip`), the capped sides are the sides on `B(u, R)` (`SideGood`, `SideGoodFlip`) and the
local gradient bounds dominate the plane gradient bound on `B(u, R + 3κR)` (`GradGood`).

This ports the planar file `DarioStepTwoFiniteWeight`: the boxes are the `ℓ^∞` boxes of `ℤᵈ`, the
sides are those of the partition into good cubes of `ℤᵈ` (`partSide`, `cappedSide`), the radius of
an edge also uses the side of the configuration with its bond closed (as the radius `stepTwoRadius`
of the weight), the bound `5 + 4J` of the plane gradient becomes `1 + 2d (J + 1)`
(`planeGrad_le_siteGrad`), and the sum over the `2` edges with a given tail in the plane becomes
the sum over the `d` edges.
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

private theorem cap_le_aux₁ {κ R a : ℕ} (ha : a ≤ R) : 8 * a + R ≤ (3 * κ + 9) * R + 1 := by
  nlinarith

private theorem cap_le_aux₂ {κ R a : ℕ} (ha : a ≤ R) :
    2 * R + 1 + (3 * κ * a + R) ≤ (3 * κ + 9) * R + 1 := by
  nlinarith

private theorem cap_le_aux₃ {κ R c : ℕ} (hc : c ≤ R) : 3 * κ * c + R ≤ R + 3 * κ * R := by
  nlinarith

/-- The capped side `max(cs(v), cs♭(a, v))` of the edge `a = (v, k)`. -/
noncomputable def cappedEdgeSide (n : ℕ) (ω : Configuration d) (a : LatticeEdge d) : ℕ :=
  max (cappedSide n ω a.1) (cappedSide n (setBond (edgeBond a) false ω) a.1)

theorem cappedEdgeSide_le (n : ℕ) (ω : Configuration d) (a : LatticeEdge d) :
    cappedEdgeSide n ω a ≤ 3 ^ n :=
  max_le (cappedSide_le _ _ _) (cappedSide_le _ _ _)

/-- **Locality of the capped side of an edge.** -/
theorem cappedEdgeSide_eq_of_localBonds {ω ω' : Configuration d} {n : ℕ} {a : LatticeEdge d}
    (h : ∀ e ∈ localBonds (capCube n a.1).localRegion, ω e = ω' e) :
    cappedEdgeSide n ω' a = cappedEdgeSide n ω a := by
  unfold cappedEdgeSide
  rw [cappedSide_eq_of_localBonds h, cappedSide_setBond_eq_of_localBonds _ _ h]

theorem measurable_cappedEdgeSide (n : ℕ) (a : LatticeEdge d) :
    Measurable fun ω : Configuration d => cappedEdgeSide n ω a :=
  (measurable_cappedSide n a.1).max (measurable_cappedSide_setBond n a.1 (edgeBond a) false)

/-- `T_R(a)`, over the fixed box of radius `3κ 3ⁿ`. -/
noncomputable def finiteBallSum (κ R : ℕ) (ω : Configuration d) (a : LatticeEdge d) : ℝ :=
  ∑ z ∈ supBox a.1 (3 * κ * 3 ^ capScale R),
    if z ∈ supBox a.1 (3 * κ * cappedEdgeSide (capScale R) ω a) then
      1 + 2 * d * (siteGrad R ω z + 1) else 0

/-- **The finite-range weight.** -/
noncomputable def finiteWeight (κ R : ℕ) (ω : Configuration d) (u : Vertex d) : ℝ :=
  ∑ v ∈ supBox u R, ∑ k : Fin d,
    if u ∈ supBox v (3 * κ * cappedEdgeSide (capScale R) ω (v, k)) then
      finiteBallSum κ R ω (v, k) ^ 9 else 0

theorem finiteBallSum_eq (κ R : ℕ) (ω : Configuration d) (a : LatticeEdge d) :
    finiteBallSum κ R ω a =
      ∑ z ∈ supBox a.1 (3 * κ * cappedEdgeSide (capScale R) ω a),
        (1 + 2 * d * (siteGrad R ω z + 1)) := by
  unfold finiteBallSum
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext z
  simp only [Finset.mem_filter, and_iff_right_iff_imp]
  intro hz
  refine supBox_mono ?_ hz
  exact Nat.mul_le_mul_left _ (cappedEdgeSide_le _ _ _)

theorem finiteBallSum_nonneg {κ R : ℕ} (hR : 1 ≤ R) (ω : Configuration d) (a : LatticeEdge d) :
    0 ≤ finiteBallSum κ R ω a :=
  Finset.sum_nonneg fun z _ => by
    split_ifs
    · have := siteGrad_nonneg hR ω z; positivity
    · exact le_rfl

theorem finiteBallSum_le {κ R : ℕ} (hR : 1 ≤ R) (ω : Configuration d) (a : LatticeEdge d) :
    finiteBallSum κ R ω a ≤ (6 * κ * R + 1) ^ d * (1 + 2 * d * (6 * R + 1)) := by
  unfold finiteBallSum
  have hn := three_pow_capScale_le hR
  calc _ ≤ ∑ _z ∈ supBox a.1 (3 * κ * 3 ^ capScale R), ((1 : ℝ) + 2 * d * (6 * R + 1)) :=
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
  Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun k _ => by
    split_ifs
    · have := finiteBallSum_nonneg (κ := κ) hR ω (v, k); positivity
    · exact le_rfl

/-- **The finite-range weight is bounded**:
`W_R(u) ≤ (2R + 1)ᵈ d ((6κR + 1)ᵈ (1 + 2d (6R + 1)))⁹`. -/
theorem finiteWeight_le {κ R : ℕ} (hR : 1 ≤ R) (ω : Configuration d) (u : Vertex d) :
    finiteWeight κ R ω u ≤
      (2 * R + 1) ^ d * (d * ((6 * κ * R + 1) ^ d * (1 + 2 * d * (6 * R + 1))) ^ 9) := by
  unfold finiteWeight
  calc _ ≤ ∑ _v ∈ supBox u R, ∑ _k : Fin d,
        ((6 * κ * R + 1) ^ d * (1 + 2 * d * (6 * (R : ℝ) + 1))) ^ 9 :=
        Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun k _ => by
          split_ifs
          · have h1 := finiteBallSum_le (κ := κ) hR ω (v, k)
            have h0 := finiteBallSum_nonneg (κ := κ) hR ω (v, k)
            gcongr
          · positivity
    _ = _ := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, card_supBox,
          nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        ring

theorem measurable_finiteBallSum (κ R : ℕ) (a : LatticeEdge d) :
    Measurable fun ω => finiteBallSum κ R ω a := by
  unfold finiteBallSum
  refine Finset.measurable_sum _ fun z _ => Measurable.ite ?_
    (((measurable_siteGrad R z).add_const 1).const_mul (2 * d) |>.const_add 1) measurable_const
  have : {ω : Configuration d | z ∈ supBox a.1 (3 * κ * cappedEdgeSide (capScale R) ω a)} =
      (fun ω => cappedEdgeSide (capScale R) ω a) ⁻¹'
        {m | z ∈ supBox a.1 (3 * κ * m)} := rfl
  rw [this]
  exact measurable_cappedEdgeSide _ a (Set.to_countable _).measurableSet

theorem measurable_finiteWeight (κ R : ℕ) (u : Vertex d) :
    Measurable fun ω => finiteWeight κ R ω u := by
  unfold finiteWeight
  refine Finset.measurable_sum _ fun v _ => Finset.measurable_sum _ fun k _ => Measurable.ite ?_
    ((measurable_finiteBallSum κ R (v, k)).pow_const 9) measurable_const
  have : {ω : Configuration d | u ∈ supBox v (3 * κ * cappedEdgeSide (capScale R) ω (v, k))} =
      (fun ω => cappedEdgeSide (capScale R) ω (v, k)) ⁻¹'
        {m | u ∈ supBox v (3 * κ * m)} := rfl
  rw [this]
  exact measurable_cappedEdgeSide _ (v, k) (Set.to_countable _).measurableSet

/-- **Locality of the finite-range weight.** -/
theorem finiteWeight_eq_of_localBonds {ω ω' : Configuration d} {κ R : ℕ} (hR : 1 ≤ R)
    {u : Vertex d}
    (h : ∀ e ∈ localBonds (↑(supBox u ((3 * κ + 9) * R + 1)) : Set (Vertex d)), ω e = ω' e) :
    finiteWeight κ R ω' u = finiteWeight κ R ω u := by
  have hn := three_pow_capScale_le hR
  have hcap : ∀ v ∈ supBox u R, ∀ k : Fin d,
      cappedEdgeSide (capScale R) ω' (v, k) = cappedEdgeSide (capScale R) ω (v, k) := by
    intro v hv k
    refine cappedEdgeSide_eq_of_localBonds fun e he => h e (localBonds_mono ?_ he)
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
  have hball : ∀ v ∈ supBox u R, ∀ k : Fin d,
      finiteBallSum κ R ω' (v, k) = finiteBallSum κ R ω (v, k) := by
    intro v hv k
    unfold finiteBallSum
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [hcap v hv k, hsite v hv z hz]
  unfold finiteWeight
  refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun k _ => ?_
  rw [hcap v hv k, hball v hv k]

/-- Every vertex `v` with `u` in the box `B(v, 3κ s(v))` lies in `B(u, R)`; with `FarGoodFlip`, no
edge with its tail outside `B(u, R)` has `u` in its box. -/
def FarGood (κ R : ℕ) (ω : Configuration d) (u : Vertex d) : Prop :=
  ∀ v, u ∈ supBox v (3 * κ * partSide ω v) → v ∈ supBox u R

/-- The capped sides are the sides on `B(u, R)`. -/
def SideGood (R : ℕ) (ω : Configuration d) (u : Vertex d) : Prop :=
  ∀ v ∈ supBox u R, partSide ω v = cappedSide (capScale R) ω v

/-- No edge with its tail `v` outside `B(u, R)` has `u` in the box of radius `3κ` times the side at
`v` of the configuration with the bond `E (v, k)` closed. -/
def FarGoodFlip (E : LatticeEdge d → Bond d) (κ R : ℕ) (ω : Configuration d) (u : Vertex d) :
    Prop :=
  ∀ v (k : Fin d), u ∈ supBox v (3 * κ * partSide (setBond (E (v, k)) false ω) v) →
    v ∈ supBox u R

/-- The capped sides of the configurations with the bond `E (v, k)` closed are their sides at the
points `v` of `B(u, R)`. -/
def SideGoodFlip (E : LatticeEdge d → Bond d) (R : ℕ) (ω : Configuration d) (u : Vertex d) :
    Prop :=
  ∀ v ∈ supBox u R, ∀ k : Fin d, partSide (setBond (E (v, k)) false ω) v =
    cappedSide (capScale R) (setBond (E (v, k)) false ω) v

/-- On the side events the capped side of an edge at a point of `B(u, R)` is
`max(s(v), s♭(a, v))`. -/
theorem cappedEdgeSide_eq_max {ω : Configuration d} {R : ℕ} {u v : Vertex d} (k : Fin d)
    (hs : SideGood R ω u) (hsF : SideGoodFlip edgeBond R ω u) (hv : v ∈ supBox u R) :
    cappedEdgeSide (capScale R) ω (v, k) =
      max (partSide ω v) (partSide (setBond (edgeBond (v, k)) false ω) v) := by
  unfold cappedEdgeSide
  rw [← hs v hv, ← hsF v hv k]

section Grad

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The local gradient bounds dominate the plane gradient bound on `B(u, R + 3κR)`. -/
def GradGood (κ R : ℕ) (i : Fin d) (ω : Configuration d) (u : Vertex d) : Prop :=
  ∀ z ∈ supBox u (R + 3 * κ * R), planeGrad hG hGv i ω z ≤ 1 + 2 * d * (siteGrad R ω z + 1)

/-- **The finite-range weight dominates the weight on the good events.** -/
theorem stepTwoWeight_le_finiteWeight {ω : Configuration d} (hP : PartitionEvent ω)
    {κ R : ℕ} (hR : 1 ≤ R) {i : Fin d} {u : Vertex d} (hfar : FarGood κ R ω u)
    (hfarF : FarGoodFlip edgeBond κ R ω u) (hside : SideGood R ω u)
    (hsideF : SideGoodFlip edgeBond R ω u) (hgrad : GradGood hG hGv κ R i ω u) :
    stepTwoWeight hG hGv κ i ω u ≤ ENNReal.ofReal (finiteWeight κ R ω u) := by
  have hn := three_pow_capScale_le hR
  have hg1 : ∀ z, 1 ≤ 1 + 2 * (d : ℝ) * (siteGrad R ω z + 1) := fun z => by
    have := siteGrad_nonneg hR ω z
    have h2 : 0 ≤ 2 * (d : ℝ) * (siteGrad R ω z + 1) := by positivity
    linarith
  have key : ∀ v (k : Fin d), u ∈ stepTwoBox κ ω (v, k) → v ∈ supBox u R ∧
      max (partSide ω v) (partSide (setBond (edgeBond (v, k)) false ω) v) =
        cappedEdgeSide (capScale R) ω (v, k) := by
    intro v k hu
    have hu' : u ∈ supBox v
        (3 * κ * max (partSide ω v) (partSide (setBond (edgeBond (v, k)) false ω) v)) :=
      mem_supBox_of_mem_stepTwoBox (a := (v, k)) hP hu
    have hvu : v ∈ supBox u R := by
      rcases le_total (partSide ω v) (partSide (setBond (edgeBond (v, k)) false ω) v) with h | h
      · rw [max_eq_right h] at hu'
        exact hfarF v k hu'
      · rw [max_eq_left h] at hu'
        exact hfar v hu'
    exact ⟨hvu, (cappedEdgeSide_eq_max k hside hsideF hvu).symm⟩
  have hedge : ∀ v (k : Fin d), (if u ∈ stepTwoBox κ ω (v, k) then
      ENNReal.ofReal (stepTwoFactor hG hGv κ i ω (v, k)) else 0) ≤
      if v ∈ supBox u R ∧ u ∈ supBox v (3 * κ * cappedEdgeSide (capScale R) ω (v, k)) then
        ENNReal.ofReal (finiteBallSum κ R ω (v, k) ^ 9) else 0 := by
    intro v k
    split_ifs with hu hc
    · obtain ⟨hvu, hmax⟩ := key v k hu
      refine ENNReal.ofReal_le_ofReal ?_
      have hb := stepTwoFactor_le_of_bound hG hGv hP (a := (v, k)) hg1 fun z hz => by
        refine hgrad z (supBox_mono ?_ (mem_supBox_trans hz hvu))
        change 3 * κ * max (partSide ω v) (partSide (setBond (edgeBond (v, k)) false ω) v) + R ≤
          R + 3 * κ * R
        rw [hmax]
        exact cap_le_aux₃ ((cappedEdgeSide_le _ ω _).trans hn)
      refine hb.trans (le_of_eq ?_)
      rw [finiteBallSum_eq, ← hmax]
    · exfalso
      obtain ⟨hvu, hmax⟩ := key v k hu
      have hu' : u ∈ supBox v
          (3 * κ * max (partSide ω v) (partSide (setBond (edgeBond (v, k)) false ω) v)) :=
        mem_supBox_of_mem_stepTwoBox (a := (v, k)) hP hu
      rw [hmax] at hu'
      exact hc ⟨hvu, hu'⟩
    · positivity
    · exact le_rfl
  have hnn : ∀ v (k : Fin d), 0 ≤ (if u ∈ supBox v (3 * κ * cappedEdgeSide (capScale R) ω (v, k))
      then finiteBallSum κ R ω (v, k) ^ 9 else 0) := fun v k => by
    split_ifs
    · have := finiteBallSum_nonneg (κ := κ) hR ω (v, k); positivity
    · exact le_rfl
  unfold stepTwoWeight
  rw [ENNReal.tsum_prod (f := fun v k => if u ∈ stepTwoBox κ ω (v, k) then
    ENNReal.ofReal (stepTwoFactor hG hGv κ i ω (v, k)) else 0)]
  calc ∑' v, ∑' k : Fin d, (if u ∈ stepTwoBox κ ω (v, k) then
        ENNReal.ofReal (stepTwoFactor hG hGv κ i ω (v, k)) else 0)
      ≤ ∑' v, ∑ k : Fin d, (if v ∈ supBox u R ∧
          u ∈ supBox v (3 * κ * cappedEdgeSide (capScale R) ω (v, k)) then
            ENNReal.ofReal (finiteBallSum κ R ω (v, k) ^ 9) else 0) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        rw [tsum_fintype]
        exact Finset.sum_le_sum fun k _ => hedge v k
    _ = ENNReal.ofReal (finiteWeight κ R ω u) := by
        rw [tsum_eq_sum (s := supBox u R) fun v hv =>
          Finset.sum_eq_zero fun k _ => if_neg fun h => hv h.1]
        unfold finiteWeight
        rw [ENNReal.ofReal_sum_of_nonneg fun v _ => Finset.sum_nonneg fun k _ => hnn v k]
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun k _ => hnn v k]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hc : u ∈ supBox v (3 * κ * cappedEdgeSide (capScale R) ω (v, k))
        · rw [if_pos ⟨hv, hc⟩, if_pos hc]
        · rw [if_neg fun h => hc h.2, if_neg hc, ENNReal.ofReal_zero]

end Grad

end Rigidity.Corrector.GeneralDim
