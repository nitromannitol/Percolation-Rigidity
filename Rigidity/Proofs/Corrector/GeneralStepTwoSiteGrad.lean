import Rigidity.Proofs.Corrector.GeneralLocalGradientProb
import Rigidity.Proofs.Corrector.GeneralStepTwoWeightBound

/-!
# The local gradient bound at the sites of `ℤᵈ`

* `planeGrad_translation`: the plane gradient bound commutes with translations of the configuration
  (`correctorDiff_translate`);
* `siteGrad R ω z`: the local gradient bound at scale `R` of the configuration seen from `z`;
  it is measurable, at most `6R`, depends only on the bonds inside `B(z, 2R + 1)`
  (`siteGrad_eq_of_localBonds`), and dominates the plane gradient bound at `z` on the good event
  of the configuration seen from `z` (`planeGrad_le_siteGrad`);
* `stepTwoFactor_le_of_bound`: the factor of an edge `a = (x, i')` of the weight of the Step 2 sum
  is at most `(Σ_{B(x, 3κ m)} g)⁹`, `m = max(s(x), s♭(x))` with `s♭(x)` the side at `x` of the
  partition of the configuration with the bond of `a` closed, for any `g ≥ 1` dominating the plane
  gradient bound on that box.

This is the planar file `DarioStepTwoSiteGrad` on `ℤᵈ`. The planar partition is replaced by the
partition into good cubes of `ℤᵈ` (`partSide`, `max_partSide_setBond_le`), the radius of the box of
an edge also carries the side `s♭(x)` of the partition with the bond of the edge closed, the bound
`5 + 4 siteGrad` of the plane gradient becomes `1 + 2d(siteGrad + 1)`, and in the factor
`R_a^{7d} (Σ_{B_a} G)²` the power `7d` of the radius is bounded by the `7`-th power of the
`(3κ m)^d` points of the box, so that the power `9` of the planar bound is unchanged.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare.GeneralDim
open scoped Classical ENNReal

variable {d : ℕ}

theorem edgeOpen_translation_iff (t : Vertex d) (ω : Configuration d) (z : Vertex d) (k : Fin d) :
    EdgeOpen (configurationTranslation t ω) (z + t, k) ↔ EdgeOpen ω (z, k) := by
  unfold EdgeOpen edgeHead
  simp only
  rw [show z + t + LatticeProb.unit k = (z + LatticeProb.unit k) + t by abel]
  exact openGraph_adj_translation_iff t ω _ _

section Grad

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

theorem correctorDiff_translate_of_adj {ω : Configuration d} (hω : ω ∈ G) (t : Vertex d)
    (hω' : configurationTranslation t ω ∈ G) {q : Fin d → ℝ} {a b : Vertex d}
    (hab : (openGraph ω).Adj a b) :
    correctorDiff hG hGv q (configurationTranslation t ω) (a + t) (b + t) =
      correctorDiff hG hGv q ω a b := by
  by_cases ha : ω ∈ infiniteComponentEvent a
  · exact correctorDiff_translate hG hGv t hω hω' ha (mem_infiniteComponentEvent_of_adj hab ha)
  · have hb : ω ∉ infiniteComponentEvent b := fun h =>
      ha (mem_infiniteComponentEvent_of_adj hab.symm h)
    have hb' : configurationTranslation t ω ∉ infiniteComponentEvent (b + t) := fun h =>
      hb ((mem_infiniteComponentEvent_translation_iff t ω b).1 h)
    unfold correctorDiff
    rw [dif_neg fun h => hb' h.2, dif_neg fun h => hb h.2]

/-- **The plane gradient bound commutes with translations.** -/
theorem planeGrad_translation {ω : Configuration d} (hω : ω ∈ G) (t : Vertex d)
    (hω' : configurationTranslation t ω ∈ G) (i : Fin d) (z : Vertex d) :
    planeGrad hG hGv i (configurationTranslation t ω) (z + t) = planeGrad hG hGv i ω z := by
  unfold planeGrad
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  · rw [edgeOpen_translation_iff]
    split_ifs with h
    · rw [show z + t + LatticeProb.unit k = (z + LatticeProb.unit k) + t by abel,
        correctorDiff_translate_of_adj hG hGv hω t hω' (a := z) (b := z + LatticeProb.unit k) h]
    · rfl
  · rw [show z + t - LatticeProb.unit k = (z - LatticeProb.unit k) + t by abel,
      edgeOpen_translation_iff]
    split_ifs with h
    · have hadj : (openGraph ω).Adj z (z - LatticeProb.unit k) := by
        have : (openGraph ω).Adj (z - LatticeProb.unit k)
            (z - LatticeProb.unit k + LatticeProb.unit k) := h
        rw [sub_add_cancel] at this
        exact this.symm
      rw [correctorDiff_translate_of_adj hG hGv hω t hω' hadj]
    · rfl

end Grad

/-- The local gradient bound at scale `R` of the configuration seen from `z`. -/
noncomputable def siteGrad (R : ℕ) (ω : Configuration d) (z : Vertex d) : ℝ :=
  localGrad R (configurationTranslation (-z) ω)

theorem measurable_siteGrad (R : ℕ) (z : Vertex d) : Measurable fun ω => siteGrad R ω z :=
  (measurable_localGrad R).comp (configurationTranslationMeasurableEquiv (-z)).measurable

theorem siteGrad_nonneg {R : ℕ} (hR : 1 ≤ R) (ω : Configuration d) (z : Vertex d) :
    0 ≤ siteGrad R ω z :=
  localGrad_nonneg _ hR

theorem siteGrad_le {R : ℕ} (hR : 1 ≤ R) (ω : Configuration d) (z : Vertex d) :
    siteGrad R ω z ≤ 6 * R :=
  localGrad_le _ hR

/-- **Locality of the local gradient bound at a site.** -/
theorem siteGrad_eq_of_localBonds {ω ω' : Configuration d} {R : ℕ} {z : Vertex d}
    (h : ∀ e ∈ localBonds (↑(supBox z (2 * R + 1)) : Set (Vertex d)), ω e = ω' e) :
    siteGrad R ω' z = siteGrad R ω z := by
  unfold siteGrad
  refine localGrad_eq_of_adj_iff fun a ha b hb => ?_
  have hagree := openGraph_adj_iff_of_localBonds h
  have ha' : a + z ∈ (↑(supBox z (2 * R + 1)) : Set (Vertex d)) := by
    rw [Finset.mem_coe, mem_supBox] at *
    intro i
    have := ha i
    simpa using this
  have hb' : b + z ∈ (↑(supBox z (2 * R + 1)) : Set (Vertex d)) := by
    rw [Finset.mem_coe, mem_supBox] at *
    intro i
    have := hb i
    simpa using this
  have e1 := openGraph_adj_translation_iff (-z) ω' (a + z) (b + z)
  have e2 := openGraph_adj_translation_iff (-z) ω (a + z) (b + z)
  rw [show a + z + -z = a by abel, show b + z + -z = b by abel] at e1 e2
  rw [e1, e2]
  exact hagree _ ha' _ hb'

section Grad

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The local gradient bound dominates the plane gradient bound at a site** on the good event of
the configuration seen from the site. -/
theorem planeGrad_le_siteGrad {ω : Configuration d} (hω : ω ∈ G) {i : Fin d} {R : ℕ}
    (hR : 1 ≤ R) {z : Vertex d} (hω' : configurationTranslation (-z) ω ∈ G)
    (hgood : LocalGradGood hG hGv i R (configurationTranslation (-z) ω)) :
    planeGrad hG hGv i ω z ≤ 1 + 2 * d * (siteGrad R ω z + 1) := by
  have h := planeGrad_translation hG hGv hω (-z) hω' i z
  rw [add_neg_cancel] at h
  rw [← h]
  have := planeGrad_le_localGrad hG hGv hω' hR hgood
  unfold siteGrad
  linarith

/-- The radius of the box of an edge `a = (x, i')` is at most `3κ max(s(x), s♭(x))`. -/
theorem stepTwoRadius_le {ω : Configuration d} (hP : PartitionEvent ω) (κ : ℕ)
    (a : LatticeEdge d) :
    stepTwoRadius κ ω a ≤
      3 * κ * max (partSide ω a.1) (partSide (setBond (edgeBond a) false ω) a.1) := by
  unfold stepTwoRadius
  calc κ * max (max (partSide ω a.1) (partSide ω (edgeHead a)))
        (partSide (setBond (edgeBond a) false ω) a.1)
      ≤ κ * (3 * max (partSide ω a.1) (partSide (setBond (edgeBond a) false ω) a.1)) :=
        Nat.mul_le_mul_left _ (max_partSide_setBond_le hP (edgeBond a) a)
    _ = 3 * κ * max (partSide ω a.1) (partSide (setBond (edgeBond a) false ω) a.1) := by ring

/-- A point of the box of an edge `a = (x, i')` is within `3κ max(s(x), s♭(x))` of `x`. -/
theorem mem_supBox_of_mem_stepTwoBox {ω : Configuration d} (hP : PartitionEvent ω)
    {κ : ℕ} {a : LatticeEdge d} {u : Vertex d} (hu : u ∈ stepTwoBox κ ω a) :
    u ∈ supBox a.1
      (3 * κ * max (partSide ω a.1) (partSide (setBond (edgeBond a) false ω) a.1)) := by
  unfold stepTwoBox at hu
  rw [LatticeProb.mem_boxFinset_iff] at hu
  exact mem_supBox.2 fun j => (hu j).trans (by exact_mod_cast stepTwoRadius_le hP κ a)

/-- **The factor of an edge under a dominating function**: if `g ≥ 1` dominates the plane gradient
bound on `B(x, 3κ m)`, `m = max(s(x), s♭(x))`, the factor of the edge `a = (x, i')` is at most
`(Σ_{B(x, 3κ m)} g)⁹`. -/
theorem stepTwoFactor_le_of_bound {ω : Configuration d} (hP : PartitionEvent ω) {κ : ℕ}
    {i : Fin d} {a : LatticeEdge d} {g : Vertex d → ℝ} (hg1 : ∀ z, 1 ≤ g z)
    (hgb : ∀ z ∈ supBox a.1
        (3 * κ * max (partSide ω a.1) (partSide (setBond (edgeBond a) false ω) a.1)),
      planeGrad hG hGv i ω z ≤ g z) :
    stepTwoFactor hG hGv κ i ω a ≤
      (∑ z ∈ supBox a.1
        (3 * κ * max (partSide ω a.1) (partSide (setBond (edgeBond a) false ω) a.1)), g z) ^ 9 := by
  have hrad' := stepTwoRadius_le hP κ a
  have hsubB : stepTwoBox κ ω a ⊆
      supBox a.1 (3 * κ * max (partSide ω a.1) (partSide (setBond (edgeBond a) false ω) a.1)) :=
    fun u hu => mem_supBox_of_mem_stepTwoBox hP hu
  set s := max (partSide ω a.1) (partSide (setBond (edgeBond a) false ω) a.1) with hs
  set S := supBox a.1 (3 * κ * s) with hS
  set T : ℝ := ∑ z ∈ S, g z with hT
  have hcardT : ((3 * κ * s : ℕ) : ℝ) ^ d ≤ T := by
    have hc : (S.card : ℝ) ≤ T := by
      calc (S.card : ℝ) = ∑ _z ∈ S, (1 : ℝ) := by simp
        _ ≤ T := Finset.sum_le_sum fun z _ => hg1 z
    refine le_trans ?_ hc
    rw [hS, card_supBox]
    push_cast
    have : (0 : ℝ) ≤ 3 * κ * s := by positivity
    exact pow_le_pow_left₀ this (by linarith) d
  have hGsum : ∑ z ∈ stepTwoBox κ ω a, planeGrad hG hGv i ω z ≤ T :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsubB fun z _ _ => planeGrad_nonneg hG hGv i ω z).trans
      (Finset.sum_le_sum fun z hz => hgb z hz)
  have hG0 : 0 ≤ ∑ z ∈ stepTwoBox κ ω a, planeGrad hG hGv i ω z :=
    Finset.sum_nonneg fun z _ => planeGrad_nonneg hG hGv i ω z
  have hrad : (stepTwoRadius κ ω a : ℝ) ≤ 3 * κ * s := by exact_mod_cast hrad'
  unfold stepTwoFactor
  have h7 : (stepTwoRadius κ ω a : ℝ) ^ (7 * d) ≤ T ^ 7 := by
    have hr0 : (0 : ℝ) ≤ stepTwoRadius κ ω a := Nat.cast_nonneg _
    have hrd : (stepTwoRadius κ ω a : ℝ) ^ d ≤ T := by
      refine le_trans ?_ hcardT
      push_cast
      exact pow_le_pow_left₀ hr0 hrad d
    rw [pow_mul']
    exact pow_le_pow_left₀ (by positivity) hrd 7
  calc (stepTwoRadius κ ω a : ℝ) ^ (7 * d) *
        (∑ z ∈ stepTwoBox κ ω a, planeGrad hG hGv i ω z) ^ 2 ≤ T ^ 7 * T ^ 2 :=
        mul_le_mul h7 (pow_le_pow_left₀ hG0 hGsum 2) (sq_nonneg _)
          (pow_nonneg (le_trans (by positivity) hcardT) 7)
    _ = T ^ 9 := by ring

end Grad

end Rigidity.Corrector.GeneralDim
