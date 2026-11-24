import Rigidity.Proofs.Corrector.DarioStepTwoCapped

/-!
# The local gradient bound at the sites

* `planeGrad_translation`: the plane gradient bound commutes with translations of the configuration
  (`correctorDiff_translate`);
* `siteGrad R ω z`: the local gradient bound at scale `R` of the configuration seen from `z`;
  it is measurable, at most `6R`, depends only on the bonds inside `B(z, 2R + 1)`
  (`siteGrad_eq_of_localBonds`), and dominates the plane gradient bound at `z` on the good event
  of the configuration seen from `z` (`planeGrad_le_siteGrad`);
* `stepTwoFactor_le_of_bound`: the factor of an edge of the weight of the Step 2 sum is at most
  `(Σ_{B(x, 3κ s(x))} g)⁹` for any `g ≥ 1` dominating the plane gradient bound on that box.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

theorem edgeOpen_translation_iff (t : Vertex 2) (ω : Configuration 2) (z : Vertex 2) (k : Fin 2) :
    EdgeOpen (configurationTranslation t ω) (z + t, k) ↔ EdgeOpen ω (z, k) := by
  unfold EdgeOpen edgeHead
  simp only
  rw [show z + t + LatticeProb.unit k = (z + LatticeProb.unit k) + t by abel]
  exact openGraph_adj_translation_iff t ω _ _

section Grad

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

theorem correctorDiff_translate_of_adj {ω : Configuration 2} (hω : ω ∈ G) (t : Vertex 2)
    (hω' : configurationTranslation t ω ∈ G) {q : Fin 2 → ℝ} {a b : Vertex 2}
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
theorem planeGrad_translation {ω : Configuration 2} (hω : ω ∈ G) (t : Vertex 2)
    (hω' : configurationTranslation t ω ∈ G) (i : Fin 2) (z : Vertex 2) :
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
noncomputable def siteGrad (R : ℕ) (ω : Configuration 2) (z : Vertex 2) : ℝ :=
  localGrad R (configurationTranslation (-z) ω)

theorem measurable_siteGrad (R : ℕ) (z : Vertex 2) : Measurable fun ω => siteGrad R ω z :=
  (measurable_localGrad R).comp (measurable_configurationTranslation (-z))

theorem siteGrad_nonneg {R : ℕ} (hR : 1 ≤ R) (ω : Configuration 2) (z : Vertex 2) :
    0 ≤ siteGrad R ω z :=
  localGrad_nonneg _ hR

theorem siteGrad_le {R : ℕ} (hR : 1 ≤ R) (ω : Configuration 2) (z : Vertex 2) :
    siteGrad R ω z ≤ 6 * R :=
  localGrad_le _ hR

/-- **Locality of the local gradient bound at a site.** -/
theorem siteGrad_eq_of_localBonds {ω ω' : Configuration 2} {R : ℕ} {z : Vertex 2}
    (h : ∀ e ∈ localBonds (↑(supBox z (2 * R + 1)) : Set (Vertex 2)), ω e = ω' e) :
    siteGrad R ω' z = siteGrad R ω z := by
  unfold siteGrad
  refine localGrad_eq_of_adj_iff fun a ha b hb => ?_
  have hagree := adj_iff_of_localBonds h
  have ha' : a + z ∈ (↑(supBox z (2 * R + 1)) : Set (Vertex 2)) := by
    rw [Finset.mem_coe, mem_supBox] at *
    intro i
    have := ha i
    simpa using this
  have hb' : b + z ∈ (↑(supBox z (2 * R + 1)) : Set (Vertex 2)) := by
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

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **The local gradient bound dominates the plane gradient bound at a site** on the good event of
the configuration seen from the site. -/
theorem planeGrad_le_siteGrad {ω : Configuration 2} (hω : ω ∈ G) {i : Fin 2} {R : ℕ} (hR : 1 ≤ R)
    {z : Vertex 2} (hω' : configurationTranslation (-z) ω ∈ G)
    (hgood : LocalGradGood hG hGv i R (configurationTranslation (-z) ω)) :
    planeGrad hG hGv i ω z ≤ 5 + 4 * siteGrad R ω z := by
  have h := planeGrad_translation hG hGv hω (-z) hω' i z
  rw [add_neg_cancel] at h
  rw [← h]
  have := planeGrad_le_localGrad hG hGv hω' hR hgood
  unfold siteGrad
  linarith

/-- **The factor of an edge under a dominating function**: if `g ≥ 1` dominates the plane gradient
bound on `B(x, 3κ s(x))`, the factor of the edge is at most `(Σ_{B(x, 3κ s(x))} g)⁹`. -/
theorem stepTwoFactor_le_of_bound {ω : Configuration 2} (hP : PlanarPartitionEvent ω) {κ : ℕ}
    {i : Fin 2} {a : LatticeEdge} {g : Vertex 2 → ℝ} (hg1 : ∀ z, 1 ≤ g z)
    (hgb : ∀ z ∈ supBox a.1 (3 * κ * planarSide ω a.1), planeGrad hG hGv i ω z ≤ g z) :
    stepTwoFactor hG hGv κ i ω a ≤ (∑ z ∈ supBox a.1 (3 * κ * planarSide ω a.1), g z) ^ 9 := by
  set s := planarSide ω a.1 with hs
  have hm := max_planarSide_le hP a
  set S := supBox a.1 (3 * κ * s) with hS
  have hsubB : stepTwoBox κ ω a ⊆ S := by
    unfold stepTwoBox stepTwoRadius
    refine supBox_mono ?_
    rw [← hs]
    calc κ * max (planarSide ω a.1) (planarSide ω (edgeHead a)) ≤ κ * (3 * s) :=
          Nat.mul_le_mul_left _ hm
      _ = 3 * κ * s := by ring
  set T : ℝ := ∑ z ∈ S, g z with hT
  have hcardT : ((3 * κ * s : ℕ) : ℝ) ^ 2 ≤ T := by
    have hc : (S.card : ℝ) ≤ T := by
      calc (S.card : ℝ) = ∑ _z ∈ S, (1 : ℝ) := by simp
        _ ≤ T := Finset.sum_le_sum fun z _ => hg1 z
    refine le_trans ?_ hc
    rw [hS, card_supBox]
    push_cast
    have : (0 : ℝ) ≤ 3 * κ * s := by positivity
    nlinarith
  have hGsum : ∑ z ∈ stepTwoBox κ ω a, planeGrad hG hGv i ω z ≤ T :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsubB fun z _ _ => planeGrad_nonneg hG hGv i ω z).trans
      (Finset.sum_le_sum fun z hz => hgb z hz)
  have hG0 : 0 ≤ ∑ z ∈ stepTwoBox κ ω a, planeGrad hG hGv i ω z :=
    Finset.sum_nonneg fun z _ => planeGrad_nonneg hG hGv i ω z
  have hrad : (stepTwoRadius κ ω a : ℝ) ≤ 3 * κ * s := by
    unfold stepTwoRadius
    rw [← hs]
    have : κ * max (planarSide ω a.1) (planarSide ω (edgeHead a)) ≤ 3 * κ * s := by
      calc κ * max (planarSide ω a.1) (planarSide ω (edgeHead a)) ≤ κ * (3 * s) :=
            Nat.mul_le_mul_left _ hm
        _ = 3 * κ * s := by ring
    exact_mod_cast this
  unfold stepTwoFactor
  have h14 : (stepTwoRadius κ ω a : ℝ) ^ 14 ≤ T ^ 7 := by
    have hr0 : (0 : ℝ) ≤ stepTwoRadius κ ω a := Nat.cast_nonneg _
    have hr2 : (stepTwoRadius κ ω a : ℝ) ^ 2 ≤ T := by
      refine le_trans ?_ hcardT
      push_cast
      exact pow_le_pow_left₀ hr0 hrad 2
    calc (stepTwoRadius κ ω a : ℝ) ^ 14 = ((stepTwoRadius κ ω a : ℝ) ^ 2) ^ 7 := by ring
      _ ≤ T ^ 7 := pow_le_pow_left₀ (by positivity) hr2 7
  calc (stepTwoRadius κ ω a : ℝ) ^ 14 *
        (∑ z ∈ stepTwoBox κ ω a, planeGrad hG hGv i ω z) ^ 2 ≤ T ^ 7 * T ^ 2 :=
        mul_le_mul h14 (pow_le_pow_left₀ hG0 hGsum 2) (sq_nonneg _)
          (pow_nonneg (le_trans (by positivity) hcardT) 7)
    _ = T ^ 9 := by ring

/-- A point of the box of an edge is within `3κ s(x)` of its tail. -/
theorem mem_supBox_of_mem_stepTwoBox {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {κ : ℕ} {a : LatticeEdge} {u : Vertex 2} (hu : u ∈ stepTwoBox κ ω a) :
    u ∈ supBox a.1 (3 * κ * planarSide ω a.1) := by
  refine supBox_mono ?_ hu
  unfold stepTwoRadius
  have hm := max_planarSide_le hP a
  calc κ * max (planarSide ω a.1) (planarSide ω (edgeHead a)) ≤ κ * (3 * planarSide ω a.1) :=
        Nat.mul_le_mul_left _ hm
    _ = 3 * κ * planarSide ω a.1 := by ring

end Grad

end Rigidity.Corrector
