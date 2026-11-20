import Rigidity.Percolation.Bootstrap.Scales

/-!
# The bootstrap recursion

`BootGood a u m p₀ q π` says that at scale `m` every left seed `S` and every right seed `T` (a set
whose reflection is a left seed) are joined inside `Q_{6m}` at level `q` with conditional
probability at least `π`, given that the cuts from `S` and `T` inside their zones are closed at
level `p₀`. If left seeds of scale `3m'` reach the anchors of the two subregions with probability
at least `1 - η` at level `p₀`, then `BootGood` at scale `m'` with `π` gives `BootGood` at scale
`3m'` with `(1 - 4ε₁)(1 - (1 - π)²)`, where `ε₁ = η / (1 - p₀)^K + (1 - δ)^K` and `q = p₀ + δ`.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

variable {d : ℕ}

/-- The bootstrap quantity at scale `m` is at least `π`. -/
def BootGood (a : Fin d) (u m : ℕ) (p₀ q : unitInterval) (π : ℝ) : Prop :=
  ∀ S T : Finset (Vertex d), LeftSeed a u m S → LeftSeed a u m (T.image (flipA a)) →
    π * (bondMarkLaw d).real
        (cutClosed p₀ S (leftZoneFinset a m) ∩ cutClosed p₀ T (rightZoneFinset a m)) ≤
      (bondMarkLaw d).real
        ({ω | ConnectsRegions (thresholdBondMarks q ω) (cubeAt 0 (6 * m)) S T} ∩
          (cutClosed p₀ S (leftZoneFinset a m) ∩ cutClosed p₀ T (rightZoneFinset a m)))

/-- The image of the image under the inverse bijection. -/
theorem image_image_symm (f : Vertex d ≃ Vertex d) (X : Finset (Vertex d)) :
    (X.image f.symm).image f = X := by
  classical
  rw [Finset.image_image]
  simp

/-- The reflection fixes a translation vector with vanishing `a`-coordinate. -/
theorem flipA_sub {a : Fin d} {c : Vertex d} (hc : c a = 0) (z : Vertex d) :
    flipA a (z - c) = flipA a z - c := by
  funext i
  simp only [flipA_apply, Pi.sub_apply]
  split_ifs with h
  · subst h
    rw [hc]
    ring
  · rfl

/-- **The bootstrap quantity in a subregion.** `BootGood` at the origin applies to translated
seeds in the subregion `c + Q_{6m'}`. -/
theorem bootGood_subRegion {a b : Fin d} (hab : a ≠ b) {u m' : ℕ} {p₀ q : unitInterval}
    {π : ℝ} (h : BootGood a u m' p₀ q π) (k : Bool) (X Y : Finset (Vertex d))
    (hX : LeftSeed a u m' (X.image (translateEquiv (subCentre b k m')).symm))
    (hY : LeftSeed a u m' ((Y.image (translateEquiv (subCentre b k m')).symm).image (flipA a))) :
    π * (bondMarkLaw d).real (cutClosed p₀ X (subRegion b k m' ∩ leftExploreFinset a m') ∩
        cutClosed p₀ Y (subRegion b k m' ∩ rightExploreFinset a m')) ≤
      (bondMarkLaw d).real ({ω | ConnectsRegions (thresholdBondMarks q ω) (subRegion b k m') X Y} ∩
        (cutClosed p₀ X (subRegion b k m' ∩ leftExploreFinset a m') ∩
          cutClosed p₀ Y (subRegion b k m' ∩ rightExploreFinset a m'))) := by
  classical
  set f := translateEquiv (subCentre b k m') with hf
  have hiso : CoordIsometry f := coordIsometry_translateEquiv _
  set S₀ := X.image f.symm with hS₀
  set T₀ := Y.image f.symm with hT₀
  have hXS : X = S₀.image f := (image_image_symm f X).symm
  have hYT : Y = T₀.image f := (image_image_symm f Y).symm
  have hXc : (X : Set (Vertex d)) = f '' (S₀ : Set (Vertex d)) := by
    rw [← Finset.coe_image, ← hXS]
  have hYc : (Y : Set (Vertex d)) = f '' (T₀ : Set (Vertex d)) := by
    rw [← Finset.coe_image, ← hYT]
  have hZL : subRegion b k m' ∩ leftExploreFinset a m' = (leftZoneFinset a m').image f :=
    subRegion_inter_leftExplore hab m' k
  have hZR : subRegion b k m' ∩ rightExploreFinset a m' = (rightZoneFinset a m').image f :=
    subRegion_inter_rightExplore hab m' k
  have hR : ((subRegion b k m' : Finset (Vertex d)) : Set (Vertex d)) = f '' cubeAt 0 (6 * m') := by
    rw [hiso.image_cubeAt, subRegion, coe_cubeFinset]
    simp [hf, translateEquiv, latticeVertexTranslation]
  have hH : latticeBondMarkEquiv f hiso.dist ⁻¹'
      (cutClosed p₀ X (subRegion b k m' ∩ leftExploreFinset a m') ∩
        cutClosed p₀ Y (subRegion b k m' ∩ rightExploreFinset a m')) =
      cutClosed p₀ S₀ (leftZoneFinset a m') ∩ cutClosed p₀ T₀ (rightZoneFinset a m') := by
    rw [Set.preimage_inter, hZL, hZR]
    conv_lhs => rw [hXS, hYT]
    rw [latticeBondMarkEquiv_preimage_cutClosed, latticeBondMarkEquiv_preimage_cutClosed]
  have hA : latticeBondMarkEquiv f hiso.dist ⁻¹'
      {ω | ConnectsRegions (thresholdBondMarks q ω) (subRegion b k m') X Y} =
      {ω | ConnectsRegions (thresholdBondMarks q ω) (cubeAt 0 (6 * m')) S₀ T₀} := by
    rw [hR, hXc, hYc]
    exact latticeBondMarkEquiv_preimage_connectsRegions f hiso.dist q _ _ _
  have e1 := bondMarkLaw_real_preimage_latticeBondMarkEquiv f hiso.dist
    (cutClosed p₀ X (subRegion b k m' ∩ leftExploreFinset a m') ∩
      cutClosed p₀ Y (subRegion b k m' ∩ rightExploreFinset a m'))
  have e2 := bondMarkLaw_real_preimage_latticeBondMarkEquiv f hiso.dist
    ({ω | ConnectsRegions (thresholdBondMarks q ω) (subRegion b k m') X Y} ∩
      (cutClosed p₀ X (subRegion b k m' ∩ leftExploreFinset a m') ∩
        cutClosed p₀ Y (subRegion b k m' ∩ rightExploreFinset a m')))
  rw [hH] at e1
  rw [Set.preimage_inter, hA, hH] at e2
  rw [← e1, ← e2]
  exact h S₀ T₀ hX hY

/-- The reflection is a coordinate isometry. -/
theorem coordIsometry_flipA (a : Fin d) : CoordIsometry (flipA a) :=
  coordIsometry_coordinateSignFlip _

/-- **Left admissibility.** If the sprinkled cluster of a left set of scale `3m'` contains a vertex
of the left anchor of a subregion, its trace in the left zone of the subregion is, after
translation, a left seed of scale `m'`. -/
theorem leftSeed_of_mem_shiftedAnchor {a b : Fin d} (hab : a ≠ b) {u m' : ℕ}
    (hu : u + 1 ≤ m' / 8) (k : Bool) {p₀ q : unitInterval} {S : Finset (Vertex d)}
    (hSZ : S ⊆ leftZoneFinset a (3 * m')) {ω : BondMarks d} {z : Vertex d}
    (hz : z ∈ shiftedAnchorFinset a b (sgOf k) m')
    (hzC : z ∈ sprinkledCluster p₀ q S (leftExploreFinset a m') ω) :
    LeftSeed a u m' ((sprinkledCluster p₀ q S (leftExploreFinset a m') ω ∩
      (subRegion b k m' ∩ leftExploreFinset a m')).image
        (translateEquiv (subCentre b k m')).symm) := by
  classical
  set C := sprinkledCluster p₀ q S (leftExploreFinset a m') ω with hC
  set Z := subRegion b k m' ∩ leftExploreFinset a m' with hZ
  set f := translateEquiv (subCentre b k m') with hf
  have hiso : CoordIsometry f := coordIsometry_translateEquiv _
  obtain ⟨hcube, hfar⟩ := shiftedAnchor_cube hab hu k hz
  have hSW : S ⊆ leftExploreFinset a m' := hSZ.trans (leftZoneFinset_subset_leftExplore a m')
  have hseed : HasSeedPath (C : Set (Vertex d)) z u :=
    hasSeedPath_sprinkledCluster hSW hzC (fun g hg => hfar g (hSZ hg))
  have hseed' := (hseed.inter hcube).image hiso.symm
  have hcoe : (((C ∩ Z).image f.symm : Finset (Vertex d)) : Set (Vertex d)) =
      f.symm '' ((C : Set (Vertex d)) ∩ (Z : Set (Vertex d))) := by
    rw [Finset.coe_image, Finset.coe_inter]
  refine ⟨?_, f.symm z, ?_, hcoe ▸ hseed'⟩
  · intro y hy
    rw [Finset.mem_coe] at hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hxZ : x ∈ Z := (Finset.mem_inter.1 hx).2
    rw [hZ, subRegion_inter_leftExplore hab m' k, mem_image_equiv] at hxZ
    rw [← coe_leftZoneFinset]
    exact hxZ
  · rw [hf, translateEquiv_symm_apply]
    exact (mem_shiftedAnchorFinset.1 hz).2

/-- **Right admissibility.** The reflected statement for right sets. -/
theorem rightSeed_of_mem_shiftedAnchor {a b : Fin d} (hab : a ≠ b) {u m' : ℕ}
    (hu : u + 1 ≤ m' / 8) (k : Bool) {p₀ q : unitInterval} {T : Finset (Vertex d)}
    (hTZ : T ⊆ rightZoneFinset a (3 * m')) {ω : BondMarks d} {z : Vertex d}
    (hz : z ∈ (shiftedAnchorFinset a b (sgOf k) m').image (flipA a))
    (hzC : z ∈ sprinkledCluster p₀ q T (rightExploreFinset a m') ω) :
    LeftSeed a u m' (((sprinkledCluster p₀ q T (rightExploreFinset a m') ω ∩
      (subRegion b k m' ∩ rightExploreFinset a m')).image
        (translateEquiv (subCentre b k m')).symm).image (flipA a)) := by
  classical
  set C := sprinkledCluster p₀ q T (rightExploreFinset a m') ω with hC
  set Z := subRegion b k m' ∩ rightExploreFinset a m' with hZ
  set f := translateEquiv (subCentre b k m') with hf
  have hiso : CoordIsometry f := coordIsometry_translateEquiv _
  obtain ⟨hcube, hfar⟩ := flipShiftedAnchor_cube hab hu k hz
  have hTW : T ⊆ rightExploreFinset a m' := hTZ.trans (rightZoneFinset_subset_rightExplore a m')
  have hseed : HasSeedPath (C : Set (Vertex d)) z u :=
    hasSeedPath_sprinkledCluster hTW hzC (fun g hg => hfar g (hTZ hg))
  have hseed' := ((hseed.inter hcube).image hiso.symm).image (coordIsometry_flipA a)
  have hcoe : ((((C ∩ Z).image f.symm).image (flipA a) : Finset (Vertex d)) : Set (Vertex d)) =
      flipA a '' (f.symm '' ((C : Set (Vertex d)) ∩ (Z : Set (Vertex d)))) := by
    rw [Finset.coe_image, Finset.coe_image, Finset.coe_inter]
  refine ⟨?_, flipA a (f.symm z), ?_, hcoe ▸ hseed'⟩
  · intro y hy
    rw [Finset.mem_coe] at hy
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy'
    have hxZ : x ∈ Z := (Finset.mem_inter.1 hx).2
    rw [hZ, subRegion_inter_rightExplore hab m' k, mem_image_equiv,
      ← image_flipA_leftZoneFinset, mem_image_equiv, flipA_symm] at hxZ
    rw [← coe_leftZoneFinset]
    exact hxZ
  · rw [mem_image_equiv, flipA_symm] at hz
    rw [hf, translateEquiv_symm_apply, flipA_sub (subCentre_apply_of_ne hab k m')]
    exact (mem_shiftedAnchorFinset.1 hz).2

/-- Reflecting twice gives back the set. -/
theorem image_flipA_image_flipA (a : Fin d) (T : Finset (Vertex d)) :
    (T.image (flipA a)).image (flipA a) = T := by
  classical
  rw [Finset.image_image]
  have : (flipA a) ∘ (flipA a) = id := funext (flipA_flipA a)
  rw [this, Finset.image_id]

/-- A sprinkled-exploration failure bound from an unconditional connection bound. -/
theorem sprinkled_failure_le (p₀ : unitInterval) (hp₀ : (p₀ : ℝ) < 1) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : (p₀ : ℝ) + δ ≤ 1) {S Z W T₁ : Finset (Vertex d)} (hSZ : S ⊆ Z) (hZW : Z ⊆ W)
    (hST : ∀ z ∈ T₁, z ∉ S) (K : ℕ) {η : ℝ}
    (hconn : 1 - η ≤ (latticeBondLaw d p₀).real {ω | ConnectsRegions ω W S T₁})
    (P : Finset (Vertex d) → Prop)
    (hP : ∀ ω, (∃ z ∈ T₁, z ∈ sprinkledCluster p₀ (raisedLevel p₀ δ hδ.le hδ1) S W ω) →
      P (sprinkledCluster p₀ (raisedLevel p₀ δ hδ.le hδ1) S W ω)) :
    (bondMarkLaw d).real (cutClosed p₀ S Z ∩
        {ω | ¬ P (sprinkledCluster p₀ (raisedLevel p₀ δ hδ.le hδ1) S W ω)}) ≤
      (η / (1 - (p₀ : ℝ)) ^ K + (1 - δ) ^ K) * (bondMarkLaw d).real (cutClosed p₀ S Z) := by
  have hreach := sprinkledCluster_reach_le p₀ hp₀ δ hδ hδ1 hSZ hZW T₁ K
  have hsub : cutClosed p₀ S Z ∩
      {ω | ¬ P (sprinkledCluster p₀ (raisedLevel p₀ δ hδ.le hδ1) S W ω)} ⊆
      cutClosed p₀ S Z ∩
        {ω | ¬ ∃ z ∈ T₁, z ∈ sprinkledCluster p₀ (raisedLevel p₀ δ hδ.le hδ1) S W ω} := by
    rintro ω ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 (hP ω h)⟩
  have hprob : (latticeBondLaw d p₀).real {η' | ¬ ∃ x ∈ S, ∃ z ∈ T₁,
      z ∈ (W : Set (Vertex d)) \ (S : Set (Vertex d)) ∧ (openIn η' W).Reachable x z} ≤ η := by
    have hsub' : {η' : Configuration d | ¬ ∃ x ∈ S, ∃ z ∈ T₁,
        z ∈ (W : Set (Vertex d)) \ (S : Set (Vertex d)) ∧ (openIn η' W).Reachable x z} ⊆
        {ω | ConnectsRegions ω W S T₁}ᶜ := by
      intro ω hω hc
      obtain ⟨x, -, hxS, z, hzW, hzT, hr⟩ := hc
      exact hω ⟨x, hxS, z, hzT, ⟨hzW, hST z hzT⟩, hr⟩
    calc _ ≤ (latticeBondLaw d p₀).real {ω | ConnectsRegions ω W S T₁}ᶜ :=
          measureReal_mono hsub'
      _ = 1 - (latticeBondLaw d p₀).real {ω | ConnectsRegions ω W S T₁} := by
          rw [measureReal_compl (measurableSet_connectsRegions _ _ _), probReal_univ]
      _ ≤ η := by linarith
  have hpK : 0 < (1 - (p₀ : ℝ)) ^ K := pow_pos (by linarith) _
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans (hreach.trans ?_)
  exact mul_le_mul_of_nonneg_right
    (add_le_add_left (div_le_div_of_nonneg_right hprob hpK.le) _) measureReal_nonneg

/-- **The bootstrap recursion.** -/
theorem bootGood_step {a b : Fin d} (hab : a ≠ b) {u m' : ℕ} (hm : 1 ≤ m')
    (hu : u + 1 ≤ m' / 8) (p₀ : unitInterval) (hp₀ : (p₀ : ℝ) < 1) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : (p₀ : ℝ) + δ ≤ 1) (K : ℕ) {η π : ℝ} (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hFL : ∀ (k : Bool) (S : Finset (Vertex d)), LeftSeed a u (3 * m') S →
      1 - η ≤ (latticeBondLaw d p₀).real
        {ω | ConnectsRegions ω (leftExplore a m') S (shiftedAnchorFinset a b (sgOf k) m')})
    (hGood : BootGood a u m' p₀ (raisedLevel p₀ δ hδ.le hδ1) π) :
    BootGood a u (3 * m') p₀ (raisedLevel p₀ δ hδ.le hδ1)
      ((1 - 4 * (η / (1 - (p₀ : ℝ)) ^ K + (1 - δ) ^ K)) * (1 - (1 - π) ^ 2)) := by
  classical
  intro S T hS hT
  set q := raisedLevel p₀ δ hδ.le hδ1 with hq
  set ε₁ := η / (1 - (p₀ : ℝ)) ^ K + (1 - δ) ^ K with hε₁
  set WS := leftExploreFinset a m' with hWS
  set WT := rightExploreFinset a m' with hWT
  have hSZ : S ⊆ leftZoneFinset a (3 * m') := by
    intro x hx
    have := hS.1 (Finset.mem_coe.2 hx)
    rw [← coe_leftZoneFinset] at this
    exact this
  have hTZ : T ⊆ rightZoneFinset a (3 * m') := by
    intro t ht
    have := hT.1 (Finset.mem_coe.2 (Finset.mem_image_of_mem (flipA a) ht))
    rw [← coe_leftZoneFinset, Finset.mem_coe] at this
    rw [← image_flipA_leftZoneFinset, mem_image_equiv, flipA_symm]
    exact this
  have hWSc : ((WS : Finset (Vertex d)) : Set (Vertex d)) = leftExplore a m' :=
    coe_leftExploreFinset a m'
  -- per-side failure bounds
  have hFS : ∀ k, (bondMarkLaw d).real (cutClosed p₀ S (leftZoneFinset a (3 * m')) ∩
      {ω | ¬ LeftSeed a u m' ((sprinkledCluster p₀ q S WS ω ∩ (subRegion b k m' ∩ WS)).image
        (translateEquiv (subCentre b k m')).symm)}) ≤
      ε₁ * (bondMarkLaw d).real (cutClosed p₀ S (leftZoneFinset a (3 * m'))) := by
    intro k
    refine sprinkled_failure_le p₀ hp₀ δ hδ hδ1 hSZ (leftZoneFinset_subset_leftExplore a m')
      (fun z hz hzS => (shiftedAnchor_cube hab hu k hz).2 z (hSZ hzS) (fun i => by simp)) K
      (by rw [hWSc]; exact hFL k S hS)
      (fun c => LeftSeed a u m' ((c ∩ (subRegion b k m' ∩ WS)).image
        (translateEquiv (subCentre b k m')).symm)) ?_
    rintro ω ⟨z, hz, hzC⟩
    exact leftSeed_of_mem_shiftedAnchor hab hu k hSZ hz hzC
  have hFT : ∀ k, (bondMarkLaw d).real (cutClosed p₀ T (rightZoneFinset a (3 * m')) ∩
      {ω | ¬ LeftSeed a u m' (((sprinkledCluster p₀ q T WT ω ∩ (subRegion b k m' ∩ WT)).image
        (translateEquiv (subCentre b k m')).symm).image (flipA a))}) ≤
      ε₁ * (bondMarkLaw d).real (cutClosed p₀ T (rightZoneFinset a (3 * m'))) := by
    intro k
    have hconn : 1 - η ≤ (latticeBondLaw d p₀).real {ω | ConnectsRegions ω
        (WT : Set (Vertex d)) T ((shiftedAnchorFinset a b (sgOf k) m').image (flipA a))} := by
      have h := hFL k (T.image (flipA a)) hT
      rw [← latticeBondLaw_real_connectsRegions_image p₀ (flipA a) (coordIsometry_flipA a).dist]
        at h
      rw [← coe_leftExploreFinset, ← Finset.coe_image, image_flipA_leftExploreFinset,
        ← Finset.coe_image, image_flipA_image_flipA, ← Finset.coe_image] at h
      exact h
    refine sprinkled_failure_le p₀ hp₀ δ hδ hδ1 hTZ (rightZoneFinset_subset_rightExplore a m')
      (fun z hz hzT => (flipShiftedAnchor_cube hab hu k hz).2 z (hTZ hzT) (fun i => by simp)) K
      hconn
      (fun c => LeftSeed a u m' (((c ∩ (subRegion b k m' ∩ WT)).image
        (translateEquiv (subCentre b k m')).symm).image (flipA a))) ?_
    rintro ω ⟨z, hz, hzC⟩
    exact rightSeed_of_mem_shiftedAnchor hab hu k hTZ hz hzC
  have hF := twoSided_failure_le p₀ q hSZ (leftZoneFinset_subset_leftExplore a m') hTZ
    (rightZoneFinset_subset_rightExplore a m') (disjoint_leftExplore_rightExplore a hm)
    (fun k => subRegion b k m' ∩ WS) (fun k => subRegion b k m' ∩ WT)
    (fun k X => LeftSeed a u m' (X.image (translateEquiv (subCentre b k m')).symm))
    (fun k Y => LeftSeed a u m' ((Y.image (translateEquiv (subCentre b k m')).symm).image
      (flipA a))) hFS hFT
  have hmain := two_chances p₀ q (by change (p₀ : ℝ) ≤ (p₀ : ℝ) + δ; linarith)
    (cubeAt 0 (6 * (3 * m'))) S T (leftZoneFinset a (3 * m')) (rightZoneFinset a (3 * m')) WS WT
    (fun k => subRegion b k m') (fun k => subRegion b k m' ∩ WS)
    (fun k => subRegion b k m' ∩ WT) hSZ (leftZoneFinset_subset_leftExplore a m') hTZ
    (rightZoneFinset_subset_rightExplore a m') (disjoint_leftExplore_rightExplore a hm)
    (coe_leftExplore_subset a m') (coe_rightExplore_subset a m')
    (fun k => coe_subRegion_subset b k m') (disjoint_subRegion b hm) (fun k => rfl)
    (fun k => rfl) (fun k => Finset.disjoint_of_subset_left hSZ (disjoint_leftZone_subRegion hab hm k))
    (fun k => Finset.disjoint_of_subset_left hTZ (disjoint_rightZone_subRegion hab hm k))
    (fun k X Y => LeftSeed a u m' (X.image (translateEquiv (subCentre b k m')).symm) ∧
      LeftSeed a u m' ((Y.image (translateEquiv (subCentre b k m')).symm).image (flipA a)))
    hπ0 hπ1 (fun k X Y _ _ hA => bootGood_subRegion hab hGood k X Y hA.1 hA.2) hF
  have h4 : 2 * ε₁ + 2 * ε₁ = 4 * ε₁ := by ring
  rw [h4] at hmain
  exact hmain

end Rigidity.Percolation
