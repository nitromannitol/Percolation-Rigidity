import Rigidity.Percolation.Bootstrap.Recursion
import Rigidity.Percolation.SlabRectangularConnectivity
import Rigidity.Vendor.FormalMathPercolation.Literature.HarrisInequality

/-!
# Iterating the bootstrap

At the first scale every pair of seeds is joined along a fixed lattice path whose marks all lie
in `(p₀, q]`, which has conditional probability at least `(q - p₀)^N`. The recursion
`π ↦ (1 - e)(1 - (1 - π)²)` started from any positive value exceeds `1 - 3e` after finitely many
steps. Harris' inequality for the marks removes the conditioning: a connection is a decreasing
event of the marks and a closed cut an increasing one.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

variable {d : ℕ}

/-! ### Paths with prescribed marks -/

/-- The bonds of a walk with all bonds open. -/
def walkBonds {B : Set (Vertex d)} : ∀ {x y : Vertex d}, (openIn (allOpen d) B).Walk x y →
    Finset (Bond d)
  | _, _, .nil => ∅
  | _, _, .cons h w => by
      classical
      exact insert (bondOfAdjacent ((openGraph_adj_iff _ _ _).1 h.1).1) (walkBonds w)

theorem card_walkBonds_le {B : Set (Vertex d)} :
    ∀ {x y : Vertex d} (w : (openIn (allOpen d) B).Walk x y), (walkBonds w).card ≤ w.length
  | _, _, .nil => by simp [walkBonds]
  | _, _, .cons h w => by
      classical
      simp only [walkBonds, SimpleGraph.Walk.length_cons]
      exact (Finset.card_insert_le _ _).trans (by have := card_walkBonds_le w; omega)

/-- If all bonds of a walk have marks at most `q`, its ends are joined at level `q`. -/
theorem reachable_of_walkBonds {B : Set (Vertex d)} {q : unitInterval} {ω : BondMarks d} :
    ∀ {x y : Vertex d} (w : (openIn (allOpen d) B).Walk x y),
      (∀ e ∈ walkBonds w, ω e ≤ q) → (openIn (thresholdBondMarks q ω) B).Reachable x y
  | _, _, .nil, _ => SimpleGraph.Reachable.refl _
  | x, _, .cons (v := v) h w, hle => by
      classical
      have hadj := ((openGraph_adj_iff _ _ _).1 h.1).1
      have hmem : bondOfAdjacent hadj ∈ walkBonds (SimpleGraph.Walk.cons h w) := by
        simp only [walkBonds]
        exact Finset.mem_insert_self _ _
      have hopen : thresholdBondMarks q ω (bondOfAdjacent hadj) = true := by
        change markThreshold q (ω (bondOfAdjacent hadj)) = true
        simp [markThreshold, hle _ hmem]
      have hedge : (openIn (thresholdBondMarks q ω) B).Adj x v :=
        ⟨(openGraph_adj_iff _ x v).2 ⟨hadj, hopen⟩, h.2.1, h.2.2⟩
      refine hedge.reachable.trans (reachable_of_walkBonds w fun e he => hle e ?_)
      simp only [walkBonds]
      exact Finset.mem_insert_of_mem he

/-- The probability that the marks of finitely many bonds all lie in `(p₀, q]`. -/
theorem bondMarkLaw_real_box_Ioc (E : Finset (Bond d)) {p₀ q : unitInterval} (hpq : p₀ ≤ q) :
    (bondMarkLaw d).real {ω | ∀ e ∈ E, p₀ < ω e ∧ ω e ≤ q} =
      ((q : ℝ) - p₀) ^ E.card := by
  have heq : {ω : BondMarks d | ∀ e ∈ E, p₀ < ω e ∧ ω e ≤ q} =
      (↑E : Set (Bond d)).pi (fun _ => Set.Ioc p₀ q) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, Set.mem_Ioc]
  rw [measureReal_def, heq, bondMarkLaw, Measure.infinitePi_pi]
  · rw [ENNReal.toReal_prod, Finset.prod_congr rfl (fun e _ => by
      rw [unitInterval.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hpq)]),
      Finset.prod_const]
  · exact fun _ _ => measurableSet_Ioc

/-- Marks of finitely many bonds at most `q`, together with marks above `p₀` on a finite family,
have conditional probability at least `(q - p₀)^{|E|}`. -/
theorem le_bondMarkLaw_real_paths_inter (E F : Finset (Bond d)) {p₀ q : unitInterval}
    (hpq : p₀ ≤ q) :
    ((q : ℝ) - p₀) ^ E.card * (bondMarkLaw d).real (bondMarksAbove F (constThreshold p₀)) ≤
      (bondMarkLaw d).real ({ω | ∀ e ∈ E, ω e ≤ q} ∩ bondMarksAbove F (constThreshold p₀)) := by
  classical
  set μ := bondMarkLaw d with hμ
  set P := {ω : BondMarks d | ∀ e ∈ E, p₀ < ω e ∧ ω e ≤ q} with hP
  set G := bondMarksAbove (F \ E) (constThreshold p₀) with hG
  have hPm : MeasurableSet[bondMarkSigma (E : Set (Bond d))] P := by
    have heq : P = ⋂ e ∈ E, (fun ω : BondMarks d => ω e) ⁻¹' Set.Ioc p₀ q := by
      ext ω
      simp only [hP, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioc]
    rw [heq]
    refine E.measurableSet_biInter fun e he => measurableSet_Ioc.preimage ?_
    exact measurable_iff_comap_le.mpr (le_iSup_of_le e (le_iSup_of_le he le_rfl))
  have hGm : MeasurableSet[bondMarkSigma ((F \ E : Finset (Bond d)) : Set (Bond d))] G :=
    measurableSet_bondMarksAbove_local _ _
  have hdisj : Disjoint (E : Set (Bond d)) ((F \ E : Finset (Bond d)) : Set (Bond d)) := by
    rw [Finset.coe_sdiff]
    exact Set.disjoint_sdiff_right
  have hind := bondMarkLaw_real_inter_of_disjoint hdisj hPm hGm
  have hsub : P ∩ G ⊆ {ω | ∀ e ∈ E, ω e ≤ q} ∩ bondMarksAbove F (constThreshold p₀) := by
    rintro ω ⟨h1, h2⟩
    refine ⟨fun e he => (h1 e he).2, fun e he => ?_⟩
    by_cases heE : e ∈ E
    · exact (h1 e heE).1
    · exact h2 e (Finset.mem_sdiff.2 ⟨he, heE⟩)
  have hHG : bondMarksAbove F (constThreshold p₀) ⊆ G := fun ω h e he =>
    h e (Finset.mem_sdiff.1 he).1
  calc ((q : ℝ) - p₀) ^ E.card * μ.real (bondMarksAbove F (constThreshold p₀))
      ≤ μ.real P * μ.real G := by
        rw [hP, bondMarkLaw_real_box_Ioc E hpq]
        exact mul_le_mul_of_nonneg_left (measureReal_mono hHG (measure_ne_top _ _))
          (pow_nonneg (sub_nonneg.2 (show (p₀ : ℝ) ≤ q from hpq)) _)
    _ = μ.real (P ∩ G) := hind.symm
    _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)

/-- Two families of mark lower bounds at a common level combine. -/
theorem bondMarksAbove_inter (F₁ F₂ : Finset (Bond d)) (β : Bond d → unitInterval) :
    bondMarksAbove F₁ β ∩ bondMarksAbove F₂ β = bondMarksAbove (F₁ ∪ F₂) β := by
  classical
  ext ω
  simp only [bondMarksAbove, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_union]
  constructor
  · rintro ⟨h1, h2⟩ e (he | he)
    · exact h1 e he
    · exact h2 e he
  · intro h
    exact ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩

/-- The centred cube is a lattice rectangle. -/
theorem cubeAt_zero_eq_latticeRectangle (n : ℕ) :
    cubeAt (0 : Vertex d) n = latticeRectangle (fun _ => -(n : ℤ)) (fun _ => (n : ℤ) + 1) := by
  ext z
  simp only [mem_cubeAt, latticeRectangle, Set.mem_setOf_eq, Pi.zero_apply, sub_zero, abs_le]
  exact forall_congr' fun i => ⟨fun h => ⟨h.1, by omega⟩, fun h => ⟨h.1, by omega⟩⟩

/-- The reflection preserves the centred cube. -/
theorem flipA_mem_cubeAt_zero {a : Fin d} {n : ℕ} {z : Vertex d} (hz : z ∈ cubeAt 0 n) :
    flipA a z ∈ cubeAt 0 n := by
  have h := (coordIsometry_flipA a).image_cubeAt 0 n
  have h0 : flipA a (0 : Vertex d) = 0 := by
    funext i
    simp [flipA_apply]
  rw [h0] at h
  exact h ▸ ⟨z, hz, rfl⟩

/-- **The first scale.** Every left and right seed of scale `m` are joined inside `Q_{6m}` at
level `q > p₀` with conditional probability at least `(q - p₀)^N`, `N` the number of vertices of
`Q_{6m}`. -/
theorem bootGood_base (a : Fin d) (u m : ℕ) {p₀ q : unitInterval} (hpq : p₀ ≤ q) :
    BootGood a u m p₀ q (((q : ℝ) - p₀) ^ (cubeFinset (0 : Vertex d) (6 * m)).card) := by
  classical
  intro S T hS hT
  obtain ⟨hSZ, s, -, hsS⟩ := hS
  obtain ⟨hTZ, s', -, hs'T⟩ := hT
  have hs : s ∈ S := hsS.1
  have ht : flipA a s' ∈ T := by
    have := hs'T.1
    rw [Finset.mem_coe, mem_image_equiv, flipA_symm] at this
    exact this
  set B := cubeFinset (0 : Vertex d) (6 * m) with hB
  have hBc : ((B : Finset (Vertex d)) : Set (Vertex d)) = cubeAt 0 (6 * m) := coe_cubeFinset _ _
  have hsB : s ∈ cubeAt 0 (6 * m) := (hSZ (Finset.mem_coe.2 hs)).1
  have htB : flipA a s' ∈ cubeAt 0 (6 * m) := flipA_mem_cubeAt_zero (hTZ hs'T.1).1
  have hreach : (openIn (allOpen d) (cubeAt 0 (6 * m))).Reachable s (flipA a s') := by
    rw [cubeAt_zero_eq_latticeRectangle] at hsB htB ⊢
    exact reachable_allOpen_latticeRectangle _ _ hsB htB
  obtain ⟨w, hpath⟩ := hreach.exists_isPath
  have hlen : w.length ≤ B.card := by
    have hsupp : w.support.toFinset ⊆ B := by
      intro z hz
      rw [← Finset.mem_coe, hBc]
      exact walk_support_subset_openIn w hsB z (List.mem_toFinset.mp hz)
    have hcard := Finset.card_le_card hsupp
    rw [List.toFinset_card_of_nodup hpath.support_nodup, SimpleGraph.Walk.length_support]
      at hcard
    omega
  set E := walkBonds w with hE
  have hEcard : E.card ≤ B.card := (card_walkBonds_le w).trans hlen
  set H := cutClosed p₀ S (leftZoneFinset a m) ∩ cutClosed p₀ T (rightZoneFinset a m) with hH
  have hHeq : H = bondMarksAbove (vertexCutBondsIn S (leftZoneFinset a m : Set (Vertex d)) ∪
      vertexCutBondsIn T (rightZoneFinset a m : Set (Vertex d))) (constThreshold p₀) :=
    bondMarksAbove_inter _ _ _
  have hδ0 : 0 ≤ (q : ℝ) - p₀ := sub_nonneg.2 (show (p₀ : ℝ) ≤ q from hpq)
  have hδ1 : (q : ℝ) - p₀ ≤ 1 := by linarith [q.property.2, p₀.property.1]
  have key := le_bondMarkLaw_real_paths_inter E (vertexCutBondsIn S (leftZoneFinset a m :
    Set (Vertex d)) ∪ vertexCutBondsIn T (rightZoneFinset a m : Set (Vertex d))) hpq
  rw [← hHeq] at key
  have hsub : {ω : BondMarks d | ∀ e ∈ E, ω e ≤ q} ∩ H ⊆
      {ω | ConnectsRegions (thresholdBondMarks q ω) (cubeAt 0 (6 * m)) S T} ∩ H := by
    rintro ω ⟨hP, hωH⟩
    exact ⟨⟨s, hsB, hs, flipA a s', htB, ht, reachable_of_walkBonds w hP⟩, hωH⟩
  calc ((q : ℝ) - p₀) ^ B.card * (bondMarkLaw d).real H
      ≤ ((q : ℝ) - p₀) ^ E.card * (bondMarkLaw d).real H :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hδ0 hδ1 hEcard) measureReal_nonneg
    _ ≤ _ := key
    _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)

/-! ### Removing the conditioning -/

/-- A decreasing and an increasing event of the marks are negatively correlated. -/
theorem bondMarkLaw_real_inter_le_mul {A H : Set (BondMarks d)} (hA : IsLowerSet A)
    (hH : IsUpperSet H) (hAm : MeasurableSet A) (hHm : MeasurableSet H) :
    (bondMarkLaw d).real (A ∩ H) ≤ (bondMarkLaw d).real A * (bondMarkLaw d).real H := by
  have harris := Percolation.Literature.infinitePi_harris (fun _ : Bond d =>
    (volume : Measure unitInterval)) hA.compl hH hAm.compl hHm
  change (bondMarkLaw d).real Aᶜ * (bondMarkLaw d).real H ≤ (bondMarkLaw d).real (Aᶜ ∩ H)
    at harris
  have h1 : (bondMarkLaw d).real (H ∩ A) + (bondMarkLaw d).real (H \ A) =
      (bondMarkLaw d).real H := measureReal_inter_add_sdiff hAm
  have h2 : (bondMarkLaw d).real Aᶜ = 1 - (bondMarkLaw d).real A := by
    rw [measureReal_compl hAm, probReal_univ]
  have h3 : H \ A = Aᶜ ∩ H := by
    rw [Set.sdiff_eq, Set.inter_comm]
  rw [Set.inter_comm] at h1
  rw [h3] at h1
  rw [h2] at harris
  nlinarith

/-- Connections are decreasing events of the marks. -/
theorem isLowerSet_connectsRegions_marks (q : unitInterval) (B L R : Set (Vertex d)) :
    IsLowerSet {ω : BondMarks d | ConnectsRegions (thresholdBondMarks q ω) B L R} := by
  intro ω ω' hle hω
  refine isUpperSet_connectsRegions B L R (fun e => ?_) hω
  change markThreshold q (ω e) ≤ markThreshold q (ω' e)
  unfold markThreshold
  by_cases h : ω e ≤ q
  · simp [h, (hle e).trans h]
  · simp [h]

/-- Mark lower bounds are increasing events. -/
theorem isUpperSet_bondMarksAbove (F : Finset (Bond d)) (β : Bond d → unitInterval) :
    IsUpperSet (bondMarksAbove F β) :=
  fun _ _ hle hω e he => lt_of_lt_of_le (hω e he) (hle e)

/-- **Unconditional connection of seeds.** -/
theorem BootGood.le_connect {a : Fin d} {u m : ℕ} {p₀ q : unitInterval} {π : ℝ}
    (h : BootGood a u m p₀ q π) (hp₀ : (p₀ : ℝ) < 1) {S T : Finset (Vertex d)}
    (hS : LeftSeed a u m S) (hT : LeftSeed a u m (T.image (flipA a))) :
    π ≤ (latticeBondLaw d q).real {η | ConnectsRegions η (cubeAt 0 (6 * m)) S T} := by
  classical
  set H := cutClosed p₀ S (leftZoneFinset a m) ∩ cutClosed p₀ T (rightZoneFinset a m) with hH
  set A := {ω : BondMarks d | ConnectsRegions (thresholdBondMarks q ω) (cubeAt 0 (6 * m)) S T}
    with hA
  have hHeq : H = bondMarksAbove (vertexCutBondsIn S (leftZoneFinset a m : Set (Vertex d)) ∪
      vertexCutBondsIn T (rightZoneFinset a m : Set (Vertex d))) (constThreshold p₀) :=
    bondMarksAbove_inter _ _ _
  have hHpos : 0 < (bondMarkLaw d).real H := by
    rw [hHeq, bondMarkLaw_real_bondMarksAbove]
    exact Finset.prod_pos fun e _ => by
      change 0 < 1 - (p₀ : ℝ)
      linarith
  have hAm : MeasurableSet A :=
    (measurableSet_connectsRegions _ _ _).preimage (measurable_thresholdBondMarks q)
  have hHm : MeasurableSet H := by
    rw [hHeq]
    exact measurableSet_bondMarksAbove _ _
  have h1 := h S T hS hT
  have h2 := bondMarkLaw_real_inter_le_mul (isLowerSet_connectsRegions_marks q _ _ _)
    (by rw [hHeq]; exact isUpperSet_bondMarksAbove _ _) hAm hHm
  have h3 : π * (bondMarkLaw d).real H ≤ (bondMarkLaw d).real A * (bondMarkLaw d).real H :=
    h1.trans h2
  have h4 : π ≤ (bondMarkLaw d).real A := le_of_mul_le_mul_right h3 hHpos
  rw [hA, show {ω : BondMarks d | ConnectsRegions (thresholdBondMarks q ω)
      (cubeAt 0 (6 * m)) S T} = thresholdBondMarks q ⁻¹'
        {η | ConnectsRegions η (cubeAt 0 (6 * m)) S T} from rfl,
    bondMarkLaw_real_preimage_threshold q (measurableSet_connectsRegions _ _ _)] at h4
  exact h4

/-! ### The recursion map -/

/-- The recursion map `π ↦ (1 - e)(1 - (1 - π)²)`. -/
def bootMap (e π : ℝ) : ℝ := (1 - e) * (1 - (1 - π) ^ 2)

theorem bootMap_nonneg {e π : ℝ} (he1 : e ≤ 1) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) :
    0 ≤ bootMap e π := by
  unfold bootMap
  apply mul_nonneg (by linarith)
  nlinarith

theorem bootMap_le_one {e π : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) : bootMap e π ≤ 1 := by
  unfold bootMap
  have h1 : 0 ≤ (1 - π) ^ 2 := sq_nonneg _
  nlinarith

theorem add_mul_le_bootMap {e π : ℝ} (he0 : 0 ≤ e) (hπ0 : 0 ≤ π)
    (hπ : π ≤ 1 - 3 * e) : π + e * π ≤ bootMap e π := by
  unfold bootMap
  have h : e ≤ (1 - e) * (2 - π) - 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h hπ0]

theorem bootMap_mono {e π π' : ℝ} (he1 : e ≤ 1) (hle : π ≤ π') (hπ' : π' ≤ 1) :
    bootMap e π ≤ bootMap e π' := by
  unfold bootMap
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  nlinarith

theorem le_bootMap_of_le {e π : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 4) (hπ : 1 - 3 * e ≤ π)
    (hπ1 : π ≤ 1) : 1 - 3 * e ≤ bootMap e π := by
  have h1 := add_mul_le_bootMap he0 (by linarith) (le_refl (1 - 3 * e))
  have h2 := bootMap_mono (by linarith) hπ hπ1 (e := e)
  nlinarith

theorem iterate_bootMap_mem {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) {π₀ : ℝ} (hπ0 : 0 ≤ π₀)
    (hπ1 : π₀ ≤ 1) (r : ℕ) :
    0 ≤ (bootMap e)^[r] π₀ ∧ (bootMap e)^[r] π₀ ≤ 1 := by
  induction r with
  | zero => exact ⟨hπ0, hπ1⟩
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨bootMap_nonneg he1 ih.1 ih.2, bootMap_le_one he0 he1⟩

/-- **The fixed point is approached.** From any positive starting value, the iterates of the
recursion map eventually stay above `1 - 3e`. -/
theorem exists_iterate_bootMap {e : ℝ} (he0 : 0 < e) (he : e ≤ 1 / 4) {π₀ : ℝ} (hπ0 : 0 < π₀)
    (hπ1 : π₀ ≤ 1) : ∃ R : ℕ, ∀ r, R ≤ r → 1 - 3 * e ≤ (bootMap e)^[r] π₀ := by
  have hmem := iterate_bootMap_mem he0.le (by linarith) hπ0.le hπ1
  have hclaim : ∀ r : ℕ, 1 - 3 * e ≤ (bootMap e)^[r] π₀ ∨
      π₀ + r * (e * π₀) ≤ (bootMap e)^[r] π₀ := by
    intro r
    induction r with
    | zero => right; simp
    | succ r ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · exact Or.inl (le_bootMap_of_le he0.le he h (hmem r).2)
      · by_cases h3 : (bootMap e)^[r] π₀ ≤ 1 - 3 * e
        · right
          have h4 := add_mul_le_bootMap he0.le (hmem r).1 h3
          have h5 : π₀ ≤ (bootMap e)^[r] π₀ := by
            have : 0 ≤ (r : ℝ) * (e * π₀) := by positivity
            linarith
          push_cast
          nlinarith [mul_le_mul_of_nonneg_left h5 he0.le]
        · left
          exact le_bootMap_of_le he0.le he (le_of_lt (not_le.1 h3)) (hmem r).2
  obtain ⟨R, hR⟩ := exists_nat_gt (1 / (e * π₀))
  have hfirst : 1 - 3 * e ≤ (bootMap e)^[R] π₀ := by
    rcases hclaim R with h | h
    · exact h
    · exfalso
      have hpos : 0 < e * π₀ := mul_pos he0 hπ0
      have : 1 < (R : ℝ) * (e * π₀) := by
        rw [div_lt_iff₀ hpos] at hR
        linarith
      linarith [(hmem R).2]
  refine ⟨R, fun r hr => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction k with
  | zero => simpa using hfirst
  | succ k ih =>
    rw [← add_assoc, Function.iterate_succ_apply']
    exact le_bootMap_of_le he0.le he (ih (Nat.le_add_right _ _)) (hmem _).2

end Rigidity.Percolation
