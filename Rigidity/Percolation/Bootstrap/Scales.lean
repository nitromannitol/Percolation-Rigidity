import Rigidity.Percolation.Bootstrap.Exploration
import Rigidity.Percolation.Bootstrap.AnchorReach

/-!
# Two consecutive scales of the bootstrap

At scale `m` the region is `Q_{6m}` with left zone `{z_a ≤ -4m}` and right zone `{z_a ≥ 4m}`; the
right objects are the images of the left ones under the reflection of the coordinate `a`. At
scale `3m'` the left and right exploration regions `{z ∈ Q_{18m'} : ±z_a ≥ 4m'}` are disjoint and
meet the two subregions `±9m' e_b + Q_{6m'}` exactly in the translates of their zones; the zones
of scale `3m'` are at distance `6m'` from the subregions.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

variable {d : ℕ}

/-! ### Zones and the reflection -/

/-- The left zone as a finite set. -/
def leftZoneFinset (a : Fin d) (m : ℕ) : Finset (Vertex d) := by
  classical
  exact (cubeFinset 0 (6 * m)).filter fun z => z a ≤ -(4 * m : ℤ)

/-- The right zone `{z ∈ Q_{6m} : z_a ≥ 4m}` as a finite set. -/
def rightZoneFinset (a : Fin d) (m : ℕ) : Finset (Vertex d) := by
  classical
  exact (cubeFinset 0 (6 * m)).filter fun z => (4 * m : ℤ) ≤ z a

/-- The right exploration region `{z ∈ Q_{18m'} : z_a ≥ 4m'}` as a finite set. -/
def rightExploreFinset (a : Fin d) (m' : ℕ) : Finset (Vertex d) := by
  classical
  exact (cubeFinset 0 (18 * m')).filter fun z => (4 * m' : ℤ) ≤ z a

/-- The reflection of the coordinate `a`. -/
def flipA (a : Fin d) : Vertex d ≃ Vertex d := coordinateSignFlip fun i => decide (i = a)

theorem flipA_apply (a : Fin d) (x : Vertex d) (i : Fin d) :
    flipA a x i = if i = a then -x i else x i := by
  change (if decide (i = a) then -(x i) else x i) = _
  simp only [decide_eq_true_eq]

theorem flipA_flipA (a : Fin d) (x : Vertex d) : flipA a (flipA a x) = x := by
  funext i
  simp only [flipA_apply]
  split_ifs <;> simp

theorem flipA_symm (a : Fin d) : (flipA a).symm = flipA a :=
  Equiv.ext fun x => by rw [Equiv.symm_apply_eq, flipA_flipA]

/-- Membership in the image of a finite set under a vertex bijection. -/
theorem mem_image_equiv {f : Vertex d ≃ Vertex d} {X : Finset (Vertex d)} {z : Vertex d} :
    z ∈ X.image f ↔ f.symm z ∈ X := by
  classical
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
    simpa using hx
  · intro h
    exact Finset.mem_image.2 ⟨_, h, f.apply_symm_apply z⟩

/-- Membership in the left zone in coordinates. -/
theorem mem_leftZoneFinset {a : Fin d} {m : ℕ} {z : Vertex d} :
    z ∈ leftZoneFinset a m ↔ (∀ i, |z i| ≤ (6 * m : ℕ)) ∧ z a ≤ -(4 * m : ℤ) := by
  classical
  simp [leftZoneFinset, mem_cubeFinset, mem_cubeAt]

/-- Membership in the right zone in coordinates. -/
theorem mem_rightZoneFinset {a : Fin d} {m : ℕ} {z : Vertex d} :
    z ∈ rightZoneFinset a m ↔ (∀ i, |z i| ≤ (6 * m : ℕ)) ∧ (4 * m : ℤ) ≤ z a := by
  classical
  simp [rightZoneFinset, mem_cubeFinset, mem_cubeAt]

/-- Membership in the left exploration region in coordinates. -/
theorem mem_leftExploreFinset {a : Fin d} {m' : ℕ} {z : Vertex d} :
    z ∈ leftExploreFinset a m' ↔ (∀ i, |z i| ≤ (18 * m' : ℕ)) ∧ z a ≤ -(4 * m' : ℤ) := by
  classical
  simp [leftExploreFinset, mem_cubeFinset, mem_cubeAt]

/-- Membership in the right exploration region in coordinates. -/
theorem mem_rightExploreFinset {a : Fin d} {m' : ℕ} {z : Vertex d} :
    z ∈ rightExploreFinset a m' ↔ (∀ i, |z i| ≤ (18 * m' : ℕ)) ∧ (4 * m' : ℤ) ≤ z a := by
  classical
  simp [rightExploreFinset, mem_cubeFinset, mem_cubeAt]

/-- The finite left zone is the left zone. -/
theorem coe_leftZoneFinset (a : Fin d) (m : ℕ) :
    ((leftZoneFinset a m : Finset (Vertex d)) : Set (Vertex d)) = leftZone a m := by
  ext z
  rw [Finset.mem_coe, mem_leftZoneFinset]
  simp [leftZone, mem_cubeAt]

/-- The reflection carries the left zone onto the right zone. -/
theorem image_flipA_leftZoneFinset (a : Fin d) (m : ℕ) :
    (leftZoneFinset a m).image (flipA a) = rightZoneFinset a m := by
  ext z
  rw [mem_image_equiv, flipA_symm, mem_leftZoneFinset, mem_rightZoneFinset]
  simp only [flipA_apply, ↓reduceIte]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, by omega⟩
    have := h1 i
    split_ifs at this <;> simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, by omega⟩
    have := h1 i
    split_ifs <;> simpa using this

/-- The reflection carries the left exploration region onto the right one. -/
theorem image_flipA_leftExploreFinset (a : Fin d) (m' : ℕ) :
    (leftExploreFinset a m').image (flipA a) = rightExploreFinset a m' := by
  ext z
  rw [mem_image_equiv, flipA_symm, mem_leftExploreFinset, mem_rightExploreFinset]
  simp only [flipA_apply, ↓reduceIte]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, by omega⟩
    have := h1 i
    split_ifs at this <;> simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, by omega⟩
    have := h1 i
    split_ifs <;> simpa using this

/-! ### The subregions -/

/-- The sign of a side. -/
def sgOf (k : Bool) : ℤˣ := if k then 1 else -1

/-- The centre `±9m' e_b` of a subregion. -/
def subCentre (b : Fin d) (k : Bool) (m' : ℕ) : Vertex d :=
  offsetVec b ((sgOf k : ℤ) * ((9 * m' : ℕ) : ℤ))

/-- The subregion `±9m' e_b + Q_{6m'}`. -/
def subRegion (b : Fin d) (k : Bool) (m' : ℕ) : Finset (Vertex d) :=
  cubeFinset (subCentre b k m') (6 * m')

theorem subCentre_apply_self (b : Fin d) (k : Bool) (m' : ℕ) :
    subCentre b k m' b = (if k then (9 * m' : ℤ) else -(9 * m' : ℤ)) := by
  cases k <;> simp [subCentre, offsetVec_apply, sgOf]

theorem subCentre_apply_of_ne {b i : Fin d} (h : i ≠ b) (k : Bool) (m' : ℕ) :
    subCentre b k m' i = 0 := by
  simp [subCentre, offsetVec_apply, h]

theorem abs_subCentre_le (b : Fin d) (k : Bool) (m' : ℕ) (i : Fin d) :
    |subCentre b k m' i| ≤ 9 * m' := by
  by_cases h : i = b
  · subst h
    rw [subCentre_apply_self]
    cases k <;> simp
  · rw [subCentre_apply_of_ne h]
    simp

/-- Translation by a vector, inverted. -/
theorem translateEquiv_symm_apply (c z : Vertex d) : (translateEquiv c).symm z = z - c := by
  simp [translateEquiv, latticeVertexTranslation, sub_eq_add_neg]

/-- The two exploration regions are disjoint. -/
theorem disjoint_leftExplore_rightExplore (a : Fin d) {m' : ℕ} (hm : 1 ≤ m') :
    Disjoint (leftExploreFinset a m') (rightExploreFinset a m') := by
  rw [Finset.disjoint_left]
  intro z h1 h2
  have := (mem_leftExploreFinset.1 h1).2
  have := (mem_rightExploreFinset.1 h2).2
  omega

/-- The two subregions are disjoint. -/
theorem disjoint_subRegion (b : Fin d) {m' : ℕ} (hm : 1 ≤ m') :
    Disjoint (subRegion b true m') (subRegion b false m') := by
  rw [Finset.disjoint_left]
  intro z h1 h2
  have h1' := abs_le.1 ((mem_cubeAt.1 (mem_cubeFinset.1 h1)) b)
  have h2' := abs_le.1 ((mem_cubeAt.1 (mem_cubeFinset.1 h2)) b)
  rw [subCentre_apply_self] at h1' h2'
  simp only [↓reduceIte, Bool.false_eq_true] at h1' h2'
  push_cast at h1' h2'
  omega

/-- The zone of scale `3m'` lies in the exploration region. -/
theorem leftZoneFinset_subset_leftExplore (a : Fin d) (m' : ℕ) :
    leftZoneFinset a (3 * m') ⊆ leftExploreFinset a m' := by
  intro z hz
  obtain ⟨h1, h2⟩ := mem_leftZoneFinset.1 hz
  refine mem_leftExploreFinset.2 ⟨fun i => ?_, by push_cast at h2 ⊢; omega⟩
  have := h1 i
  push_cast at this ⊢
  linarith

theorem rightZoneFinset_subset_rightExplore (a : Fin d) (m' : ℕ) :
    rightZoneFinset a (3 * m') ⊆ rightExploreFinset a m' := by
  intro z hz
  obtain ⟨h1, h2⟩ := mem_rightZoneFinset.1 hz
  refine mem_rightExploreFinset.2 ⟨fun i => ?_, by push_cast at h2 ⊢; omega⟩
  have := h1 i
  push_cast at this ⊢
  linarith

/-- The exploration regions and the subregions lie in `Q_{18m'}`. -/
theorem coe_leftExplore_subset (a : Fin d) (m' : ℕ) :
    ((leftExploreFinset a m' : Finset (Vertex d)) : Set (Vertex d)) ⊆ cubeAt 0 (6 * (3 * m')) := by
  intro z hz i
  have := (mem_leftExploreFinset.1 hz).1 i
  simp only [Pi.zero_apply, sub_zero]
  push_cast at this ⊢
  linarith

theorem coe_rightExplore_subset (a : Fin d) (m' : ℕ) :
    ((rightExploreFinset a m' : Finset (Vertex d)) : Set (Vertex d)) ⊆
      cubeAt 0 (6 * (3 * m')) := by
  intro z hz i
  have := (mem_rightExploreFinset.1 hz).1 i
  simp only [Pi.zero_apply, sub_zero]
  push_cast at this ⊢
  linarith

theorem coe_subRegion_subset (b : Fin d) (k : Bool) (m' : ℕ) :
    ((subRegion b k m' : Finset (Vertex d)) : Set (Vertex d)) ⊆ cubeAt 0 (6 * (3 * m')) := by
  intro z hz i
  have h1 := abs_le.1 ((mem_cubeAt.1 (mem_cubeFinset.1 (Finset.mem_coe.1 hz))) i)
  have h2 := abs_le.1 (abs_subCentre_le b k m' i)
  simp only [Pi.zero_apply, sub_zero]
  rw [abs_le]
  push_cast at h1 h2 ⊢
  constructor <;> linarith

/-- The zones of scale `3m'` are disjoint from the subregions. -/
theorem disjoint_leftZone_subRegion {a b : Fin d} (hab : a ≠ b) {m' : ℕ} (hm : 1 ≤ m')
    (k : Bool) :
    Disjoint (leftZoneFinset a (3 * m')) (subRegion b k m') := by
  rw [Finset.disjoint_left]
  intro z h1 h2
  have h1' := (mem_leftZoneFinset.1 h1).2
  have h2' := abs_le.1 ((mem_cubeAt.1 (mem_cubeFinset.1 h2)) a)
  rw [subCentre_apply_of_ne hab] at h2'
  push_cast at h1' h2'
  omega

theorem disjoint_rightZone_subRegion {a b : Fin d} (hab : a ≠ b) {m' : ℕ} (hm : 1 ≤ m')
    (k : Bool) :
    Disjoint (rightZoneFinset a (3 * m')) (subRegion b k m') := by
  rw [Finset.disjoint_left]
  intro z h1 h2
  have h1' := (mem_rightZoneFinset.1 h1).2
  have h2' := abs_le.1 ((mem_cubeAt.1 (mem_cubeFinset.1 h2)) a)
  rw [subCentre_apply_of_ne hab] at h2'
  push_cast at h1' h2'
  omega

/-- A subregion meets the left exploration region exactly in the translate of its left zone. -/
theorem subRegion_inter_leftExplore {a b : Fin d} (hab : a ≠ b) (m' : ℕ) (k : Bool) :
    subRegion b k m' ∩ leftExploreFinset a m' =
      (leftZoneFinset a m').image (translateEquiv (subCentre b k m')) := by
  ext z
  rw [Finset.mem_inter, mem_image_equiv, translateEquiv_symm_apply, mem_leftZoneFinset,
    mem_leftExploreFinset, subRegion, mem_cubeFinset, mem_cubeAt]
  have hca := subCentre_apply_of_ne hab k m'
  simp only [Pi.sub_apply, hca, sub_zero]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i => ?_, by omega⟩
    have h3 := abs_le.1 (h1 i)
    have h4 := abs_le.1 (abs_subCentre_le b k m' i)
    rw [abs_le]
    push_cast at h3 h4 ⊢
    constructor <;> linarith

/-- A subregion meets the right exploration region exactly in the translate of its right
zone. -/
theorem subRegion_inter_rightExplore {a b : Fin d} (hab : a ≠ b) (m' : ℕ) (k : Bool) :
    subRegion b k m' ∩ rightExploreFinset a m' =
      (rightZoneFinset a m').image (translateEquiv (subCentre b k m')) := by
  ext z
  rw [Finset.mem_inter, mem_image_equiv, translateEquiv_symm_apply, mem_rightZoneFinset,
    mem_rightExploreFinset, subRegion, mem_cubeFinset, mem_cubeAt]
  have hca := subCentre_apply_of_ne hab k m'
  simp only [Pi.sub_apply, hca, sub_zero]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i => ?_, by omega⟩
    have h3 := abs_le.1 (h1 i)
    have h4 := abs_le.1 (abs_subCentre_le b k m' i)
    rw [abs_le]
    push_cast at h3 h4 ⊢
    constructor <;> linarith

/-! ### Anchors of the subregions -/

/-- Membership in the shifted anchor. -/
theorem mem_shiftedAnchorFinset {a b : Fin d} {sg : ℤˣ} {m' : ℕ} {z : Vertex d} :
    z ∈ shiftedAnchorFinset a b sg m' ↔ (∀ i, |z i| ≤ (18 * m' : ℕ)) ∧
      z - offsetVec b ((sg : ℤ) * (9 * m' : ℕ)) ∈ leftAnchor a m' := by
  classical
  simp [shiftedAnchorFinset, mem_cubeFinset, mem_cubeAt]

/-- The cube of radius `u < m'/8` around a vertex of the left anchor of a subregion lies in the
trace of the subregion in the left exploration region, and misses the left zone of scale `3m'`. -/
theorem shiftedAnchor_cube {a b : Fin d} (hab : a ≠ b) {m' u : ℕ} (hu : u + 1 ≤ m' / 8)
    (k : Bool) {z : Vertex d} (hz : z ∈ shiftedAnchorFinset a b (sgOf k) m') :
    cubeAt z u ⊆ ((subRegion b k m' ∩ leftExploreFinset a m' : Finset (Vertex d)) :
      Set (Vertex d)) ∧ ∀ g ∈ leftZoneFinset a (3 * m'), g ∉ cubeAt z u := by
  obtain ⟨-, ⟨hza1, hza2⟩, hzj⟩ := mem_shiftedAnchorFinset.1 hz
  have hc : z - offsetVec b ((sgOf k : ℤ) * (9 * m' : ℕ)) = z - subCentre b k m' := rfl
  rw [hc] at hza1 hza2 hzj
  have hca := subCentre_apply_of_ne hab k m'
  simp only [Pi.sub_apply, hca, sub_zero] at hza1 hza2
  have hR : ∀ y ∈ cubeAt z u, ∀ i, |y i - subCentre b k m' i| ≤ 6 * m' := by
    intro y hy i
    have h1 := abs_le.1 (hy i)
    rw [abs_le]
    by_cases hi : i = a
    · subst hi
      rw [hca]
      push_cast at h1 hza1 hza2 ⊢
      constructor <;> omega
    · have h2 := abs_le.1 (hzj i hi)
      simp only [Pi.sub_apply] at h2
      push_cast at h1 h2 ⊢
      constructor <;> omega
  refine ⟨fun y hy => ?_, fun g hg hgy => ?_⟩
  · rw [Finset.mem_coe, Finset.mem_inter, subRegion, mem_cubeFinset, mem_cubeAt,
      mem_leftExploreFinset]
    refine ⟨fun i => by exact_mod_cast hR y hy i, fun i => ?_, ?_⟩
    · have h1 := abs_le.1 (hR y hy i)
      have h2 := abs_le.1 (abs_subCentre_le b k m' i)
      rw [abs_le]
      push_cast at h1 h2 ⊢
      constructor <;> linarith
    · have h1 := abs_le.1 (hy a)
      push_cast at h1 hza2 ⊢
      omega
  · have h1 := abs_le.1 (hgy a)
    have h2 := (mem_leftZoneFinset.1 hg).2
    push_cast at h1 h2 hza1
    omega

/-- The reflected statement for the right anchors of the subregions. -/
theorem flipShiftedAnchor_cube {a b : Fin d} (hab : a ≠ b) {m' u : ℕ} (hu : u + 1 ≤ m' / 8)
    (k : Bool) {z : Vertex d}
    (hz : z ∈ (shiftedAnchorFinset a b (sgOf k) m').image (flipA a)) :
    cubeAt z u ⊆ ((subRegion b k m' ∩ rightExploreFinset a m' : Finset (Vertex d)) :
      Set (Vertex d)) ∧ ∀ g ∈ rightZoneFinset a (3 * m'), g ∉ cubeAt z u := by
  rw [mem_image_equiv, flipA_symm] at hz
  obtain ⟨-, ⟨hza1, hza2⟩, hzj⟩ := mem_shiftedAnchorFinset.1 hz
  have hc : flipA a z - offsetVec b ((sgOf k : ℤ) * (9 * m' : ℕ)) =
      flipA a z - subCentre b k m' := rfl
  rw [hc] at hza1 hza2 hzj
  have hca := subCentre_apply_of_ne hab k m'
  simp only [Pi.sub_apply, hca, sub_zero, flipA_apply, ↓reduceIte] at hza1 hza2
  have hR : ∀ y ∈ cubeAt z u, ∀ i, |y i - subCentre b k m' i| ≤ 6 * m' := by
    intro y hy i
    have h1 := abs_le.1 (hy i)
    rw [abs_le]
    by_cases hi : i = a
    · subst hi
      rw [hca]
      push_cast at h1 hza1 hza2 ⊢
      constructor <;> omega
    · have h2 := abs_le.1 (hzj i hi)
      simp only [Pi.sub_apply, flipA_apply, hi, ↓reduceIte] at h2
      push_cast at h1 h2 ⊢
      constructor <;> omega
  refine ⟨fun y hy => ?_, fun g hg hgy => ?_⟩
  · rw [Finset.mem_coe, Finset.mem_inter, subRegion, mem_cubeFinset, mem_cubeAt,
      mem_rightExploreFinset]
    refine ⟨fun i => by exact_mod_cast hR y hy i, fun i => ?_, ?_⟩
    · have h1 := abs_le.1 (hR y hy i)
      have h2 := abs_le.1 (abs_subCentre_le b k m' i)
      rw [abs_le]
      push_cast at h1 h2 ⊢
      constructor <;> linarith
    · have h1 := abs_le.1 (hy a)
      push_cast at h1 hza1 ⊢
      omega
  · have h1 := abs_le.1 (hgy a)
    have h2 := (mem_rightZoneFinset.1 hg).2
    push_cast at h1 h2 hza2
    omega

end Rigidity.Percolation
