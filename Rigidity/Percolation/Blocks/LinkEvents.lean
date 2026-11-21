import Rigidity.Percolation.Blocks.LocalEvents

/-!
# Links between neighbouring boxes

The link event at a centre `c` in direction `a` at scale `m` joins the box `c + Q_u` to the box
`c + 10m e_a + Q_u` inside the cube of radius `6m` around their midpoint. The two boxes are a
left and a right seed of scale `m` after translation, so above criticality the link event has
probability close to one at arbitrarily large scales, at every centre and, by a permutation of
the coordinates, in every direction.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

variable {d : ℕ}

/-- The link from the box at `c` to the box at `c + 10m e_a`. -/
def linkEvent (c : Vertex d) (a : Fin d) (m u : ℕ) : Set (Configuration d) :=
  {ω | ConnectsRegions ω (cubeAt (c + offsetVec a ((5 * m : ℕ) : ℤ)) (6 * m)) (cubeAt c u)
    (cubeAt (c + offsetVec a ((10 * m : ℕ) : ℤ)) u)}

/-- Cubes are lattice rectangles. -/
theorem cubeAt_eq_latticeRectangle (c : Vertex d) (r : ℕ) :
    cubeAt c r = latticeRectangle (fun i => c i - r) (fun i => c i + r + 1) := by
  ext z
  simp only [mem_cubeAt, latticeRectangle, Set.mem_setOf_eq, abs_le]
  exact forall_congr' fun i => ⟨fun h => ⟨by linarith [h.1], by linarith [h.2]⟩,
    fun h => ⟨by linarith [h.1], by omega⟩⟩

/-- A cube carries a seed path at its centre of every smaller radius. -/
theorem hasSeedPath_cubeAt [NeZero d] (s : Vertex d) {u u' : ℕ} (h : u ≤ u') :
    HasSeedPath (cubeAt s u') s u := by
  have hs : s ∈ cubeAt s u := fun i => by simp
  set v : Vertex d := s + offsetVec 0 (u : ℤ) with hv
  have hvc : v ∈ cubeAt s u := by
    intro i
    simp only [hv, Pi.add_apply, offsetVec_apply, add_sub_cancel_left]
    split_ifs <;> simp
  refine ⟨cubeAt_mono h hs, v, ⟨hvc, 0, by simp [hv, offsetVec_apply]⟩, ?_⟩
  have hr : (openIn (allOpen d) (cubeAt s u)).Reachable s v := by
    rw [cubeAt_eq_latticeRectangle] at hs hvc ⊢
    exact reachable_allOpen_latticeRectangle _ _ hs hvc
  refine openIn_reachable_mono_region (fun z hz => ?_) hr
  exact ⟨cubeAt_mono h hz, hz⟩

/-- The box at `-5m e_a` is a left seed of scale `m`. -/
theorem leftSeed_box [NeZero d] (a : Fin d) {m u u' : ℕ} (hu : u ≤ u') (hu' : u' ≤ m / 8) :
    LeftSeed a u m (cubeFinset (offsetVec a (-((5 * m : ℕ) : ℤ))) u') := by
  rw [LeftSeed, coe_cubeFinset]
  refine ⟨fun z hz => ⟨fun i => ?_, ?_⟩, _, ⟨⟨?_, ?_⟩, fun j hj => ?_⟩, hasSeedPath_cubeAt _ hu⟩
  · have := abs_le.1 (hz i)
    simp only [offsetVec_apply, Pi.zero_apply, sub_zero] at this ⊢
    rw [abs_le]
    split_ifs at this <;> push_cast at this ⊢ <;> constructor <;> omega
  · have := abs_le.1 (hz a)
    simp only [offsetVec_apply, ↓reduceIte] at this
    push_cast at this ⊢
    omega
  · simp only [offsetVec_apply, ↓reduceIte]
    push_cast
    omega
  · simp only [offsetVec_apply, ↓reduceIte]
    push_cast
    omega
  · simp only [offsetVec_apply, hj, ↓reduceIte, abs_zero]
    push_cast
    omega

/-- The reflection carries the box at `5m e_a` to the box at `-5m e_a`. -/
theorem image_flipA_box (a : Fin d) (k : ℤ) (u : ℕ) :
    (cubeFinset (offsetVec a k) u).image (flipA a) = cubeFinset (offsetVec a (-k)) u := by
  classical
  apply Finset.coe_injective
  rw [Finset.coe_image, coe_cubeFinset, coe_cubeFinset, (coordIsometry_flipA a).image_cubeAt]
  congr 1
  funext i
  simp only [flipA_apply, offsetVec_apply]
  split_ifs <;> simp_all

/-- A coordinate permutation carries cubes onto cubes. -/
theorem image_coordinatePermutation_cubeAt (σ : Equiv.Perm (Fin d)) (x : Vertex d) (r : ℕ) :
    coordinatePermutation σ '' cubeAt x r = cubeAt (coordinatePermutation σ x) r := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩ i
    exact hz (σ i)
  · intro hy
    refine ⟨(coordinatePermutation σ).symm y, fun i => ?_, Equiv.apply_symm_apply _ y⟩
    have := hy (σ.symm i)
    change |y (σ.symm i) - x (σ (σ.symm i))| ≤ r at this
    rw [Equiv.apply_symm_apply] at this
    exact this

theorem coordinatePermutation_offsetVec (σ : Equiv.Perm (Fin d)) (a : Fin d) (k : ℤ) :
    coordinatePermutation σ (offsetVec a k) = offsetVec (σ.symm a) k := by
  funext i
  change offsetVec a k (σ i) = offsetVec (σ.symm a) k i
  simp only [offsetVec_apply, Equiv.eq_symm_apply]

theorem coordinatePermutation_add (σ : Equiv.Perm (Fin d)) (x y : Vertex d) :
    coordinatePermutation σ (x + y) = coordinatePermutation σ x + coordinatePermutation σ y := rfl

theorem offsetVec_add (a : Fin d) (k l : ℤ) : offsetVec a k + offsetVec a l = offsetVec a (k + l) := by
  funext i
  simp only [Pi.add_apply, offsetVec_apply]
  split_ifs <;> simp

/-- The probability of a link does not depend on the centre nor on the direction. -/
theorem linkEvent_prob_eq (p : unitInterval) (a b : Fin d) (c : Vertex d) (m u : ℕ) :
    (latticeBondLaw d p).real (linkEvent c b m u) =
      (latticeBondLaw d p).real {η | ConnectsRegions η (cubeAt 0 (6 * m))
        (cubeAt (offsetVec a (-((5 * m : ℕ) : ℤ))) u) (cubeAt (offsetVec a ((5 * m : ℕ) : ℤ)) u)} := by
  set σ : Equiv.Perm (Fin d) := Equiv.swap a b with hσ
  set g : Vertex d ≃ Vertex d :=
    (coordinatePermutation σ).trans (translateEquiv (c + offsetVec b ((5 * m : ℕ) : ℤ))) with hg
  have hgd : ∀ x y, latticeL1Dist (g x) (g y) = latticeL1Dist x y := fun x y =>
    (translateEquiv_dist _ _ _).trans (latticeL1Dist_coordinatePermutation σ x y)
  have himg : ∀ (x : Vertex d) (r : ℕ), g '' cubeAt x r =
      cubeAt (coordinatePermutation σ x + (c + offsetVec b ((5 * m : ℕ) : ℤ))) r := by
    intro x r
    rw [hg, Equiv.coe_trans, Set.image_comp, image_coordinatePermutation_cubeAt,
      image_translate_cubeAt]
  have hσa : σ.symm a = b := by simp [hσ]
  rw [← latticeBondLaw_real_connectsRegions_image p g hgd, himg, himg, himg,
    coordinatePermutation_offsetVec, coordinatePermutation_offsetVec, hσa]
  have h0 : coordinatePermutation σ (0 : Vertex d) = 0 := rfl
  rw [h0, zero_add]
  have e2 : offsetVec b (-((5 * m : ℕ) : ℤ)) + (c + offsetVec b ((5 * m : ℕ) : ℤ)) = c := by
    funext i
    simp only [Pi.add_apply, offsetVec_apply]
    split_ifs <;> ring
  have e3 : offsetVec b ((5 * m : ℕ) : ℤ) + (c + offsetVec b ((5 * m : ℕ) : ℤ)) =
      c + offsetVec b ((10 * m : ℕ) : ℤ) := by
    funext i
    simp only [Pi.add_apply, offsetVec_apply]
    split_ifs <;> push_cast <;> ring
  rw [e2, e3]
  rfl

/-- **Links at all large scales.** Above criticality in dimension at least two, for every
`ε > 0` there is a box radius `u` such that at arbitrarily large scales `m` every link event has
probability at least `1 - ε`. -/
theorem exists_link_scale [NeZero d] {a b : Fin d} (hab : a ≠ b) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℕ, ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ u + 1 ≤ m / 8 ∧
      ∀ (c : Vertex d) (b' : Fin d), 1 - ε ≤ (latticeBondLaw d p).real (linkEvent c b' m u) := by
  obtain ⟨u, hu⟩ := exists_seed_link hab hp hε
  refine ⟨u, fun N => ?_⟩
  obtain ⟨m, hNm, hum, hlink⟩ := hu N
  refine ⟨m, hNm, hum, fun c b' => ?_⟩
  rw [linkEvent_prob_eq p a b' c m u]
  have hS := leftSeed_box a (m := m) (le_refl u) (by omega)
  have hT : LeftSeed a u m ((cubeFinset (offsetVec a ((5 * m : ℕ) : ℤ)) u).image (flipA a)) := by
    rw [image_flipA_box]
    exact hS
  have := hlink _ _ hS hT
  rwa [coe_cubeFinset, coe_cubeFinset] at this

end Rigidity.Percolation
