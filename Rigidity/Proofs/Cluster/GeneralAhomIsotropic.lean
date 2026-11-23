import Rigidity.Proofs.Cluster.TriadicSignedPerm
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLimit
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLocal
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLowerBoundMean

/-!
# The homogenized matrix of `ℤ^d` is a multiple of the identity

Armstrong and Dario remark after (5.22) that `ā` is a multiple of the identity, by the
invariance of the model under the permutations and reflections of the coordinate axes. Here this
is proved in every dimension `d ≥ 2` for the matrix `cubeAhom` of the general quantities `ν`.
For a signed permutation `φ(x)ᵢ = sᵢ x_{π i}` of `ℤ^d` and the transported configuration `φ·ω`
(`configurationMap`), `φ` maps open paths inside a triadic cube `Q` to open paths inside `φ(Q)`
and the faces of `Q` to the faces of `φ(Q)` (a lower face to a lower or an upper face according
to the sign), so the crossing cluster of `φ(Q)` in `φ·ω` is the image of the crossing cluster of
`Q` (`signedPerm_mem_crossingCluster_iff`). Since `ν(U, p)` depends only on the crossing cluster and
its open edges, `ν(φ(U), φ_* p)` in `φ·ω` equals `ν(U, p)` (`cubeNu_signedPerm`), the law is
invariant, and the cube `□_m` centred at the origin is fixed by `φ`: the expectations, their
limit and the matrix `ā` are invariant (`cubeNuLimit_signedPermSlope`). The reflection of one
coordinate kills the off-diagonal entries and the transpositions equalize the diagonal ones
(`exists_cubeAhom_eq_smul_one`). The goodness of cubes is not used: the rounded three-quarter
cubes of the good cubes are not symmetric about their centres, but `ν` is defined through the
crossing cluster alone. The planar case is `PlanarAhomIsotropic`.
-/

namespace Rigidity.Percolation

open MeasureTheory LatticeProb.Percolation Rigidity.Proofs.S3 Rigidity.External Filter Topology
open scoped Classical

variable {d : ℕ}

/-- **Transport of `ν` along a bijection of clusters, with a transformed slope** (one
inequality). -/
theorem cubeNu_le_of_equiv_slope {ω ω' : Configuration d} {U U' : TriadicCube d}
    (p p' : Fin d → ℝ)
    (e : ↥(crossingClusterVertices ω U) ≃ ↥(crossingClusterVertices ω' U'))
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (hint : ∀ x, U'.IsLatticeInterior (e x).1 ↔ U.IsLatticeInterior x.1)
    (hflux : ∀ x y, ∑ i, p' i * (((e y).1 i : ℝ) - (e x).1 i) =
      ∑ i, p i * ((y.1 i : ℝ) - x.1 i))
    (hvol : U'.latticeVolume = U.latticeVolume) :
    cubeNu ω U p ≤ cubeNu ω' U' p' := by
  obtain ⟨v, hv, -, hν⟩ := exists_cubeNu_maximizer (ω := ω) (U := U) p
  obtain ⟨g, hg⟩ : ∃ g : CubeFun ω' U', g = fun y => v (e.symm y) := ⟨_, rfl⟩
  have hge : ∀ x, g (e x) = v x := fun x => by simp [hg]
  have hB : cubeForm ω' U' g g = cubeForm ω U v v := by
    rw [cubeForm_apply, cubeForm_apply]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [cubeFormTerm, hge, hadj]
  have hF : cubeFluxPairing ω' U' p' g = cubeFluxPairing ω U p v := by
    rw [cubeFluxPairing_apply, cubeFluxPairing_apply]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hge, hadj, hflux]
  have hgA : g ∈ cubeHarmonic ω' U' := by
    rw [mem_cubeHarmonic]
    intro y' hy'
    obtain ⟨x, rfl⟩ := e.surjective y'
    rw [hint] at hy'
    have h0 := mem_cubeHarmonic.1 hv x hy'
    rw [cubeLaplacianAt_apply] at h0 ⊢
    rw [← e.sum_comp]
    simp only [hge, hadj]
    exact h0
  have h := le_cubeNu (ω := ω') (U := U') p' hgA
  rw [hF, hB, hvol, ← hν] at h
  exact h

/-- **Transport of `ν` along a bijection of clusters, with a transformed slope.** -/
theorem cubeNu_eq_of_equiv_slope {ω ω' : Configuration d} {U U' : TriadicCube d}
    (p p' : Fin d → ℝ)
    (e : ↥(crossingClusterVertices ω U) ≃ ↥(crossingClusterVertices ω' U'))
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (hint : ∀ x, U'.IsLatticeInterior (e x).1 ↔ U.IsLatticeInterior x.1)
    (hflux : ∀ x y, ∑ i, p' i * (((e y).1 i : ℝ) - (e x).1 i) =
      ∑ i, p i * ((y.1 i : ℝ) - x.1 i))
    (hvol : U'.latticeVolume = U.latticeVolume) :
    cubeNu ω U p = cubeNu ω' U' p' := by
  refine le_antisymm (cubeNu_le_of_equiv_slope p p' e hadj hint hflux hvol)
    (cubeNu_le_of_equiv_slope p' p e.symm (fun x' y' => ?_) (fun x' => ?_) (fun x' y' => ?_)
      hvol.symm)
  · rw [← hadj, e.apply_symm_apply, e.apply_symm_apply]
  · rw [← hint, e.apply_symm_apply]
  · rw [← hflux, e.apply_symm_apply, e.apply_symm_apply]

section SignedPerm

variable (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ)

/-- Open paths inside a region are carried to open paths inside its image. -/
theorem reachable_openIn_configurationMap_iff (ω : Configuration d) {B B' : Set (Vertex d)}
    (hB : ∀ v, signedPermIso π s v ∈ B' ↔ v ∈ B) (x y : Vertex d) :
    (openIn (configurationMap (signedPermIso π s) ω) B').Reachable (signedPermIso π s x)
        (signedPermIso π s y) ↔ (openIn ω B).Reachable x y := by
  let φ : openIn ω B ≃g openIn (configurationMap (signedPermIso π s) ω) B' :=
    { toEquiv := (signedPermIso π s).toEquiv
      map_rel_iff' := by
        intro a b
        change (openGraph _).Adj (signedPermIso π s a) (signedPermIso π s b) ∧
            signedPermIso π s a ∈ B' ∧ signedPermIso π s b ∈ B' ↔
          (openGraph ω).Adj a b ∧ a ∈ B ∧ b ∈ B
        rw [openGraph_adj_configurationMap_iff, hB, hB] }
  exact SimpleGraph.Iso.reachable_iff (φ := φ)

theorem signedPermIso_apply (x : Vertex d) (i : Fin d) :
    signedPermIso π s x i = (s i : ℤ) * x (π i) := rfl

/-- **Lower faces of the image cube.** -/
theorem signedPerm_mem_lowerFace_iff (Q : TriadicCube d) {y : Vertex d} (hy : y ∈ Q.vertices)
    (j : Fin d) :
    signedPermIso π s y ∈ (Q.signedPerm π s).toIntegerCube.lowerFace j ↔
      ((s j : ℤ) = 1 ∧ y ∈ Q.toIntegerCube.lowerFace (π j)) ∨
        ((s j : ℤ) = -1 ∧ y ∈ Q.toIntegerCube.upperFace (π j)) := by
  have hyv : signedPermIso π s y ∈ (Q.signedPerm π s).toIntegerCube.vertices :=
    ((Q.signedPerm π s).mem_toIntegerCube_vertices _).2
      ((Q.signedPermVertex_mem_vertices_iff π s y).2 hy)
  have hyv' : y ∈ Q.toIntegerCube.vertices := (Q.mem_toIntegerCube_vertices _).2 hy
  rw [IntegerCube.mem_lowerFace, IntegerCube.mem_lowerFace, IntegerCube.mem_upperFace]
  simp only [hyv, hyv', true_and]
  change (s j : ℤ) * y (π j) = Q.side * ((s j : ℤ) * Q.index (π j)) - Q.side / 2 ↔
    ((s j : ℤ) = 1 ∧ y (π j) = Q.side * Q.index (π j) - Q.side / 2) ∨
      ((s j : ℤ) = -1 ∧ y (π j) + 1 = Q.side * Q.index (π j) - Q.side / 2 + ((3 ^ Q.scale : ℕ) : ℤ))
  have ho : Q.side % 2 = 1 := by
    have : Odd Q.side := (show Odd (3 : ℤ) from ⟨1, by norm_num⟩).pow
    exact Int.odd_iff.mp this
  have hside : ((3 ^ Q.scale : ℕ) : ℤ) = Q.side := by
    push_cast
    rfl
  rw [hside]
  have hneg : Q.side * (-1 * Q.index (π j)) = -(Q.side * Q.index (π j)) := by ring
  rcases units_int_eq_one_or (s j) with h | h <;> rw [h] <;> constructor
  · intro h1; left; exact ⟨rfl, by linarith⟩
  · rintro (⟨-, h1⟩ | ⟨h2, -⟩)
    · linarith
    · norm_num at h2
  · intro h1; right; refine ⟨rfl, ?_⟩; omega
  · rintro (⟨h2, -⟩ | ⟨-, h1⟩)
    · norm_num at h2
    · omega

/-- **Upper faces of the image cube.** -/
theorem signedPerm_mem_upperFace_iff (Q : TriadicCube d) {y : Vertex d} (hy : y ∈ Q.vertices)
    (j : Fin d) :
    signedPermIso π s y ∈ (Q.signedPerm π s).toIntegerCube.upperFace j ↔
      ((s j : ℤ) = 1 ∧ y ∈ Q.toIntegerCube.upperFace (π j)) ∨
        ((s j : ℤ) = -1 ∧ y ∈ Q.toIntegerCube.lowerFace (π j)) := by
  have hyv : signedPermIso π s y ∈ (Q.signedPerm π s).toIntegerCube.vertices :=
    ((Q.signedPerm π s).mem_toIntegerCube_vertices _).2
      ((Q.signedPermVertex_mem_vertices_iff π s y).2 hy)
  have hyv' : y ∈ Q.toIntegerCube.vertices := (Q.mem_toIntegerCube_vertices _).2 hy
  rw [IntegerCube.mem_upperFace, IntegerCube.mem_lowerFace, IntegerCube.mem_upperFace]
  simp only [hyv, hyv', true_and]
  change (s j : ℤ) * y (π j) + 1 = Q.side * ((s j : ℤ) * Q.index (π j)) - Q.side / 2 +
      ((3 ^ Q.scale : ℕ) : ℤ) ↔
    ((s j : ℤ) = 1 ∧ y (π j) + 1 = Q.side * Q.index (π j) - Q.side / 2 +
      ((3 ^ Q.scale : ℕ) : ℤ)) ∨
      ((s j : ℤ) = -1 ∧ y (π j) = Q.side * Q.index (π j) - Q.side / 2)
  have ho : Q.side % 2 = 1 := by
    have : Odd Q.side := (show Odd (3 : ℤ) from ⟨1, by norm_num⟩).pow
    exact Int.odd_iff.mp this
  have hside : ((3 ^ Q.scale : ℕ) : ℤ) = Q.side := by
    push_cast
    rfl
  rw [hside]
  have hneg : Q.side * (-1 * Q.index (π j)) = -(Q.side * Q.index (π j)) := by ring
  rcases units_int_eq_one_or (s j) with h | h <;> rw [h] <;> constructor
  · intro h1; left; exact ⟨rfl, by linarith⟩
  · rintro (⟨-, h1⟩ | ⟨h2, -⟩)
    · linarith
    · norm_num at h2
  · intro h1; right; refine ⟨rfl, ?_⟩; omega
  · rintro (⟨h2, -⟩ | ⟨-, h1⟩)
    · norm_num at h2
    · omega

end SignedPerm

section SignedPermCluster

variable (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ)

/-- **Crossing roots of the image cube.** -/
theorem signedPerm_isCrossingRoot_iff (ω : Configuration d) (Q : TriadicCube d) (r : Vertex d) :
    IsCrossingRoot (configurationMap (signedPermIso π s) ω) (Q.signedPerm π s).vertices
        (fun i => ↑((Q.signedPerm π s).toIntegerCube.lowerFace i))
        (fun i => ↑((Q.signedPerm π s).toIntegerCube.upperFace i)) (signedPermIso π s r) ↔
      IsCrossingRoot ω Q.vertices (fun i => ↑(Q.toIntegerCube.lowerFace i))
        (fun i => ↑(Q.toIntegerCube.upperFace i)) r := by
  have hB : ∀ v, signedPermIso π s v ∈ (Q.signedPerm π s).vertices ↔ v ∈ Q.vertices :=
    fun v => Q.signedPermVertex_mem_vertices_iff π s v
  have hR := reachable_openIn_configurationMap_iff π s ω hB
  constructor
  · rintro ⟨hr, hall⟩
    refine ⟨(hB r).1 hr, fun i => ?_⟩
    have hπj : π (π.symm i) = i := π.apply_symm_apply i
    obtain ⟨⟨y₁, hy₁B, hy₁F, hy₁R⟩, ⟨y₂, hy₂B, hy₂F, hy₂R⟩⟩ := hall (π.symm i)
    obtain ⟨z₁, rfl⟩ := (signedPermIso π s).surjective y₁
    obtain ⟨z₂, rfl⟩ := (signedPermIso π s).surjective y₂
    have hz₁ := (hB z₁).1 hy₁B
    have hz₂ := (hB z₂).1 hy₂B
    rw [Finset.mem_coe, signedPerm_mem_lowerFace_iff π s Q hz₁, hπj] at hy₁F
    rw [Finset.mem_coe, signedPerm_mem_upperFace_iff π s Q hz₂, hπj] at hy₂F
    rw [hR] at hy₁R hy₂R
    rcases hy₁F with ⟨hs1, h1⟩ | ⟨hs1, h1⟩ <;> rcases hy₂F with ⟨hs2, h2⟩ | ⟨hs2, h2⟩
    · exact ⟨⟨z₁, hz₁, h1, hy₁R⟩, ⟨z₂, hz₂, h2, hy₂R⟩⟩
    · rw [hs1] at hs2; norm_num at hs2
    · rw [hs1] at hs2; norm_num at hs2
    · exact ⟨⟨z₂, hz₂, h2, hy₂R⟩, ⟨z₁, hz₁, h1, hy₁R⟩⟩
  · rintro ⟨hr, hall⟩
    refine ⟨(hB r).2 hr, fun j => ?_⟩
    obtain ⟨⟨y₁, hy₁B, hy₁F, hy₁R⟩, ⟨y₂, hy₂B, hy₂F, hy₂R⟩⟩ := hall (π j)
    have hl₁ := fun h => (signedPerm_mem_lowerFace_iff π s Q hy₁B j).2 h
    have hl₂ := fun h => (signedPerm_mem_lowerFace_iff π s Q hy₂B j).2 h
    have hu₁ := fun h => (signedPerm_mem_upperFace_iff π s Q hy₁B j).2 h
    have hu₂ := fun h => (signedPerm_mem_upperFace_iff π s Q hy₂B j).2 h
    have hR₁ := (hR r y₁).2 hy₁R
    have hR₂ := (hR r y₂).2 hy₂R
    rcases units_int_eq_one_or (s j) with h | h
    · exact ⟨⟨_, (hB y₁).2 hy₁B, Finset.mem_coe.2 (hl₁ (Or.inl ⟨h, hy₁F⟩)), hR₁⟩,
        ⟨_, (hB y₂).2 hy₂B, Finset.mem_coe.2 (hu₂ (Or.inl ⟨h, hy₂F⟩)), hR₂⟩⟩
    · exact ⟨⟨_, (hB y₂).2 hy₂B, Finset.mem_coe.2 (hl₂ (Or.inr ⟨h, hy₂F⟩)), hR₂⟩,
        ⟨_, (hB y₁).2 hy₁B, Finset.mem_coe.2 (hu₁ (Or.inr ⟨h, hy₁F⟩)), hR₁⟩⟩

/-- **The crossing cluster of the image cube is the image of the crossing cluster.** -/
theorem signedPerm_mem_crossingCluster_iff (ω : Configuration d) (Q : TriadicCube d)
    (x : Vertex d) :
    signedPermIso π s x ∈ (Q.signedPerm π s).crossingCluster
        (configurationMap (signedPermIso π s) ω) ↔ x ∈ Q.crossingCluster ω := by
  have hB : ∀ v, signedPermIso π s v ∈ (Q.signedPerm π s).vertices ↔ v ∈ Q.vertices :=
    fun v => Q.signedPermVertex_mem_vertices_iff π s v
  have hR := reachable_openIn_configurationMap_iff π s ω hB
  simp only [TriadicCube.crossingCluster, Set.mem_setOf_eq]
  constructor
  · rintro ⟨r', hr', hreach⟩
    obtain ⟨r, rfl⟩ := (signedPermIso π s).surjective r'
    exact ⟨r, (signedPerm_isCrossingRoot_iff π s ω Q r).1 hr', (hR r x).1 hreach⟩
  · rintro ⟨r, hr, hreach⟩
    exact ⟨signedPermIso π s r, (signedPerm_isCrossingRoot_iff π s ω Q r).2 hr,
      (hR r x).2 hreach⟩

/-- The signed permutation as a bijection of the crossing clusters. -/
noncomputable def crossingClusterVerticesSignedPermEquiv (ω : Configuration d) (U : TriadicCube d) :
    ↥(crossingClusterVertices ω U) ≃ ↥(crossingClusterVertices
      (configurationMap (signedPermIso π s) ω) (U.signedPerm π s)) where
  toFun x := ⟨signedPermIso π s x.1, mem_crossingClusterVertices.2
    ((signedPerm_mem_crossingCluster_iff π s ω U x.1).2 (mem_crossingClusterVertices.1 x.2))⟩
  invFun y := ⟨(signedPermIso π s).symm y.1, mem_crossingClusterVertices.2
    ((signedPerm_mem_crossingCluster_iff π s ω U _).1 (by
      rw [RelIso.apply_symm_apply]
      exact mem_crossingClusterVertices.1 y.2))⟩
  left_inv x := Subtype.ext ((signedPermIso π s).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((signedPermIso π s).apply_symm_apply y.1)

/-- **Invariance of `ν` under the signed permutations.** -/
theorem cubeNu_signedPerm (ω : Configuration d) (U : TriadicCube d) (p : Fin d → ℝ) :
    cubeNu (configurationMap (signedPermIso π s) ω) (U.signedPerm π s) (signedPermSlope π s p) =
      cubeNu ω U p := by
  have hB : ∀ v, signedPermIso π s v ∈ (U.signedPerm π s).vertices ↔ v ∈ U.vertices :=
    fun v => U.signedPermVertex_mem_vertices_iff π s v
  refine (cubeNu_eq_of_equiv_slope p (signedPermSlope π s p)
    (crossingClusterVerticesSignedPermEquiv π s ω U) (fun x y => ?_) (fun x => ?_)
    (fun x y => ?_) rfl).symm
  · exact openGraph_adj_configurationMap_iff (signedPermIso π s) ω x.1 y.1
  · change (U.signedPerm π s).IsLatticeInterior (signedPermIso π s x.1) ↔
      U.IsLatticeInterior x.1
    constructor
    · intro h y' hadj
      exact (hB y').1 (h (signedPermIso π s y') ((signedPermIso π s).map_adj_iff.2 hadj))
    · intro h y hadj
      obtain ⟨y', rfl⟩ := (signedPermIso π s).surjective y
      exact (hB y').2 (h y' ((signedPermIso π s).map_adj_iff.1 hadj))
  · change ∑ i, signedPermSlope π s p i * ((signedPermIso π s y.1 i : ℝ) -
      (signedPermIso π s x.1 i : ℝ)) = _
    simp only [mul_sub, Finset.sum_sub_distrib, sum_signedPermSlope_mul]

/-- The cube centred at the origin is fixed by the signed permutations. -/
theorem signedPerm_origin (m : ℕ) :
    (⟨m, 0⟩ : TriadicCube d).signedPerm π s = ⟨m, 0⟩ := by
  simp only [TriadicCube.signedPerm, TriadicCube.mk.injEq, true_and]
  funext i
  simp [signedPermVertex_apply]

/-- **Invariance of the expectations of `ν`.** -/
theorem cubeNuMean_signedPermSlope (prob : unitInterval) (m : ℕ) (p : Fin d → ℝ) :
    cubeNuMean prob m (signedPermSlope π s p) = cubeNuMean prob m p := by
  unfold cubeNuMean
  have hmp := measurePreserving_configurationMap (signedPermIso π s) prob
  rw [← hmp.integral_comp (configurationMap (signedPermIso π s)).measurableEmbedding
    (fun ω => cubeNu ω (⟨m, 0⟩ : TriadicCube d) (signedPermSlope π s p))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have h := cubeNu_signedPerm π s ω (⟨m, 0⟩ : TriadicCube d) p
  rw [signedPerm_origin] at h
  exact h

/-- **Invariance of the limit of the expectations of `ν`.** -/
theorem cubeNuLimit_signedPermSlope (prob : unitInterval) (p : Fin d → ℝ) :
    cubeNuLimit prob (signedPermSlope π s p) = cubeNuLimit prob p := by
  unfold cubeNuLimit
  congr 1
  funext m
  exact cubeNuMean_signedPermSlope π s prob m p

end SignedPermCluster

end Rigidity.Percolation
