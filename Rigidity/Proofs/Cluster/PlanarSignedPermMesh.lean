import Rigidity.Proofs.Cluster.TriadicSignedPerm
import Rigidity.Proofs.Percolation.PlanarPartition
import Rigidity.Proofs.Percolation.PlanarLocalConnectivity

/-!
# Symmetries of the planar meshes and of the planar partition

For a signed permutation `φ` of `ℤ²` and the configuration `φ·ω` transported by `φ`
(`configurationMap`), open connections inside a region `S` are carried to open connections inside
`φ(S)`. The image of an integer square is an integer square of the same side, and the image of the
family of squares around a triadic cube `Q` is the family of squares around `φ(Q)`. For the
reflection `x ↦ (-x₀, x₁)` and the transposition `x ↦ (x₁, x₀)`, the strips of a square are carried
to the strips of its image, so a square carries a strip mesh in `ω` exactly when its image carries
one in `φ·ω`. Hence the meshed cubes, the good cubes and the maximal stopping cubes are carried to
those of `φ·ω`, the partition event is invariant, and the partition cube of `φ(x)` in `φ·ω` is the
image of the partition cube of `x` in `ω`.
-/

open LatticeProb.Percolation Rigidity.Proofs.S3 Rigidity.Proofs.Section5

namespace Rigidity.Percolation

section Transport

variable (φ : nearestNeighborGraph 2 ≃g nearestNeighborGraph 2)

/-- **Open connections are transported by a lattice automorphism.** -/
theorem reachIn_configurationMap_iff (ω : Configuration 2) {S S' : Set (Vertex 2)}
    (hS : ∀ v, φ v ∈ S' ↔ v ∈ S) (x y : Vertex 2) :
    ReachIn (configurationMap φ ω) S' (φ x) (φ y) ↔ ReachIn ω S x y := by
  constructor
  · rintro ⟨W, hW⟩
    let f := (openGraphMap φ ω).symm.toHom
    refine ⟨(W.map f).copy ((openGraphMap φ ω).symm_apply_apply x)
      ((openGraphMap φ ω).symm_apply_apply y), ?_⟩
    intro v hv
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [← hS]
    have e : φ (f u) = u := (openGraphMap φ ω).apply_symm_apply u
    rw [e]
    exact hW u hu
  · rintro ⟨W, hW⟩
    refine ⟨(W.map (openGraphMap φ ω).toHom).copy rfl rfl, ?_⟩
    intro v hv
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    exact (hS u).2 (hW u hu)

/-- An involutive lattice automorphism permutes the bonds involutively. -/
theorem bondMap_bondMap (hφ : ∀ x, φ (φ x) = x) (e : Bond 2) : bondMap φ (bondMap φ e) = e := by
  apply Subtype.ext
  change Sym2.map φ (Sym2.map φ e.val) = e.val
  rw [Sym2.map_map]
  have h : (⇑φ ∘ ⇑φ) = fun x => x := funext hφ
  rw [h, Sym2.map_id']
  rfl

/-- **An involutive lattice automorphism acts involutively on configurations.** -/
theorem configurationMap_configurationMap (hφ : ∀ x, φ (φ x) = x) (ω : Configuration 2) :
    configurationMap φ (configurationMap φ ω) = ω := by
  funext e
  have h := configurationMap_apply_bondMap φ (configurationMap φ ω) (bondMap φ e)
  rw [bondMap_bondMap φ hφ, configurationMap_apply_bondMap] at h
  exact h

end Transport

variable (π : Equiv.Perm (Fin 2)) (s : Fin 2 → ℤˣ)

/-- The image of an integer square under a signed permutation. -/
def IntegerCube.signedPerm (R : IntegerCube 2) : IntegerCube 2 where
  corner i := if (s i : ℤ) = 1 then R.corner (π i) else -(R.corner (π i) + R.size - 1)
  size := R.size

@[simp] theorem IntegerCube.size_signedPerm (R : IntegerCube 2) :
    (R.signedPerm π s).size = R.size := rfl

theorem IntegerCube.corner_signedPerm (R : IntegerCube 2) (i : Fin 2) :
    (R.signedPerm π s).corner i =
      if (s i : ℤ) = 1 then R.corner (π i) else -(R.corner (π i) + R.size - 1) := rfl

/-- **Vertices of the image square.** -/
theorem IntegerCube.signedPermVertex_mem_vertices_iff (R : IntegerCube 2) (x : Vertex 2) :
    signedPermVertex π s x ∈ (R.signedPerm π s).vertices ↔ x ∈ R.vertices := by
  rw [IntegerCube.mem_vertices, IntegerCube.mem_vertices]
  have h : ∀ i, ((R.signedPerm π s).corner i ≤ signedPermVertex π s x i ∧
      signedPermVertex π s x i < (R.signedPerm π s).corner i + ((R.signedPerm π s).size : ℤ)) ↔
      (R.corner (π i) ≤ x (π i) ∧ x (π i) < R.corner (π i) + (R.size : ℤ)) := by
    intro i
    rw [corner_signedPerm, size_signedPerm, signedPermVertex_apply]
    rcases units_int_eq_one_or (s i) with hs | hs
    · rw [if_pos hs, hs, one_mul]
    · rw [if_neg (by rw [hs]; norm_num), hs]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp only [h]
  exact forall_perm_iff π (fun i => R.corner i ≤ x i ∧ x i < R.corner i + (R.size : ℤ))

/-- The image squares exhaust the squares. -/
theorem IntegerCube.signedPerm_surjective (R' : IntegerCube 2) :
    ∃ R : IntegerCube 2, R.signedPerm π s = R' := by
  refine ⟨⟨fun j => if (s (π.symm j) : ℤ) = 1 then R'.corner (π.symm j)
    else -(R'.corner (π.symm j) + R'.size - 1), R'.size⟩, ?_⟩
  cases R' with
  | mk c n =>
    simp only [IntegerCube.signedPerm, Equiv.symm_apply_apply, IntegerCube.mk.injEq, and_true]
    funext i
    split_ifs with h <;> ring

/-- The centre of the image of a triadic cube. -/
theorem TriadicCube.center_signedPerm (Q : TriadicCube 2) (i : Fin 2) :
    (Q.signedPerm π s).center i = (s i : ℤ) * Q.center (π i) := by
  change Q.side * ((s i : ℤ) * Q.index (π i)) = (s i : ℤ) * (Q.side * Q.index (π i))
  ring

theorem TriadicCube.ninefoldRadius_signedPerm (Q : TriadicCube 2) :
    (Q.signedPerm π s).ninefoldRadius = Q.ninefoldRadius := rfl

/-- **The squares around the image of a triadic cube** are the images of the squares around it. -/
theorem TriadicCube.signedPerm_mem_planarSquares_iff (Q : TriadicCube 2) (R : IntegerCube 2) :
    R.signedPerm π s ∈ (Q.signedPerm π s).planarSquares ↔ R ∈ Q.planarSquares := by
  rw [TriadicCube.mem_planarSquares, TriadicCube.mem_planarSquares]
  simp only [IntegerCube.size_signedPerm, scale_signedPerm, ninefoldRadius_signedPerm]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  have h : ∀ i, ((Q.signedPerm π s).center i - Q.ninefoldRadius ≤ (R.signedPerm π s).corner i ∧
      (R.signedPerm π s).corner i + R.size ≤ (Q.signedPerm π s).center i + Q.ninefoldRadius + 1) ↔
      (Q.center (π i) - Q.ninefoldRadius ≤ R.corner (π i) ∧
        R.corner (π i) + R.size ≤ Q.center (π i) + Q.ninefoldRadius + 1) := by
    intro i
    rw [center_signedPerm, IntegerCube.corner_signedPerm]
    rcases units_int_eq_one_or (s i) with hs | hs
    · rw [if_pos hs, hs, one_mul]
    · rw [if_neg (by rw [hs]; norm_num), hs]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp only [h]
  exact forall_perm_iff π (fun i => Q.center i - Q.ninefoldRadius ≤ R.corner i ∧
    R.corner i + R.size ≤ Q.center i + Q.ninefoldRadius + 1)

/-- **Meshed cubes are carried to meshed cubes** when the strip meshes are. -/
theorem TriadicCube.signedPerm_planarMeshed_iff
    (hmesh : ∀ (ω : Configuration 2) (R : IntegerCube 2) (w : ℕ),
      PlanarMesh (configurationMap (signedPermIso π s) ω) (R.signedPerm π s) w ↔ PlanarMesh ω R w)
    (ω : Configuration 2) (Q : TriadicCube 2) :
    (Q.signedPerm π s).planarMeshed (configurationMap (signedPermIso π s) ω) ↔ Q.planarMeshed ω := by
  unfold TriadicCube.planarMeshed
  simp only [scale_signedPerm]
  constructor
  · intro h R hR
    rw [← hmesh]
    exact h _ ((Q.signedPerm_mem_planarSquares_iff π s R).2 hR)
  · intro h R' hR'
    obtain ⟨R, rfl⟩ := IntegerCube.signedPerm_surjective π s R'
    rw [hmesh]
    exact h R ((Q.signedPerm_mem_planarSquares_iff π s R).1 hR')

/-- **Good cubes are carried to good cubes.** -/
theorem TriadicCube.signedPerm_mem_planarGoodCubes_iff
    (hmesh : ∀ (ω : Configuration 2) (R : IntegerCube 2) (w : ℕ),
      PlanarMesh (configurationMap (signedPermIso π s) ω) (R.signedPerm π s) w ↔ PlanarMesh ω R w)
    (ω : Configuration 2) (Q : TriadicCube 2) :
    Q.signedPerm π s ∈ planarGoodCubes (configurationMap (signedPermIso π s) ω) ↔
      Q ∈ planarGoodCubes ω := by
  unfold planarGoodCubes
  refine TriadicCube.signedPerm_mem_goodOfWellConnected_iff (fun R => ?_) Q
  unfold planarMeshedFamily
  simp only [Set.mem_setOf_eq, scale_signedPerm, signedPerm_planarMeshed_iff π s hmesh]

/-- **Maximal stopping cubes are carried to maximal stopping cubes.** -/
theorem TriadicCube.signedPerm_isMaximalStopping_planar_iff
    (hmesh : ∀ (ω : Configuration 2) (R : IntegerCube 2) (w : ℕ),
      PlanarMesh (configurationMap (signedPermIso π s) ω) (R.signedPerm π s) w ↔ PlanarMesh ω R w)
    (ω : Configuration 2) (Q : TriadicCube 2) :
    (Q.signedPerm π s).IsMaximalStopping (planarGoodCubes (configurationMap (signedPermIso π s) ω)) ↔
      Q.IsMaximalStopping (planarGoodCubes ω) :=
  TriadicCube.signedPerm_isMaximalStopping_iff
    (fun R => signedPerm_mem_planarGoodCubes_iff π s hmesh ω R) Q

/-- **The partition event is invariant.** -/
theorem planarPartitionEvent_configurationMap_iff
    (hmesh : ∀ (ω : Configuration 2) (R : IntegerCube 2) (w : ℕ),
      PlanarMesh (configurationMap (signedPermIso π s) ω) (R.signedPerm π s) w ↔ PlanarMesh ω R w)
    (ω : Configuration 2) :
    PlanarPartitionEvent (configurationMap (signedPermIso π s) ω) ↔ PlanarPartitionEvent ω := by
  have hmax := TriadicCube.signedPerm_isMaximalStopping_planar_iff π s hmesh ω
  have hmem := fun (Q : TriadicCube 2) (x : Vertex 2) =>
    Q.signedPermVertex_mem_vertices_iff π s x
  unfold PlanarPartitionEvent
  constructor
  · intro h x
    obtain ⟨Q', ⟨hxQ', hQ'⟩, huniq⟩ := h (signedPermVertex π s x)
    obtain ⟨Q, rfl⟩ := TriadicCube.signedPerm_surjective π s Q'
    refine ⟨Q, ⟨(hmem Q x).1 hxQ', (hmax Q).1 hQ'⟩, fun R ⟨hxR, hR⟩ => ?_⟩
    exact TriadicCube.signedPerm_injective π s
      (huniq _ ⟨(hmem R x).2 hxR, (hmax R).2 hR⟩)
  · intro h y
    obtain ⟨x, rfl⟩ := (signedPermVertex π s).surjective y
    obtain ⟨Q, ⟨hxQ, hQ⟩, huniq⟩ := h x
    refine ⟨Q.signedPerm π s, ⟨(hmem Q x).2 hxQ, (hmax Q).2 hQ⟩, fun R' ⟨hxR', hR'⟩ => ?_⟩
    obtain ⟨R, rfl⟩ := TriadicCube.signedPerm_surjective π s R'
    rw [huniq R ⟨(hmem R x).1 hxR', (hmax R).1 hR'⟩]

/-- **The partition cube of the image vertex is the image of the partition cube.** -/
theorem planarPartCube_configurationMap
    (hmesh : ∀ (ω : Configuration 2) (R : IntegerCube 2) (w : ℕ),
      PlanarMesh (configurationMap (signedPermIso π s) ω) (R.signedPerm π s) w ↔ PlanarMesh ω R w)
    {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (x : Vertex 2) :
    planarPartCube (configurationMap (signedPermIso π s) ω) (signedPermVertex π s x) =
      (planarPartCube ω x).signedPerm π s := by
  have hP' := (planarPartitionEvent_configurationMap_iff π s hmesh ω).2 hP
  obtain ⟨hx, hmax⟩ := planarPartCube_spec hP x
  exact planarPartCube_eq hP' (((planarPartCube ω x).signedPermVertex_mem_vertices_iff π s x).2 hx)
    ((TriadicCube.signedPerm_isMaximalStopping_planar_iff π s hmesh ω _).2 hmax)

end Rigidity.Percolation
