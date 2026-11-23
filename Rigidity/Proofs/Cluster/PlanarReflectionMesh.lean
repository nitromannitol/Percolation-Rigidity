import Rigidity.Proofs.Cluster.PlanarSignedPermMesh

/-!
# Strip meshes under the reflection and the transposition of the plane

The reflection `ρ(x) = (-x₀, x₁)` carries the horizontal strips of a square to the horizontal
strips of its image, reversing the direction of the crossings, and the vertical strip
`[r, r + w] × [c₁, c₁ + S - 1]` to the vertical strip `[-r - w, -r] × [c₁, c₁ + S - 1]`. The
transposition `τ(x) = (x₁, x₀)` exchanges the horizontal and the vertical strips. Both are
involutions, so a square carries a strip mesh in `ω` exactly when its image carries one in the
transported configuration.
-/

open LatticeProb.Percolation Rigidity.Proofs.S3 Rigidity.Proofs.Section5

namespace Rigidity.Percolation

/-- The signs of the reflection `x ↦ (-x₀, x₁)`. -/
def reflectSigns : Fin 2 → ℤˣ := ![-1, 1]

/-- The reflection `x ↦ (-x₀, x₁)` as a lattice automorphism. -/
abbrev reflectIso : nearestNeighborGraph 2 ≃g nearestNeighborGraph 2 :=
  signedPermIso (Equiv.refl (Fin 2)) reflectSigns

/-- The transposition `x ↦ (x₁, x₀)` as a lattice automorphism. -/
abbrev swapIso : nearestNeighborGraph 2 ≃g nearestNeighborGraph 2 :=
  signedPermIso (Equiv.swap 0 1) (fun _ => 1)

@[simp] theorem reflectSigns_zero : ((reflectSigns 0 : ℤˣ) : ℤ) = -1 := rfl

@[simp] theorem reflectSigns_one : ((reflectSigns 1 : ℤˣ) : ℤ) = 1 := rfl

theorem reflectIso_apply_zero (x : Vertex 2) : reflectIso x 0 = -x 0 := by
  change ((reflectSigns 0 : ℤˣ) : ℤ) * x 0 = -x 0
  simp

theorem reflectIso_apply_one (x : Vertex 2) : reflectIso x 1 = x 1 := by
  change ((reflectSigns 1 : ℤˣ) : ℤ) * x 1 = x 1
  simp

theorem swapIso_apply_zero (x : Vertex 2) : swapIso x 0 = x 1 := by
  change ((1 : ℤˣ) : ℤ) * x (Equiv.swap 0 1 0) = x 1
  simp

theorem swapIso_apply_one (x : Vertex 2) : swapIso x 1 = x 0 := by
  change ((1 : ℤˣ) : ℤ) * x (Equiv.swap 0 1 1) = x 0
  simp

theorem reflectIso_reflectIso (x : Vertex 2) : reflectIso (reflectIso x) = x := by
  funext i
  fin_cases i
  · change reflectIso (reflectIso x) 0 = x 0
    rw [reflectIso_apply_zero, reflectIso_apply_zero, neg_neg]
  · change reflectIso (reflectIso x) 1 = x 1
    rw [reflectIso_apply_one, reflectIso_apply_one]

theorem swapIso_swapIso (x : Vertex 2) : swapIso (swapIso x) = x := by
  funext i
  fin_cases i
  · change swapIso (swapIso x) 0 = x 0
    rw [swapIso_apply_zero, swapIso_apply_one]
  · change swapIso (swapIso x) 1 = x 1
    rw [swapIso_apply_one, swapIso_apply_zero]

/-- The image square of the reflection. -/
abbrev IntegerCube.reflect (R : IntegerCube 2) : IntegerCube 2 :=
  R.signedPerm (Equiv.refl (Fin 2)) reflectSigns

/-- The image square of the transposition. -/
abbrev IntegerCube.swap (R : IntegerCube 2) : IntegerCube 2 :=
  R.signedPerm (Equiv.swap 0 1) (fun _ => 1)

theorem IntegerCube.reflect_corner_zero (R : IntegerCube 2) :
    R.reflect.corner 0 = -(R.corner 0 + R.size - 1) := by
  rw [IntegerCube.corner_signedPerm, if_neg (by simp)]
  rfl

theorem IntegerCube.reflect_corner_one (R : IntegerCube 2) : R.reflect.corner 1 = R.corner 1 := by
  rw [IntegerCube.corner_signedPerm, if_pos (by simp)]
  rfl

theorem IntegerCube.swap_corner_zero (R : IntegerCube 2) : R.swap.corner 0 = R.corner 1 := by
  rw [IntegerCube.corner_signedPerm, if_pos (by simp)]
  simp

theorem IntegerCube.swap_corner_one (R : IntegerCube 2) : R.swap.corner 1 = R.corner 0 := by
  rw [IntegerCube.corner_signedPerm, if_pos (by simp)]
  simp

theorem IntegerCube.eq_of_corner_eq {R R' : IntegerCube 2} (hc : ∀ i, R.corner i = R'.corner i)
    (hs : R.size = R'.size) : R = R' := by
  cases R
  cases R'
  simp only [IntegerCube.mk.injEq] at hc hs ⊢
  exact ⟨funext hc, hs⟩

theorem IntegerCube.reflect_reflect (R : IntegerCube 2) : R.reflect.reflect = R := by
  refine IntegerCube.eq_of_corner_eq (fun i => ?_) rfl
  fin_cases i
  · change R.reflect.reflect.corner 0 = R.corner 0
    rw [IntegerCube.reflect_corner_zero, IntegerCube.reflect_corner_zero,
      IntegerCube.size_signedPerm]
    ring
  · change R.reflect.reflect.corner 1 = R.corner 1
    rw [IntegerCube.reflect_corner_one, IntegerCube.reflect_corner_one]

theorem IntegerCube.swap_swap (R : IntegerCube 2) : R.swap.swap = R := by
  refine IntegerCube.eq_of_corner_eq (fun i => ?_) rfl
  fin_cases i
  · change R.swap.swap.corner 0 = R.corner 0
    rw [IntegerCube.swap_corner_zero, IntegerCube.swap_corner_one]
  · change R.swap.swap.corner 1 = R.corner 1
    rw [IntegerCube.swap_corner_one, IntegerCube.swap_corner_zero]

/-- **Strip meshes under the reflection.** -/
theorem planarMesh_reflect {ω : Configuration 2} {R : IntegerCube 2} {w : ℕ}
    (h : PlanarMesh ω R w) : PlanarMesh (configurationMap reflectIso ω) R.reflect w := by
  obtain ⟨hH, hV⟩ := h
  have c0 := R.reflect_corner_zero
  have c1 := R.reflect_corner_one
  have hn : R.reflect.size = R.size := rfl
  refine ⟨fun r hr1 hr2 => ?_, fun r hr1 hr2 => ?_⟩
  · rw [c1] at hr1
    rw [c1, hn] at hr2
    have hn1 : 1 ≤ R.size := by omega
    have hcast := IntegerCube.size_sub_one_cast hn1
    obtain ⟨a, b, hab, ha, hb⟩ := hH r hr1 hr2
    have hS : ∀ v, reflectIso v ∈ R.reflect.hStrip r w ↔ v ∈ R.hStrip r w := by
      intro v
      simp only [IntegerCube.hStrip, Set.mem_setOf_eq, c0, hn, hcast, reflectIso_apply_zero,
        reflectIso_apply_one]
      constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h3, h4⟩
    refine ⟨reflectIso b, reflectIso a,
      (reachIn_configurationMap_iff reflectIso ω hS b a).2 hab.symm, ?_, ?_⟩
    · rw [reflectIso_apply_zero, hb, c0, hcast]
      ring
    · rw [reflectIso_apply_zero, ha, c0, hn, hcast]
      ring
  · rw [c0] at hr1
    rw [c0, hn] at hr2
    obtain ⟨a, b, hab, ha, hb⟩ := hV (-r - w) (by linarith) (by linarith)
    have hS : ∀ v, reflectIso v ∈ R.reflect.vStrip r w ↔ v ∈ R.vStrip (-r - w) w := by
      intro v
      simp only [IntegerCube.vStrip, Set.mem_setOf_eq, c1, hn, reflectIso_apply_zero,
        reflectIso_apply_one]
      constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h3, h4⟩
    refine ⟨reflectIso a, reflectIso b,
      (reachIn_configurationMap_iff reflectIso ω hS a b).2 hab, ?_, ?_⟩
    · rw [reflectIso_apply_one, ha, c1]
    · rw [reflectIso_apply_one, hb, c1, hn]

/-- **Strip meshes under the transposition.** -/
theorem planarMesh_swap {ω : Configuration 2} {R : IntegerCube 2} {w : ℕ}
    (h : PlanarMesh ω R w) : PlanarMesh (configurationMap swapIso ω) R.swap w := by
  obtain ⟨hH, hV⟩ := h
  have c0 := R.swap_corner_zero
  have c1 := R.swap_corner_one
  have hn : R.swap.size = R.size := rfl
  refine ⟨fun r hr1 hr2 => ?_, fun r hr1 hr2 => ?_⟩
  · rw [c1] at hr1
    rw [c1, hn] at hr2
    obtain ⟨a, b, hab, ha, hb⟩ := hV r hr1 hr2
    have hS : ∀ v, swapIso v ∈ R.swap.hStrip r w ↔ v ∈ R.vStrip r w := by
      intro v
      simp only [IntegerCube.hStrip, IntegerCube.vStrip, Set.mem_setOf_eq, c0, hn,
        swapIso_apply_zero, swapIso_apply_one]
      constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> exact ⟨⟨h3, h4⟩, h1, h2⟩
    refine ⟨swapIso a, swapIso b, (reachIn_configurationMap_iff swapIso ω hS a b).2 hab, ?_, ?_⟩
    · rw [swapIso_apply_zero, ha, c0]
    · rw [swapIso_apply_zero, hb, c0, hn]
  · rw [c0] at hr1
    rw [c0, hn] at hr2
    obtain ⟨a, b, hab, ha, hb⟩ := hH r hr1 hr2
    have hS : ∀ v, swapIso v ∈ R.swap.vStrip r w ↔ v ∈ R.hStrip r w := by
      intro v
      simp only [IntegerCube.hStrip, IntegerCube.vStrip, Set.mem_setOf_eq, c1, hn,
        swapIso_apply_zero, swapIso_apply_one]
      constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> exact ⟨⟨h3, h4⟩, h1, h2⟩
    refine ⟨swapIso a, swapIso b, (reachIn_configurationMap_iff swapIso ω hS a b).2 hab, ?_, ?_⟩
    · rw [swapIso_apply_one, ha, c1]
    · rw [swapIso_apply_one, hb, c1, hn]

theorem planarMesh_reflect_iff (ω : Configuration 2) (R : IntegerCube 2) (w : ℕ) :
    PlanarMesh (configurationMap reflectIso ω) R.reflect w ↔ PlanarMesh ω R w := by
  refine ⟨fun h => ?_, planarMesh_reflect⟩
  have h' := planarMesh_reflect h
  rwa [configurationMap_configurationMap reflectIso reflectIso_reflectIso,
    IntegerCube.reflect_reflect] at h'

theorem planarMesh_swap_iff (ω : Configuration 2) (R : IntegerCube 2) (w : ℕ) :
    PlanarMesh (configurationMap swapIso ω) R.swap w ↔ PlanarMesh ω R w := by
  refine ⟨fun h => ?_, planarMesh_swap⟩
  have h' := planarMesh_swap h
  rwa [configurationMap_configurationMap swapIso swapIso_swapIso, IntegerCube.swap_swap] at h'

end Rigidity.Percolation
