import Rigidity.External.JordanCurve
import Rigidity.Proofs.Topology.PlanarJordan.Crossing
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Punctures of the sphere

The two-sphere with two points removed is connected, by stereographic projection onto a
punctured plane.
-/

open Set Metric

namespace Rigidity.Topology

open Rigidity.External MatedCRTHarmonic.Planar.Jordan

/-- Removing two distinct points from the two-sphere leaves a connected set. -/
theorem isConnected_sphere_compl_pair (x y : S2) (hxy : x ≠ y) :
    IsConnected ({x, y} : Set S2)ᶜ := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  let chart := stereographic' 2 x
  have hsource (z : S2) : z ∈ chart.source ↔ z ≠ x := by
    simp [chart]
  have hy : y ∈ chart.source := (hsource y).mpr hxy.symm
  have htarget (u : Plane) : u ∈ chart.target := by simp [chart]
  have hcont : Continuous chart.symm := by
    apply continuousOn_univ.mp
    simpa only [chart, stereographic'_target] using chart.continuousOn_symm
  have hplane : IsConnected ({chart y} : Set Plane)ᶜ :=
    isConnected_compl_singleton_of_one_lt_rank one_lt_rank_plane (chart y)
  have himg := hplane.image chart.symm hcont.continuousOn
  have himg_eq : chart.symm '' ({chart y} : Set Plane)ᶜ = ({x, y} : Set S2)ᶜ := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hxu : chart.symm u ≠ x := (hsource _).mp (chart.map_target (htarget u))
      have hyu : chart.symm u ≠ y := by
        intro heq
        have := congrArg chart heq
        rw [chart.right_inv (htarget u)] at this
        exact hu this
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hxu, hyu⟩
    · intro hz
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
      have hxz : z ≠ x := hz.1
      have hyz : z ≠ y := hz.2
      refine ⟨chart z, ?_, chart.left_inv ((hsource z).mpr hxz)⟩
      simp only [mem_compl_iff, mem_singleton_iff]
      intro heq
      exact hyz (chart.injOn ((hsource z).mpr hxz) hy heq)
  rw [himg_eq] at himg
  exact himg

/-- A continuous injective circle in the two-sphere omits a point. -/
theorem exists_not_mem_range_circle (f : Circle → S2) (hf : Continuous f)
    (hinj : Function.Injective f) : ∃ x : S2, x ∉ range f := by
  classical
  by_contra h
  have hsurj : Function.Surjective f := by
    intro y
    by_contra hy
    exact h ⟨y, hy⟩
  let e : Circle ≃ S2 := Equiv.ofBijective f ⟨hinj, hsurj⟩
  let h' : Circle ≃ₜ S2 := hf.homeoOfEquivCompactToT2 (f := e)
  have hne : (1 : Circle) ≠ -1 := by
    exact (Circle.neg_ne_self (1 : Circle)).symm
  have hcon := isConnected_sphere_compl_pair (f 1) (f (-1)) (hinj.ne hne)
  have himg := hcon.isPreconnected.image h'.symm h'.symm.continuous.continuousOn
  have hset : h'.symm '' ({f 1, f (-1)} : Set S2)ᶜ = ({(1 : Circle), -1} : Set Circle)ᶜ := by
    rw [image_compl_eq h'.symm.bijective, image_insert_eq, image_singleton]
    have h1 : h'.symm (f 1) = 1 := h'.left_inv 1
    have h2 : h'.symm (f (-1)) = -1 := h'.left_inv (-1)
    rw [h1, h2]
  rw [hset] at himg
  exact Circle.not_isPreconnected_compl_pair hne himg

end Rigidity.Topology
