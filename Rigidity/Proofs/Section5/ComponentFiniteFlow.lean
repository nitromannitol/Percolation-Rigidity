import Rigidity.Proofs.Section5.FiniteFlowExtension
import Rigidity.Proofs.Section5.FlowGraphIso

/-!
# Finite lattice flows inside an open component

An open subgraph contained in a component has the same flows and energy whether its vertices
are viewed in the lattice or in the component.
-/

open LatticeProb.Percolation LatticeProb.Network
open scoped Classical

namespace Rigidity.Proofs.Section5

/-- A finite induced open graph is unchanged when its vertices are viewed in a component. -/
noncomputable def componentFiniteGraphIso {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (V : Finset (Vertex d)) (hV : ∀ x ∈ V, x ∈ C.supp) :
    (componentGraph C).induce (V.subtype (· ∈ C.supp) : Set C) ≃g
      (openGraph ω).induce (V : Set (Vertex d)) where
  toFun x := ⟨x.val.val, Finset.mem_subtype.mp x.property⟩
  invFun x := ⟨⟨x.val, hV x.val x.property⟩, Finset.mem_subtype.mpr x.property⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_rel_iff' := by intro x y; rfl

/-- A finite lattice flow in an infinite component bounds its truncated potential. -/
theorem truncatedComponentPotential_le_lattice_flow_energy {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (hC : C.supp.Infinite) (y x : C)
    (V : Finset (Vertex d)) (hV : ∀ z ∈ V, z ∈ C.supp)
    (hy : y.val ∈ V) (hx : x.val ∈ V) (θ : V → V → ℝ) (K : ℝ)
    (hθ : IsFlow ((openGraph ω).induce (V : Set (Vertex d))) θ)
    (hdiv : ∀ z : V, divergence ((openGraph ω).induce (V : Set (Vertex d))) θ z =
      (if z = ⟨y.val, hy⟩ then 1 else 0) - (if z = ⟨x.val, hx⟩ then 1 else 0))
    (henergy : flowEnergyOn ((openGraph ω).induce (V : Set (Vertex d)))
      (unitCond ((openGraph ω).induce (V : Set (Vertex d)))) Finset.univ θ ≤ 2 * K)
    (n : ℕ) : truncatedComponentPotential C n y x ≤ K := by
  let T := V.subtype (· ∈ C.supp)
  have hyT : y ∈ T := Finset.mem_subtype.mpr hy
  have hxT : x ∈ T := Finset.mem_subtype.mpr hx
  let e : (componentGraph C).induce (T : Set C) ≃g
      (openGraph ω).induce (V : Set (Vertex d)) := componentFiniteGraphIso C V hV
  let θ' : T → T → ℝ := fun a b => θ (e a) (e b)
  apply truncatedComponentPotential_le_induced_flow_energy C hC y x T hyT hxT θ' K
    (isFlow_comp_graphIso _ _ e θ hθ)
  · intro z
    have hd : divergence ((componentGraph C).induce (T : Set C)) θ' z =
        divergence ((openGraph ω).induce (V : Set (Vertex d))) θ (e z) := by
      convert divergence_comp_graphIso _ _ e θ z using 1
      rfl
    rw [hd, hdiv]
    have hyEq : (e z = ⟨y.val, hy⟩) ↔ z = ⟨y, hyT⟩ := by
      constructor
      · intro h
        apply Subtype.ext
        apply Subtype.ext
        change z.val.val = y.val
        exact congrArg (fun t : V => t.val) h
      · rintro rfl
        rfl
    have hxEq : (e z = ⟨x.val, hx⟩) ↔ z = ⟨x, hxT⟩ := by
      constructor
      · intro h
        apply Subtype.ext
        apply Subtype.ext
        change z.val.val = x.val
        exact congrArg (fun t : V => t.val) h
      · rintro rfl
        rfl
    simp only [hyEq, hxEq]
  · have he : flowEnergyOn ((componentGraph C).induce (T : Set C))
        (unitCond ((componentGraph C).induce (T : Set C))) Finset.univ θ' =
        flowEnergyOn ((openGraph ω).induce (V : Set (Vertex d)))
          (unitCond ((openGraph ω).induce (V : Set (Vertex d))))
          (Finset.univ.map e.toEquiv.toEmbedding) θ := by
      convert flowEnergyOn_comp_graphIso _ _ e θ Finset.univ using 1
      rfl
    rw [he]
    have hmap : Finset.univ.map e.toEquiv.toEmbedding = (Finset.univ : Finset V) := by
      ext z
      simp
    rw [hmap]
    exact henergy

end Rigidity.Proofs.Section5
