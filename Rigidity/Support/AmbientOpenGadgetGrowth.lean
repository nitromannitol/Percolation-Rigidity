import Rigidity.Support.CorrectedOpenGadgetGrowthResult
import LatticeProb.Network.OpenLadderEmbedding

/-!
# Growth on the ambient corrected open gadget

Real functions on the integer lattice, integer valued on the literal finite open carrier,
satisfy the intrinsic growth bound when harmonic at every actual nonterminal. The finite
neighbor sums are transported through the accepted ambient graph isomorphism.
-/

namespace Rigidity.OpenGadget.Ambient

open LatticeProb.Network LatticeProb.Network.OpenLadder
open LatticeProb.Network.OpenLadder.Embedding

noncomputable section

variable {d : ℕ} {n : ℤ}

/-- The literal ambient open carrier is finite, with its certified finite enumeration. -/
instance ambientSitesFintype (hd : 2 ≤ d) (n : ℤ) : Fintype (ambientSites hd n) :=
  (ambientSites_finite hd n).fintype

/-- The actual left leaf in the ambient lattice is `(1,1,0,...,0)`. -/
def ambientSource (d : ℕ) : (Fin d → ℤ) := zeroPad d (1, 1)

/-- The actual right leaf in the ambient lattice is `(4,1,0,...,0)`. -/
def ambientTarget (d : ℕ) : (Fin d → ℤ) := zeroPad d (4, 1)

/-- Sum of the differences over exactly the induced nearest neighbors in the open carrier. -/
def ambientLaplacian (hd : 2 ≤ d) (n : ℤ) (u : (Fin d → ℤ) → ℝ)
    (x : ambientSites hd n) : ℝ := by
  classical
  exact ∑ y : ambientSites hd n,
    if (ambientGraph hd n).Adj x y then u y.val - u x.val else 0

/-- Harmonicity is required at every actual open vertex except the two terminal leaves. -/
def AmbientHarmonic (hd : 2 ≤ d) (n : ℤ) (u : (Fin d → ℤ) → ℝ) : Prop :=
  ∀ x : ambientSites hd n, x.val ≠ ambientSource d → x.val ≠ ambientTarget d →
    ambientLaplacian hd n u x = 0

/-- The literal ambient sum equals the intrinsic unit-conductance Laplacian. -/
theorem ambientLaplacian_eq (hd : 2 ≤ d) (u : (Fin d → ℤ) → ℝ)
    (x : Vertex n) :
    ambientLaplacian hd n u (ambientIso hd n x) =
      netLaplacian (graph n) (unitCond (graph n)) (fun v => u (ambientMap hd v)) x := by
  classical
  rw [ambientLaplacian, ← (ambientIso hd n).toEquiv.sum_comp]
  rw [netLaplacian_unitCond, LatticeProb.Graph.laplacian,
    SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  change (if (ambientGraph hd n).Adj (ambientIso hd n x) (ambientIso hd n y)
    then u (ambientMap hd y) - u (ambientMap hd x) else 0) = _
  rw [(ambientIso hd n).map_rel_iff]
  split_ifs <;> rfl

/-- Harmonicity transports in both directions, including all actual nonterminals. -/
theorem ambientHarmonic_iff (hd : 2 ≤ d) (u : (Fin d → ℤ) → ℝ) :
    AmbientHarmonic hd n u ↔ Harmonic (n := n) (fun v => u (ambientMap hd v)) := by
  constructor
  · intro hu x hx
    rw [← ambientLaplacian_eq hd u x]
    apply hu
    · intro h
      exact hx.1 (ambientMap_injective hd h)
    · intro h
      exact hx.2 (ambientMap_injective hd h)
  · intro hu x hs ht
    obtain ⟨v, rfl⟩ := (ambientIso hd n).surjective x
    rw [ambientLaplacian_eq]
    apply hu v
    constructor
    · intro h
      exact hs (congrArg (ambientMap hd) h)
    · intro h
      exact ht (congrArg (ambientMap hd) h)

/-- One positive constant works in every dimension and at every positive height for real
ambient functions with pointwise integer values on the literal open carrier. -/
theorem ambient_open_gadget_exponential_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 2 ≤ d) (n : ℕ), 1 ≤ n →
      ∀ (u : (Fin d → ℤ) → ℝ),
        (∀ x ∈ ambientSites hd (n : ℤ), ∃ z : ℤ, u x = (z : ℝ)) →
        AmbientHarmonic hd (n : ℤ) u →
        (∃ x ∈ ambientSites hd (n : ℤ), ∃ y ∈ ambientSites hd (n : ℤ), u x ≠ u y) →
        C * (3 : ℝ) ^ n ≤ |u (ambientTarget d) - u (ambientSource d)| := by
  obtain ⟨C, hC, hgrowth⟩ := corrected_open_gadget_exponential_growth
  refine ⟨C, hC, ?_⟩
  intro d hd n hn u hint hu hnonconstant
  have hex : ∀ x : Vertex (n : ℤ), ∃! z : ℤ, u (ambientMap hd x) = (z : ℝ) := by
    intro x
    obtain ⟨z, hz⟩ := hint (ambientMap hd x) (zeroPad_mem hd x)
    refine ⟨z, hz, ?_⟩
    intro w hw
    exact Int.cast_injective (hw.symm.trans hz)
  let v : Vertex (n : ℤ) → ℤ := fun x => (hex x).choose
  have hv : ∀ x, u (ambientMap hd x) = (v x : ℝ) :=
    fun x => (hex x).choose_spec.1
  have hvh : Harmonic (fun x => (v x : ℝ)) := by
    have h := (ambientHarmonic_iff hd u).mp hu
    simpa only [hv] using h
  have hvn : ∃ x y, v x ≠ v y := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnonconstant
    rw [ambientSites_eq_range] at hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a, b, ?_⟩
    intro hab
    apply hxy
    rw [← ha, ← hb, hv, hv, hab]
  have h := hgrowth n hn v hvh hvn
  rw [← hv, ← hv] at h
  exact h

end

end Rigidity.OpenGadget.Ambient
