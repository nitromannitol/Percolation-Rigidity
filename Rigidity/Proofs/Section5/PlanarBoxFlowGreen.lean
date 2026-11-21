import Rigidity.Proofs.Section5.ComponentFiniteFlow
import Rigidity.Proofs.Section5.PlanarBoxRadius

/-!
# Green columns from finite-box flows

Logarithmic-energy flows on absorbing finite boxes give a planar Green column.
-/

open LatticeProb.Percolation LatticeProb.Network Rigidity.Section5
open scoped Classical

namespace Rigidity.Proofs.Section5

/-- Logarithmic finite-box flow bounds imply existence of a planar Green column. -/
theorem exists_greenColumn_of_box_flows {ω : Configuration 2} (C : OpenComponent ω)
    (hC : C.supp.Infinite) (y : C) (A : ℝ) (hA : 0 ≤ A) (N : ℕ)
    (hbox : ∀ n : ℕ, N ≤ n → 1 ≤ n → ∃ V : Finset (Vertex 2),
      (∀ z ∈ V, z ∈ C.supp) ∧
      (∀ z : C, (∀ i, 2 * |z.val i| ≤ (n : ℤ)) → z.val ∈ V) ∧
      ∀ a b : V, ∃ θ : V → V → ℝ,
        IsFlow ((openGraph ω).induce (V : Set (Vertex 2))) θ ∧
        (∀ z : V, divergence ((openGraph ω).induce (V : Set (Vertex 2))) θ z =
          (if z = a then 1 else 0) - (if z = b then 1 else 0)) ∧
        flowEnergyOn ((openGraph ω).induce (V : Set (Vertex 2)))
          (unitCond ((openGraph ω).induce (V : Set (Vertex 2)))) Finset.univ θ ≤
            2 * (A * Real.log n)) :
    ∃ g, IsGreenColumn 2 le_rfl C y g := by
  obtain ⟨B, hB, hchoose⟩ := exists_box_radius y.val N
  refine exists_greenColumn_of_truncatedPotential_log_bound C hC y (2 * A)
    (max (2 * B) 2) (by positivity) ?_
  intro m x hx
  have hxB : 2 * B ≤ eucl x.val := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ eucl x.val := (le_max_right _ _).trans hx
  obtain ⟨n, hnN, hn1, hxn, hyn, hnupper⟩ := hchoose x.val
  obtain ⟨V, hV, hinner, hflows⟩ := hbox n hnN hn1
  have hy : y.val ∈ V := hinner y hyn
  have hxV : x.val ∈ V := hinner x hxn
  obtain ⟨θ, hθ, hdiv, henergy⟩ := hflows ⟨y.val, hy⟩ ⟨x.val, hxV⟩
  have hpot := truncatedComponentPotential_le_lattice_flow_energy C hC y x V hV hy hxV θ
    (A * Real.log n) hθ hdiv henergy m
  have hscale : B * (eucl x.val + 1) ≤ (eucl x.val) ^ 2 := by nlinarith
  have hlog : Real.log (n : ℝ) ≤ 2 * Real.log (eucl x.val) := by
    calc
      _ ≤ Real.log ((eucl x.val) ^ 2) :=
        Real.log_le_log (by exact_mod_cast hn1) (hnupper.trans hscale)
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [abs_of_nonneg (truncatedComponentPotential_nonneg C m y x)]
  nlinarith [mul_le_mul_of_nonneg_left hlog hA]

end Rigidity.Proofs.Section5
