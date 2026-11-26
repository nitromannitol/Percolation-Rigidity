import Rigidity.Proofs.Green.DarioGuFluxHeat
import Rigidity.Proofs.Corrector.DarioStepTwoOpen
import Rigidity.Proofs.Corrector.DarioCoarseHeatField

/-!
# The flip difference of the heat average of the flux

The heat field `heatEdge ω r x i = Σ_z Φ_{r²}(x, z) 1_{(z, i)}`, over the open edges `(z, i)` whose
tail lies in an infinite component, is an element of `ℓ²` of the edges, and its pairing with a field
`g` is the heat average of `g` along these edges (`inner_heatEdge`). With the flip formulas of
`DarioGuFluxFlip`, the change of the heat average `X = Σ_z Φ_{r²}(x, z) planeFlux(z, i)` of the
flux when the bond `e` of `a` is flipped is, in Case 3 (Gu, Steps 3 and 4: the terms
`A_e + B_e`, with the symmetry (2.15) of the Green projection),

* `X(ω^{e,1}) - X(ω^{e,0}) = c ((P₁ h₁)(a) - 1{a.2 = i} Φ_{r²}(x, a.1))` with
  `c = ℓ₀(a.1) - ℓ₀(edgeHead a)`, `P₁` the Green projection of `ω^{e,1}` and `h₁` its heat field
  (`ae_heat_planeFlux_sub_open`);
* `X(ω^{e,1}) - X(ω^{e,0}) = c' (Σ_{b ∈ π} (P₀ h₀)(b) - 1{a.2 = i} Φ_{r²}(x, a.1))` for an open path
  `π` of `ω^{e,0}` joining the endpoints, with `c' = ℓ₁(a.1) - ℓ₁(edgeHead a)`
  (`ae_heat_planeFlux_sub_closed`);

and in Cases 1 and 2 it vanishes (`ae_heat_planeFlux_sub_eq_zero`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Green

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.Corrector
open scoped Classical InnerProductSpace ENNReal

section HeatEdge

variable (ω : Configuration 2) (r : ℝ) (x : Vertex 2) (i : Fin 2)

/-- The unit field of the edge `(z, i)` when it is open with its tail in an infinite component. -/
noncomputable def heatEdgeTerm (z : Vertex 2) : EdgeField :=
  if EdgeOpen ω (z, i) ∧ ω ∈ infiniteComponentEvent z then lp.single 2 (z, i) (1 : ℝ) else 0

theorem norm_heatEdgeTerm_le (z : Vertex 2) : ‖heatEdgeTerm ω i z‖ ≤ 1 := by
  unfold heatEdgeTerm
  split_ifs
  · rw [lp.norm_single (by norm_num)]
    simp
  · simp

/-- **The heat field** `Σ_z Φ_{r²}(x, z) 1_{(z, i)}` over the open edges of the infinite components. -/
noncomputable def heatEdge : EdgeField :=
  ∑' z, latticeHeat (r ^ 2) x z • heatEdgeTerm ω i z

theorem summable_heatEdge :
    Summable fun z => latticeHeat (r ^ 2) x z • heatEdgeTerm ω i z :=
  Summable.of_norm_bounded (summable_latticeHeat (sq_nonneg r) x) fun z => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (latticeHeat_nonneg (sq_nonneg r) x z)]
    exact mul_le_of_le_one_right (latticeHeat_nonneg (sq_nonneg r) x z) (norm_heatEdgeTerm_le ω i z)

/-- **The pairing with the heat field** is the heat average along the open edges of direction `i`
of the infinite components. -/
theorem inner_heatEdge (g : EdgeField) :
    ⟪g, heatEdge ω r x i⟫_ℝ = ∑' z, latticeHeat (r ^ 2) x z *
      (if EdgeOpen ω (z, i) ∧ ω ∈ infiniteComponentEvent z then g (z, i) else 0) := by
  unfold heatEdge
  have hmap := (innerSL ℝ g).map_tsum (summable_heatEdge ω r x i)
  simp only [innerSL_apply_apply] at hmap
  rw [hmap]
  refine tsum_congr fun z => ?_
  rw [real_inner_smul_right]
  congr 1
  unfold heatEdgeTerm
  split_ifs <;> simp [lp.inner_single_right]

end HeatEdge

theorem summable_heat_ite_greenProj (ω : Configuration 2) (r : ℝ) (x : Vertex 2) (i : Fin 2)
    (ξ : EdgeField) (B : ℝ) (hB : ∀ b, |greenProj ω ξ b| ≤ B) :
    Summable fun z => latticeHeat (r ^ 2) x z *
      (if EdgeOpen ω (z, i) ∧ ω ∈ infiniteComponentEvent z then greenProj ω ξ (z, i) else 0) := by
  refine Summable.of_norm_bounded ((summable_latticeHeat (sq_nonneg r) x).mul_right B) fun z => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (latticeHeat_nonneg (sq_nonneg r) x z)]
  refine mul_le_mul_of_nonneg_left ?_ (latticeHeat_nonneg (sq_nonneg r) x z)
  split_ifs
  · exact hB _
  · rw [abs_zero]; exact (abs_nonneg _).trans (hB (z, i))

/-- The heat average of the indicator of one edge. -/
theorem tsum_heat_ite_eq (r : ℝ) (x : Vertex 2) (i : Fin 2) (a : LatticeEdge) :
    ∑' z, latticeHeat (r ^ 2) x z * (if ((z, i) : LatticeEdge) = a then 1 else 0) =
      if a.2 = i then latticeHeat (r ^ 2) x a.1 else 0 := by
  rw [tsum_eq_single a.1]
  · by_cases h : a.2 = i
    · have : ((a.1, i) : LatticeEdge) = a := Prod.ext rfl h.symm
      rw [if_pos this, if_pos h, mul_one]
    · have : ((a.1, i) : LatticeEdge) ≠ a := fun e => h (congrArg Prod.snd e).symm
      rw [if_neg this, if_neg h, mul_zero]
  · intro z hz
    have : ((z, i) : LatticeEdge) ≠ a := fun e => hz (congrArg Prod.fst e)
    rw [if_neg this, mul_zero]

theorem summable_heat_ite_eq (r : ℝ) (x : Vertex 2) (i : Fin 2) (a : LatticeEdge) :
    Summable fun z => latticeHeat (r ^ 2) x z * (if ((z, i) : LatticeEdge) = a then 1 else 0) := by
  refine summable_of_ne_finset_zero (s := {a.1}) fun z hz => ?_
  have : ((z, i) : LatticeEdge) ≠ a := fun e => hz (by rw [← e]; exact Finset.mem_singleton_self _)
  rw [if_neg this, mul_zero]

/-- **Case 3, through the configuration with the bond open**: the flip difference of the heat
average of the flux is `c ((P₁ h₁)(a) - 1{a.2 = i} Φ_{r²}(x, a.1))`. -/
theorem ae_heat_planeFlux_sub_open {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ a : LatticeEdge,
      ∀ (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
        (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω))
        (hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp)
        (hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp)
        (q : Fin 2 → ℝ) (ℓ₁ : uniqueInfiniteComponent h₁ → ℝ)
        (ℓ₀ : uniqueInfiniteComponent h₀ → ℝ),
        IsCorrectedPlane (uniqueInfiniteComponent h₁) q ℓ₁ →
        IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ →
        ∀ (r : ℝ), 0 < r → ∀ (x : Vertex 2) (i : Fin 2),
          (∑' z, latticeHeat (r ^ 2) x z * planeFlux _ ℓ₁ (z, i)) -
              ∑' z, latticeHeat (r ^ 2) x z * planeFlux _ ℓ₀ (z, i) =
            (ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩) *
              (greenProj (setBond (edgeBond a) true ω) (heatEdge (setBond (edgeBond a) true ω) r x i) a -
                if a.2 = i then latticeHeat (r ^ 2) x a.1 else 0) := by
  filter_upwards [ae_planeFlux_setBond_sub_open hpc hp1] with ω hω
  intro a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ r hr x i
  set c := ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩
  set P := greenProj (setBond (edgeBond a) true ω) (lp.single 2 a 1)
  have hpt : ∀ z, latticeHeat (r ^ 2) x z * planeFlux _ ℓ₁ (z, i) -
      latticeHeat (r ^ 2) x z * planeFlux _ ℓ₀ (z, i) =
      c * (latticeHeat (r ^ 2) x z *
        (if EdgeOpen (setBond (edgeBond a) true ω) (z, i) ∧ (setBond (edgeBond a) true ω) ∈ infiniteComponentEvent z then P (z, i) else 0)) -
      c * (latticeHeat (r ^ 2) x z * (if ((z, i) : LatticeEdge) = a then 1 else 0)) := by
    intro z
    rw [← mul_sub, hω a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ (z, i)]
    have e1 : (EdgeOpen (setBond (edgeBond a) true ω) (z, i) ∧ ((z, i) : LatticeEdge).1 ∈ (uniqueInfiniteComponent h₁).supp) ↔
        (EdgeOpen (setBond (edgeBond a) true ω) (z, i) ∧ (setBond (edgeBond a) true ω) ∈ infiniteComponentEvent z) :=
      and_congr_right fun _ => mem_uniqueInfiniteComponent_iff h₁ z
    by_cases hc1 : EdgeOpen (setBond (edgeBond a) true ω) (z, i) ∧ (setBond (edgeBond a) true ω) ∈ infiniteComponentEvent z
    · rw [if_pos (e1.2 hc1), if_pos hc1]
      split_ifs <;> ring
    · rw [if_neg (fun h => hc1 (e1.1 h)), if_neg hc1]
      split_ifs <;> ring
  rw [← (summable_heat_planeFlux hℓ₁ i hr x).tsum_sub (summable_heat_planeFlux hℓ₀ i hr x)]
  rw [tsum_congr hpt]
  have hS1 := (summable_heat_ite_greenProj (setBond (edgeBond a) true ω) r x i (lp.single 2 a 1) 1
    (fun b => abs_greenProj_single_le (setBond (edgeBond a) true ω) a b)).mul_left c
  have hS2 := (summable_heat_ite_eq r x i a).mul_left c
  rw [hS1.tsum_sub hS2, tsum_mul_left, tsum_mul_left, ← inner_heatEdge, tsum_heat_ite_eq,
    inner_greenProj_comm, lp.inner_single_left]
  rw [Real.inner_apply, one_mul]
  split_ifs <;> ring

/-- **Case 3, through the configuration with the bond closed**: for an open path `pw` of
`ω^{e,0}` joining the endpoints, the flip difference of the heat average of the flux is
`c' (Σ_{b ∈ pw} (P₀ h₀)(b) - 1{a.2 = i} Φ_{r²}(x, a.1))`. -/
theorem ae_heat_planeFlux_sub_closed {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ a : LatticeEdge,
      ∀ (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
        (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω))
        (hx : a.1 ∈ (uniqueInfiniteComponent h₀).supp)
        (hy : edgeHead a ∈ (uniqueInfiniteComponent h₀).supp)
        (q : Fin 2 → ℝ) (ℓ₁ : uniqueInfiniteComponent h₁ → ℝ)
        (ℓ₀ : uniqueInfiniteComponent h₀ → ℝ),
        IsCorrectedPlane (uniqueInfiniteComponent h₁) q ℓ₁ →
        IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ →
        ∀ (pw : (openGraph (setBond (edgeBond a) false ω)).Walk a.1 (edgeHead a))
          (r : ℝ), 0 < r → ∀ (x : Vertex 2) (i : Fin 2),
          (∑' z, latticeHeat (r ^ 2) x z * planeFlux _ ℓ₁ (z, i)) -
              ∑' z, latticeHeat (r ^ 2) x z * planeFlux _ ℓ₀ (z, i) =
            (extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a)) *
              (walkSum (setBond (edgeBond a) false ω) (greenProj (setBond (edgeBond a) false ω)
                  (heatEdge (setBond (edgeBond a) false ω) r x i)) pw -
                if a.2 = i then latticeHeat (r ^ 2) x a.1 else 0) := by
  filter_upwards [ae_planeFlux_setBond_sub_closed hpc hp1] with ω hω
  intro a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ pw r hr x i
  set c := extendComp _ ℓ₁ a.1 - extendComp _ ℓ₁ (edgeHead a)
  set P := greenProj (setBond (edgeBond a) false ω) (pathField (setBond (edgeBond a) false ω) pw)
  have hpt : ∀ z, latticeHeat (r ^ 2) x z * planeFlux _ ℓ₁ (z, i) -
      latticeHeat (r ^ 2) x z * planeFlux _ ℓ₀ (z, i) =
      c * (latticeHeat (r ^ 2) x z *
        (if EdgeOpen (setBond (edgeBond a) false ω) (z, i) ∧ (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent z then P (z, i) else 0)) -
      c * (latticeHeat (r ^ 2) x z * (if ((z, i) : LatticeEdge) = a then 1 else 0)) := by
    intro z
    rw [← mul_sub, hω a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ pw (z, i)]
    have e1 : (EdgeOpen (setBond (edgeBond a) false ω) (z, i) ∧ ((z, i) : LatticeEdge).1 ∈ (uniqueInfiniteComponent h₀).supp) ↔
        (EdgeOpen (setBond (edgeBond a) false ω) (z, i) ∧ (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent z) :=
      and_congr_right fun _ => mem_uniqueInfiniteComponent_iff h₀ z
    by_cases hc1 : EdgeOpen (setBond (edgeBond a) false ω) (z, i) ∧ (setBond (edgeBond a) false ω) ∈ infiniteComponentEvent z
    · rw [if_pos (e1.2 hc1), if_pos hc1]
      split_ifs <;> ring
    · rw [if_neg (fun h => hc1 (e1.1 h)), if_neg hc1]
      split_ifs <;> ring
  rw [← (summable_heat_planeFlux hℓ₁ i hr x).tsum_sub (summable_heat_planeFlux hℓ₀ i hr x)]
  rw [tsum_congr hpt]
  have hB : ∀ b, |P b| ≤ ‖pathField (setBond (edgeBond a) false ω) pw‖ := fun b =>
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) P b).trans (norm_greenProj_le (setBond (edgeBond a) false ω) _)
  have hS1 := (summable_heat_ite_greenProj (setBond (edgeBond a) false ω) r x i (pathField (setBond (edgeBond a) false ω) pw) _ hB).mul_left c
  have hS2 := (summable_heat_ite_eq r x i a).mul_left c
  rw [hS1.tsum_sub hS2, tsum_mul_left, tsum_mul_left, ← inner_heatEdge, tsum_heat_ite_eq,
    inner_greenProj_comm, real_inner_comm, inner_pathField]
  split_ifs <;> ring

/-- **Cases 1 and 2**: the flip difference of the heat average of the flux vanishes. -/
theorem ae_heat_planeFlux_sub_eq_zero {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ a : LatticeEdge,
      ∀ (h₁ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) true ω))
        (h₀ : HasUniqueInfiniteOpenComponent (setBond (edgeBond a) false ω)),
        ¬ (a.1 ∈ (uniqueInfiniteComponent h₀).supp ∧
          edgeHead a ∈ (uniqueInfiniteComponent h₀).supp) →
        ∀ (q : Fin 2 → ℝ) (ℓ₁ : uniqueInfiniteComponent h₁ → ℝ)
          (ℓ₀ : uniqueInfiniteComponent h₀ → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h₁) q ℓ₁ →
          IsCorrectedPlane (uniqueInfiniteComponent h₀) q ℓ₀ →
          ∀ (r : ℝ) (x : Vertex 2) (i : Fin 2),
            (∑' z, latticeHeat (r ^ 2) x z * planeFlux _ ℓ₁ (z, i)) -
              ∑' z, latticeHeat (r ^ 2) x z * planeFlux _ ℓ₀ (z, i) = 0 := by
  filter_upwards [ae_planeFlux_setBond_eq hpc hp1] with ω hω
  intro a h₁ h₀ hnot q ℓ₁ ℓ₀ hℓ₁ hℓ₀ r x i
  rw [sub_eq_zero]
  exact tsum_congr fun z => by rw [hω a h₁ h₀ hnot q ℓ₁ ℓ₀ hℓ₁ hℓ₀ (z, i)]

end Rigidity.Green
