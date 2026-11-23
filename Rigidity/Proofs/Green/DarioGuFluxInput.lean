import Rigidity.Proofs.Green.DarioGuHeatKernelInputs

/-!
# Proposition 2.13 of Dario–Gu: the weak norm of the centered flux, in dimension two

Proposition 2.13 of Dario–Gu (lines 1126-1144 of the source, proved as Proposition B.1 in
Appendix B, lines 2968-3188) bounds the `H̲^{-1}`-norm of the centered flux
`g̃_p = a(Dχ_p + p) - (σ̄²/2) p` on `𝒞_∞ ∩ B_r(y)` by `C |p| r^α` for `r ≥ M_flux,α(y)`. The
diffusivity `σ̄² = 2 θ(p)^{-1} ā` is defined by (B.5) so that this estimate holds. The proof in
Appendix B rests on the decay of the spatial averages of the flux on `ℤ^d` (Gu, *An efficient
algorithm for solving elliptic problems on percolation clusters*, Section 3.1 and Proposition 1.1,
cited as (B.8)), the multiscale Poincaré inequality (D.28) of Armstrong–Kuusi–Mourrat and the
homogenized coefficient of Armstrong–Dario (Definition 5.1); this file states it as a named
hypothesis, with unit conductances on the open edges (`a ∈ {0, 1}`).

* `openInterior ω V` is `int_a(V)` and `C_0^a(V)` is the set of functions vanishing on
  `V \ int_a(V)` (§1.6.3, (1.28));
* `openGradNorm ω V v x` is `|∇v|(x) = Σ_{z ∼ x} |v(z) - v(x)|` over the open edges of `V`;
* `clusterH1Norm ω V v` is `‖v‖_{H̲¹(V)} = |V|^{-1/2} ‖v‖_{L̲²(V)} + ‖∇v‖_{L̲²(V)}` ((1.32), `d = 2`);
* `WeakNormLe ω V g B` is `‖g‖_{H̲^{-1}(V)} ≤ B` ((1.33), `p = 2`): for every `v ∈ C_0^a(V)`,
  `|V|^{-1} Σ_V g v ≤ B ‖v‖_{H̲¹(V)}`, which is the bound on the supremum of (1.33);
* `centeredFlux ω σ χ k i` is the `i`-th component of `g̃_{e_k}` (§2.2.2), and
  `translatedFlux ω σ χ k i` the `i`-th component of the translated flux `g̃*_{e_k}` of (4.26),
  `[g̃*_{e_k}]_i = T_{-e_i} [a(Dχ_{e_k} + e_k) - (σ̄²/2) e_k]_i`.
-/

open scoped Classical
open LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

/-- `int_a(V)`: the points of `V` whose open neighbours all lie in `V` (Dario–Gu, §1.6.3). -/
def openInterior (ω : Configuration 2) (V : Finset (Vertex 2)) : Set (Vertex 2) :=
  {x | x ∈ V ∧ ∀ z, (openGraph ω).Adj x z → z ∈ V}

/-- `|∇v|(x) = Σ_{z ∼ x} |v(z) - v(x)|` over the open edges `{x, z}` with `z ∈ V` ((1.29)). -/
noncomputable def openGradNorm (ω : Configuration 2) (V : Finset (Vertex 2)) (v : Vertex 2 → ℝ)
    (x : Vertex 2) : ℝ :=
  ∑ z ∈ LatticeProb.nbrFinset x, if (openGraph ω).Adj x z ∧ z ∈ V then |v z - v x| else 0

/-- **Dario–Gu, (1.32)** with `p = 2`, `d = 2`:
`‖v‖_{H̲¹(V)} = |V|^{-1/2} ‖v‖_{L̲²(V)} + ‖∇v‖_{L̲²(V)}`. -/
noncomputable def clusterH1Norm (ω : Configuration 2) (V : Finset (Vertex 2))
    (v : Vertex 2 → ℝ) : ℝ :=
  (V.card : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt ((V.card : ℝ)⁻¹ * ∑ x ∈ V, v x ^ 2) +
    Real.sqrt ((V.card : ℝ)⁻¹ * ∑ x ∈ V, openGradNorm ω V v x ^ 2)

/-- **Dario–Gu, (1.33)** with `p = 2`: `‖g‖_{H̲^{-1}(V)} ≤ B`, that is
`|V|^{-1} Σ_{x ∈ V} g(x) v(x) ≤ B ‖v‖_{H̲¹(V)}` for every `v` vanishing on `∂_a V`. -/
def WeakNormLe (ω : Configuration 2) (V : Finset (Vertex 2)) (g : Vertex 2 → ℝ) (B : ℝ) : Prop :=
  ∀ v : Vertex 2 → ℝ, (∀ x ∈ V, x ∉ openInterior ω V → v x = 0) →
    (V.card : ℝ)⁻¹ * ∑ x ∈ V, g x * v x ≤ B * clusterH1Norm ω V v

/-- `𝒞 ∩ B_r(y)` for a component `𝒞`, as a finite set of lattice points. -/
noncomputable def clusterBall {ω : Configuration 2} (K : OpenComponent ω) (y : Vertex 2)
    (r : ℝ) : Finset (Vertex 2) :=
  (componentEuclideanBall K y r).image Subtype.val

/-- The `i`-th component of the centered flux `g̃_{e_k} = a(Dχ_{e_k} + e_k) - (σ/2) e_k` at `x`
(Dario–Gu, §2.2.2, `σ = σ̄²`), with `a = 1` on the open edges and `a = 0` on the closed ones. -/
noncomputable def centeredFlux (ω : Configuration 2) (σ : ℝ) (χ : Fin 2 → Vertex 2 → ℝ)
    (k i : Fin 2) (x : Vertex 2) : ℝ :=
  (if (openGraph ω).Adj x (x + Pi.single i 1) then
      (if i = k then 1 else 0) + (χ k (x + Pi.single i 1) - χ k x) else 0) -
    σ / 2 * (if i = k then 1 else 0)

/-- The `i`-th component of the translated flux `g̃*_{e_k}` of (4.26):
`T_{-e_i} [a(Dχ_{e_k} + e_k)]_i - (σ/2) δ_{ik}`, the flux on the edge `{x - e_i, x}`. -/
noncomputable def translatedFlux (ω : Configuration 2) (σ : ℝ) (χ : Fin 2 → Vertex 2 → ℝ)
    (k i : Fin 2) (x : Vertex 2) : ℝ :=
  (if (openGraph ω).Adj (x - Pi.single i 1) x then
      (if i = k then 1 else 0) + (χ k x - χ k (x - Pi.single i 1)) else 0) -
    σ / 2 * (if i = k then 1 else 0)

/-- **Dario–Gu, Proposition 2.13** (Proposition B.1, lines 2974-2986), in dimension two, on the
event `{y ∈ 𝒞_∞}`: for every `α > 0` there are `C`, `s > 0` and `M_flux,α(y) ≤ O_s(C)` such
that for every radius `r ≥ M_flux,α(y)`, `‖[g̃_{e_k}]_i‖_{H̲^{-1}(𝒞_∞ ∩ B_r(y))} ≤ C r^α` for all
`k, i`. Printed statement: *for any exponent `α > 0`, there exist a positive constant `C`, an
exponent `s > 0` such that, for any `y ∈ ℤ^d`, there exists a non-negative random variable
`M_flux,α(y)` satisfying `M_flux,α(y) ≤ O_s(C)` such that for each radius `r ≥ M_flux,α(y)`,
`‖g̃_p‖_{H̲^{-1}(𝒞_∞ ∩ B_r(y))} ≤ C |p| r^α`.* The norm of a vector field is taken
componentwise (equivalent up to a factor `2`). The flux does not depend on the additive constant
of the corrector; `χ` is the corrector of `IsDGCorrector`. -/
def DarioGuFluxWeakNormTwo (p : unitInterval) (σ : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex 2,
    ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        y ∈ (uniqueInfiniteComponent h).supp → ∀ χ : Fin 2 → Vertex 2 → ℝ,
          IsDGCorrector (uniqueInfiniteComponent h) y χ → ∀ r : ℝ, M ω ≤ r → ∀ k i : Fin 2,
            WeakNormLe ω (clusterBall (uniqueInfiniteComponent h) y r)
              (centeredFlux ω σ χ k i) (C * r ^ α)

theorem mem_clusterBall {ω : Configuration 2} (K : OpenComponent ω) (y x : Vertex 2) (r : ℝ) :
    x ∈ clusterBall K y r ↔ x ∈ K.supp ∧ latticeDist x y < r := by
  rw [clusterBall, mem_image_componentEuclideanBall, latticeDist, dist_eq_norm]

/-- The weak norm is monotone in the bound. -/
theorem WeakNormLe.mono {ω : Configuration 2} {V : Finset (Vertex 2)} {g : Vertex 2 → ℝ}
    {B B' : ℝ} (h : WeakNormLe ω V g B) (hBB : B ≤ B') : WeakNormLe ω V g B' := by
  intro v hv
  have hn : 0 ≤ clusterH1Norm ω V v := by
    unfold clusterH1Norm
    positivity
  exact (h v hv).trans (mul_le_mul_of_nonneg_right hBB hn)

/-- The weak norm satisfies the triangle inequality. -/
theorem WeakNormLe.add {ω : Configuration 2} {V : Finset (Vertex 2)} {g g' : Vertex 2 → ℝ}
    {B B' : ℝ} (h : WeakNormLe ω V g B) (h' : WeakNormLe ω V g' B') :
    WeakNormLe ω V (g + g') (B + B') := by
  intro v hv
  have e : (V.card : ℝ)⁻¹ * ∑ x ∈ V, (g + g') x * v x =
      (V.card : ℝ)⁻¹ * ∑ x ∈ V, g x * v x + (V.card : ℝ)⁻¹ * ∑ x ∈ V, g' x * v x := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.add_apply]
    ring
  rw [e, add_mul]
  exact add_le_add (h v hv) (h' v hv)

end Rigidity.Green
