import Rigidity.Proofs.Green.DarioGuFluxInput

/-!
# Proposition 2.13 of Dario–Gu in every dimension: the statement

Proposition 2.13 of Dario–Gu (lines 1126-1144 of the source, estimates (2.13)-(2.14); proved as
Proposition B.1 in Appendix B) bounds the `H̲^{-1}`-norm of the centered flux
`g̃_p = a(Dχ_p + p) - (σ̄²/2) p` on `𝒞_∞ ∩ B_r(y)` by `C |p| r^α` for `r ≥ M_flux,α(y)`,
`M_flux,α(y) ≤ O_s(C)`. This file states it on `ℤ^d` (`DarioGuFluxWeakNormD d p σ`), with unit
conductances on the open edges (`a ∈ {0, 1}`), and proves that at `d = 2` it is the planar
statement `DarioGuFluxWeakNormTwo` (`darioGuFluxWeakNormD_two_iff`).

The objects are those of `Rigidity.Proofs.Green.DarioGuFluxInput` on `ℤ^d`; the only exponent
that depends on the dimension is the factor `|V|^{-1/d}` of the normalized Sobolev norm (1.32).

* `openInteriorD ω V` is `int_a(V)` (§1.6.3); `C_0^a(V)` is the set of functions vanishing on
  `V \ int_a(V)` ((1.25));
* `openGradNormD ω V v x` is `|∇v|(x) = Σ_{z ∼ x} |v(z) - v(x)|` over the open edges of `V`;
* `clusterH1NormD ω V v` is `‖v‖_{H̲¹(V)} = |V|^{-1/d} ‖v‖_{L̲²(V)} + ‖∇v‖_{L̲²(V)}` ((1.32));
* `WeakNormLeD ω V g B` is `‖g‖_{H̲^{-1}(V)} ≤ B` ((1.33), `p = 2`): for every `v ∈ C_0^a(V)`,
  `|V|^{-1} Σ_V g v ≤ B ‖v‖_{H̲¹(V)}`, which is the bound on the supremum of (1.33);
* `IsDGCorrectorD K y χ`: the correctors `χ_{e_k}` of the cluster `K`, normalized at `y`;
* `centeredFluxD ω σ χ k i` is the `i`-th component of `g̃_{e_k}` (§2.2.2), and
  `translatedFluxD ω σ χ k i` the `i`-th component of the translated flux `g̃*_{e_k}` of (4.26).
-/

open scoped Classical
open LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

variable {d : ℕ}

/-- `int_a(V)`: the points of `V` whose open neighbours all lie in `V` (Dario–Gu, §1.6.3), on
`ℤ^d`. -/
def openInteriorD (ω : Configuration d) (V : Finset (Vertex d)) : Set (Vertex d) :=
  {x | x ∈ V ∧ ∀ z, (openGraph ω).Adj x z → z ∈ V}

/-- `|∇v|(x) = Σ_{z ∼ x} |v(z) - v(x)|` over the open edges `{x, z}` with `z ∈ V` (the definition
after (1.28)), on `ℤ^d`. -/
noncomputable def openGradNormD (ω : Configuration d) (V : Finset (Vertex d))
    (v : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  ∑ z ∈ LatticeProb.nbrFinset x, if (openGraph ω).Adj x z ∧ z ∈ V then |v z - v x| else 0

/-- **Dario–Gu, (1.32)** with `p = 2`:
`‖v‖_{H̲¹(V)} = |V|^{-1/d} ‖v‖_{L̲²(V)} + ‖∇v‖_{L̲²(V)}`. -/
noncomputable def clusterH1NormD (ω : Configuration d) (V : Finset (Vertex d))
    (v : Vertex d → ℝ) : ℝ :=
  (V.card : ℝ) ^ (-(1 / d : ℝ)) * Real.sqrt ((V.card : ℝ)⁻¹ * ∑ x ∈ V, v x ^ 2) +
    Real.sqrt ((V.card : ℝ)⁻¹ * ∑ x ∈ V, openGradNormD ω V v x ^ 2)

/-- **Dario–Gu, (1.33)** with `p = 2`, on `ℤ^d`: `‖g‖_{H̲^{-1}(V)} ≤ B`, that is
`|V|^{-1} Σ_{x ∈ V} g(x) v(x) ≤ B ‖v‖_{H̲¹(V)}` for every `v` vanishing on `V \ int_a(V)`. -/
def WeakNormLeD (ω : Configuration d) (V : Finset (Vertex d)) (g : Vertex d → ℝ) (B : ℝ) :
    Prop :=
  ∀ v : Vertex d → ℝ, (∀ x ∈ V, x ∉ openInteriorD ω V → v x = 0) →
    (V.card : ℝ)⁻¹ * ∑ x ∈ V, g x * v x ≤ B * clusterH1NormD ω V v

/-- `𝒞 ∩ B_r(y)` for a component `𝒞` of `ℤ^d`, as a finite set of lattice points. -/
noncomputable def dgClusterBallD {ω : Configuration d} (K : OpenComponent ω) (y : Vertex d)
    (r : ℝ) : Finset (Vertex d) :=
  (componentEuclideanBall K y r).image Subtype.val

/-- The correctors `χ_{e_k}` of the cluster `K` of `ℤ^d` normalized around `y ∈ K` (Dario–Gu,
§2.3.1): `x ↦ x_k + χ_{e_k}(x)` is a corrected plane of slope `e_k` and `χ_{e_k}(y) = 0`. -/
def IsDGCorrectorD {ω : Configuration d} (K : OpenComponent ω) (y : Vertex d)
    (χ : Fin d → Vertex d → ℝ) : Prop :=
  ∀ k : Fin d, IsCorrectedPlane K (Pi.single k 1) (fun a => (a.val k : ℝ) + χ k a.val) ∧
    χ k y = 0

/-- The `i`-th component of the centered flux `g̃_{e_k} = a(Dχ_{e_k} + e_k) - (σ/2) e_k` at `x`
(Dario–Gu, §2.2.2, `σ = σ̄²`) on `ℤ^d`, with `a = 1` on the open edges and `a = 0` on the closed
ones. -/
noncomputable def centeredFluxD (ω : Configuration d) (σ : ℝ) (χ : Fin d → Vertex d → ℝ)
    (k i : Fin d) (x : Vertex d) : ℝ :=
  (if (openGraph ω).Adj x (x + Pi.single i 1) then
      (if i = k then 1 else 0) + (χ k (x + Pi.single i 1) - χ k x) else 0) -
    σ / 2 * (if i = k then 1 else 0)

/-- The `i`-th component of the translated flux `g̃*_{e_k}` of (4.26) on `ℤ^d`:
`T_{-e_i} [a(Dχ_{e_k} + e_k)]_i - (σ/2) δ_{ik}`, the flux on the edge `{x - e_i, x}`. -/
noncomputable def translatedFluxD (ω : Configuration d) (σ : ℝ) (χ : Fin d → Vertex d → ℝ)
    (k i : Fin d) (x : Vertex d) : ℝ :=
  (if (openGraph ω).Adj (x - Pi.single i 1) x then
      (if i = k then 1 else 0) + (χ k x - χ k (x - Pi.single i 1)) else 0) -
    σ / 2 * (if i = k then 1 else 0)

/-- **Dario–Gu, Proposition 2.13** (Proposition B.1), on `ℤ^d`, on the event `{y ∈ 𝒞_∞}`: for
every `α > 0` there are `C`, `s > 0` and `M_flux,α(y) ≤ O_s(C)` such that for every radius
`r ≥ M_flux,α(y)`, `‖[g̃_{e_k}]_i‖_{H̲^{-1}(𝒞_∞ ∩ B_r(y))} ≤ C r^α` for all `k, i`. Printed
statement (lines 1126-1144): *for any exponent `α > 0`, there exist a positive constant `C`, an
exponent `s > 0` such that, for any `y ∈ ℤ^d`, there exists a non-negative random variable
`M_flux,α(y)` satisfying `M_flux,α(y) ≤ O_s(C)` such that for each radius `r ≥ M_flux,α(y)`,
`‖g̃_p‖_{H̲^{-1}(𝒞_∞ ∩ B_r(y))} ≤ C |p| r^α`.* Differences: the norm of a vector field is taken
componentwise and `p` ranges over the basis vectors `e_k` (equivalent up to factors depending on
`d`, by linearity of `p ↦ g̃_p`); the conclusion is required on the event `{y ∈ 𝒞_∞}`. The flux
does not depend on the additive constant of the corrector; `χ` is the corrector of
`IsDGCorrectorD`. -/
def DarioGuFluxWeakNormD (d : ℕ) [NeZero d] (p : unitInterval) (σ : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex d,
    ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        y ∈ (uniqueInfiniteComponent h).supp → ∀ χ : Fin d → Vertex d → ℝ,
          IsDGCorrectorD (uniqueInfiniteComponent h) y χ → ∀ r : ℝ, M ω ≤ r → ∀ k i : Fin d,
            WeakNormLeD ω (dgClusterBallD (uniqueInfiniteComponent h) y r)
              (centeredFluxD ω σ χ k i) (C * r ^ α)

theorem mem_dgClusterBallD {ω : Configuration d} (K : OpenComponent ω) (y x : Vertex d)
    (r : ℝ) :
    x ∈ dgClusterBallD K y r ↔
      x ∈ K.supp ∧ dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y) < r := by
  rw [dgClusterBallD, mem_image_componentEuclideanBall]

theorem clusterH1NormD_nonneg (ω : Configuration d) (V : Finset (Vertex d))
    (v : Vertex d → ℝ) : 0 ≤ clusterH1NormD ω V v := by
  unfold clusterH1NormD
  positivity

/-- The weak norm is monotone in the bound. -/
theorem WeakNormLeD.mono {ω : Configuration d} {V : Finset (Vertex d)} {g : Vertex d → ℝ}
    {B B' : ℝ} (h : WeakNormLeD ω V g B) (hBB : B ≤ B') : WeakNormLeD ω V g B' := fun v hv =>
  (h v hv).trans (mul_le_mul_of_nonneg_right hBB (clusterH1NormD_nonneg ω V v))

/-- The weak norm satisfies the triangle inequality. -/
theorem WeakNormLeD.add {ω : Configuration d} {V : Finset (Vertex d)} {g g' : Vertex d → ℝ}
    {B B' : ℝ} (h : WeakNormLeD ω V g B) (h' : WeakNormLeD ω V g' B') :
    WeakNormLeD ω V (g + g') (B + B') := by
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

/-! ### The planar case -/

theorem openInteriorD_two : openInteriorD (d := 2) = openInterior := rfl

theorem openGradNormD_two : openGradNormD (d := 2) = openGradNorm := rfl

theorem clusterH1NormD_two : clusterH1NormD (d := 2) = clusterH1Norm := by
  funext ω V v
  unfold clusterH1NormD
  rw [Nat.cast_ofNat]
  rfl

theorem weakNormLeD_two : WeakNormLeD (d := 2) = WeakNormLe := by
  funext ω V g B
  unfold WeakNormLeD
  rw [clusterH1NormD_two]
  rfl

theorem dgClusterBallD_two : @dgClusterBallD 2 = @dgClusterBall := rfl

theorem isDGCorrectorD_two : @IsDGCorrectorD 2 = @IsDGCorrector := rfl

theorem centeredFluxD_two : centeredFluxD (d := 2) = centeredFlux := rfl

theorem translatedFluxD_two : translatedFluxD (d := 2) = translatedFlux := rfl

/-- At `d = 2`, `DarioGuFluxWeakNormD` is the planar statement `DarioGuFluxWeakNormTwo`. -/
theorem darioGuFluxWeakNormD_two_iff (p : unitInterval) (σ : ℝ) :
    DarioGuFluxWeakNormD 2 p σ ↔ DarioGuFluxWeakNormTwo p σ := by
  unfold DarioGuFluxWeakNormD
  rw [weakNormLeD_two]
  rfl

end Rigidity.Green
