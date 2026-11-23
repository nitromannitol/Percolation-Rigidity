import Rigidity.Proofs.Corrector.DarioFlipCluster

/-!
# Dario's (3.22) for the correctors

Case 3 of Step 2 of Dario's proof of Lemma 3.3, for bond percolation in dimension two, with the
bond `e` of the oriented edge `a = (x, i)` opened (`ω^{e,1}`) and closed (`ω^{e,0}`): if `x` and
`y = x + e_i` are in the infinite cluster of `ω^{e,0}`, the corrected planes `ℓ₁` of `ω^{e,1}` and
`ℓ₀` of `ω^{e,0}` of the same slope satisfy, on every open edge `b` of the cluster,

`∇(ℓ₁ - ℓ₀)(b) = (ℓ₀(x) - ℓ₀(y)) ∇∇G(e, b)`,

with `∇∇G(e, ·) = greenProj ω^{e,1} (1_a)` (`ae_correctedPlane_sub_eq_smul_greenProj`). This is
(3.22): `(a - a^e)(e) = 1` and `ℓ₀(x) - ℓ₀(y) = p·(x - y) + χ_p^e(x) - χ_p^e(y)`. The proof is
Dario's: `ℓ₁ - ℓ₀` solves `-∇·∇(ℓ₁ - ℓ₀) = (ℓ₀(x) - ℓ₀(y))(δ_x - δ_y)` (`edgeDiv_edgeGrad_setBond`)
and grows sublinearly (the slope asymptotics of both planes), so `ae_edgeGrad_eq_smul_greenProj`
applies at `ω^{e,1}` (`ae_setBond`).

* `extendComp`: a function on a component, extended by zero to the lattice;
* `edgeDiv_edgeGrad_extendComp_of_harmonic`: harmonic functions on the component have
  `∇·∇ = 0` there;
* `sublinearOn_of_componentSlopeAsymptotics`: the slope asymptotics give sublinear growth of
  `ℓ - q·z`.
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

/-- A function on a component, extended by zero to the lattice. -/
noncomputable def extendComp {ω : Configuration 2} (C : OpenComponent ω) (u : C → ℝ)
    (z : Vertex 2) : ℝ :=
  if h : z ∈ C.supp then u ⟨z, h⟩ else 0

theorem extendComp_of_mem {ω : Configuration 2} (C : OpenComponent ω) (u : C → ℝ)
    {z : Vertex 2} (h : z ∈ C.supp) : extendComp C u z = u ⟨z, h⟩ := by
  simp [extendComp, h]

theorem edgeDiv_edgeGrad_extendComp_of_harmonic {ω : Configuration 2} (C : OpenComponent ω)
    {u : C → ℝ} (hu : ∀ x, componentLaplacian C u x = 0) {z : Vertex 2} (hz : z ∈ C.supp) :
    edgeDiv ω (edgeGrad ω (extendComp C u)) z = 0 := by
  rw [← laplacian_openGraph_eq_edgeDiv, ← componentLaplacian_restrict_eq C (extendComp C u)
    ⟨z, hz⟩]
  have hfun : (fun y : C => extendComp C u y.val) = u := by
    funext y
    rw [extendComp_of_mem C u y.2]
  rw [hfun]
  exact hu _

theorem sublinearOn_of_componentSlopeAsymptotics {ω : Configuration 2} (C : OpenComponent ω)
    {q : Fin 2 → ℝ} {u : C → ℝ} (hu : componentSlopeAsymptotics C q u) :
    SublinearOn C.supp (fun z => extendComp C u z - ∑ i, q i * (z i : ℝ)) := by
  intro ε hε
  obtain ⟨R₀, hR₀, htail⟩ := hu (ε / 2) (by positivity)
  refine ⟨max R₀ 1, fun z hz hR => ?_⟩
  set e := Rigidity.Section5.eucl z with he
  have he1 : 1 ≤ e := (le_max_right _ _).trans hR
  have hball : (⟨z, hz⟩ : C) ∈ componentEuclideanBall C 0 (e + 1) := by
    rw [mem_componentEuclideanBall, Rigidity.Proofs.Section5.dist_latticeEuclideanEmbedding_zero]
    linarith
  have h := htail (e + 1) (by linarith [(le_max_left R₀ 1).trans hR]) ⟨z, hz⟩ hball
  simp only [componentSlope] at h
  beta_reduce
  rw [extendComp_of_mem C u hz]
  calc |u ⟨z, hz⟩ - ∑ i, q i * (z i : ℝ)| ≤ ε / 2 * (e + 1) := h
    _ ≤ ε * e := by nlinarith

/-- **Dario, (3.22), for the corrected planes**: almost surely, for every oriented edge `a = (x, i)`
with bond `e`, if `x` and `y = x + e_i` are in the infinite cluster of `ω^{e,0}`, then for corrected
planes `ℓ₁` of `ω^{e,1}` and `ℓ₀` of `ω^{e,0}` of the same slope and every open edge `b` of the
cluster, `∇(ℓ₁ - ℓ₀)(b) = (ℓ₀(x) - ℓ₀(y)) (greenProj ω^{e,1} (1_a))(b)`. -/
theorem ae_correctedPlane_sub_eq_smul_greenProj {p : unitInterval}
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
        ∀ b : LatticeEdge, EdgeOpen (setBond (edgeBond a) true ω) b →
          b.1 ∈ (uniqueInfiniteComponent h₁).supp →
          (extendComp _ ℓ₁ (edgeHead b) - extendComp _ ℓ₁ b.1) -
              (extendComp _ ℓ₀ (edgeHead b) - extendComp _ ℓ₀ b.1) =
            (ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩) *
              greenProj (setBond (edgeBond a) true ω) (lp.single 2 a 1) b := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 (ae_edgeGrad_eq_smul_greenProj hpc hp1)] with ω hω
  intro a h₁ h₀ hx hy q ℓ₁ ℓ₀ hℓ₁ hℓ₀ b hb hb1
  have hC : ∀ z, z ∈ (uniqueInfiniteComponent h₁).supp ↔ z ∈ (uniqueInfiniteComponent h₀).supp :=
    mem_supp_iff_of_mem_supp_setBond_false h₁ h₀ hx hy
  have ha : EdgeOpen (setBond (edgeBond a) true ω) a := (edgeOpen_setBond_self a true ω).2 rfl
  have hdiv : ∀ z ∈ (uniqueInfiniteComponent h₁).supp,
      edgeDiv (setBond (edgeBond a) true ω) (edgeGrad (setBond (edgeBond a) true ω)
        (fun z => extendComp _ ℓ₁ z - 1 * extendComp _ ℓ₀ z)) z =
      (ℓ₀ ⟨a.1, hx⟩ - ℓ₀ ⟨edgeHead a, hy⟩) *
        ((if z = a.1 then 1 else 0) - (if z = edgeHead a then 1 else 0)) := by
    intro z hz
    rw [edgeDiv_edgeGrad_sub_smul, edgeDiv_edgeGrad_extendComp_of_harmonic _ hℓ₁.1.1 hz,
      edgeDiv_edgeGrad_setBond,
      edgeDiv_edgeGrad_extendComp_of_harmonic _ hℓ₀.1.1 ((hC z).1 hz),
      extendComp_of_mem _ ℓ₀ hx, extendComp_of_mem _ ℓ₀ hy]
    ring
  have hsub : SublinearOn (uniqueInfiniteComponent h₁).supp
      (fun z => extendComp _ ℓ₁ z - 1 * extendComp _ ℓ₀ z) := by
    have h1 := sublinearOn_of_componentSlopeAsymptotics _ hℓ₁.2
    have h0 := sublinearOn_of_componentSlopeAsymptotics _ hℓ₀.2
    have h0' : SublinearOn (uniqueInfiniteComponent h₁).supp
        (fun z => extendComp _ ℓ₀ z - ∑ i, q i * (z i : ℝ)) := fun ε hε => by
      obtain ⟨R, hR⟩ := h0 ε hε
      exact ⟨R, fun z hz => hR z ((hC z).1 hz)⟩
    have h2 := h1.sub_smul h0' 1
    intro ε hε
    obtain ⟨R, hR⟩ := h2 ε hε
    refine ⟨R, fun z hz hRz => ?_⟩
    have h3 := hR z hz hRz
    convert h3 using 2
    ring
  have key := hω (edgeBond a) true h₁ a ha _ _ hdiv hsub b hb hb1
  simp only [edgeGrad, if_pos hb] at key
  rw [← key]
  ring

end Rigidity.Corrector
