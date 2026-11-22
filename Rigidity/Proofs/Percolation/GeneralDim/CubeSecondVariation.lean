import Rigidity.Proofs.Percolation.GeneralDim.CubeSubadditive

/-!
# Subadditivity of `μ` and `ν` with the energies of the differences, in `ℤ^d`

Testing `μ(V, q)` and `ν(V, p)` on the resolved subcubes `V` of scale `n` of a triadic cube `U`
with the restrictions of the optimizers on `U`, and keeping the second variation terms
(Armstrong and Dario, Lemma 4.2), gives the subadditivity inequalities with the energies of the
differences on the left side:

`∑_V B_V(u|_V - u_V)/2 + ∑_V |V| μ(V, q) ≤ |U| μ(U, q) + E_q(u)`,
`∑_V B_V(v|_V - v_V)/2 + |U| ν(U, p) ≤ ∑_V |V| ν(V, p) + F_p^{exc}(v)`,

with the error terms of the subadditivity of `μ` and `ν`. This is the deterministic step in the
proof of Lemma 5.4 of Armstrong and Dario (display (5.11) and its analogue for `ν`), in every
dimension.
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The coarse pairing of a function on the cluster of `U` splits into the coarse pairings of its
restrictions to the resolved subcubes of scale `n` and the pairing over the exceptional edges. -/
theorem cubeCoarsePairing_eq_sum_restrictExt_add (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale) (q : Fin d → ℝ) (u : CubeFun ω U) :
    cubeCoarsePairing ω U q u =
      ∑ V ∈ U.resolvedSubcubesAt ω n, cubeCoarsePairing ω V q (cubeRestrictExt V u) +
        ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
          (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices ∧
              ¬ (PartitionResolved ω (triadicCubeAt n x) ∧
                x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices) then
            q i * (cubeCoarsen ω U u (x + LatticeProb.unit i) - cubeCoarsen ω U u x) else 0) := by
  set D : Vertex d → Fin d → ℝ := fun x i =>
    q i * (cubeCoarsen ω U u (x + LatticeProb.unit i) - cubeCoarsen ω U u x) with hD
  have hpair : ∑ V ∈ U.resolvedSubcubesAt ω n, cubeCoarsePairing ω V q (cubeRestrictExt V u) =
      ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
        (if PartitionResolved ω (triadicCubeAt n x) ∧
          x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices then D x i
          else 0) := by
    rw [sum_resolvedSubcubesAt]
    have e1 : ∀ V ∈ U.subcubesAt n, (if PartitionResolved ω V then
        cubeCoarsePairing ω V q (cubeRestrictExt V u) else 0) =
        ∑ x ∈ V.toIntegerCube.vertices, ∑ i : Fin d,
          (if PartitionResolved ω V ∧ x + LatticeProb.unit i ∈ V.toIntegerCube.vertices then
            D x i else 0) := by
      intro V _
      split_ifs with hres
      · rw [cubeCoarsePairing_restrictExt hd hP hres]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
        simp only [hres, true_and, hD]
      · simp [hres]
    rw [Finset.sum_congr rfl e1,
      ← sum_triadicCubeAt_eq hn (fun V x => ∑ i : Fin d,
        (if PartitionResolved ω V ∧ x + LatticeProb.unit i ∈ V.toIntegerCube.vertices then D x i
          else 0))]
  have hℓU : cubeCoarsePairing ω U q u = ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
      (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices then D x i else 0) := by
    rw [cubeCoarsePairing_apply]
    rfl
  have hsplit : ∀ x ∈ U.toIntegerCube.vertices, ∀ i : Fin d,
      (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices then D x i else 0) =
      (if PartitionResolved ω (triadicCubeAt n x) ∧
        x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices then D x i else 0) +
      (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices ∧
        ¬ (PartitionResolved ω (triadicCubeAt n x) ∧
          x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices) then D x i
        else 0) := by
    intro x hx i
    have hsub := triadicCubeAt_subset hn ((U.mem_toIntegerCube_vertices x).1 hx)
    by_cases h1 : PartitionResolved ω (triadicCubeAt n x) ∧
        x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices
    · have h2 : x + LatticeProb.unit i ∈ U.toIntegerCube.vertices :=
        (U.mem_toIntegerCube_vertices _).2
          (hsub (((triadicCubeAt n x).mem_toIntegerCube_vertices _).1 h1.2))
      simp [h1, h2]
    · by_cases h2 : x + LatticeProb.unit i ∈ U.toIntegerCube.vertices <;> simp [h1, h2]
  rw [hℓU, hpair, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hsplit x hx i

/-- **Subadditivity of `μ` with the energies of the differences** (Armstrong and Dario, proof of
Lemma 5.4, display (5.11)). For any solutions `u_V` of the first variation equations of `μ(V, q)`
on the resolved subcubes `V` of scale `n`, the restriction of any solution `u` of the first
variation equation of `μ(U, q)` satisfies
`∑_V B_V(u|_V - u_V)/2 + ∑_{x ∈ U} 1{V(x) resolved} μ(V(x), q) ≤ |U| μ(U, q) + E_q(u)`. -/
theorem sum_cubeForm_sub_add_sum_cubeMu_subcubes_le (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) {n : ℕ} (hn : n ≤ U.scale) (q : Fin d → ℝ)
    {u : CubeFun ω U} (hu : u ∈ cubeHarmonic ω U)
    (hvar : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w u = cubeCoarsePairing ω U q w)
    (uV : (V : TriadicCube d) → CubeFun ω V)
    (huV : ∀ V ∈ U.resolvedSubcubesAt ω n, uV V ∈ cubeHarmonic ω V ∧
      ∀ w ∈ cubeHarmonic ω V, cubeForm ω V w (uV V) = cubeCoarsePairing ω V q w) :
      ∑ V ∈ U.resolvedSubcubesAt ω n,
          cubeForm ω V (cubeRestrictExt V u - uV V) (cubeRestrictExt V u - uV V) / 2 +
        ∑ x ∈ U.toIntegerCube.vertices,
          (if PartitionResolved ω (triadicCubeAt n x) then cubeMu ω (triadicCubeAt n x) q
            else 0) ≤
        cubeMu ω U q * U.latticeVolume + ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
          (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices ∧
              ¬ (PartitionResolved ω (triadicCubeAt n x) ∧
                x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices) then
            q i * (cubeCoarsen ω U u (x + LatticeProb.unit i) - cubeCoarsen ω U u x) else 0) := by
  set T := U.resolvedSubcubesAt ω n
  have hV : ∀ V ∈ T, cubeForm ω V (cubeRestrictExt V u - uV V)
        (cubeRestrictExt V u - uV V) / 2 + V.latticeVolume * cubeMu ω V q =
      cubeForm ω V (cubeRestrictExt V u) (cubeRestrictExt V u) / 2 -
        cubeCoarsePairing ω V q (cubeRestrictExt V u) := by
    intro V hVT
    obtain ⟨hVS, hVres⟩ := mem_resolvedSubcubesAt.1 hVT
    have hVU := TriadicCube.subset_of_mem_subcubesAt hn hVS
    have hmem : cubeRestrictExt V u ∈ cubeHarmonic ω V :=
      cubeRestrictExt_mem_cubeHarmonic hVU
        (crossingClusterVertices_subset_of_mem_resolvedSubcubesAt hd hP hn hVT) hu
    obtain ⟨huV1, huV2⟩ := huV V hVT
    have h := cubeMu_mul_latticeVolume_add_cubeForm_sub hd hP hVres q huV1 huV2 hmem
    linarith
  have hBU := sum_cubeForm_restrictExt_le T (Finset.filter_subset _ _)
    (fun V hV => crossingClusterVertices_subset_of_mem_resolvedSubcubesAt hd hP hn hV) u
  have hℓ := cubeCoarsePairing_eq_sum_restrictExt_add hd hP hn q u
  have hμU : cubeMu ω U q * U.latticeVolume =
      cubeForm ω U u u / 2 - cubeCoarsePairing ω U q u := by
    rw [cubeMu_mul_latticeVolume_eq hd hP hU q hu hvar, hvar u hu]
    ring
  have hL : ∑ x ∈ U.toIntegerCube.vertices,
      (if PartitionResolved ω (triadicCubeAt n x) then cubeMu ω (triadicCubeAt n x) q else 0) =
      ∑ V ∈ T, V.latticeVolume * cubeMu ω V q :=
    sum_vertices_ite_triadicCubeAt_eq hn (fun V => cubeMu ω V q)
  rw [hL, ← Finset.sum_add_distrib, Finset.sum_congr rfl hV,
    Finset.sum_sub_distrib, ← Finset.sum_div]
  linarith

/-- The flux pairing of a function on the cluster of `U` splits into the flux pairings of its
restrictions to the resolved subcubes of scale `n` and the flux over the exceptional pairs. -/
theorem cubeFluxPairing_eq_sum_restrictExt_add (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale) (p : Fin d → ℝ) (v : CubeFun ω U) :
    cubeFluxPairing ω U p v =
      ∑ V ∈ U.resolvedSubcubesAt ω n, cubeFluxPairing ω V p (cubeRestrictExt V v) +
        (1 / 2 : ℝ) * ∑ x ∈ crossingClusterVertices ω U, ∑ y ∈ crossingClusterVertices ω U,
          (if IsResolvedSubcubePair ω n x y then 0 else cubeFluxTerm ω U p v x y) := by
  rw [sum_cubeFluxPairing_restrictExt hd hP hn p v, cubeFluxPairing_eq_sum, ← mul_add,
    ← Finset.sum_add_distrib]
  refine congrArg (fun t => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl fun x _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [cubeFluxTerm]
  split_ifs <;> simp

/-- **Subadditivity of `ν` with the energies of the differences** (Armstrong and Dario, proof of
Lemma 5.4, analogue of display (5.11) for `ν`). For any solutions `v_V` of the first variation
equations of `ν(V, p)` on the resolved subcubes `V` of scale `n`, the restriction of any solution
`v` of the first variation equation of `ν(U, p)` satisfies
`∑_V B_V(v|_V - v_V)/2 + |U| ν(U, p) ≤ ∑_{x ∈ U} 1{V(x) resolved} ν(V(x), p) + F_p^{exc}(v)`. -/
theorem sum_cubeForm_sub_add_cubeNu_le_sum_subcubes (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale) (p : Fin d → ℝ)
    {v : CubeFun ω U} (hv : v ∈ cubeHarmonic ω U)
    (hvar : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w v = cubeFluxPairing ω U p w)
    (vV : (V : TriadicCube d) → CubeFun ω V)
    (hvV : ∀ V ∈ U.resolvedSubcubesAt ω n, vV V ∈ cubeHarmonic ω V ∧
      ∀ w ∈ cubeHarmonic ω V, cubeForm ω V w (vV V) = cubeFluxPairing ω V p w) :
      ∑ V ∈ U.resolvedSubcubesAt ω n,
          cubeForm ω V (cubeRestrictExt V v - vV V) (cubeRestrictExt V v - vV V) / 2 +
        cubeNu ω U p * U.latticeVolume ≤
        ∑ x ∈ U.toIntegerCube.vertices,
          (if PartitionResolved ω (triadicCubeAt n x) then cubeNu ω (triadicCubeAt n x) p
            else 0) +
        (1 / 2 : ℝ) * ∑ x ∈ crossingClusterVertices ω U, ∑ y ∈ crossingClusterVertices ω U,
          (if IsResolvedSubcubePair ω n x y then 0 else cubeFluxTerm ω U p v x y) := by
  set T := U.resolvedSubcubesAt ω n
  have hV : ∀ V ∈ T, cubeFluxPairing ω V p (cubeRestrictExt V v) -
        cubeForm ω V (cubeRestrictExt V v) (cubeRestrictExt V v) / 2 +
        cubeForm ω V (cubeRestrictExt V v - vV V) (cubeRestrictExt V v - vV V) / 2 =
      V.latticeVolume * cubeNu ω V p := by
    intro V hVT
    obtain ⟨hVS, -⟩ := mem_resolvedSubcubesAt.1 hVT
    have hVU := TriadicCube.subset_of_mem_subcubesAt hn hVS
    have hmem : cubeRestrictExt V v ∈ cubeHarmonic ω V :=
      cubeRestrictExt_mem_cubeHarmonic hVU
        (crossingClusterVertices_subset_of_mem_resolvedSubcubesAt hd hP hn hVT) hv
    obtain ⟨hvV1, hvV2⟩ := hvV V hVT
    rw [cubeFluxPairing_sub_add_cubeForm_sub p hvV1 hvV2 hmem, mul_comm]
  have hBU := sum_cubeForm_restrictExt_le T (Finset.filter_subset _ _)
    (fun V hV => crossingClusterVertices_subset_of_mem_resolvedSubcubesAt hd hP hn hV) v
  have hF := cubeFluxPairing_eq_sum_restrictExt_add hd hP hn p v
  have hνU : cubeNu ω U p * U.latticeVolume = cubeFluxPairing ω U p v - cubeForm ω U v v / 2 := by
    rw [cubeNu_mul_latticeVolume_eq p hv hvar, hvar v hv]
    ring
  have hL : ∑ x ∈ U.toIntegerCube.vertices,
      (if PartitionResolved ω (triadicCubeAt n x) then cubeNu ω (triadicCubeAt n x) p else 0) =
      ∑ V ∈ T, V.latticeVolume * cubeNu ω V p :=
    sum_vertices_ite_triadicCubeAt_eq hn (fun V => cubeNu ω V p)
  have hsum := Finset.sum_congr rfl hV
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div] at hsum
  rw [hL]
  linarith

end Rigidity.Percolation
