import Rigidity.Proofs.Percolation.PlanarNuSubadditive

/-!
# Second variations and the strengthened subadditivity of `μ` and `ν`

If `u ∈ A_*(U)` solves the first variation equation of `μ(U, q)`, then for every `w ∈ A_*(U)`
the second variation identity holds:

`|U| μ(U, q) + B(w - u, w - u) / 2 = B(w, w) / 2 - ℓ_q(w)`,

and similarly, if `v` solves the first variation equation of `ν(U, p)`,

`F_p(w) - B(w, w) / 2 + B(w - v, w - v) / 2 = |U| ν(U, p)`

(Armstrong and Dario, Lemma 4.2). Testing `μ(V, q)` and `ν(V, p)` on the resolved subcubes `V` of
scale `n` with the restrictions of the optimizers on `U` and keeping the second variation term, we
obtain the subadditivity inequalities with the energies of the differences on the left side:

`∑_V B_V(u|_V - u_V)/2 + ∑_V |V| μ(V, q) ≤ |U| μ(U, q) + E_q(u)`,
`∑_V B_V(v|_V - v_V)/2 + |U| ν(U, p) ≤ ∑_V |V| ν(V, p) + F_p^{exc}(v)`,

with the same error terms as in the subadditivity of `μ` and `ν`. This is the deterministic step
in the proof of Lemma 5.4 of Armstrong and Dario (display (5.11) and its analogue for `ν`).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- Expansion of the energy of a difference. -/
theorem clusterForm_sub_sub {U : TriadicCube 2} (u w : ClusterFun ω U) :
    clusterForm ω U (w - u) (w - u) =
      clusterForm ω U w w - 2 * clusterForm ω U w u + clusterForm ω U u u := by
  simp only [map_sub, LinearMap.sub_apply]
  rw [clusterForm_symm u w]
  ring

/-- **Second variation for `μ`** (Armstrong and Dario, Lemma 4.2). -/
theorem planarMu_mul_volume_add_clusterForm_sub (hP : PlanarPartitionEvent ω)
    {U : TriadicCube 2} (hU : PlanarResolved ω U) (q : Fin 2 → ℝ) {u : ClusterFun ω U}
    (hu : u ∈ clusterHarmonic ω U)
    (hvar : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w u = coarsePairing ω U q w)
    {w : ClusterFun ω U} (hw : w ∈ clusterHarmonic ω U) :
    planarMu ω U q * U.volume + clusterForm ω U (w - u) (w - u) / 2 =
      clusterForm ω U w w / 2 - coarsePairing ω U q w := by
  obtain ⟨u', hu', hvar', hμ'⟩ := exists_planarMu_minimizer hP hU q
  have h1 := hvar u' hu'
  have h2 := hvar' u hu
  have h3 := hvar u hu
  have h4 := hvar' u' hu'
  have h5 := hvar w hw
  have hs := clusterForm_symm u' u
  have hμ : planarMu ω U q * U.volume = clusterForm ω U u' u' / 2 - coarsePairing ω U q u' := by
    rw [hμ', div_mul_cancel₀ _ U.volume_pos.ne']
  rw [hμ, clusterForm_sub_sub]
  linarith

/-- The value of `μ(U, q)` at any solution of the first variation equation. -/
theorem planarMu_mul_volume_eq (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (q : Fin 2 → ℝ) {u : ClusterFun ω U}
    (hu : u ∈ clusterHarmonic ω U)
    (hvar : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w u = coarsePairing ω U q w) :
    planarMu ω U q * U.volume = -(clusterForm ω U u u / 2) := by
  have h := planarMu_mul_volume_add_clusterForm_sub hP hU q hu hvar hu
  have h3 := hvar u hu
  simp only [sub_self, map_zero, zero_div, add_zero] at h
  linarith

/-- **Second variation for `ν`** (Armstrong and Dario, Lemma 4.2). -/
theorem fluxPairing_sub_add_clusterForm_sub {U : TriadicCube 2} (p : Fin 2 → ℝ)
    {v : ClusterFun ω U} (hv : v ∈ clusterHarmonic ω U)
    (hvar : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w v = fluxPairing ω U p w)
    {w : ClusterFun ω U} (hw : w ∈ clusterHarmonic ω U) :
    fluxPairing ω U p w - clusterForm ω U w w / 2 + clusterForm ω U (w - v) (w - v) / 2 =
      planarNu ω U p * U.volume := by
  obtain ⟨v', hv', hvar', hν'⟩ := exists_planarNu_maximizer (ω := ω) (U := U) p
  have h1 := hvar v' hv'
  have h2 := hvar' v hv
  have h3 := hvar v hv
  have h4 := hvar' v' hv'
  have h5 := hvar w hw
  have hs := clusterForm_symm v' v
  have hν : planarNu ω U p * U.volume = fluxPairing ω U p v' - clusterForm ω U v' v' / 2 := by
    rw [hν', div_mul_cancel₀ _ U.volume_pos.ne']
  rw [hν, clusterForm_sub_sub]
  linarith

/-- The value of `ν(U, p)` at any solution of the first variation equation. -/
theorem planarNu_mul_volume_eq {U : TriadicCube 2} (p : Fin 2 → ℝ) {v : ClusterFun ω U}
    (hv : v ∈ clusterHarmonic ω U)
    (hvar : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w v = fluxPairing ω U p w) :
    planarNu ω U p * U.volume = clusterForm ω U v v / 2 := by
  have h := fluxPairing_sub_add_clusterForm_sub p hv hvar hv
  have h3 := hvar v hv
  simp only [sub_self, map_zero, zero_div, add_zero] at h
  linarith

/-- Sums over the vertices of `U` of a quantity of the resolved subcube containing the vertex. -/
theorem sum_vertices_ite_scaleCube_eq {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    (f : TriadicCube 2 → ℝ) :
    ∑ x ∈ U.toIntegerCube.vertices,
        (if PlanarResolved ω (scaleCube n x) then f (scaleCube n x) else 0) =
      ∑ V ∈ (subcubesAt U n).filter (fun V => PlanarResolved ω V), V.volume * f V := by
  rw [sum_scaleCube_eq hn (fun V _ => if PlanarResolved ω V then f V else 0),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← volume_eq_card]
  split_ifs <;> simp

/-- The coarse pairing of a function on the cluster of `U` splits into the coarse pairings of its
restrictions to the resolved subcubes of scale `n` and the pairing over the exceptional edges. -/
theorem coarsePairing_eq_sum_restrict_add (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    {n : ℕ} (hn : n ≤ U.scale) (q : Fin 2 → ℝ) (u : ClusterFun ω U) :
    coarsePairing ω U q u =
      ∑ V ∈ (subcubesAt U n).filter (fun V => PlanarResolved ω V),
          coarsePairing ω V q (clusterRestrictExt V u) +
        ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
          (if x + unitVertex i ∈ U.toIntegerCube.vertices ∧
              ¬ (PlanarResolved ω (scaleCube n x) ∧
                x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices) then
            q i * (coarsen ω U u (x + unitVertex i) - coarsen ω U u x) else 0) := by
  set S := subcubesAt U n
  set D : Vertex 2 → Fin 2 → ℝ := fun x i =>
    q i * (coarsen ω U u (x + unitVertex i) - coarsen ω U u x) with hD
  have hpair : ∑ V ∈ S.filter (fun V => PlanarResolved ω V),
      coarsePairing ω V q (clusterRestrictExt V u) =
      ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
        (if PlanarResolved ω (scaleCube n x) ∧
          x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices then D x i else 0) := by
    rw [Finset.sum_filter]
    have e1 : ∀ V ∈ S, (if PlanarResolved ω V then
        coarsePairing ω V q (clusterRestrictExt V u) else 0) =
        ∑ x ∈ V.toIntegerCube.vertices, ∑ i : Fin 2,
          (if PlanarResolved ω V ∧ x + unitVertex i ∈ V.toIntegerCube.vertices then D x i
            else 0) := by
      intro V hVS
      split_ifs with hres
      · rw [coarsePairing_restrict hP hres (subset_of_mem_subcubesAt hn hVS)]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
        simp only [hres, true_and, hD]
      · simp [hres]
    rw [Finset.sum_congr rfl e1,
      ← sum_scaleCube_eq hn (fun V x => ∑ i : Fin 2,
        (if PlanarResolved ω V ∧ x + unitVertex i ∈ V.toIntegerCube.vertices then D x i
          else 0))]
  have hℓU : coarsePairing ω U q u = ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
      (if x + unitVertex i ∈ U.toIntegerCube.vertices then D x i else 0) := by
    rw [coarsePairing_apply]
    rfl
  have hsplit : ∀ x ∈ U.toIntegerCube.vertices, ∀ i : Fin 2,
      (if x + unitVertex i ∈ U.toIntegerCube.vertices then D x i else 0) =
      (if PlanarResolved ω (scaleCube n x) ∧
        x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices then D x i else 0) +
      (if x + unitVertex i ∈ U.toIntegerCube.vertices ∧
        ¬ (PlanarResolved ω (scaleCube n x) ∧
          x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices) then D x i else 0) := by
    intro x hx i
    have hsub := scaleCube_subset hn ((U.mem_toIntegerCube_vertices x).1 hx)
    by_cases h1 : PlanarResolved ω (scaleCube n x) ∧
        x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices
    · have h2 : x + unitVertex i ∈ U.toIntegerCube.vertices :=
        (U.mem_toIntegerCube_vertices _).2
          (hsub (((scaleCube n x).mem_toIntegerCube_vertices _).1 h1.2))
      simp [h1, h2]
    · by_cases h2 : x + unitVertex i ∈ U.toIntegerCube.vertices <;> simp [h1, h2]
  rw [hℓU, hpair, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hsplit x hx i

/-- **Subadditivity of `μ` with the energies of the differences** (Armstrong and Dario, proof of
Lemma 5.4, display (5.11), planar form). For any solutions `u_V` of the first variation equations
of `μ(V, q)` on the resolved subcubes `V` of scale `n`, the restriction of any solution `u` of the
first variation equation of `μ(U, q)` satisfies
`∑_V B_V(u|_V - u_V)/2 + ∑_{x ∈ U} 1{V(x) resolved} μ(V(x), q) ≤ |U| μ(U, q) + E_q(u)`. -/
theorem sum_clusterForm_sub_add_sum_planarMu_subcubes_le (hP : PlanarPartitionEvent ω)
    {U : TriadicCube 2} (hU : PlanarResolved ω U) {n : ℕ} (hn : n ≤ U.scale) (q : Fin 2 → ℝ)
    {u : ClusterFun ω U} (hu : u ∈ clusterHarmonic ω U)
    (hvar : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w u = coarsePairing ω U q w)
    (uV : (V : TriadicCube 2) → ClusterFun ω V)
    (huV : ∀ V ∈ subcubesAt U n, PlanarResolved ω V → uV V ∈ clusterHarmonic ω V ∧
      ∀ w ∈ clusterHarmonic ω V, clusterForm ω V w (uV V) = coarsePairing ω V q w) :
      ∑ V ∈ (subcubesAt U n).filter (fun V => PlanarResolved ω V),
          clusterForm ω V (clusterRestrictExt V u - uV V) (clusterRestrictExt V u - uV V) / 2 +
        ∑ x ∈ U.toIntegerCube.vertices,
          (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) ≤
        planarMu ω U q * U.volume + ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
          (if x + unitVertex i ∈ U.toIntegerCube.vertices ∧
              ¬ (PlanarResolved ω (scaleCube n x) ∧
                x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices) then
            q i * (coarsen ω U u (x + unitVertex i) - coarsen ω U u x) else 0) := by
  set T := (subcubesAt U n).filter (fun V => PlanarResolved ω V)
  have hV : ∀ V ∈ T, clusterForm ω V (clusterRestrictExt V u - uV V)
        (clusterRestrictExt V u - uV V) / 2 + V.volume * planarMu ω V q =
      clusterForm ω V (clusterRestrictExt V u) (clusterRestrictExt V u) / 2 -
        coarsePairing ω V q (clusterRestrictExt V u) := by
    intro V hVT
    obtain ⟨hVS, hVres⟩ := Finset.mem_filter.1 hVT
    have hVU := subset_of_mem_subcubesAt hn hVS
    have hmem : clusterRestrictExt V u ∈ clusterHarmonic ω V := by
      rw [clusterRestrictExt_eq hVU]
      exact clusterRestrict_mem_clusterHarmonic hP hVres hVU hu
    obtain ⟨huV1, huV2⟩ := huV V hVS hVres
    have h := planarMu_mul_volume_add_clusterForm_sub hP hVres q huV1 huV2 hmem
    linarith
  have hBU := sum_clusterForm_restrict_le hn T (Finset.filter_subset _ _) u
  have hℓ := coarsePairing_eq_sum_restrict_add hP hn q u
  have hμU : planarMu ω U q * U.volume = clusterForm ω U u u / 2 - coarsePairing ω U q u := by
    rw [planarMu_mul_volume_eq hP hU q hu hvar, hvar u hu]
    ring
  have hL : ∑ x ∈ U.toIntegerCube.vertices,
      (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) =
      ∑ V ∈ T, V.volume * planarMu ω V q :=
    sum_vertices_ite_scaleCube_eq hn (fun V => planarMu ω V q)
  rw [hL, ← Finset.sum_add_distrib, Finset.sum_congr rfl hV,
    Finset.sum_sub_distrib, ← Finset.sum_div]
  linarith

/-- The flux pairing of a function on the cluster of `U` splits into the flux pairings of its
restrictions to the resolved subcubes of scale `n` and the flux over the exceptional pairs. -/
theorem fluxPairing_eq_sum_restrict_add {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    (p : Fin 2 → ℝ) (v : ClusterFun ω U) :
    fluxPairing ω U p v =
      ∑ V ∈ (subcubesAt U n).filter (fun V => PlanarResolved ω V),
          fluxPairing ω V p (clusterRestrictExt V v) +
        (1 / 2 : ℝ) * ∑ x ∈ clusterVertices ω U, ∑ y ∈ clusterVertices ω U,
          (if IsSubcubePair ω n x y then 0 else fluxTerm ω U p v x y) := by
  rw [sum_fluxPairing_restrictExt hn p v, fluxPairing_eq_sum_fluxTerm, ← mul_add,
    ← Finset.sum_add_distrib]
  refine congrArg (fun t => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl fun x _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

/-- **Subadditivity of `ν` with the energies of the differences** (Armstrong and Dario, proof of
Lemma 5.4, analogue of display (5.11) for `ν`, planar form). For any solutions `v_V` of the first
variation equations of `ν(V, p)` on the resolved subcubes `V` of scale `n`, the restriction of any
solution `v` of the first variation equation of `ν(U, p)` satisfies
`∑_V B_V(v|_V - v_V)/2 + |U| ν(U, p) ≤ ∑_{x ∈ U} 1{V(x) resolved} ν(V(x), p) + F_p^{exc}(v)`. -/
theorem sum_clusterForm_sub_add_planarNu_le_sum_subcubes (hP : PlanarPartitionEvent ω)
    {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale) (p : Fin 2 → ℝ)
    {v : ClusterFun ω U} (hv : v ∈ clusterHarmonic ω U)
    (hvar : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w v = fluxPairing ω U p w)
    (vV : (V : TriadicCube 2) → ClusterFun ω V)
    (hvV : ∀ V ∈ subcubesAt U n, PlanarResolved ω V → vV V ∈ clusterHarmonic ω V ∧
      ∀ w ∈ clusterHarmonic ω V, clusterForm ω V w (vV V) = fluxPairing ω V p w) :
      ∑ V ∈ (subcubesAt U n).filter (fun V => PlanarResolved ω V),
          clusterForm ω V (clusterRestrictExt V v - vV V) (clusterRestrictExt V v - vV V) / 2 +
        planarNu ω U p * U.volume ≤
        ∑ x ∈ U.toIntegerCube.vertices,
          (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) p else 0) +
        (1 / 2 : ℝ) * ∑ x ∈ clusterVertices ω U, ∑ y ∈ clusterVertices ω U,
          (if IsSubcubePair ω n x y then 0 else fluxTerm ω U p v x y) := by
  set T := (subcubesAt U n).filter (fun V => PlanarResolved ω V)
  have hV : ∀ V ∈ T, fluxPairing ω V p (clusterRestrictExt V v) -
        clusterForm ω V (clusterRestrictExt V v) (clusterRestrictExt V v) / 2 +
        clusterForm ω V (clusterRestrictExt V v - vV V) (clusterRestrictExt V v - vV V) / 2 =
      V.volume * planarNu ω V p := by
    intro V hVT
    obtain ⟨hVS, hVres⟩ := Finset.mem_filter.1 hVT
    have hVU := subset_of_mem_subcubesAt hn hVS
    have hmem : clusterRestrictExt V v ∈ clusterHarmonic ω V := by
      rw [clusterRestrictExt_eq hVU]
      exact clusterRestrict_mem_clusterHarmonic hP hVres hVU hv
    obtain ⟨hvV1, hvV2⟩ := hvV V hVS hVres
    rw [fluxPairing_sub_add_clusterForm_sub p hvV1 hvV2 hmem, mul_comm]
  have hBU := sum_clusterForm_restrict_le hn T (Finset.filter_subset _ _) v
  have hF := fluxPairing_eq_sum_restrict_add (ω := ω) hn p v
  have hνU : planarNu ω U p * U.volume = fluxPairing ω U p v - clusterForm ω U v v / 2 := by
    rw [planarNu_mul_volume_eq p hv hvar, hvar v hv]
    ring
  have hL : ∑ x ∈ U.toIntegerCube.vertices,
      (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) p else 0) =
      ∑ V ∈ T, V.volume * planarNu ω V p :=
    sum_vertices_ite_scaleCube_eq hn (fun V => planarNu ω V p)
  have hsum := Finset.sum_congr rfl hV
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div] at hsum
  rw [hL]
  linarith

end Rigidity.Percolation
