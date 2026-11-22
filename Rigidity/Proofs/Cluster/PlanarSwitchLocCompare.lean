import Rigidity.Proofs.Cluster.PlanarSwitchLocLocal

/-!
# The pointwise comparison of display (5.31) of Armstrong and Dario

For a triadic cube `V` of scale `n`, a field `g` bounded by `G` and a slope `q`, let
`X = |V|⁻¹ ⟨∇[u(·, V, q)]_𝒫, g⟩_V`. On the event `PlanarCapGood k V`, with `D` the interior square
at distance `6 · 3^k` and `u_loc` the solution of the first variation with the field `q|D`,
the second variation comparison and the counting bounds give
`(X - |V|⁻¹ ℓ_{g|D}(u_loc))² ≤ C G² |q|₁² 3^{9k} / 3ⁿ` (`sq_sub_switchLocValue_le`); this is
display (e.ulocloccoarse) combined with the bound on the boundary layer in the proof of
Lemma 5.7. Without any event, `|X| ≤ 72 · 81ⁿ G |q|₁` (`abs_subcubePairing_le`).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

theorem fieldPairing_restrictField_self {U : TriadicCube 2} (g : Vertex 2 → Fin 2 → ℝ)
    (u : ClusterFun ω U) :
    fieldPairing ω U (restrictField U.toIntegerCube.vertices g) u = fieldPairing ω U g u := by
  rw [fieldPairing_eq_sum_latticeEdgesIn, fieldPairing_eq_sum_latticeEdgesIn]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
  rw [restrictField, if_pos ⟨(Finset.mem_product.1 hk1).1, hk2⟩]

/-- The subcube pairing as a field pairing. -/
theorem subcubePairing_eq (V : TriadicCube 2) (g : Vertex 2 → Fin 2 → ℝ) (u : ClusterFun ω V) :
    edgePairing V.toIntegerCube.vertices g (coarsen ω V u) = fieldPairing ω V g u := by
  rw [edgePairing_coarsen_eq_fieldPairing subset_rfl, fieldPairing_restrictField_self]

theorem abs_le_abs_add_abs (q : Fin 2 → ℝ) (i : Fin 2) : |q i| ≤ |q 0| + |q 1| := by
  fin_cases i
  · simp
  · simp

/-- The Dirichlet form of a solution of the first variation with the field `h`. -/
theorem clusterForm_le_of_variation {U : TriadicCube 2} {h : Vertex 2 → Fin 2 → ℝ}
    {u : ClusterFun ω U} (hu : u ∈ clusterHarmonic ω U)
    (hv : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w u = fieldPairing ω U h w) {K : ℝ}
    (hK0 : 0 ≤ K)
    (hK : ∀ (f : Vertex 2 → Fin 2 → ℝ) (w : ClusterFun ω U),
      fieldPairing ω U f w ^ 2 ≤ K * edgeNormSq U f * (2 * clusterForm ω U w w)) :
    clusterForm ω U u u ≤ 2 * (K * edgeNormSq U h) := by
  have hB : 0 ≤ clusterForm ω U u u := by
    have h2 := two_mul_clusterForm_self (ω := ω) (U := U) u
    have : 0 ≤ 2 * clusterForm ω U u u := by
      rw [h2]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  exact le_of_le_abs_of_sq_le (X := fieldPairing ω U h u) hB
    (mul_nonneg hK0 (edgeNormSq_nonneg _ _)) (by rw [← hv u hu]; exact le_abs_self _) (hK _ _)

/-- The constant field `q` has squared edge norm at most `2 |U| |q|₁²`. -/
theorem edgeNormSq_const_le (U : TriadicCube 2) (q : Fin 2 → ℝ) :
    edgeNormSq U (fun _ => q) ≤ 2 * U.volume * (|q 0| + |q 1|) ^ 2 :=
  edgeNormSq_le fun _ i => abs_le_abs_add_abs q i

/-- **A deterministic bound for the subcube pairing.** -/
theorem abs_subcubePairing_le (V : TriadicCube 2) (q : Fin 2 → ℝ) {g : Vertex 2 → Fin 2 → ℝ}
    {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) (ω : Configuration 2) :
    |edgePairing V.toIntegerCube.vertices g (coarsen ω V (planarMuMinimizer ω V q)) /
        9 ^ V.scale| ≤ 72 * 81 ^ V.scale * G * (|q 0| + |q 1|) := by
  have hG : 0 ≤ G := (abs_nonneg _).trans (hg 0 0)
  have hvol : V.volume = (9 : ℝ) ^ V.scale := rfl
  have hv0 : (0 : ℝ) < 9 ^ V.scale := by positivity
  have h81 : (81 : ℝ) ^ V.scale = (9 ^ V.scale) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  by_cases hω : PlanarPartitionEvent ω ∧ PlanarResolved ω V
  · obtain ⟨hP, hV⟩ := hω
    have hN : ∀ a, coarseWeight ω V a ≤ 2 * V.volume := fun a => by
      unfold coarseWeight
      rw [Finset.sum_boole]
      refine le_trans ?_ (card_latticeEdgesIn_le V)
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hW : ∀ k ∈ latticeEdgesIn V,
        ((coarseEdgeWindow ω V k.1 (k.1 + unitVertex k.2)).card : ℝ) ≤ V.volume := fun k _ => by
      have h1 := Finset.card_le_card (coarseEdgeWindow_subset (ω := ω) (U := V) k.1
        (k.1 + unitVertex k.2))
      have h2 : (clusterVertices ω V).card ≤ V.toIntegerCube.vertices.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have h3 := card_toIntegerCube_vertices_eq V
      rw [hvol, ← h3]
      exact_mod_cast h1.trans h2
    have hK0 : 0 ≤ 9 * (2 * V.volume) * V.volume := by positivity
    have hK := fun f w => fieldPairing_sq_le_of_bounds hP hV hN hW f w
    obtain ⟨hu, hv⟩ := planarMuMinimizer_spec hP hV q
    have hv' : ∀ w ∈ clusterHarmonic ω V, clusterForm ω V w (planarMuMinimizer ω V q) =
        fieldPairing ω V (fun _ => q) w := fun w hw => by rw [hv w hw, fieldPairing_const]
    have hB := clusterForm_le_of_variation hu hv' hK0 hK
    have hq := edgeNormSq_const_le V q
    have hgN := edgeNormSq_le (U := V) hg
    have h1 := hK g (planarMuMinimizer ω V q)
    rw [subcubePairing_eq, abs_div, abs_of_pos hv0, div_le_iff₀ hv0]
    rw [← sq_le_sq₀ (abs_nonneg _) (by positivity), sq_abs]
    set Q := |q 0| + |q 1|
    have hQ : 0 ≤ Q := by positivity
    have hn0 := edgeNormSq_nonneg V (fun _ => q)
    have hg0 := edgeNormSq_nonneg V g
    have hB2 : 2 * clusterForm ω V (planarMuMinimizer ω V q) (planarMuMinimizer ω V q) ≤
        2 * (2 * (9 * (2 * V.volume) * V.volume * (2 * V.volume * Q ^ 2))) := by
      have := mul_le_mul_of_nonneg_left hq hK0
      linarith
    have hBn : 0 ≤ 2 * clusterForm ω V (planarMuMinimizer ω V q) (planarMuMinimizer ω V q) := by
      rw [two_mul_clusterForm_self]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine h1.trans ?_
    have hstep : 9 * (2 * V.volume) * V.volume * edgeNormSq V g *
        (2 * clusterForm ω V (planarMuMinimizer ω V q) (planarMuMinimizer ω V q)) ≤
        9 * (2 * V.volume) * V.volume * (2 * V.volume * G ^ 2) * (2 * (2 * (9 * (2 * V.volume) * V.volume * (2 * V.volume * Q ^ 2)))) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hgN hK0) hB2 hBn (by positivity)
    refine hstep.trans (le_of_eq ?_)
    rw [hvol, h81]
    ring
  · have h0 : planarMuMinimizer ω V q = 0 := by rw [planarMuMinimizer, dif_neg hω]
    rw [h0, subcubePairing_eq, map_zero, zero_div, abs_zero]
    positivity

/-- The constant of the weighted bound on the event `PlanarCapGood k V`. -/
theorem switchK_le {k : ℕ} (hk1 : 1 ≤ k) :
    9 * (2 * (10 * (3 : ℝ) ^ k + 3) ^ 2) * (2 * 81 * 9 ^ k) ≤ 352836 * 81 ^ k := by
  have h3 : (3 : ℝ) ≤ 3 ^ k := by
    calc (3 : ℝ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) hk1
  have h1 : (10 * (3 : ℝ) ^ k + 3) ^ 2 ≤ 121 * 9 ^ k := by
    have e : (9 : ℝ) ^ k = (3 ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e]
    nlinarith
  have e2 : (81 : ℝ) ^ k = 9 ^ k * 9 ^ k := by rw [← mul_pow]; norm_num
  rw [e2]
  have h9 : (0 : ℝ) ≤ 9 ^ k := by positivity
  nlinarith

/-- The arithmetic of the pointwise comparison. -/
theorem switch_arith {a K G Q S v Ng Nqq Ngg Nq t : ℝ} (hv : 0 < v)
    (hS : 0 ≤ S) (hNqq0 : 0 ≤ Nqq) (hNq0 : 0 ≤ Nq)
    (ha : a ^ 2 ≤ 8 * K ^ 2 * (Ng * Nqq + Ngg * Nq))
    (h1 : Ng ≤ 2 * v * G ^ 2) (h2 : Nqq ≤ 4 * S * Q ^ 2) (h3 : Ngg ≤ 4 * S * G ^ 2)
    (h4 : Nq ≤ 2 * v * Q ^ 2) (hSv : S ≤ t * v) :
    (a / v) ^ 2 ≤ 128 * K ^ 2 * G ^ 2 * Q ^ 2 * t := by
  have hb : Ng * Nqq + Ngg * Nq ≤ 16 * v * S * G ^ 2 * Q ^ 2 := by
    have e1 : Ng * Nqq ≤ (2 * v * G ^ 2) * (4 * S * Q ^ 2) :=
      mul_le_mul h1 h2 hNqq0 (by positivity)
    have e2 : Ngg * Nq ≤ (4 * S * G ^ 2) * (2 * v * Q ^ 2) :=
      mul_le_mul h3 h4 hNq0 (by positivity)
    nlinarith
  have hc : a ^ 2 ≤ 8 * K ^ 2 * (16 * v * S * G ^ 2 * Q ^ 2) :=
    ha.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  rw [div_pow, div_le_iff₀ (by positivity)]
  have hd : 8 * K ^ 2 * (16 * v * S * G ^ 2 * Q ^ 2) ≤ 128 * K ^ 2 * G ^ 2 * Q ^ 2 * t * v ^ 2 := by
    have : 128 * K ^ 2 * G ^ 2 * Q ^ 2 * t * v ^ 2 = 128 * K ^ 2 * G ^ 2 * Q ^ 2 * v * (t * v) := by
      ring
    rw [this]
    have e : 8 * K ^ 2 * (16 * v * S * G ^ 2 * Q ^ 2) = 128 * K ^ 2 * G ^ 2 * Q ^ 2 * v * S := by
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hSv (by positivity)
  linarith

/-- **The pointwise comparison of display (5.31).** On the event that the partition agrees on `V`
with the partition capped at `k`, the subcube pairing and the localized pairing differ by at most
`C G |q|₁ 3^{9k/2 - n/2}`. -/
theorem sq_sub_switchLocValue_le {k : ℕ} {V : TriadicCube 2} (hω : PlanarCapGood k V ω)
    (hk1 : 1 ≤ k) (hkn : k ≤ V.scale) (h2r : 2 * (6 * 3 ^ k) ≤ 3 ^ V.scale) (q : Fin 2 → ℝ)
    {g : Vertex 2 → Fin 2 → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) :
    (edgePairing V.toIntegerCube.vertices g (coarsen ω V (planarMuMinimizer ω V q)) /
        9 ^ V.scale - switchLocValue k V g q ω) ^ 2 ≤
      128 * 352836 ^ 2 * G ^ 2 * (|q 0| + |q 1|) ^ 2 * (24 * 3 ^ (9 * k) / 3 ^ V.scale) := by
  have hP := hω.1
  have hV := hω.resolved hkn
  have hsc := hω.scale_le
  have hG : 0 ≤ G := (abs_nonneg _).trans (hg 0 0)
  have hN := coarseWeight_le_of_scale_le hP hV hsc
  have hW : ∀ k' ∈ latticeEdgesIn V,
      ((coarseEdgeWindow ω V k'.1 (k'.1 + unitVertex k'.2)).card : ℝ) ≤ 2 * 81 * 9 ^ k := by
    intro k' hk'
    obtain ⟨hk1', hk2'⟩ := Finset.mem_filter.1 hk'
    exact card_coarseEdgeWindow_le_of_scale_le hP hV hsc
      ((V.mem_toIntegerCube_vertices _).1 (Finset.mem_product.1 hk1').1)
      ((V.mem_toIntegerCube_vertices _).1 hk2') (abs_sub_unitVertex_le k'.1 k'.2)
  have hK0 : (0 : ℝ) ≤ 9 * (2 * (10 * 3 ^ k + 3) ^ 2) * (2 * 81 * 9 ^ k) := by positivity
  have hK := fun f w => fieldPairing_sq_le_of_bounds hP hV hN hW f w
  obtain ⟨hu, hv⟩ := planarMuMinimizer_spec hP hV q
  have hv' : ∀ w ∈ clusterHarmonic ω V, clusterForm ω V w (planarMuMinimizer ω V q) =
      fieldPairing ω V (fun _ => q) w := fun w hw => by rw [hv w hw, fieldPairing_const]
  obtain ⟨ul, hul, hvl⟩ :=
    exists_planarMuGen_variation hP hV (restrictField (switchInterior k V) (fun _ => q)) 0
  have hvl' : ∀ w ∈ clusterHarmonic ω V, clusterForm ω V w ul =
      fieldPairing ω V (restrictField (switchInterior k V) (fun _ => q)) w := fun w hw => by
    rw [hvl w hw, fluxPairing_zero, add_zero]
  have hvol : V.volume = (9 : ℝ) ^ V.scale := rfl
  have hv0 : (0 : ℝ) < 9 ^ V.scale := by positivity
  have hΨ : switchLocValue k V g q ω =
      fieldPairing ω V (restrictField (switchInterior k V) g) ul / 9 ^ V.scale := by
    unfold switchLocValue
    rw [if_pos ⟨hP, hV⟩, fieldPairing_eq_planarMuGen hP hV hul hvl, hvol]
    field_simp
  rw [subcubePairing_eq, hΨ, ← sub_div]
  have hcmp := sq_fieldPairing_sub_le (g := g) (g' := restrictField (switchInterior k V) g)
    hu hul hv' hvl' hK0 hK
  have hQ : ∀ x i, |(fun _ : Vertex 2 => q) x i| ≤ |q 0| + |q 1| :=
    fun _ i => abs_le_abs_add_abs q i
  have h1 := edgeNormSq_le (U := V) hg
  have h2 := edgeNormSq_sub_restrictField_le V (switchInterior k V) hQ
  have h3 := edgeNormSq_sub_restrictField_le V (switchInterior k V) hg
  have h4 := (edgeNormSq_restrictField_le V (switchInterior k V) (fun _ => q)).trans
    (edgeNormSq_const_le V q)
  have hS := card_sdiff_interiorCube_le (V := V) h2r
  have hSv : ((V.toIntegerCube.vertices \ switchInterior k V).card : ℝ) ≤
      (24 * 3 ^ k / 3 ^ V.scale) * V.volume := by
    refine hS.trans (le_of_eq ?_)
    rw [hvol]
    have e : (9 : ℝ) ^ V.scale = 3 ^ V.scale * 3 ^ V.scale := by rw [← mul_pow]; norm_num
    rw [e]
    have h3n : (0 : ℝ) < 3 ^ V.scale := by positivity
    field_simp
    push_cast
    ring
  have key := switch_arith hv0
    (Nat.cast_nonneg _) (edgeNormSq_nonneg _ _) (edgeNormSq_nonneg _ _) hcmp (by rw [← hvol]; exact h1) (by exact h2) (by exact h3)
    (by rw [← hvol]; exact h4) (by rw [← hvol]; exact hSv)
  refine key.trans ?_
  have hKle := switchK_le hk1
  have hKsq : (9 * (2 * (10 * (3 : ℝ) ^ k + 3) ^ 2) * (2 * 81 * 9 ^ k)) ^ 2 ≤
      (352836 * 81 ^ k) ^ 2 := pow_le_pow_left₀ hK0 hKle 2
  have e81 : ((352836 : ℝ) * 81 ^ k) ^ 2 * (24 * 3 ^ k / 3 ^ V.scale) =
      352836 ^ 2 * (24 * 3 ^ (9 * k) / 3 ^ V.scale) := by
    have : ((81 : ℝ) ^ k) ^ 2 * 3 ^ k = 3 ^ (9 * k) := by
      rw [← pow_mul, show (81 : ℝ) = 3 ^ 4 by norm_num, ← pow_mul, ← pow_add]
      congr 1
      ring
    rw [mul_pow, ← this]
    ring
  have ht : (0 : ℝ) ≤ 24 * 3 ^ k / 3 ^ V.scale := by positivity
  calc 128 * (9 * (2 * (10 * (3 : ℝ) ^ k + 3) ^ 2) * (2 * 81 * 9 ^ k)) ^ 2 * G ^ 2 *
        (|q 0| + |q 1|) ^ 2 * (24 * 3 ^ k / 3 ^ V.scale)
      ≤ 128 * (352836 * 81 ^ k) ^ 2 * G ^ 2 * (|q 0| + |q 1|) ^ 2 *
          (24 * 3 ^ k / 3 ^ V.scale) := by
        gcongr
    _ = 128 * 352836 ^ 2 * G ^ 2 * (|q 0| + |q 1|) ^ 2 * (24 * 3 ^ (9 * k) / 3 ^ V.scale) := by
        rw [show 128 * ((352836 : ℝ) * 81 ^ k) ^ 2 * G ^ 2 * (|q 0| + |q 1|) ^ 2 *
            (24 * 3 ^ k / 3 ^ V.scale) = 128 * G ^ 2 * (|q 0| + |q 1|) ^ 2 *
            (((352836 : ℝ) * 81 ^ k) ^ 2 * (24 * 3 ^ k / 3 ^ V.scale)) by ring, e81]
        ring

end Rigidity.Proofs.Cluster
