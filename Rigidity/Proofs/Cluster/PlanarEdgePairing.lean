import Rigidity.Proofs.Cluster.PlanarCoarseMeyers

/-!
# Pairings of edge fields with gradients on a square and its boundary layer

For a finite set `D` of vertices of `ℤ²`, a field `g` on the lattice edges `(x, x + e_i)` and a
function `f`, the pairing `⟨∇f, g⟩_D = ∑_{x ∈ D} ∑_i 1{x + e_i ∈ D} g(x, i) (f(x + e_i) - f(x))`
is the quantity `⟨∇[u]_𝒫, g⟩` of Armstrong and Dario (Section 5) when `f` is a coarsened function;
with `g = q` constant it is the coarse pairing `ℓ_q` of `μ`. By the Cauchy–Schwarz inequality, it
is controlled by the edge energy `∑_{x ∈ D} ∑_i 1{x + e_i ∈ D} (f(x + e_i) - f(x))²`, which is at
most twice `∑_{x ∈ D} |∇f|²(x)`. For `B ⊆ V`, the pairing on `V` is the pairing on `B` plus the
pairing over the edges of `V` with an endpoint in `V \ B`, of which there are at most `4 |V \ B|`:
`|⟨∇f, g⟩_V|² ≤ 8 G² |B| ∑_B |∇f|² + 16 G² |V \ B| ∑_V |∇f|²` when `|g| ≤ G`. This is Step 2 of the
proof of Lemma 5.5 of Armstrong and Dario (the removal of the boundary layer `K_z`), in a form
which also serves Step 2 of Lemma 5.7.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation
open scoped BigOperators Classical

/-- The pairing `⟨∇f, g⟩_D` of an edge field with the gradient of `f` over the edges inside `D`. -/
noncomputable def edgePairing (D : Finset (Vertex 2)) (g : Vertex 2 → Fin 2 → ℝ)
    (f : Vertex 2 → ℝ) : ℝ :=
  ∑ x ∈ D, ∑ i : Fin 2, if x + unitVertex i ∈ D then g x i * (f (x + unitVertex i) - f x) else 0

/-- The energy `∑_{x ∈ D} ∑_i 1{x + e_i ∈ D} (f(x + e_i) - f(x))²` of `f` over the edges inside
`D`. -/
noncomputable def edgeEnergy (D : Finset (Vertex 2)) (f : Vertex 2 → ℝ) : ℝ :=
  ∑ x ∈ D, ∑ i : Fin 2, if x + unitVertex i ∈ D then (f (x + unitVertex i) - f x) ^ 2 else 0

theorem edgeEnergy_nonneg (D : Finset (Vertex 2)) (f : Vertex 2 → ℝ) : 0 ≤ edgeEnergy D f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ite_nonneg (sq_nonneg _) le_rfl

/-- The coarse pairing of `μ` is the pairing of the constant field `q` with the gradient of the
coarsened function. -/
theorem coarsePairing_eq_edgePairing {ω : Configuration 2} (U : TriadicCube 2)
    (q : Fin 2 → ℝ) (u : ClusterFun ω U) :
    coarsePairing ω U q u = edgePairing U.toIntegerCube.vertices (fun _ => q)
      (fun x => clusterExtend ω U u (planarCoarseAnchor ω x)) := by
  rw [coarsePairing_apply]
  rfl

theorem unitVertex_zero_ne_one : unitVertex 0 ≠ unitVertex 1 := by
  intro h
  have := congrFun h 0
  simp [unitVertex] at this

theorem nearestNeighborGraph_adj_add_unitVertex (x : Vertex 2) (i : Fin 2) :
    (nearestNeighborGraph 2).Adj x (x + unitVertex i) :=
  ⟨i, Or.inl rfl⟩

/-- **The edge energy and the magnitude of the gradient.**
`∑_{x ∈ D} ∑_i 1{x + e_i ∈ D} (f(x + e_i) - f(x))² ≤ 2 ∑_{x ∈ D} |∇f|²(x)`. -/
theorem edgeEnergy_le_two_mul_sum_gradNormIn_sq (D : Finset (Vertex 2)) (f : Vertex 2 → ℝ) :
    edgeEnergy D f ≤ 2 * ∑ x ∈ D, gradNormIn (nearestNeighborGraph 2) D f x ^ 2 := by
  rw [edgeEnergy, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have hsq : gradNormIn (nearestNeighborGraph 2) D f x ^ 2 = (1 / 2) * ∑ y ∈ D,
      (if (nearestNeighborGraph 2).Adj x y then (f x - f y) ^ 2 else 0) := by
    rw [gradNormIn, Real.sq_sqrt]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => ite_nonneg (sq_nonneg _) le_rfl)
  rw [hsq]
  have hterm : ∀ i : Fin 2, (if x + unitVertex i ∈ D then (f (x + unitVertex i) - f x) ^ 2 else 0)
      = ∑ y ∈ D, if y = x + unitVertex i then (f x - f y) ^ 2 else 0 := by
    intro i
    rw [Finset.sum_ite_eq']
    split_ifs
    · ring
    · rfl
  simp only [hterm]
  rw [Finset.sum_comm, show (2 : ℝ) * (1 / 2 * ∑ y ∈ D, (if (nearestNeighborGraph 2).Adj x y then
    (f x - f y) ^ 2 else 0)) = ∑ y ∈ D, (if (nearestNeighborGraph 2).Adj x y then
    (f x - f y) ^ 2 else 0) by ring]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [Fin.sum_univ_two]
  by_cases h0 : y = x + unitVertex 0
  · have h1 : ¬ y = x + unitVertex 1 := by
      intro h1
      exact unitVertex_zero_ne_one (add_left_cancel (h0.symm.trans h1))
    rw [if_pos h0, if_neg h1, if_pos (h0 ▸ nearestNeighborGraph_adj_add_unitVertex x 0)]
    simp
  · by_cases h1 : y = x + unitVertex 1
    · rw [if_neg h0, if_pos h1, if_pos (h1 ▸ nearestNeighborGraph_adj_add_unitVertex x 1)]
      simp
    · rw [if_neg h0, if_neg h1, zero_add]
      exact ite_nonneg (sq_nonneg _) le_rfl

/-- **Cauchy–Schwarz for the edge pairing.**
`⟨∇f, g⟩_D² ≤ (∑_{x ∈ D} ∑_i 1{x + e_i ∈ D} g(x, i)²) · edgeEnergy D f`. -/
theorem edgePairing_sq_le (D : Finset (Vertex 2)) (g : Vertex 2 → Fin 2 → ℝ)
    (f : Vertex 2 → ℝ) :
    edgePairing D g f ^ 2 ≤
      (∑ x ∈ D, ∑ i : Fin 2, if x + unitVertex i ∈ D then g x i ^ 2 else 0) * edgeEnergy D f := by
  set a : Vertex 2 × Fin 2 → ℝ := fun c =>
    if c.1 + unitVertex c.2 ∈ D then g c.1 c.2 else 0 with ha
  set b : Vertex 2 × Fin 2 → ℝ := fun c =>
    if c.1 + unitVertex c.2 ∈ D then f (c.1 + unitVertex c.2) - f c.1 else 0 with hb
  have h1 : edgePairing D g f = ∑ c ∈ D ×ˢ (Finset.univ : Finset (Fin 2)), a c * b c := by
    rw [edgePairing, Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [ha, hb]
    split_ifs <;> simp
  have h2 : (∑ x ∈ D, ∑ i : Fin 2, if x + unitVertex i ∈ D then g x i ^ 2 else 0) =
      ∑ c ∈ D ×ˢ (Finset.univ : Finset (Fin 2)), a c ^ 2 := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [ha]
    split_ifs <;> simp
  have h3 : edgeEnergy D f = ∑ c ∈ D ×ˢ (Finset.univ : Finset (Fin 2)), b c ^ 2 := by
    rw [edgeEnergy, Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [hb]
    split_ifs <;> simp
  rw [h1, h2, h3]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ a b

/-- The square of a bounded field summed over the edges inside `D` is at most `2 G² |D|`. -/
theorem sum_edge_sq_le (D : Finset (Vertex 2)) {g : Vertex 2 → Fin 2 → ℝ} {G : ℝ}
    (hg : ∀ x i, |g x i| ≤ G) :
    (∑ x ∈ D, ∑ i : Fin 2, if x + unitVertex i ∈ D then g x i ^ 2 else 0) ≤
      2 * G ^ 2 * D.card := by
  have hG : ∀ x i, g x i ^ 2 ≤ G ^ 2 := fun x i => by
    have h := hg x i
    have h0 : 0 ≤ G := (abs_nonneg _).trans h
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  calc (∑ x ∈ D, ∑ i : Fin 2, if x + unitVertex i ∈ D then g x i ^ 2 else 0)
      ≤ ∑ x ∈ D, ∑ _i : Fin 2, G ^ 2 := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · exact hG x i
        · exact sq_nonneg G
    _ = 2 * G ^ 2 * D.card := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The number of edges `(x, x + e_i)` of `V` with an endpoint outside `B` is at most
`4 |V \ B|`. -/
theorem card_layer_edges_le (V B : Finset (Vertex 2)) :
    (∑ x ∈ V, ∑ i : Fin 2,
      if x + unitVertex i ∈ V ∧ ¬ (x ∈ B ∧ x + unitVertex i ∈ B) then (1 : ℝ) else 0) ≤
      4 * (V \ B).card := by
  have hpt : ∀ x i, (if x + unitVertex i ∈ V ∧ ¬ (x ∈ B ∧ x + unitVertex i ∈ B) then (1 : ℝ)
      else 0) ≤ (if x ∉ B then 1 else 0) +
        (if x + unitVertex i ∈ V ∧ x + unitVertex i ∉ B then 1 else 0) := by
    intro x i
    by_cases h1 : x + unitVertex i ∈ V ∧ ¬ (x ∈ B ∧ x + unitVertex i ∈ B)
    · rw [if_pos h1]
      by_cases h2 : x ∈ B
      · have h3 : x + unitVertex i ∈ V ∧ x + unitVertex i ∉ B := ⟨h1.1, fun h => h1.2 ⟨h2, h⟩⟩
        rw [if_neg (not_not.2 h2), if_pos h3]
        norm_num
      · rw [if_pos h2]
        have : (0 : ℝ) ≤ if x + unitVertex i ∈ V ∧ x + unitVertex i ∉ B then 1 else 0 :=
          ite_nonneg zero_le_one le_rfl
        linarith
    · rw [if_neg h1]
      exact add_nonneg (ite_nonneg zero_le_one le_rfl) (ite_nonneg zero_le_one le_rfl)
  have hA : ∀ i : Fin 2, (∑ x ∈ V, (if x ∉ B then (1 : ℝ) else 0)) = (V \ B).card := by
    intro i
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sdiff_eq_filter]
  have hB : ∀ i : Fin 2, (∑ x ∈ V,
      (if x + unitVertex i ∈ V ∧ x + unitVertex i ∉ B then (1 : ℝ) else 0)) ≤ (V \ B).card := by
    intro i
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hinj : Set.InjOn (fun x => x + unitVertex i)
        ↑(V.filter fun x => x + unitVertex i ∈ V ∧ x + unitVertex i ∉ B) :=
      fun x _ y _ h => add_right_cancel h
    have hmaps : ∀ x ∈ V.filter fun x => x + unitVertex i ∈ V ∧ x + unitVertex i ∉ B,
        x + unitVertex i ∈ V \ B := fun x hx => by
      rw [Finset.mem_filter] at hx
      exact Finset.mem_sdiff.2 hx.2
    exact_mod_cast Finset.card_le_card_of_injOn _ hmaps hinj
  calc (∑ x ∈ V, ∑ i : Fin 2,
        if x + unitVertex i ∈ V ∧ ¬ (x ∈ B ∧ x + unitVertex i ∈ B) then (1 : ℝ) else 0)
      ≤ ∑ x ∈ V, ∑ i : Fin 2, ((if x ∉ B then (1 : ℝ) else 0) +
          (if x + unitVertex i ∈ V ∧ x + unitVertex i ∉ B then 1 else 0)) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => hpt x i
    _ = ∑ i : Fin 2, ((∑ x ∈ V, (if x ∉ B then (1 : ℝ) else 0)) +
          ∑ x ∈ V, (if x + unitVertex i ∈ V ∧ x + unitVertex i ∉ B then 1 else 0)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    _ ≤ ∑ _i : Fin 2, (((V \ B).card : ℝ) + (V \ B).card) :=
        Finset.sum_le_sum fun i _ => by rw [hA i]; linarith [hB i]
    _ = 4 * (V \ B).card := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **Removal of the boundary layer** (Step 2 of the proof of Lemma 5.5 of Armstrong and Dario,
in dimension two). For `B ⊆ V` and a field `g` with `|g| ≤ G`,
`⟨∇f, g⟩_V² ≤ 8 G² |B| ∑_{x ∈ B} |∇f|²_B(x) + 16 G² |V \ B| ∑_{x ∈ V} |∇f|²_V(x)`. -/
theorem edgePairing_sq_le_of_subset {V B : Finset (Vertex 2)} (hBV : B ⊆ V)
    {g : Vertex 2 → Fin 2 → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) (f : Vertex 2 → ℝ) :
    edgePairing V g f ^ 2 ≤
      8 * G ^ 2 * B.card * ∑ x ∈ B, gradNormIn (nearestNeighborGraph 2) B f x ^ 2 +
        16 * G ^ 2 * (V \ B).card * ∑ x ∈ V, gradNormIn (nearestNeighborGraph 2) V f x ^ 2 := by
  set L : Vertex 2 → Fin 2 → Prop := fun x i =>
    x + unitVertex i ∈ V ∧ ¬ (x ∈ B ∧ x + unitVertex i ∈ B) with hL
  set layer : ℝ := ∑ x ∈ V, ∑ i : Fin 2,
    if L x i then g x i * (f (x + unitVertex i) - f x) else 0 with hlayer
  have hsplit : edgePairing V g f = edgePairing B g f + layer := by
    have hB0 : edgePairing B g f = ∑ x ∈ V, ∑ i : Fin 2,
        if x ∈ B ∧ x + unitVertex i ∈ B then g x i * (f (x + unitVertex i) - f x) else 0 := by
      rw [edgePairing, ← Finset.sum_filter_add_sum_filter_not V (· ∈ B)]
      have hf : V.filter (· ∈ B) = B := Finset.filter_mem_eq_inter.trans
        (Finset.inter_eq_right.2 hBV)
      rw [hf]
      have hz : ∑ x ∈ V.filter (fun x => ¬ x ∈ B), ∑ i : Fin 2,
          (if x ∈ B ∧ x + unitVertex i ∈ B then g x i * (f (x + unitVertex i) - f x)
            else 0) = 0 :=
        Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun i _ => by
          rw [if_neg fun h => (Finset.mem_filter.1 hx).2 h.1]
      rw [hz, add_zero]
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
      by_cases h : x + unitVertex i ∈ B
      · rw [if_pos h, if_pos ⟨hx, h⟩]
      · rw [if_neg h, if_neg fun h' => h h'.2]
    rw [hB0, hlayer, edgePairing, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hL]
    by_cases h1 : x ∈ B ∧ x + unitVertex i ∈ B
    · rw [if_pos (hBV h1.2), if_pos h1, if_neg fun h => h.2 h1, add_zero]
    · rw [if_neg h1, zero_add]
      by_cases h2 : x + unitVertex i ∈ V
      · rw [if_pos h2, if_pos ⟨h2, h1⟩]
      · rw [if_neg h2, if_neg fun h => h2 h.1]
  -- the layer
  have hlayer_sq : layer ^ 2 ≤ (2 * (4 * G ^ 2 * (V \ B).card)) *
      ∑ x ∈ V, gradNormIn (nearestNeighborGraph 2) V f x ^ 2 := by
    set a : Vertex 2 × Fin 2 → ℝ := fun c => if L c.1 c.2 then g c.1 c.2 else 0 with ha
    set b : Vertex 2 × Fin 2 → ℝ := fun c =>
      if L c.1 c.2 then f (c.1 + unitVertex c.2) - f c.1 else 0 with hb
    have h1 : layer = ∑ c ∈ V ×ˢ (Finset.univ : Finset (Fin 2)), a c * b c := by
      rw [hlayer, Finset.sum_product]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [ha, hb]
      split_ifs <;> simp
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (V ×ˢ (Finset.univ : Finset (Fin 2))) a b
    have ha2 : ∑ c ∈ V ×ˢ (Finset.univ : Finset (Fin 2)), a c ^ 2 ≤ 4 * G ^ 2 * (V \ B).card := by
      have hG : ∀ x i, g x i ^ 2 ≤ G ^ 2 := fun x i => by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hg x i) 2
      have hcnt := card_layer_edges_le V B
      calc ∑ c ∈ V ×ˢ (Finset.univ : Finset (Fin 2)), a c ^ 2
          ≤ ∑ c ∈ V ×ˢ (Finset.univ : Finset (Fin 2)),
              G ^ 2 * (if L c.1 c.2 then (1 : ℝ) else 0) :=
            Finset.sum_le_sum fun c _ => by
              simp only [ha]
              split_ifs
              · rw [mul_one]
                exact hG _ _
              · simp
        _ = G ^ 2 * ∑ x ∈ V, ∑ i : Fin 2, (if L x i then (1 : ℝ) else 0) := by
            rw [← Finset.mul_sum, Finset.sum_product]
        _ ≤ G ^ 2 * (4 * (V \ B).card) := mul_le_mul_of_nonneg_left hcnt (sq_nonneg G)
        _ = 4 * G ^ 2 * (V \ B).card := by ring
    have hb2 : ∑ c ∈ V ×ˢ (Finset.univ : Finset (Fin 2)), b c ^ 2 ≤
        2 * ∑ x ∈ V, gradNormIn (nearestNeighborGraph 2) V f x ^ 2 := by
      refine le_trans ?_ (edgeEnergy_le_two_mul_sum_gradNormIn_sq V f)
      rw [edgeEnergy, Finset.sum_product]
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => ?_
      simp only [hb, hL]
      split_ifs with h h'
      · exact le_rfl
      · exact absurd h.1 h'
      · rw [zero_pow two_ne_zero]
        exact sq_nonneg _
      · simp
    have hb0 : 0 ≤ ∑ c ∈ V ×ˢ (Finset.univ : Finset (Fin 2)), b c ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [h1]
    calc (∑ c ∈ V ×ˢ (Finset.univ : Finset (Fin 2)), a c * b c) ^ 2
        ≤ (∑ c ∈ V ×ˢ (Finset.univ : Finset (Fin 2)), a c ^ 2) *
            ∑ c ∈ V ×ˢ (Finset.univ : Finset (Fin 2)), b c ^ 2 := hcs
      _ ≤ (4 * G ^ 2 * (V \ B).card) *
            (2 * ∑ x ∈ V, gradNormIn (nearestNeighborGraph 2) V f x ^ 2) :=
          mul_le_mul ha2 hb2 hb0 (by positivity)
      _ = (2 * (4 * G ^ 2 * (V \ B).card)) *
            ∑ x ∈ V, gradNormIn (nearestNeighborGraph 2) V f x ^ 2 := by ring
  -- the inner square
  have hinner : edgePairing B g f ^ 2 ≤ (2 * G ^ 2 * B.card) *
      (2 * ∑ x ∈ B, gradNormIn (nearestNeighborGraph 2) B f x ^ 2) :=
    (edgePairing_sq_le B g f).trans (mul_le_mul (sum_edge_sq_le B hg)
      (edgeEnergy_le_two_mul_sum_gradNormIn_sq B f) (edgeEnergy_nonneg B f) (by positivity))
  rw [hsplit]
  have h2 : (edgePairing B g f + layer) ^ 2 ≤ 2 * edgePairing B g f ^ 2 + 2 * layer ^ 2 := by
    nlinarith [sq_nonneg (edgePairing B g f - layer)]
  calc (edgePairing B g f + layer) ^ 2 ≤ 2 * edgePairing B g f ^ 2 + 2 * layer ^ 2 := h2
    _ ≤ 2 * ((2 * G ^ 2 * B.card) * (2 * ∑ x ∈ B, gradNormIn (nearestNeighborGraph 2) B f x ^ 2))
        + 2 * ((2 * (4 * G ^ 2 * (V \ B).card)) *
          ∑ x ∈ V, gradNormIn (nearestNeighborGraph 2) V f x ^ 2) := by
        linarith
    _ = _ := by ring

end Rigidity.Percolation
