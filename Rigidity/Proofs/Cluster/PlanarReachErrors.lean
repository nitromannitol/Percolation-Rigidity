import Rigidity.Proofs.Cluster.PlanarReachEvent
import Rigidity.Proofs.Cluster.PlanarMinimalSet

/-!
# Deterministic error bounds on the event that the reach is small

On the event `PlanarReachLe ω U ℓ` (the planar partition exists and its reach is at most `3^ℓ`
on `U`), the random quantities of Section 5 of Armstrong and Dario are bounded by deterministic
ones, polynomial in `3^ℓ`:

* `-μ(V, q) ≤ 2108304 · 81^ℓ |q|₁²` for every triadic cube `V ⊆ U` of scale at least `ℓ`
  (`neg_planarMu_le_of_planarReachLe`, from the upper bound (4.14) of `-μ` by the reach), hence
  `ρ(V)` is bounded (`planarRho_le_of_planarReachLe`, the bound `ρ ≤ C₁` of Step 1 of the proof of
  Lemma 5.11);
* the error `Y(U)` of the comparison of `μ` and `ν` (Corollary 4.6) is at most
  `10⁹ (ℓ + 1) 729^ℓ 3^{-U.scale/2}` (`planarComparisonError_le_of_planarReachLe`);
* the errors in the subadditivity of `μ` and `ν` over the subcubes of scale `n ≥ ℓ` ((4.30),
  (4.31)) are at most `C (ℓ + 1) 531441^ℓ |q|₁² |U| 3^{-n/2}`
  (`sum_planarMu_subcubes_sub_le_of_planarReachLe`,
  `planarNu_sub_sum_subcubes_le_of_planarReachLe`).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal Matrix

variable {ω : Configuration 2}

theorem sum_le_ofReal_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {b : ℝ}
    (h : ∀ i ∈ s, f i ≤ ENNReal.ofReal b) : ∑ i ∈ s, f i ≤ ENNReal.ofReal (s.card * b) := by
  refine (Finset.sum_le_sum h).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

theorem ennreal_three_pow_eq_ofReal (k : ℕ) :
    (3 : ℝ≥0∞) ^ k = ENNReal.ofReal ((3 : ℝ) ^ k) := by
  rw [ENNReal.ofReal_pow (by norm_num)]
  norm_num

theorem three_pow_pow_eq (k ℓ : ℕ) : ((3 : ℝ) ^ k) ^ ℓ = ((3 ^ k : ℕ) : ℝ) ^ ℓ := by
  norm_cast

/-- The reach sums on the event, as real bounds. -/
theorem reachSum_le_ofReal_of_planarReach_le {a : Vertex 2} {ℓ : ℕ}
    (h : planarReach ω a ≤ 3 ^ ℓ) (k : ℕ) :
    reachSum ω k a ≤ ENNReal.ofReal (121 * (ℓ + 1) * ((3 : ℝ) ^ k) ^ ℓ) := by
  refine (reachSum_le_of_planarReach_le h k).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ← pow_mul,
    ← ennreal_three_pow_eq_ofReal, ENNReal.ofReal_ofNat]
  congr 1
  rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]

theorem mem_of_mem_latticeEdgesIn {U : TriadicCube 2} {k : Vertex 2 × Fin 2}
    (hk : k ∈ latticeEdgesIn U) :
    k.1 ∈ U.toIntegerCube.vertices ∧ k.1 + unitVertex k.2 ∈ U.toIntegerCube.vertices := by
  obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
  exact ⟨(Finset.mem_product.1 hk1).1, hk2⟩

theorem mem_of_mem_boundaryIndex {U : TriadicCube 2} {k : Fin 2 × Bool × Vertex 2}
    (hk : k ∈ boundaryIndex U) : k.2.2 ∈ U.toIntegerCube.vertices :=
  (Finset.mem_product.1 (Finset.mem_product.1 (Finset.mem_filter.1 hk).1).2).2

theorem mem_of_mem_scaleCube {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale) {x z : Vertex 2}
    (hx : x ∈ U.toIntegerCube.vertices) (hz : z ∈ (scaleCube n x).toIntegerCube.vertices) :
    z ∈ U.toIntegerCube.vertices :=
  (U.mem_toIntegerCube_vertices z).2 (scaleCube_subset hn ((U.mem_toIntegerCube_vertices x).1 hx)
    (((scaleCube n x).mem_toIntegerCube_vertices z).1 hz))

/-- **Upper bound for `-μ` on the event.** -/
theorem neg_planarMu_le_of_planarReachLe {U V : TriadicCube 2} {ℓ : ℕ}
    (h : PlanarReachLe ω U ℓ) (hV : V.vertices ⊆ U.vertices) (hℓ : ℓ ≤ V.scale)
    (q : Fin 2 → ℝ) : -planarMu ω V q ≤ 2108304 * 81 ^ ℓ * (|q 0| + |q 1|) ^ 2 := by
  have hres := planarResolved_of_planarReachLe h hV hℓ
  have hmu := ofReal_neg_planarMu_le h.1 hres q
  have hvol := V.volume_pos
  have hR : ∀ a ∈ V.toIntegerCube.vertices,
      234256 * planarReach ω a ^ 4 ≤ ENNReal.ofReal (234256 * 81 ^ ℓ) := by
    intro a ha
    have ha' : a ∈ U.toIntegerCube.vertices :=
      (U.mem_toIntegerCube_vertices a).2 (hV ((V.mem_toIntegerCube_vertices a).1 ha))
    have h1 : planarReach ω a ≤ ENNReal.ofReal ((3 : ℝ) ^ ℓ) := by
      rw [← ennreal_three_pow_eq_ofReal]
      exact h.2 a ha'
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      show (81 : ℝ) ^ ℓ = ((3 : ℝ) ^ ℓ) ^ 4 by rw [← pow_mul, pow_mul']; norm_num,
      ENNReal.ofReal_pow (by positivity)]
    gcongr
  have hsum := sum_le_ofReal_card_mul _ _ hR
  rw [card_toIntegerCube_vertices_eq] at hsum
  have h2 : ENNReal.ofReal (-planarMu ω V q) ≤
      ENNReal.ofReal (9 * (|q 0| + |q 1|) ^ 2 / V.volume) *
        ENNReal.ofReal ((9 : ℝ) ^ V.scale * (234256 * 81 ^ ℓ)) := hmu.trans (by gcongr)
  rw [← ENNReal.ofReal_mul (by positivity)] at h2
  have e : 9 * (|q 0| + |q 1|) ^ 2 / V.volume * ((9 : ℝ) ^ V.scale * (234256 * 81 ^ ℓ)) =
      2108304 * 81 ^ ℓ * (|q 0| + |q 1|) ^ 2 := by
    have : V.volume = (9 : ℝ) ^ V.scale := rfl
    rw [this]
    field_simp
    ring
  rw [e] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

theorem abs_dotProduct_le (q w : Fin 2 → ℝ) :
    |∑ i, q i * w i| ≤ (|q 0| + |q 1|) * (|w 0| + |w 1|) := by
  rw [Fin.sum_univ_two]
  calc |q 0 * w 0 + q 1 * w 1| ≤ |q 0| * |w 0| + |q 1| * |w 1| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ _ := by nlinarith [abs_nonneg (q 0), abs_nonneg (q 1), abs_nonneg (w 0), abs_nonneg (w 1)]

theorem l1_sq_le_two_mul (q : Fin 2 → ℝ) : (|q 0| + |q 1|) ^ 2 ≤ 2 * (q 0 ^ 2 + q 1 ^ 2) := by
  have h0 := sq_abs (q 0)
  have h1 := sq_abs (q 1)
  nlinarith [sq_nonneg (|q 0| - |q 1|)]

/-- **The bound `ρ ≤ C₁` on the event** (Step 1 of the proof of Lemma 5.11). -/
theorem planarRho_le_of_planarReachLe (p : unitInterval) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ v : Fin 2 → ℝ, |((planarAhom p)⁻¹ *ᵥ v) 0| + |((planarAhom p)⁻¹ *ᵥ v) 1| ≤
      S * (|v 0| + |v 1|))
    {U V : TriadicCube 2} {ℓ : ℕ} (h : PlanarReachLe ω U ℓ) (hV : V.vertices ⊆ U.vertices)
    (hℓ : ℓ ≤ V.scale) :
    planarRho p ω V ≤ 2 * (9 / 4 * S ^ 2 + 2108304 * 81 ^ ℓ + S) := by
  have hres := planarResolved_of_planarReachLe h hV hℓ
  refine planarRho_le (by positivity) fun q => max_le ?_ (by positivity)
  have hc : PlanarPartitionEvent ω ∧ PlanarResolved ω V := ⟨h.1, hres⟩
  unfold planarOmega
  rw [if_pos hc, if_pos hc]
  have hw := hS q
  have hν := planarNu_le (ω := ω) (U := V) ((planarAhom p)⁻¹ *ᵥ q)
  have hμ := neg_planarMu_le_of_planarReachLe h hV hℓ q
  have hd := abs_dotProduct_le q ((planarAhom p)⁻¹ *ᵥ q)
  have hQ0 : 0 ≤ |q 0| + |q 1| := by positivity
  have hw0 : 0 ≤ |((planarAhom p)⁻¹ *ᵥ q) 0| + |((planarAhom p)⁻¹ *ᵥ q) 1| := by positivity
  have hw2 := pow_le_pow_left₀ hw0 hw 2
  have hl := l1_sq_le_two_mul q
  have hdot : -∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i ≤ S * (|q 0| + |q 1|) ^ 2 := by
    have h1 := neg_le_abs (∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i)
    have h2 := mul_le_mul_of_nonneg_left hw hQ0
    nlinarith
  have hB := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ 9 / 4 * S ^ 2 + 2108304 * 81 ^ ℓ + S by positivity)
  nlinarith

/-- **The comparison error on the event.** -/
theorem planarComparisonError_le_of_planarReachLe {U : TriadicCube 2} {ℓ : ℕ}
    (h : PlanarReachLe ω U ℓ) :
    planarComparisonError ω U ≤
      ENNReal.ofReal (10 ^ 9 * (ℓ + 1) * 729 ^ ℓ / Real.sqrt ((3 : ℝ) ^ U.scale)) := by
  unfold planarComparisonError
  have hs0 : 0 < Real.sqrt ((3 : ℝ) ^ U.scale) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt ((3 : ℝ) ^ U.scale) ^ 2 = 3 ^ U.scale := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ Real.sqrt ((3 : ℝ) ^ U.scale) := Real.one_le_sqrt.2 (one_le_pow₀ (by norm_num))
  generalize Real.sqrt ((3 : ℝ) ^ U.scale) = s at hs0 hs2 hs1 ⊢
  generalize hn : U.scale = n at hs0 hs2 hs1 ⊢
  have hs3 : s ≤ 3 ^ n := by nlinarith
  have h4 : ∀ a ∈ U.toIntegerCube.vertices,
      reachSum ω 4 a ≤ ENNReal.ofReal (121 * (ℓ + 1) * 81 ^ ℓ) := fun a ha => by
    have := reachSum_le_ofReal_of_planarReach_le (h.2 a ha) 4
    rwa [three_pow_pow_eq, show ((3 ^ 4 : ℕ) : ℝ) = 81 by norm_num] at this
  have h6 : ∀ a ∈ U.toIntegerCube.vertices,
      ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * reachSum ω 6 a ≤
        ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1)) * (121 * (ℓ + 1) * 729 ^ ℓ)) := fun a ha => by
    have := reachSum_le_ofReal_of_planarReach_le (h.2 a ha) 6
    rw [three_pow_pow_eq, show ((3 ^ 6 : ℕ) : ℝ) = 729 by norm_num] at this
    rw [ENNReal.ofReal_mul (by positivity)]
    gcongr
  have hb := sum_le_ofReal_card_mul (boundaryIndex U) (fun k => reachSum ω 4 k.2.2)
    fun k hk => h4 k.2.2 (mem_of_mem_boundaryIndex hk)
  have hz := sum_le_ofReal_card_mul U.toIntegerCube.vertices _ h6
  have hcb := card_boundaryIndex_le U
  have hcU : ((U.toIntegerCube.vertices.card : ℕ) : ℝ) = 9 ^ n := by
    rw [card_toIntegerCube_vertices_eq, hn]
  have hsize : (U.toIntegerCube.size : ℝ) = 3 ^ n := by
    change ((3 ^ U.scale : ℕ) : ℝ) = _
    push_cast
    rw [hn]
  rw [hsize] at hcb
  refine (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hb zero_le)) hz).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [hcU]
  set A : ℝ := (ℓ + 1) * 729 ^ ℓ with hA
  have hA1 : 1 ≤ A := by
    have : (1 : ℝ) ≤ 729 ^ ℓ := one_le_pow₀ (by norm_num)
    have : (1 : ℝ) ≤ ℓ + 1 := by linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
    nlinarith
  have h81 : (ℓ + 1 : ℝ) * 81 ^ ℓ ≤ A := by
    have : (81 : ℝ) ^ ℓ ≤ 729 ^ ℓ := pow_le_pow_left₀ (by norm_num) (by norm_num) ℓ
    have : (0 : ℝ) ≤ ℓ + 1 := by positivity
    rw [hA]
    exact mul_le_mul_of_nonneg_left (by assumption) this
  -- the three terms
  have t1 : 1 / (3 : ℝ) ^ n + 9 * (1 / 2 / s) ≤ 6 * A / s := by
    rw [le_div_iff₀ hs0]
    have : 1 / (3 : ℝ) ^ n * s ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      exact hs3
    have e : 9 * (1 / 2 / s) * s = 9 / 2 := by field_simp
    nlinarith
  have t2 : 9 * 162001 / ((3 : ℝ) ^ n * s) *
      ((boundaryIndex U).card * (121 * (ℓ + 1) * 81 ^ ℓ)) ≤ 705676356 * A / s := by
    have hc : ((boundaryIndex U).card : ℝ) * (121 * ((ℓ + 1) * 81 ^ ℓ)) ≤
        4 * 3 ^ n * (121 * A) :=
      mul_le_mul hcb (by linarith) (by positivity) (by positivity)
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hs0]
    have : (9 : ℝ) * 162001 * ((boundaryIndex U).card * (121 * (ℓ + 1) * 81 ^ ℓ)) * s ≤
        9 * 162001 * (4 * 3 ^ n * (121 * A)) * s := by
      have := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 9 * 162001 by norm_num)
      nlinarith
    nlinarith
  have t3 : (9 : ℝ) ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1)) * (121 * (ℓ + 1) * 729 ^ ℓ)) ≤
      121 * A / s := by
    rw [le_div_iff₀ hs0]
    have h9 : (9 : ℝ) ^ n * s ≤ 3 ^ (6 * (n + 1)) := by
      have e : (9 : ℝ) ^ n = 3 ^ (2 * n) := by rw [pow_mul]; norm_num
      rw [e]
      calc (3 : ℝ) ^ (2 * n) * s ≤ 3 ^ (2 * n) * 3 ^ n :=
            mul_le_mul_of_nonneg_left hs3 (by positivity)
        _ = 3 ^ (3 * n) := by rw [← pow_add]; ring_nf
        _ ≤ 3 ^ (6 * (n + 1)) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e : (9 : ℝ) ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1)) * (121 * (ℓ + 1) * 729 ^ ℓ)) * s =
        (9 ^ n * s) / 3 ^ (6 * (n + 1)) * (121 * A) := by
      rw [hA]; ring
    rw [e]
    have : (9 : ℝ) ^ n * s / 3 ^ (6 * (n + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact h9
    nlinarith
  have : 6 * A / s + 705676356 * A / s + 121 * A / s ≤ 10 ^ 9 * (ℓ + 1) * 729 ^ ℓ / s := by
    rw [← add_div, ← add_div, mul_assoc]
    apply div_le_div_of_nonneg_right _ hs0.le
    rw [← hA]
    nlinarith
  linarith

theorem partSide_pow_le_of_planarReachLe {U : TriadicCube 2} {ℓ : ℕ} (h : PlanarReachLe ω U ℓ)
    {a : Vertex 2} (ha : a ∈ U.toIntegerCube.vertices) (k : ℕ) :
    partSide ω a ^ k ≤ ((3 : ℝ) ^ k) ^ ℓ := by
  have h1 := pow_le_pow_left₀ (by linarith [one_le_partSide (ω := ω) a])
    (partSide_le_of_planarReach_le h.1 (h.2 a ha)) k
  rwa [← pow_mul, mul_comm, pow_mul] at h1

theorem card_scaleCube_vertices (n : ℕ) (x : Vertex 2) :
    (((scaleCube n x).toIntegerCube.vertices.card : ℕ) : ℝ) = (9 : ℝ) ^ n := by
  rw [card_toIntegerCube_vertices_eq, scale_scaleCube]

theorem edgeSideSum_le_of_planarReachLe {U : TriadicCube 2} {ℓ : ℕ} (h : PlanarReachLe ω U ℓ)
    {F : Finset (Vertex 2 × Fin 2)} (hF : F ⊆ latticeEdgesIn U) :
    edgeSideSum ω F ≤ F.card * (2 * 729 ^ ℓ) := by
  unfold edgeSideSum
  refine (Finset.sum_le_sum fun k hk => ?_).trans (le_of_eq (by rw [Finset.sum_const,
    nsmul_eq_mul]))
  obtain ⟨h1, h2⟩ := mem_of_mem_latticeEdgesIn (hF hk)
  have a1 := partSide_pow_le_of_planarReachLe h h2 6
  have a2 := partSide_pow_le_of_planarReachLe h h1 6
  rw [three_pow_pow_eq, show ((3 ^ 6 : ℕ) : ℝ) = 729 by norm_num] at a1 a2
  linarith

/-- **The error in the subadditivity of `μ` on the event** ((4.30) with a deterministic error). -/
theorem sum_planarMu_subcubes_sub_le_of_planarReachLe {U : TriadicCube 2} {ℓ n : ℕ}
    (h : PlanarReachLe ω U ℓ) (hℓn : ℓ ≤ n) (hn : n ≤ U.scale) (q : Fin 2 → ℝ) :
    ∑ x ∈ U.toIntegerCube.vertices,
        (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) -
      planarMu ω U q * U.volume ≤
      2 * 10 ^ 10 * 531441 ^ ℓ * (|q 0| + |q 1|) ^ 2 * U.volume / Real.sqrt ((3 : ℝ) ^ n) := by
  have hU := planarResolved_of_planarReachLe h (subset_refl _) (hℓn.trans hn)
  have hbase := sum_planarMu_subcubes_sub_le h.1 hU hn q
  set s := Real.sqrt ((3 : ℝ) ^ n) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 3 ^ n := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by
    rw [hs]
    exact Real.one_le_sqrt.2 (one_le_pow₀ (by norm_num))
  have hs3 : s ≤ 3 ^ n := by nlinarith
  have hvol := U.volume_pos
  set E := latticeEdgesIn U with hE
  have hcE : (E.card : ℝ) ≤ 2 * U.volume := card_latticeEdgesIn_le U
  have hcC := card_subcubeCrossingEdges_le hn
  have hall := edgeSideSum_le_of_planarReachLe h (subset_refl E)
  have hcross := edgeSideSum_le_of_planarReachLe h (F := subcubeCrossingEdges U n)
    (Finset.filter_subset _ _)
  have hsec : ∑ k ∈ E, ∑ z ∈ (scaleCube n k.1).toIntegerCube.vertices,
      (1 / (3 : ℝ) ^ (6 * (n + 1))) * (partSide ω z ^ 12 +
        (partSide ω (k.1 + unitVertex k.2) ^ 12 + partSide ω k.1 ^ 12)) ≤
      E.card * ((9 : ℝ) ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1)) * (3 * 531441 ^ ℓ))) := by
    refine (Finset.sum_le_sum fun k hk => ?_).trans (le_of_eq (by rw [Finset.sum_const,
      nsmul_eq_mul]))
    obtain ⟨h1, h2⟩ := mem_of_mem_latticeEdgesIn hk
    rw [← card_scaleCube_vertices n k.1, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun z hz => ?_
    have hzU := mem_of_mem_scaleCube hn h1 hz
    have a0 := partSide_pow_le_of_planarReachLe h hzU 12
    have a1 := partSide_pow_le_of_planarReachLe h h2 12
    have a2 := partSide_pow_le_of_planarReachLe h h1 12
    rw [three_pow_pow_eq, show ((3 ^ 12 : ℕ) : ℝ) = 531441 by norm_num] at a0 a1 a2
    gcongr
    linarith
  have hF := (edgeSideSum_exceptional_le (ω := ω) (U := U) (n := n)).trans (add_le_add hcross hsec)
  set Q₁ := (|q 0| + |q 1|) ^ 2 with hQ₁
  have hQ0 : 0 ≤ Q₁ := by positivity
  set B : ℝ := 531441 ^ ℓ with hB
  have h729 : (729 : ℝ) ^ ℓ ≤ B := pow_le_pow_left₀ (by norm_num) (by norm_num) ℓ
  have hB0 : 0 ≤ (729 : ℝ) ^ ℓ := by positivity
  -- the bound of the bracket
  have k1 : 729000000 * s * ((subcubeCrossingEdges U n).card * (2 * 729 ^ ℓ)) ≤
      2916000000 * B * U.volume / s := by
    rw [le_div_iff₀ hs0]
    have : ((subcubeCrossingEdges U n).card : ℝ) * s ^ 2 ≤ 2 * U.volume := by rw [hs2]; exact hcC
    nlinarith [mul_le_mul_of_nonneg_left this hB0, mul_le_mul_of_nonneg_right h729 hvol.le]
  have k2 : 729000000 * s * (E.card * ((9 : ℝ) ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1)) *
      (3 * 531441 ^ ℓ)))) ≤ 4374000000 * B * U.volume / s := by
    rw [le_div_iff₀ hs0]
    have h9 : (9 : ℝ) ^ n * s ^ 2 ≤ 3 ^ (6 * (n + 1)) := by
      rw [hs2, show (9 : ℝ) ^ n = 3 ^ (2 * n) by rw [pow_mul]; norm_num, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have e : 729000000 * s * (E.card * ((9 : ℝ) ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1)) *
        (3 * 531441 ^ ℓ)))) * s =
        2187000000 * B * E.card * ((9 ^ n * s ^ 2) / 3 ^ (6 * (n + 1))) := by
      rw [hB]; ring
    rw [e]
    have : (9 : ℝ) ^ n * s ^ 2 / 3 ^ (6 * (n + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact h9
    have hB1 : 0 ≤ B := by positivity
    have := mul_le_mul_of_nonneg_left this (show 0 ≤ 2187000000 * B * E.card by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hcE hB1]
  have k3 : 2916000000 / s * (E.card * (2 * 729 ^ ℓ)) ≤ 11664000000 * B * U.volume / s := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hs0.le
    nlinarith [mul_le_mul hcE h729 hB0 (by positivity)]
  have hbr : 729000000 * s * edgeSideSum ω (subcubeExceptionalEdges ω U n) +
      2916000000 / s * edgeSideSum ω E ≤ 2 * 10 ^ 10 * B * U.volume / s := by
    have e1 := mul_le_mul_of_nonneg_left hF (show 0 ≤ 729000000 * s by positivity)
    have e2 := mul_le_mul_of_nonneg_left hall (show 0 ≤ 2916000000 / s by positivity)
    have : 2916000000 * B * U.volume / s + 4374000000 * B * U.volume / s +
        11664000000 * B * U.volume / s ≤ 2 * 10 ^ 10 * B * U.volume / s := by
      rw [← add_div, ← add_div]
      apply div_le_div_of_nonneg_right _ hs0.le
      have : 0 ≤ B * U.volume := by positivity
      nlinarith
    rw [mul_add] at e1
    linarith
  calc _ ≤ Q₁ * (729000000 * s * edgeSideSum ω (subcubeExceptionalEdges ω U n) +
        2916000000 / s * edgeSideSum ω E) := hbase
    _ ≤ Q₁ * (2 * 10 ^ 10 * B * U.volume / s) := mul_le_mul_of_nonneg_left hbr hQ0
    _ = _ := by ring

set_option maxHeartbeats 400000 in
/-- **The error in the subadditivity of `ν` on the event** ((4.31) with a deterministic error). -/
theorem planarNu_sub_sum_subcubes_le_of_planarReachLe {U : TriadicCube 2} {ℓ n : ℕ}
    (h : PlanarReachLe ω U ℓ) (hℓn : ℓ ≤ n) (hn : n ≤ U.scale) (ξ : Fin 2 → ℝ) :
    planarNu ω U ξ * U.volume - ∑ x ∈ U.toIntegerCube.vertices,
        (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0) ≤
      132100 * (ℓ + 1) * 729 ^ ℓ * (|ξ 0| + |ξ 1|) ^ 2 * U.volume /
        Real.sqrt ((3 : ℝ) ^ n) := by
  have hU := planarResolved_of_planarReachLe h (subset_refl _) (hℓn.trans hn)
  set P₁ := |ξ 0| + |ξ 1| with hP₁
  set s := Real.sqrt ((3 : ℝ) ^ n) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 3 ^ n := Real.sq_sqrt (by positivity)
  have hvol := U.volume_pos
  have hP0 : 0 ≤ P₁ := by positivity
  set G := ∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x with hG
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun x _ => exceptionalIndicator_nonneg n x
  -- the optimized Young bound
  have hb : planarNu ω U ξ * U.volume - ∑ x ∈ U.toIntegerCube.vertices,
        (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0) ≤
      9 / 4 * P₁ ^ 2 * s * G + 9 / 4 * (P₁ ^ 2 * U.volume / s) := by
    rcases hP0.eq_or_lt with hz | hpos
    · have hy := planarNu_mul_volume_le_young h.1 hU hn ξ (t := 1) one_pos
      rw [← hP₁, ← hG, ← hz] at hy
      rw [← hz]
      have e0 : (0 : ℝ) * (9 * G / 1 + 1 * (9 * 0 ^ 2 * U.volume)) / 4 = 0 := by ring
      have e1 : 9 / 4 * (0 : ℝ) ^ 2 * s * G + 9 / 4 * (0 ^ 2 * U.volume / s) = 0 := by ring
      rw [e0] at hy
      rw [e1]
      linarith
    · have ht : 0 < 1 / (P₁ * s) := by positivity
      have hy := planarNu_mul_volume_le_young h.1 hU hn ξ ht
      rw [← hP₁, ← hG] at hy
      have e : P₁ * (9 * G / (1 / (P₁ * s)) + 1 / (P₁ * s) * (9 * P₁ ^ 2 * U.volume)) / 4 =
          9 / 4 * P₁ ^ 2 * s * G + 9 / 4 * (P₁ ^ 2 * U.volume / s) := by
        field_simp
      rw [e] at hy
      linarith
  -- the number of exceptional vertices
  set A : ℝ := (ℓ + 1) * 729 ^ ℓ with hA
  have hA1 : 1 ≤ A := by
    have : (1 : ℝ) ≤ 729 ^ ℓ := one_le_pow₀ (by norm_num)
    have : (1 : ℝ) ≤ ℓ + 1 := by linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
    nlinarith
  have h9A : (ℓ + 1 : ℝ) * 9 ^ ℓ ≤ A := by
    have : (9 : ℝ) ^ ℓ ≤ 729 ^ ℓ := pow_le_pow_left₀ (by norm_num) (by norm_num) ℓ
    have : (0 : ℝ) ≤ ℓ + 1 := by positivity
    rw [hA]
    exact mul_le_mul_of_nonneg_left (by assumption) this
  have hcnt : ENNReal.ofReal G ≤ ENNReal.ofReal (U.volume * ((9 : ℝ) ^ n *
      (1 / (3 : ℝ) ^ (6 * (n + 1)) * (121 * (ℓ + 1) * 729 ^ ℓ))) +
      (subcubesAt U n).card * (4 * 3 ^ n * (121 * (121 * (ℓ + 1) * 9 ^ ℓ)))) := by
    refine (ofReal_sum_exceptionalIndicator_le h.1 hn).trans ?_
    unfold exceptionalCountBound
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    refine add_le_add ?_ ?_
    · have h1 : ∀ x ∈ U.toIntegerCube.vertices, ∑ z ∈ (scaleCube n x).toIntegerCube.vertices,
          ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * reachSum ω 6 z ≤
          ENNReal.ofReal ((9 : ℝ) ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1)) *
            (121 * (ℓ + 1) * 729 ^ ℓ))) := by
        intro x hx
        rw [← card_scaleCube_vertices n x]
        refine sum_le_ofReal_card_mul _ _ fun z hz => ?_
        have := reachSum_le_ofReal_of_planarReach_le (h.2 z (mem_of_mem_scaleCube hn hx hz)) 6
        rw [three_pow_pow_eq, show ((3 ^ 6 : ℕ) : ℝ) = 729 by norm_num] at this
        rw [ENNReal.ofReal_mul (by positivity)]
        gcongr
      have := sum_le_ofReal_card_mul _ _ h1
      rwa [card_toIntegerCube_vertices_eq] at this
    · refine sum_le_ofReal_card_mul _ _ fun V hV => ?_
      have hVs := scale_of_mem_subcubesAt hV
      have hVU := subset_of_mem_subcubesAt hn hV
      have hcb := card_boundaryIndex_le V
      have hsize : (V.toIntegerCube.size : ℝ) = 3 ^ n := by
        change ((3 ^ V.scale : ℕ) : ℝ) = _
        rw [hVs]
        push_cast
        rfl
      rw [hsize] at hcb
      refine (sum_le_ofReal_card_mul _ _ fun k hk => ?_).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcb (by positivity)))
      have hkU : k.2.2 ∈ U.toIntegerCube.vertices :=
        (U.mem_toIntegerCube_vertices _).2 (hVU ((V.mem_toIntegerCube_vertices _).1
          (mem_of_mem_boundaryIndex hk)))
      have := reachSum_le_ofReal_of_planarReach_le (h.2 _ hkU) 2
      rw [three_pow_pow_eq, show ((3 ^ 2 : ℕ) : ℝ) = 9 by norm_num] at this
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      gcongr
  have hGle := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hcnt
  have hsub : ((subcubesAt U n).card : ℝ) * (9 : ℝ) ^ n = U.volume := card_subcubesAt_mul hn
  -- the two parts of `s G`
  have g1 : s * (U.volume * ((9 : ℝ) ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1)) *
      (121 * (ℓ + 1) * 729 ^ ℓ)))) ≤ 121 * A * U.volume / s := by
    rw [le_div_iff₀ hs0]
    have h9 : (9 : ℝ) ^ n * s ^ 2 ≤ 3 ^ (6 * (n + 1)) := by
      rw [hs2, show (9 : ℝ) ^ n = 3 ^ (2 * n) by rw [pow_mul]; norm_num, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have e : s * (U.volume * ((9 : ℝ) ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1)) *
        (121 * (ℓ + 1) * 729 ^ ℓ)))) * s =
        121 * A * U.volume * ((9 ^ n * s ^ 2) / 3 ^ (6 * (n + 1))) := by
      rw [hA]; ring
    rw [e]
    have : (9 : ℝ) ^ n * s ^ 2 / 3 ^ (6 * (n + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact h9
    have := mul_le_mul_of_nonneg_left this (show 0 ≤ 121 * A * U.volume by positivity)
    linarith
  have g2 : s * ((subcubesAt U n).card * (4 * 3 ^ n * (121 * (121 * (ℓ + 1) * 9 ^ ℓ)))) ≤
      58564 * A * U.volume / s := by
    rw [le_div_iff₀ hs0]
    have e : s * ((subcubesAt U n).card * (4 * 3 ^ n * (121 * (121 * (ℓ + 1) * 9 ^ ℓ)))) * s =
        58564 * ((ℓ + 1) * 9 ^ ℓ) * ((subcubesAt U n).card * (9 : ℝ) ^ n) := by
      rw [show (9 : ℝ) ^ n = 3 ^ n * 3 ^ n by rw [← mul_pow]; norm_num]
      rw [← hs2]
      ring
    rw [e, hsub]
    have := mul_le_mul_of_nonneg_right h9A hvol.le
    nlinarith
  have hsG : s * G ≤ 58685 * A * U.volume / s := by
    have := mul_le_mul_of_nonneg_left hGle hs0.le
    rw [mul_add] at this
    have : 121 * A * U.volume / s + 58564 * A * U.volume / s = 58685 * A * U.volume / s := by
      rw [← add_div]; ring_nf
    linarith
  have hlast : 9 / 4 * (P₁ ^ 2 * U.volume / s) ≤ 9 / 4 * (A * P₁ ^ 2 * U.volume / s) := by
    gcongr
    nlinarith [sq_nonneg P₁]
  calc _ ≤ 9 / 4 * P₁ ^ 2 * s * G + 9 / 4 * (P₁ ^ 2 * U.volume / s) := hb
    _ ≤ 9 / 4 * P₁ ^ 2 * (58685 * A * U.volume / s) + 9 / 4 * (A * P₁ ^ 2 * U.volume / s) := by
        have := mul_le_mul_of_nonneg_left hsG (show 0 ≤ 9 / 4 * P₁ ^ 2 by positivity)
        nlinarith
    _ ≤ _ := by
        rw [hA]
        have : 0 ≤ (ℓ + 1 : ℝ) * 729 ^ ℓ * P₁ ^ 2 * U.volume / s := by positivity
        have e : 9 / 4 * P₁ ^ 2 * (58685 * ((ℓ + 1) * 729 ^ ℓ) * U.volume / s) +
            9 / 4 * ((ℓ + 1) * 729 ^ ℓ * P₁ ^ 2 * U.volume / s) =
            132043.5 * ((ℓ + 1 : ℝ) * 729 ^ ℓ * P₁ ^ 2 * U.volume / s) := by ring
        rw [e]
        have e2 : 132100 * (ℓ + 1 : ℝ) * 729 ^ ℓ * P₁ ^ 2 * U.volume / s =
            132100 * ((ℓ + 1 : ℝ) * 729 ^ ℓ * P₁ ^ 2 * U.volume / s) := by ring
        rw [e2]
        linarith

/-- The arithmetic of the errors in the subadditivity of `ρ`. -/
theorem rho_error_arith {S a b q2 A7 B AB vol s : ℝ} (ha : a ≤ S ^ 2 * b)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hb : b ≤ 2 * q2) (hA7 : A7 ≤ AB) (hA70 : 0 ≤ A7) (hB : B ≤ AB)
    (hvol : 0 < vol) (hs : 0 < s) :
    132100 * A7 * a * vol / s + 2 * 10 ^ 10 * B * b * vol / s ≤
      2 * (132100 * S ^ 2 + 2 * 10 ^ 10) * AB / s * vol * q2 := by
  have hAB : 0 ≤ AB := hA70.trans hA7
  have h1 : A7 * a ≤ AB * (S ^ 2 * b) := mul_le_mul hA7 ha ha0 hAB
  have h2 : B * b ≤ AB * b := mul_le_mul_of_nonneg_right hB hb0
  have h3 : (132100 * S ^ 2 + 2 * 10 ^ 10) * AB * b ≤
      (132100 * S ^ 2 + 2 * 10 ^ 10) * AB * (2 * q2) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have h4 : 132100 * A7 * a + 2 * 10 ^ 10 * B * b ≤
      2 * (132100 * S ^ 2 + 2 * 10 ^ 10) * AB * q2 := by linarith
  calc 132100 * A7 * a * vol / s + 2 * 10 ^ 10 * B * b * vol / s
      = (132100 * A7 * a + 2 * 10 ^ 10 * B * b) * vol / s := by ring
    _ ≤ (2 * (132100 * S ^ 2 + 2 * 10 ^ 10) * AB * q2) * vol / s :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hvol.le) hs.le
    _ = _ := by ring

set_option maxHeartbeats 400000 in
/-- **Subadditivity of `ρ` on the event** (display (5.55) of Armstrong and Dario, `e.rhosubadd`,
with deterministic errors): `ρ(U)` is at most the average of `ρ` over the subcubes of scale `n`
plus `C (ℓ + 1) 531441^ℓ 3^{-n/2}`. -/
theorem planarRho_le_avg_of_planarReachLe (p : unitInterval) {S : ℝ}
    (hS : ∀ v : Fin 2 → ℝ, |((planarAhom p)⁻¹ *ᵥ v) 0| + |((planarAhom p)⁻¹ *ᵥ v) 1| ≤
      S * (|v 0| + |v 1|))
    {U : TriadicCube 2} {ℓ n : ℕ} (h : PlanarReachLe ω U ℓ) (hℓn : ℓ ≤ n) (hn : n ≤ U.scale) :
    planarRho p ω U ≤ (∑ V ∈ subcubesAt U n, planarRho p ω V) / (subcubesAt U n).card +
      2 * (132100 * S ^ 2 + 2 * 10 ^ 10) * (ℓ + 1) * 531441 ^ ℓ / Real.sqrt ((3 : ℝ) ^ n) := by
  have hU := planarResolved_of_planarReachLe h (subset_refl _) (hℓn.trans hn)
  have hres : ∀ x ∈ U.toIntegerCube.vertices, PlanarResolved ω (scaleCube n x) := fun x hx =>
    planarResolved_of_planarReachLe h (scaleCube_subset hn ((U.mem_toIntegerCube_vertices x).1 hx))
      (by rw [scale_scaleCube]; exact hℓn)
  have hs0 : 0 < Real.sqrt ((3 : ℝ) ^ n) := Real.sqrt_pos.2 (by positivity)
  have hvol := U.volume_pos
  have hsub : ((subcubesAt U n).card : ℝ) * (9 : ℝ) ^ n = U.volume := card_subcubesAt_mul hn
  have hcard : (0 : ℝ) < (subcubesAt U n).card := by
    rcases (Nat.cast_nonneg (subcubesAt U n).card : (0 : ℝ) ≤ _).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hsub; linarith
    · exact h0
  set R := (∑ V ∈ subcubesAt U n, planarRho p ω V) / (subcubesAt U n).card with hR
  have hR0 : 0 ≤ R := div_nonneg (Finset.sum_nonneg fun V _ => planarRho_nonneg p ω V) hcard.le
  set K := 2 * (132100 * S ^ 2 + 2 * 10 ^ 10) * (ℓ + 1) * 531441 ^ ℓ /
    Real.sqrt ((3 : ℝ) ^ n) with hK
  have hK0 : 0 ≤ K := by positivity
  -- the sum of `ρ` over the vertices
  have hsumρ : ∑ x ∈ U.toIntegerCube.vertices, planarRho p ω (scaleCube n x) = R * U.volume := by
    rw [sum_scaleCube_eq hn (fun V _ => planarRho p ω V)]
    have e : ∀ V ∈ subcubesAt U n, ∑ _x ∈ V.toIntegerCube.vertices, planarRho p ω V =
        (9 : ℝ) ^ n * planarRho p ω V := by
      intro V hV
      rw [Finset.sum_const, nsmul_eq_mul, card_toIntegerCube_vertices_eq,
        scale_of_mem_subcubesAt hV]
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, hR, ← hsub, div_mul_eq_mul_div,
      eq_div_iff hcard.ne']
    ring
  refine planarRho_le (by positivity) fun q => max_le ?_ (by positivity)
  set w := (planarAhom p)⁻¹ *ᵥ q with hw
  set d := ∑ i, q i * w i with hd
  have hc : PlanarPartitionEvent ω ∧ PlanarResolved ω U := ⟨h.1, hU⟩
  have hωU : planarOmega p ω U q = planarNu ω U w + -planarMu ω U q - d := by
    unfold planarOmega; rw [if_pos hc, if_pos hc]
  have hωV : ∀ x ∈ U.toIntegerCube.vertices, planarOmega p ω (scaleCube n x) q =
      planarNu ω (scaleCube n x) w + -planarMu ω (scaleCube n x) q - d := fun x hx => by
    unfold planarOmega; rw [if_pos ⟨h.1, hres x hx⟩, if_pos ⟨h.1, hres x hx⟩]
  have hν := planarNu_sub_sum_subcubes_le_of_planarReachLe h hℓn hn w
  have hμ := sum_planarMu_subcubes_sub_le_of_planarReachLe h hℓn hn q
  have eν : ∑ x ∈ U.toIntegerCube.vertices,
      (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) w else 0) =
      ∑ x ∈ U.toIntegerCube.vertices, planarNu ω (scaleCube n x) w :=
    Finset.sum_congr rfl fun x hx => if_pos (hres x hx)
  have eμ : ∑ x ∈ U.toIntegerCube.vertices,
      (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) =
      ∑ x ∈ U.toIntegerCube.vertices, planarMu ω (scaleCube n x) q :=
    Finset.sum_congr rfl fun x hx => if_pos (hres x hx)
  rw [eν] at hν
  rw [eμ] at hμ
  have hsumω : ∑ x ∈ U.toIntegerCube.vertices, planarOmega p ω (scaleCube n x) q ≤
      R * U.volume * (q 0 ^ 2 + q 1 ^ 2) := by
    rw [← hsumρ, Finset.sum_mul]
    exact Finset.sum_le_sum fun x _ => planarOmega_le_planarRho_mul p ω _ q
  have hsumω' : ∑ x ∈ U.toIntegerCube.vertices, planarOmega p ω (scaleCube n x) q =
      ∑ x ∈ U.toIntegerCube.vertices, planarNu ω (scaleCube n x) w -
        ∑ x ∈ U.toIntegerCube.vertices, planarMu ω (scaleCube n x) q - d * U.volume := by
    rw [Finset.sum_congr rfl hωV, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul, card_toIntegerCube_vertices_eq]
    unfold TriadicCube.volume
    ring
  -- the errors in terms of `|q|²`
  have hw1 : (|w 0| + |w 1|) ^ 2 ≤ S ^ 2 * (|q 0| + |q 1|) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (hS q) 2
  have hl := l1_sq_le_two_mul q
  set B : ℝ := 531441 ^ ℓ with hB
  have h729 : (ℓ + 1 : ℝ) * 729 ^ ℓ ≤ (ℓ + 1) * B :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) ℓ) (by positivity)
  have hB1 : B ≤ (ℓ + 1) * B := by
    have h0 : (0 : ℝ) ≤ B := by positivity
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ ℓ + 1 by
      linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]) h0
    linarith
  have herr : 132100 * (ℓ + 1) * 729 ^ ℓ * (|w 0| + |w 1|) ^ 2 * U.volume /
        Real.sqrt ((3 : ℝ) ^ n) +
      2 * 10 ^ 10 * B * (|q 0| + |q 1|) ^ 2 * U.volume / Real.sqrt ((3 : ℝ) ^ n) ≤
      K * U.volume * (q 0 ^ 2 + q 1 ^ 2) := by
    have := rho_error_arith hw1 (by positivity) (by positivity) hl h729 (by positivity) hB1
      hvol hs0
    calc _ = 132100 * ((ℓ + 1) * 729 ^ ℓ) * (|w 0| + |w 1|) ^ 2 * U.volume /
          Real.sqrt ((3 : ℝ) ^ n) +
          2 * 10 ^ 10 * B * (|q 0| + |q 1|) ^ 2 * U.volume / Real.sqrt ((3 : ℝ) ^ n) := by ring
      _ ≤ _ := this
      _ = _ := by rw [hK]; ring
  have key : planarOmega p ω U q * U.volume ≤
      R * U.volume * (q 0 ^ 2 + q 1 ^ 2) + K * U.volume * (q 0 ^ 2 + q 1 ^ 2) := by
    rw [hωU]
    have e : (planarNu ω U w + -planarMu ω U q - d) * U.volume =
        planarNu ω U w * U.volume - planarMu ω U q * U.volume - d * U.volume := by ring
    rw [e]
    linarith
  have key2 : planarOmega p ω U q ≤ (R + K) * (q 0 ^ 2 + q 1 ^ 2) := by
    have : planarOmega p ω U q * U.volume ≤ ((R + K) * (q 0 ^ 2 + q 1 ^ 2)) * U.volume := by
      linarith
    exact le_of_mul_le_mul_right this hvol
  exact key2

end Rigidity.Proofs.Cluster
