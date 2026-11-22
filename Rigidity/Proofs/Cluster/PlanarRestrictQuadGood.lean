import Rigidity.Proofs.Cluster.PlanarRestrictBad

/-!
# The quantity of Lemma 5.5 off the bad event

Off the bad event `restrictBad` of the proof of Lemma 5.5 of Armstrong and Dario, and on the almost
sure event where the planar partition exists, the Gehring partition `s` has its properties and the
reach is finite, the hypotheses of `planarMuRestrictError_le_of_good` hold with `j = ⌊n/2⌋`, the
weight `Wt = 3 planarReach`, `W = 3 √A₂ 3^k` (`k = ⌊(n - j)/3⌋`) and `A = 27 A_τ^{1/r}`
(`τ ≥ 3r`): the quantities of display (5.12) are at most `Λ₀ D_n(U)/|U|` with a constant `Λ₀`
independent of `U`, `n` and the slope (`planarMuRestrictError_le_of_not_mem_restrictBad`,
`planarNuRestrictError_le_of_not_mem_restrictBad`).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- The constant of the bound off the bad event. -/
noncomputable def restrictConst (Aτ r CM p A₂ : ℝ) : ℝ :=
  4 * (8 * 1 ^ 2 * (coarseGradConst ^ 2 * (27 * Aτ ^ (1 / r) * (CM ^ (1 / p) * ((9 : ℕ) : ℝ)))) +
    64 * 1 ^ 2 * (coarseGradConst ^ 2 * (3 * √A₂) ^ 3))

theorem restrictConst_nonneg {Aτ r CM p A₂ : ℝ} (hAτ : 0 ≤ Aτ) (hCM : 0 ≤ CM) :
    0 ≤ restrictConst Aτ r CM p A₂ := by
  unfold restrictConst
  have h1 : 0 ≤ Aτ ^ (1 / r) := Real.rpow_nonneg hAτ _
  have h2 : 0 ≤ CM ^ (1 / p) := Real.rpow_nonneg hCM _
  positivity

/-- The constant `Λ / 9^n` of `restrictError_le_of_good` is at most `restrictConst / 4` for the
choices of the weights off the bad event. -/
theorem four_mul_restrictLambda_div_le {n j k : ℕ} (hk : j + 3 * k ≤ n) {Aτ r CM p A₂ : ℝ} :
    4 * (restrictLambda n j (27 * Aτ ^ (1 / r)) CM p (3 * √A₂ * 3 ^ k) / 9 ^ n) ≤
      restrictConst Aτ r CM p A₂ := by
  unfold restrictLambda restrictConst
  have h9 : (0 : ℝ) < 9 ^ n := by positivity
  have hpow : (3 : ℝ) ^ (n + j) * (3 ^ k) ^ 3 ≤ 9 ^ n := by
    rw [← pow_mul, ← pow_add, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hW : (3 * √A₂ * 3 ^ k) ^ 3 = (3 * √A₂) ^ 3 * (3 ^ k) ^ 3 := by ring
  have hA : 0 ≤ coarseGradConst ^ 2 * (3 * √A₂) ^ 3 := by positivity
  rw [hW]
  have e1 : 8 * 1 ^ 2 * 9 ^ n * (coarseGradConst ^ 2 * (27 * Aτ ^ (1 / r) *
      (CM ^ (1 / p) * ((9 : ℕ) : ℝ)))) / 9 ^ n = 8 * 1 ^ 2 * (coarseGradConst ^ 2 *
      (27 * Aτ ^ (1 / r) * (CM ^ (1 / p) * ((9 : ℕ) : ℝ)))) := by
    field_simp
  have e2 : 64 * 1 ^ 2 * 3 ^ (n + j) * (coarseGradConst ^ 2 * ((3 * √A₂) ^ 3 * (3 ^ k) ^ 3)) /
      9 ^ n ≤ 64 * 1 ^ 2 * (coarseGradConst ^ 2 * (3 * √A₂) ^ 3) := by
    rw [div_le_iff₀ h9]
    have := mul_le_mul_of_nonneg_left hpow hA
    nlinarith
  rw [add_div, e1]
  linarith

/-- **The quantity of display (5.12) for `μ` off the bad event** (Armstrong and Dario, proof of
Lemma 5.5, deterministic part, in dimension two). -/
theorem planarMuRestrictError_le_of_not_mem_restrictBad {CG : ℝ}
    {s : Configuration 2 → Vertex 2 → ℕ} {ε t K CM r : ℝ} {τ : ℕ} {Aτ A₂ : ℝ}
    (hpq : (1 + ε / 2).HolderConjugate r) (hτr : 3 * r ≤ τ) (hCM : 0 ≤ CM) (hAτ : 0 ≤ Aτ)
    (hA₂ : 0 ≤ A₂)
    (hMey : ∀ (ω : Configuration 2) (_ : PlanarPartitionEvent ω) (V : TriadicCube 2)
        (_ : PlanarResolved ω V) (w : ClusterFun ω V) (_ : w ∈ clusterHarmonic ω V) (n : ℕ)
        (x₀ : Vertex 2) (s : Vertex 2 → ℕ),
        (∀ x ∈ enl 1 n x₀, V.IsInterior x) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (∀ z ∈ enl 1 k y, (planarPartCube ω z).scale ≤ k) ∧
            ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * 2)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x =>
            clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
          CM * avg (enl 1 n x₀)
            (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^ (1 + ε / 2))
    (hP : PlanarPartitionEvent ω)
    (hs : (∀ x, ∀ z ∈ cube (s ω x) x, s ω z = s ω x) ∧
      (∀ x y, supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
      ∀ (k : ℕ) (y : Vertex 2), s ω y ≤ k →
        (∀ z ∈ enl 1 k y, (planarPartCube ω z).scale ≤ k) ∧
          ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * 2))
    (hfin : ∀ z, planarReach ω z ≠ ∞) {U : TriadicCube 2} {n : ℕ}
    (hmn : 9 * U.scale ≤ 10 * n) (hnm : n < U.scale)
    (hgood : ω ∉ restrictBad s t K τ Aτ A₂ U n) (q : Fin 2 → ℝ) :
    planarMuRestrictError ω U n q ≤
      restrictConst Aτ r CM (1 + ε / 2) A₂ * (planarMuDefect ω U n q / U.volume) := by
  obtain ⟨hcell, hnb, hRH⟩ := hs
  set j := n / 2 with hj
  set k := (n - n / 2) / 3 with hk
  have hn9 : 9 ≤ n := by omega
  have hj1 : 1 ≤ j := by omega
  have hjn : j < n := by omega
  have hjk : j + 3 * k ≤ n := by omega
  simp only [restrictBad, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or,
    not_exists, not_and, not_lt] at hgood
  obtain ⟨⟨hE2, hE5⟩, hE67⟩ := hgood
  have hres : ∀ x ∈ U.vertices, (planarPartCube ω x).scale ≤ j := fun x hx =>
    hE2 hP x ((U.mem_toIntegerCube_vertices x).2 hx)
  -- the weights
  set Wt : Vertex 2 → ℝ := fun z => 3 * (planarReach ω z).toReal with hWtdef
  have hWt : ∀ z, 3 * planarReach ω z ≤ ENNReal.ofReal (Wt z) := fun z => by
    show 3 * planarReach ω z ≤ ENNReal.ofReal (3 * (planarReach ω z).toReal)
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal (hfin z)]
    simp
  have hR1 : ∀ z, 1 ≤ (planarReach ω z).toReal := fun z => by
    have := ENNReal.toReal_mono (hfin z) (one_le_planarReach hP z)
    simpa using this
  have hW : ∀ z ∈ U.vertices, 3 * planarReach ω z ≤ ENNReal.ofReal (3 * √A₂ * 3 ^ k) := by
    intro z hz
    have h5 := hE5 z ((U.mem_toIntegerCube_vertices z).2 hz)
    have hfin2 : ∑ x ∈ cube k z, planarReach ω x ^ 2 ≠ ∞ :=
      ENNReal.sum_ne_top.2 fun x _ => ENNReal.pow_ne_top (hfin x)
    have h1 : planarReach ω z ^ 2 ≤ ∑ x ∈ cube k z, planarReach ω x ^ 2 :=
      Finset.single_le_sum (f := fun x => planarReach ω x ^ 2) (fun _ _ => zero_le)
        (mem_cube_self k z)
    have h2 : (planarReach ω z).toReal ^ 2 ≤ A₂ * ((3 : ℝ) ^ k) ^ 2 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h1.trans h5)
      rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (mul_nonneg hA₂ (Nat.cast_nonneg _)),
        card_cube] at this
      exact this
    have h3 : (planarReach ω z).toReal ≤ √A₂ * 3 ^ k := by
      have := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq ENNReal.toReal_nonneg, Real.sqrt_mul hA₂,
        Real.sqrt_sq (by positivity)] at this
    calc 3 * planarReach ω z = ENNReal.ofReal (3 * (planarReach ω z).toReal) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal (hfin z)]
          simp
      _ ≤ ENNReal.ofReal (3 * √A₂ * 3 ^ k) := ENNReal.ofReal_le_ofReal (by nlinarith)
  have hr0 : 0 < r := hpq.symm.pos
  have hA : ∀ V ∈ subcubesAt U n, ∀ c ∈ midCells V j,
      avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) ^ (1 / r) ≤ 27 * Aτ ^ (1 / r) := by
    intro V hV c hc
    have h6 := (hE67 V hV c hc).1
    have hfinτ : ∑ x ∈ cube c.1 c.2, planarReach ω x ^ τ ≠ ∞ :=
      ENNReal.sum_ne_top.2 fun x _ => ENNReal.pow_ne_top (hfin x)
    have hsum : ∑ x ∈ cube c.1 c.2, (planarReach ω x).toReal ^ τ ≤ Aτ * (cube c.1 c.2).card := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h6
      rw [ENNReal.toReal_sum fun x _ => ENNReal.pow_ne_top (hfin x),
        ENNReal.toReal_ofReal (mul_nonneg hAτ (Nat.cast_nonneg _))] at this
      simpa only [ENNReal.toReal_pow] using this
    have hpt : ∀ x, (Wt x ^ 3) ^ r ≤ (27 : ℝ) ^ r * (planarReach ω x).toReal ^ τ := by
      intro x
      have hR0 : 0 ≤ (planarReach ω x).toReal := ENNReal.toReal_nonneg
      have e : Wt x ^ 3 = 27 * (planarReach ω x).toReal ^ 3 := by
        show (3 * (planarReach ω x).toReal) ^ 3 = _
        ring
      rw [e, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast _ 3,
        ← Real.rpow_mul hR0, ← Real.rpow_natCast _ τ]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hR1 x)
        (by exact_mod_cast hτr)) (by positivity)
    have hcpos := card_cube_pos c.1 c.2
    have havg : avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) ≤ (27 : ℝ) ^ r * Aτ := by
      rw [avg, div_le_iff₀ hcpos]
      calc ∑ x ∈ cube c.1 c.2, (Wt x ^ 3) ^ r
          ≤ ∑ x ∈ cube c.1 c.2, (27 : ℝ) ^ r * (planarReach ω x).toReal ^ τ :=
            Finset.sum_le_sum fun x _ => hpt x
        _ = (27 : ℝ) ^ r * ∑ x ∈ cube c.1 c.2, (planarReach ω x).toReal ^ τ := by
            rw [Finset.mul_sum]
        _ ≤ (27 : ℝ) ^ r * (Aτ * (cube c.1 c.2).card) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (27 : ℝ) ^ r * Aτ * (cube c.1 c.2).card := by ring
    have havg0 : 0 ≤ avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) :=
      div_nonneg (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (by positivity) _)
        (Nat.cast_nonneg _)
    calc avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) ^ (1 / r)
        ≤ ((27 : ℝ) ^ r * Aτ) ^ (1 / r) :=
          Real.rpow_le_rpow havg0 havg (by positivity)
      _ = 27 * Aτ ^ (1 / r) := by
          rw [Real.mul_rpow (by positivity) hAτ, ← Real.rpow_mul (by norm_num),
            mul_one_div_cancel hr0.ne', Real.rpow_one]
  have hGeh : ∀ V ∈ subcubesAt U n, ∀ c ∈ midCells V j, (∀ z ∈ enl 1 c.1 c.2, s ω z ≤ c.1) ∧
      ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t ≤ K * (cube c.1 c.2).card := by
    intro V hV c hc
    obtain ⟨-, h7, h8⟩ := hE67 V hV c hc
    exact ⟨h7, h8⟩
  have hMey' : ∀ (V : TriadicCube 2), PlanarResolved ω V → ∀ (w : ClusterFun ω V),
      w ∈ clusterHarmonic ω V → ∀ (k' : ℕ) (x₀ : Vertex 2), (∀ x ∈ enl 1 k' x₀, V.IsInterior x) →
      (∀ z ∈ enl 1 k' x₀, s ω z ≤ k') →
      ∑ x ∈ cube k' x₀, ((3 : ℝ) ^ s ω x) ^ t ≤ K * (cube k' x₀).card →
      avg (cube k' x₀) (fun x =>
          clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
        CM * avg (enl 1 k' x₀) (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^
          (1 + ε / 2) := by
    intro V hV w hw k' x₀ hint hsk hmom
    refine hMey ω hP V hV w hw k' x₀ (s ω) hint hcell hnb (fun z hz => ?_)
      (fun k'' y hy _ => hRH k'' y hy) hmom
    exact (cube_mono (hsk z hz) z).trans (cube_subset_enl_of_mem hz)
  have h := planarMuRestrictError_le_of_good hP hj1 hjn hnm.le hres q (s ω) hpq hCM
    (by positivity : (0 : ℝ) ≤ 27 * Aτ ^ (1 / r)) Wt hWt hW hA hGeh hMey'
  have hD0 : 0 ≤ planarMuDefect ω U n q / U.volume :=
    div_nonneg (planarMuDefect_nonneg U n q) U.volume_pos.le
  exact h.trans (mul_le_mul_of_nonneg_right (four_mul_restrictLambda_div_le hjk) hD0)

/-- **The quantity of display (5.12) for `ν` off the bad event** (Armstrong and Dario, proof of
Lemma 5.5, second term, deterministic part, in dimension two). -/
theorem planarNuRestrictError_le_of_not_mem_restrictBad {CG : ℝ}
    {s : Configuration 2 → Vertex 2 → ℕ} {ε t K CM r : ℝ} {τ : ℕ} {Aτ A₂ : ℝ}
    (hpq : (1 + ε / 2).HolderConjugate r) (hτr : 3 * r ≤ τ) (hCM : 0 ≤ CM) (hAτ : 0 ≤ Aτ)
    (hA₂ : 0 ≤ A₂)
    (hMey : ∀ (ω : Configuration 2) (_ : PlanarPartitionEvent ω) (V : TriadicCube 2)
        (_ : PlanarResolved ω V) (w : ClusterFun ω V) (_ : w ∈ clusterHarmonic ω V) (n : ℕ)
        (x₀ : Vertex 2) (s : Vertex 2 → ℕ),
        (∀ x ∈ enl 1 n x₀, V.IsInterior x) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (∀ z ∈ enl 1 k y, (planarPartCube ω z).scale ≤ k) ∧
            ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * 2)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x =>
            clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
          CM * avg (enl 1 n x₀)
            (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^ (1 + ε / 2))
    (hP : PlanarPartitionEvent ω)
    (hs : (∀ x, ∀ z ∈ cube (s ω x) x, s ω z = s ω x) ∧
      (∀ x y, supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
      ∀ (k : ℕ) (y : Vertex 2), s ω y ≤ k →
        (∀ z ∈ enl 1 k y, (planarPartCube ω z).scale ≤ k) ∧
          ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * 2))
    (hfin : ∀ z, planarReach ω z ≠ ∞) {U : TriadicCube 2} {n : ℕ}
    (hmn : 9 * U.scale ≤ 10 * n) (hnm : n < U.scale)
    (hgood : ω ∉ restrictBad s t K τ Aτ A₂ U n) (q : Fin 2 → ℝ) :
    planarNuRestrictError ω U n q ≤
      restrictConst Aτ r CM (1 + ε / 2) A₂ * (planarNuDefect ω U n q / U.volume) := by
  obtain ⟨hcell, hnb, hRH⟩ := hs
  set j := n / 2 with hj
  set k := (n - n / 2) / 3 with hk
  have hn9 : 9 ≤ n := by omega
  have hj1 : 1 ≤ j := by omega
  have hjn : j < n := by omega
  have hjk : j + 3 * k ≤ n := by omega
  simp only [restrictBad, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or,
    not_exists, not_and, not_lt] at hgood
  obtain ⟨⟨hE2, hE5⟩, hE67⟩ := hgood
  have hres : ∀ x ∈ U.vertices, (planarPartCube ω x).scale ≤ j := fun x hx =>
    hE2 hP x ((U.mem_toIntegerCube_vertices x).2 hx)
  -- the weights
  set Wt : Vertex 2 → ℝ := fun z => 3 * (planarReach ω z).toReal with hWtdef
  have hWt : ∀ z, 3 * planarReach ω z ≤ ENNReal.ofReal (Wt z) := fun z => by
    show 3 * planarReach ω z ≤ ENNReal.ofReal (3 * (planarReach ω z).toReal)
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal (hfin z)]
    simp
  have hR1 : ∀ z, 1 ≤ (planarReach ω z).toReal := fun z => by
    have := ENNReal.toReal_mono (hfin z) (one_le_planarReach hP z)
    simpa using this
  have hW : ∀ z ∈ U.vertices, 3 * planarReach ω z ≤ ENNReal.ofReal (3 * √A₂ * 3 ^ k) := by
    intro z hz
    have h5 := hE5 z ((U.mem_toIntegerCube_vertices z).2 hz)
    have hfin2 : ∑ x ∈ cube k z, planarReach ω x ^ 2 ≠ ∞ :=
      ENNReal.sum_ne_top.2 fun x _ => ENNReal.pow_ne_top (hfin x)
    have h1 : planarReach ω z ^ 2 ≤ ∑ x ∈ cube k z, planarReach ω x ^ 2 :=
      Finset.single_le_sum (f := fun x => planarReach ω x ^ 2) (fun _ _ => zero_le)
        (mem_cube_self k z)
    have h2 : (planarReach ω z).toReal ^ 2 ≤ A₂ * ((3 : ℝ) ^ k) ^ 2 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h1.trans h5)
      rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (mul_nonneg hA₂ (Nat.cast_nonneg _)),
        card_cube] at this
      exact this
    have h3 : (planarReach ω z).toReal ≤ √A₂ * 3 ^ k := by
      have := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq ENNReal.toReal_nonneg, Real.sqrt_mul hA₂,
        Real.sqrt_sq (by positivity)] at this
    calc 3 * planarReach ω z = ENNReal.ofReal (3 * (planarReach ω z).toReal) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal (hfin z)]
          simp
      _ ≤ ENNReal.ofReal (3 * √A₂ * 3 ^ k) := ENNReal.ofReal_le_ofReal (by nlinarith)
  have hr0 : 0 < r := hpq.symm.pos
  have hA : ∀ V ∈ subcubesAt U n, ∀ c ∈ midCells V j,
      avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) ^ (1 / r) ≤ 27 * Aτ ^ (1 / r) := by
    intro V hV c hc
    have h6 := (hE67 V hV c hc).1
    have hfinτ : ∑ x ∈ cube c.1 c.2, planarReach ω x ^ τ ≠ ∞ :=
      ENNReal.sum_ne_top.2 fun x _ => ENNReal.pow_ne_top (hfin x)
    have hsum : ∑ x ∈ cube c.1 c.2, (planarReach ω x).toReal ^ τ ≤ Aτ * (cube c.1 c.2).card := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h6
      rw [ENNReal.toReal_sum fun x _ => ENNReal.pow_ne_top (hfin x),
        ENNReal.toReal_ofReal (mul_nonneg hAτ (Nat.cast_nonneg _))] at this
      simpa only [ENNReal.toReal_pow] using this
    have hpt : ∀ x, (Wt x ^ 3) ^ r ≤ (27 : ℝ) ^ r * (planarReach ω x).toReal ^ τ := by
      intro x
      have hR0 : 0 ≤ (planarReach ω x).toReal := ENNReal.toReal_nonneg
      have e : Wt x ^ 3 = 27 * (planarReach ω x).toReal ^ 3 := by
        show (3 * (planarReach ω x).toReal) ^ 3 = _
        ring
      rw [e, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast _ 3,
        ← Real.rpow_mul hR0, ← Real.rpow_natCast _ τ]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hR1 x)
        (by exact_mod_cast hτr)) (by positivity)
    have hcpos := card_cube_pos c.1 c.2
    have havg : avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) ≤ (27 : ℝ) ^ r * Aτ := by
      rw [avg, div_le_iff₀ hcpos]
      calc ∑ x ∈ cube c.1 c.2, (Wt x ^ 3) ^ r
          ≤ ∑ x ∈ cube c.1 c.2, (27 : ℝ) ^ r * (planarReach ω x).toReal ^ τ :=
            Finset.sum_le_sum fun x _ => hpt x
        _ = (27 : ℝ) ^ r * ∑ x ∈ cube c.1 c.2, (planarReach ω x).toReal ^ τ := by
            rw [Finset.mul_sum]
        _ ≤ (27 : ℝ) ^ r * (Aτ * (cube c.1 c.2).card) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (27 : ℝ) ^ r * Aτ * (cube c.1 c.2).card := by ring
    have havg0 : 0 ≤ avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) :=
      div_nonneg (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (by positivity) _)
        (Nat.cast_nonneg _)
    calc avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ r) ^ (1 / r)
        ≤ ((27 : ℝ) ^ r * Aτ) ^ (1 / r) :=
          Real.rpow_le_rpow havg0 havg (by positivity)
      _ = 27 * Aτ ^ (1 / r) := by
          rw [Real.mul_rpow (by positivity) hAτ, ← Real.rpow_mul (by norm_num),
            mul_one_div_cancel hr0.ne', Real.rpow_one]
  have hGeh : ∀ V ∈ subcubesAt U n, ∀ c ∈ midCells V j, (∀ z ∈ enl 1 c.1 c.2, s ω z ≤ c.1) ∧
      ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t ≤ K * (cube c.1 c.2).card := by
    intro V hV c hc
    obtain ⟨-, h7, h8⟩ := hE67 V hV c hc
    exact ⟨h7, h8⟩
  have hMey' : ∀ (V : TriadicCube 2), PlanarResolved ω V → ∀ (w : ClusterFun ω V),
      w ∈ clusterHarmonic ω V → ∀ (k' : ℕ) (x₀ : Vertex 2), (∀ x ∈ enl 1 k' x₀, V.IsInterior x) →
      (∀ z ∈ enl 1 k' x₀, s ω z ≤ k') →
      ∑ x ∈ cube k' x₀, ((3 : ℝ) ^ s ω x) ^ t ≤ K * (cube k' x₀).card →
      avg (cube k' x₀) (fun x =>
          clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
        CM * avg (enl 1 k' x₀) (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^
          (1 + ε / 2) := by
    intro V hV w hw k' x₀ hint hsk hmom
    refine hMey ω hP V hV w hw k' x₀ (s ω) hint hcell hnb (fun z hz => ?_)
      (fun k'' y hy _ => hRH k'' y hy) hmom
    exact (cube_mono (hsk z hz) z).trans (cube_subset_enl_of_mem hz)
  have h := planarNuRestrictError_le_of_good hP hj1 hjn hnm.le hres q (s ω) hpq hCM
    (by positivity : (0 : ℝ) ≤ 27 * Aτ ^ (1 / r)) Wt hWt hW hA hGeh hMey'
  have hD0 : 0 ≤ planarNuDefect ω U n q / U.volume :=
    div_nonneg (planarNuDefect_nonneg U n q) U.volume_pos.le
  exact h.trans (mul_le_mul_of_nonneg_right (four_mul_restrictLambda_div_le hjk) hD0)

end Rigidity.Proofs.Cluster
