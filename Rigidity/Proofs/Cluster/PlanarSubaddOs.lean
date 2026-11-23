import Rigidity.Proofs.Cluster.PlanarBoundN
import Rigidity.Proofs.Cluster.OsTailCalculus

/-!
# Proposition 5.2 of Armstrong and Dario in dimension two, in the form `O_s`

For a triadic cube `V`, with `μ` and `ν` set to `0` off the event that the planar partition exists
and resolves `V` (the convention `u ≡ 0` of the source), let
`f_μ(q) = μ(V, q) + (1/2) q · ā⁻¹ q` and `f_ν(ξ) = ν(V, ξ) - (1/2) ξ · ā ξ`. Both are quadratic
forms, so `|f_μ(q)| ≤ X(V) |q|²` and `|f_ν(ξ)| ≤ X(V) |ξ|²` for the measurable random variable
`X(V) = planarSubaddErr p V` built from their values at three slopes. Proposition 5.2
(displays (5.1) and (5.2)) is `X(V) ≤ O_r(C 3^{-α scale V})` for every triadic cube
(`planar_subadd_os`).

The proof: `X(V) ≤ 12 K 3^{-β scale V}` where Proposition 5.2 holds
(`exists_planarSubaddGood_tail_cube`, failure probability `C exp(-c 3^{m s})`), and everywhere
`X(V) ≤ c (1 + M⁴)` with `M` the largest size of the partition into coarsely good cubes on `V`
(the upper bound of `-μ` by the reach, Lemma 4.4), which is `O_1(C (1 + m))`. Hence
`X(V) ≤ 12 K 3^{-βm} + c (1 + M⁴) 1_{bad} ≤ O_{1/5}(C 3^{-α m})` by the calculus of `O_s`.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal Matrix

variable {ω : Configuration 2}

/-- The error `μ(V, q) + (1/2) q · ā⁻¹ q`, with `μ = 0` off the event. -/
noncomputable def planarMuErr (p : unitInterval) (ω : Configuration 2) (V : TriadicCube 2)
    (q : Fin 2 → ℝ) : ℝ :=
  (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then planarMu ω V q else 0) +
    1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i

/-- The error `ν(V, ξ) - (1/2) ξ · ā ξ`, with `ν = 0` off the event. -/
noncomputable def planarNuErr (p : unitInterval) (ω : Configuration 2) (V : TriadicCube 2)
    (ξ : Fin 2 → ℝ) : ℝ :=
  (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then planarNu ω V ξ else 0) -
    1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i

/-- The bound of a quadratic form by its values at `e₀`, `e₁` and `e₀ + e₁`. -/
noncomputable def quadBound (g : (Fin 2 → ℝ) → ℝ) : ℝ :=
  |g (Pi.single 0 1)| + |g (Pi.single 1 1)| +
    |g (Pi.single 0 1 + Pi.single 1 1) - g (Pi.single 0 1) - g (Pi.single 1 1)|

/-- **The random error of Proposition 5.2 on `V`.** -/
noncomputable def planarSubaddErr (p : unitInterval) (V : TriadicCube 2) (ω : Configuration 2) :
    ℝ :=
  quadBound (planarMuErr p ω V) + quadBound (planarNuErr p ω V)

theorem quadBound_nonneg (g : (Fin 2 → ℝ) → ℝ) : 0 ≤ quadBound g := by
  unfold quadBound; positivity

theorem planarSubaddErr_nonneg (p : unitInterval) (V : TriadicCube 2) (ω : Configuration 2) :
    0 ≤ planarSubaddErr p V ω :=
  add_nonneg (quadBound_nonneg _) (quadBound_nonneg _)

theorem IsPlanarQuadratic.const_mul {g : (Fin 2 → ℝ) → ℝ} (hg : IsPlanarQuadratic g) (c : ℝ) :
    IsPlanarQuadratic fun q => c * g q := by
  intro r s a b
  simp only
  rw [hg r s a b]
  ring

theorem isPlanarQuadratic_planarMuErr (p : unitInterval) (ω : Configuration 2)
    (V : TriadicCube 2) : IsPlanarQuadratic (planarMuErr p ω V) := by
  have hd :=
    IsPlanarQuadratic.const_mul (isPlanarQuadratic_dotProduct_mulVec (planarAhom p)⁻¹) (1 / 2)
  by_cases h : PlanarPartitionEvent ω ∧ PlanarResolved ω V
  · have e : planarMuErr p ω V = fun q =>
        planarMu ω V q + 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i := by
      funext q; simp only [planarMuErr, if_pos h]
    rw [e]
    exact IsPlanarQuadratic.add (isPlanarQuadratic_planarMu h.1 h.2) hd
  · have e : planarMuErr p ω V = fun q =>
        (fun _ => (0 : ℝ)) q + 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i := by
      funext q; simp only [planarMuErr, if_neg h]
    rw [e]
    exact IsPlanarQuadratic.add isPlanarQuadratic_zero hd

theorem isPlanarQuadratic_planarNuErr (p : unitInterval) (ω : Configuration 2)
    (V : TriadicCube 2) : IsPlanarQuadratic (planarNuErr p ω V) := by
  have hd :=
    IsPlanarQuadratic.const_mul (isPlanarQuadratic_dotProduct_mulVec (planarAhom p)) (1 / 2)
  by_cases h : PlanarPartitionEvent ω ∧ PlanarResolved ω V
  · have e : planarNuErr p ω V = fun ξ =>
        planarNu ω V ξ - 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i := by
      funext ξ; simp only [planarNuErr, if_pos h]
    rw [e]
    exact IsPlanarQuadratic.sub (isPlanarQuadratic_planarNu V) hd
  · have e : planarNuErr p ω V = fun ξ =>
        (fun _ => (0 : ℝ)) ξ - 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i := by
      funext ξ; simp only [planarNuErr, if_neg h]
    rw [e]
    exact IsPlanarQuadratic.sub isPlanarQuadratic_zero hd

/-- `|μ(V, q) + (1/2) q · ā⁻¹ q| ≤ X(V) |q|²`. -/
theorem abs_planarMuErr_le (p : unitInterval) (ω : Configuration 2) (V : TriadicCube 2)
    (q : Fin 2 → ℝ) : |planarMuErr p ω V q| ≤ planarSubaddErr p V ω * (q 0 ^ 2 + q 1 ^ 2) :=
  (IsPlanarQuadratic.abs_le (isPlanarQuadratic_planarMuErr p ω V) q).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (quadBound_nonneg _)) (by positivity))

/-- `|ν(V, ξ) - (1/2) ξ · ā ξ| ≤ X(V) |ξ|²`. -/
theorem abs_planarNuErr_le (p : unitInterval) (ω : Configuration 2) (V : TriadicCube 2)
    (ξ : Fin 2 → ℝ) : |planarNuErr p ω V ξ| ≤ planarSubaddErr p V ω * (ξ 0 ^ 2 + ξ 1 ^ 2) :=
  (IsPlanarQuadratic.abs_le (isPlanarQuadratic_planarNuErr p ω V) ξ).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (quadBound_nonneg _)) (by positivity))

theorem measurable_planarMuErr (p : unitInterval) (V : TriadicCube 2) (q : Fin 2 → ℝ) :
    Measurable fun ω => planarMuErr p ω V q := by
  have e : ∀ ω, planarMuErr p ω V q =
      -(if PlanarPartitionEvent ω ∧ PlanarResolved ω V then ENNReal.ofReal (-planarMu ω V q)
        else 0).toReal + 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i := by
    intro ω
    rw [toReal_planarMu_indicator, planarMuErr]
    split_ifs <;> ring
  simp only [e]
  exact ((measurable_planarMu_indicator V q).ennreal_toReal.neg).add_const _

theorem measurable_planarNuErr (p : unitInterval) (V : TriadicCube 2) (ξ : Fin 2 → ℝ) :
    Measurable fun ω => planarNuErr p ω V ξ :=
  (measurable_planarNu_indicator_real V ξ).sub_const _

theorem measurable_quadBound {f : Configuration 2 → (Fin 2 → ℝ) → ℝ}
    (hf : ∀ q, Measurable fun ω => f ω q) : Measurable fun ω => quadBound (f ω) := by
  unfold quadBound
  have ha : ∀ {g : Configuration 2 → ℝ}, Measurable g → Measurable fun ω => |g ω| :=
    fun hg => continuous_abs.measurable.comp hg
  exact ((ha (hf _)).add (ha (hf _))).add (ha (((hf _).sub (hf _)).sub (hf _)))

theorem measurable_planarSubaddErr (p : unitInterval) (V : TriadicCube 2) :
    Measurable (planarSubaddErr p V) :=
  (measurable_quadBound (measurable_planarMuErr p V)).add
    (measurable_quadBound (measurable_planarNuErr p V))

theorem norms_single :
    ((Pi.single 0 1 : Fin 2 → ℝ) 0 ^ 2 + (Pi.single 0 1 : Fin 2 → ℝ) 1 ^ 2 = 1) ∧
    ((Pi.single 1 1 : Fin 2 → ℝ) 0 ^ 2 + (Pi.single 1 1 : Fin 2 → ℝ) 1 ^ 2 = 1) ∧
    ((Pi.single 0 1 + Pi.single 1 1 : Fin 2 → ℝ) 0 ^ 2 +
      (Pi.single 0 1 + Pi.single 1 1 : Fin 2 → ℝ) 1 ^ 2 = 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [Pi.single_apply]

theorem l1norms_single :
    ((|(Pi.single 0 1 : Fin 2 → ℝ) 0| + |(Pi.single 0 1 : Fin 2 → ℝ) 1|) ^ 2 = 1) ∧
    ((|(Pi.single 1 1 : Fin 2 → ℝ) 0| + |(Pi.single 1 1 : Fin 2 → ℝ) 1|) ^ 2 = 1) ∧
    ((|(Pi.single 0 1 + Pi.single 1 1 : Fin 2 → ℝ) 0| +
      |(Pi.single 0 1 + Pi.single 1 1 : Fin 2 → ℝ) 1|) ^ 2 = 4) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [Pi.single_apply]

/-- A quadratic form bounded by `B |q|²` at the three slopes has `quadBound ≤ 6 B`. -/
theorem quadBound_le_of_sq {g : (Fin 2 → ℝ) → ℝ} {B : ℝ}
    (h : ∀ q, |g q| ≤ B * (q 0 ^ 2 + q 1 ^ 2)) : quadBound g ≤ 6 * B := by
  obtain ⟨n0, n1, n2⟩ := norms_single
  have a := h (Pi.single 0 1)
  have b := h (Pi.single 1 1)
  have c := h (Pi.single 0 1 + Pi.single 1 1)
  rw [n0] at a
  rw [n1] at b
  rw [n2] at c
  unfold quadBound
  have hd : |g (Pi.single 0 1 + Pi.single 1 1) - g (Pi.single 0 1) - g (Pi.single 1 1)| ≤
      |g (Pi.single 0 1 + Pi.single 1 1)| + |g (Pi.single 0 1)| + |g (Pi.single 1 1)| := by
    calc _ ≤ |g (Pi.single 0 1 + Pi.single 1 1) - g (Pi.single 0 1)| + |g (Pi.single 1 1)| :=
          abs_sub _ _
      _ ≤ _ := by gcongr; exact abs_sub _ _
  linarith

/-- A quadratic form bounded by `B |q|₁²` at the three slopes has `quadBound ≤ 12 B`. -/
theorem quadBound_le_of_l1 {g : (Fin 2 → ℝ) → ℝ} {B : ℝ}
    (h : ∀ q, |g q| ≤ B * (|q 0| + |q 1|) ^ 2) : quadBound g ≤ 12 * B := by
  obtain ⟨n0, n1, n2⟩ := l1norms_single
  have a := h (Pi.single 0 1)
  have b := h (Pi.single 1 1)
  have c := h (Pi.single 0 1 + Pi.single 1 1)
  rw [n0] at a
  rw [n1] at b
  rw [n2] at c
  unfold quadBound
  have hd : |g (Pi.single 0 1 + Pi.single 1 1) - g (Pi.single 0 1) - g (Pi.single 1 1)| ≤
      |g (Pi.single 0 1 + Pi.single 1 1)| + |g (Pi.single 0 1)| + |g (Pi.single 1 1)| := by
    calc _ ≤ |g (Pi.single 0 1 + Pi.single 1 1) - g (Pi.single 0 1)| + |g (Pi.single 1 1)| :=
          abs_sub _ _
      _ ≤ _ := by gcongr; exact abs_sub _ _
  have := abs_nonneg (g (Pi.single 0 1))
  linarith

/-- **The error where Proposition 5.2 holds.** -/
theorem planarSubaddErr_le_of_good {p : unitInterval} {V : TriadicCube 2} {K β : ℝ}
    (h : PlanarSubaddGood p ω V K β) :
    planarSubaddErr p V ω ≤ 12 * (K * (3 : ℝ) ^ (-(V.scale : ℝ) * β)) := by
  obtain ⟨hP, hres, hμ, hν⟩ := h
  have hc : PlanarPartitionEvent ω ∧ PlanarResolved ω V := ⟨hP, hres⟩
  have h1 := quadBound_le_of_sq (g := planarMuErr p ω V)
    (B := K * (3 : ℝ) ^ (-(V.scale : ℝ) * β)) fun q => by
      have := hμ q
      rw [planarMuErr, if_pos hc]
      calc _ ≤ _ := this
        _ = _ := by ring
  have h2 := quadBound_le_of_sq (g := planarNuErr p ω V)
    (B := K * (3 : ℝ) ^ (-(V.scale : ℝ) * β)) fun ξ => by
      have := hν ξ
      rw [planarNuErr, if_pos hc]
      calc _ ≤ _ := this
        _ = _ := by ring
  unfold planarSubaddErr
  linarith

/-- The largest size of the partition into coarsely good cubes on `V`. -/
noncomputable def coarseMax (ω : Configuration 2) (V : TriadicCube 2) : ℝ :=
  V.toIntegerCube.vertices.sup' (by
      refine ⟨V.toIntegerCube.corner, ?_⟩
      rw [IntegerCube.mem_vertices]
      intro i
      have : (0 : ℤ) < (V.toIntegerCube.size : ℤ) := by
        change (0 : ℤ) < ((3 ^ V.scale : ℕ) : ℤ); positivity
      constructor <;> omega)
    fun a => TriadicCube.stoppingSize (planarCoarseGood ω) a

theorem stoppingSize_le_coarseMax (ω : Configuration 2) {V : TriadicCube 2} {a : Vertex 2}
    (ha : a ∈ V.toIntegerCube.vertices) :
    TriadicCube.stoppingSize (planarCoarseGood ω) a ≤ coarseMax ω V :=
  Finset.le_sup' (fun a => TriadicCube.stoppingSize (planarCoarseGood ω) a) ha

theorem coarseMax_nonneg (ω : Configuration 2) (V : TriadicCube 2) : 0 ≤ coarseMax ω V :=
  (TriadicCube.stoppingSize_nonneg _ _).trans (stoppingSize_le_coarseMax ω
    (a := V.toIntegerCube.corner) (by
      rw [IntegerCube.mem_vertices]
      intro i
      have : (0 : ℤ) < (V.toIntegerCube.size : ℤ) := by
        change (0 : ℤ) < ((3 ^ V.scale : ℕ) : ℤ); positivity
      constructor <;> omega))

/-- `-μ(V, q) ≤ 2108304 M⁴ |q|₁²` with `M` the largest coarse size on `V`. -/
theorem neg_planarMu_le_coarseMax (hP : PlanarPartitionEvent ω)
    (hH : ∀ x : Vertex 2,
      ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω))
    {V : TriadicCube 2} (hres : PlanarResolved ω V) (q : Fin 2 → ℝ) :
    -planarMu ω V q ≤ 2108304 * coarseMax ω V ^ 4 * (|q 0| + |q 1|) ^ 2 := by
  have hmu := ofReal_neg_planarMu_le hP hres q
  have hvol := V.volume_pos
  have hM0 := coarseMax_nonneg ω V
  have hR : ∀ a ∈ V.toIntegerCube.vertices,
      234256 * planarReach ω a ^ 4 ≤ ENNReal.ofReal (234256 * coarseMax ω V ^ 4) := by
    intro a ha
    have h1 : planarReach ω a ≤ ENNReal.ofReal (coarseMax ω V) :=
      (planarReach_le_stoppingSize hH a).trans
        (ENNReal.ofReal_le_ofReal (stoppingSize_le_coarseMax ω ha))
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_pow hM0]
    gcongr
  have hsum := sum_le_ofReal_card_mul _ _ hR
  rw [card_toIntegerCube_vertices_eq] at hsum
  have h2 : ENNReal.ofReal (-planarMu ω V q) ≤
      ENNReal.ofReal (9 * (|q 0| + |q 1|) ^ 2 / V.volume) *
        ENNReal.ofReal ((9 : ℝ) ^ V.scale * (234256 * coarseMax ω V ^ 4)) :=
    hmu.trans (mul_le_mul_of_nonneg_left hsum zero_le)
  rw [← ENNReal.ofReal_mul (div_nonneg (by positivity) hvol.le)] at h2
  have e : 9 * (|q 0| + |q 1|) ^ 2 / V.volume * ((9 : ℝ) ^ V.scale * (234256 * coarseMax ω V ^ 4)) =
      2108304 * coarseMax ω V ^ 4 * (|q 0| + |q 1|) ^ 2 := by
    have : V.volume = (9 : ℝ) ^ V.scale := rfl
    rw [this]
    field_simp
    ring
  rw [e] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

/-- **The error everywhere**, by the largest coarse size. -/
theorem planarSubaddErr_le_coarseMax {p : unitInterval} {S Sa : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ v : Fin 2 → ℝ, |((planarAhom p)⁻¹ *ᵥ v) 0| + |((planarAhom p)⁻¹ *ᵥ v) 1| ≤
      S * (|v 0| + |v 1|))
    (hSa0 : 0 ≤ Sa) (hSa : ∀ v : Fin 2 → ℝ, |(planarAhom p *ᵥ v) 0| + |(planarAhom p *ᵥ v) 1| ≤
      Sa * (|v 0| + |v 1|))
    (hH : ∀ x : Vertex 2,
      ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω))
    (V : TriadicCube 2) :
    planarSubaddErr p V ω ≤ 12 * (2108304 + S + 3 + Sa) * (1 + coarseMax ω V ^ 4) := by
  have hM4 : 0 ≤ coarseMax ω V ^ 4 := by positivity
  have hdotμ : ∀ q : Fin 2 → ℝ, |1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i| ≤
      S * (|q 0| + |q 1|) ^ 2 := by
    intro q
    have h1 := abs_dotProduct_le q ((planarAhom p)⁻¹ *ᵥ q)
    have h2 := mul_le_mul_of_nonneg_left (hS q) (show 0 ≤ |q 0| + |q 1| by positivity)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h3 : 0 ≤ |∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i| := abs_nonneg _
    nlinarith only [h1, h2, h3]
  have hdotν : ∀ ξ : Fin 2 → ℝ, |1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i| ≤
      Sa * (|ξ 0| + |ξ 1|) ^ 2 := by
    intro ξ
    have h1 := abs_dotProduct_le ξ (planarAhom p *ᵥ ξ)
    have h2 := mul_le_mul_of_nonneg_left (hSa ξ) (show 0 ≤ |ξ 0| + |ξ 1| by positivity)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h3 : 0 ≤ |∑ i, ξ i * (planarAhom p *ᵥ ξ) i| := abs_nonneg _
    nlinarith only [h1, h2, h3]
  have hμ : ∀ q : Fin 2 → ℝ, |planarMuErr p ω V q| ≤
      (2108304 * coarseMax ω V ^ 4 + S) * (|q 0| + |q 1|) ^ 2 := by
    intro q
    have hd := hdotμ q
    have hq0 : 0 ≤ (|q 0| + |q 1|) ^ 2 := by positivity
    unfold planarMuErr
    split_ifs with hc
    · have h1 := neg_planarMu_le_coarseMax hc.1 hH hc.2 q
      have h2 := planarMu_nonpos hc.1 hc.2 q
      calc |planarMu ω V q + 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i|
          ≤ |planarMu ω V q| + |1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i| := abs_add_le _ _
        _ ≤ 2108304 * coarseMax ω V ^ 4 * (|q 0| + |q 1|) ^ 2 + S * (|q 0| + |q 1|) ^ 2 := by
            rw [abs_of_nonpos h2]; linarith
        _ = _ := by ring
    · rw [zero_add]
      have : 0 ≤ 2108304 * coarseMax ω V ^ 4 * (|q 0| + |q 1|) ^ 2 := by positivity
      calc _ ≤ S * (|q 0| + |q 1|) ^ 2 := hd
        _ ≤ _ := by nlinarith only [this]
  have hν : ∀ ξ : Fin 2 → ℝ, |planarNuErr p ω V ξ| ≤ (3 + Sa) * (|ξ 0| + |ξ 1|) ^ 2 := by
    intro ξ
    have hd := hdotν ξ
    have hq0 : 0 ≤ (|ξ 0| + |ξ 1|) ^ 2 := by positivity
    unfold planarNuErr
    split_ifs with hc
    · have h1 := planarNu_le (ω := ω) (U := V) ξ
      have h2 := planarNu_nonneg (ω := ω) (U := V) ξ
      calc |planarNu ω V ξ - 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i|
          ≤ |planarNu ω V ξ| + |1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i| := abs_sub _ _
        _ ≤ 3 * (|ξ 0| + |ξ 1|) ^ 2 + Sa * (|ξ 0| + |ξ 1|) ^ 2 := by
            rw [abs_of_nonneg h2]; linarith
        _ = _ := by ring
    · rw [zero_sub, abs_neg]
      calc _ ≤ Sa * (|ξ 0| + |ξ 1|) ^ 2 := hd
        _ ≤ _ := by nlinarith only [hq0]
  have h1 := quadBound_le_of_l1 hμ
  have h2 := quadBound_le_of_l1 hν
  unfold planarSubaddErr
  nlinarith only [h1, h2, hM4, hS0, hSa0]

end Rigidity.Proofs.Cluster
