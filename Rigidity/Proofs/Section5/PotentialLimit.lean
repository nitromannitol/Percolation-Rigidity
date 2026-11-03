import Rigidity.Steps.Section5.Common
import LatticeProb.External.GreenQuantitative
import LatticeProb.External.SupercriticalBondUniquenessInput

/-! # Section 5: the potential normalized at infinity

The infinite cluster is almost surely unique; the Green potential `u_f` of a finitely supported
charge `f` satisfies `u_f - (Σ f) Ḡ → Σ_y f(y) K_y` at infinity (Dario-Gu, `d = 2`), so for a
neutral charge `u_f` converges at infinity (the normalized Green function: corrections C3, C13 and
C14). -/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

/-- Almost surely the infinite open cluster exists and is unique. -/
theorem uniqueClusterAe (hU : LatticeProb.External.SupercriticalBondUniqueness) {p : unitInterval}
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) : UniqueClusterAe p :=
  (mem_ae_iff_prob_eq_one (measurableSet_uniqueInfiniteComponentEvent 2)).mpr
    (hU.2 2 le_rfl p hp hp1)

variable {ω : Configuration 2}

/-- Along the cofinite filter of an open component, the Euclidean norm tends to infinity. -/
theorem tendsto_norm_cofinite_atTop (C : OpenComponent ω) :
    Tendsto (fun x : C => ‖latticeEuclideanEmbedding x.val‖) cofinite atTop := by
  have h0 : latticeEuclideanEmbedding (0 : Vertex 2) = 0 := by
    ext i; simp [latticeEuclideanEmbedding]
  refine tendsto_atTop.2 fun R => eventually_cofinite.2 ?_
  refine ((finite_latticeEuclideanBall (0 : Vertex 2) R).preimage
    Subtype.val_injective.injOn).subset fun x hx => ?_
  simp only [Set.mem_setOf_eq, not_le] at hx
  simpa [h0] using hx

/-- `log |x - y| - log |x| → 0` at infinity on an open component. -/
theorem tendsto_log_norm_sub_sub_log_norm (C : OpenComponent ω) (y : C) :
    Tendsto (fun x : C => Real.log ‖latticeEuclideanEmbedding x.val -
      latticeEuclideanEmbedding y.val‖ - Real.log ‖latticeEuclideanEmbedding x.val‖)
      cofinite (𝓝 0) := by
  set e : C → EuclideanSpace ℝ (Fin 2) := fun x => latticeEuclideanEmbedding x.val with he
  have ht : Tendsto (fun x => ‖e x‖) cofinite atTop := tendsto_norm_cofinite_atTop C
  have hpos : ∀ᶠ x : C in cofinite, 1 ≤ ‖e x‖ := ht.eventually_ge_atTop 1
  have hne : ∀ᶠ x : C in cofinite, x ≠ y := eventually_cofinite_ne y
  have hq : Tendsto (fun x : C => (‖e x - e y‖ - ‖e x‖) / ‖e x‖) cofinite (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := ‖e y‖)).div_atTop ht)
    filter_upwards [hpos] with x hx
    have hb := abs_norm_sub_norm_le (e x - e y) (e x)
    rw [sub_sub_cancel_left, norm_neg] at hb
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (a := ‖e x‖) (by linarith)]
    gcongr
  have hr : Tendsto (fun x : C => ‖e x - e y‖ / ‖e x‖) cofinite (𝓝 1) := by
    have := hq.const_add 1
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [hpos] with x hx
    field_simp
    ring
  have hlog := ((Real.continuousAt_log one_ne_zero).tendsto).comp hr
  rw [Real.log_one] at hlog
  refine hlog.congr' ?_
  filter_upwards [hpos, hne] with x hx hxy
  have hxy' : e x - e y ≠ 0 := sub_ne_zero.2 fun h =>
    hxy (Subtype.val_injective (latticeEuclideanEmbedding.injective h))
  simp only [Function.comp_apply]
  rw [Real.log_div (norm_ne_zero_iff.2 hxy') (by linarith)]

/-- A Green column whose deviation from `Ḡ(x - y) + K` vanishes at infinity satisfies
`g - Ḡ → K` along the cofinite filter. -/
theorem tendsto_column_sub_greenLog (C : OpenComponent ω) (κ : {a : ℝ // 0 < a}) (y : C)
    (g : C → ℝ) (K : ℝ)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ x : C, ∀ z : {v : EuclideanSpace ℝ (Fin 2) // v ≠ 0},
        z.val = latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y.val →
        R ≤ ‖latticeEuclideanEmbedding x.val‖ →
        |g x - continuumGreen 2 le_rfl κ z - K| ≤ ε) :
    Tendsto (fun x : C => g x - greenLog κ x.val) cofinite (𝓝 K) := by
  set e : C → EuclideanSpace ℝ (Fin 2) := fun x => latticeEuclideanEmbedding x.val with he
  set c : ℝ := 2 * Real.pi * κ.val with hc
  set a : C → ℝ := fun x => -Real.log ‖e x - e y‖ / c with ha
  have ht : Tendsto (fun x => ‖e x‖) cofinite atTop := tendsto_norm_cofinite_atTop C
  have h1 : Tendsto (fun x => g x - a x - K) cofinite (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨R, -, hR⟩ := hg (ε / 2) (half_pos hε)
    filter_upwards [ht.eventually_ge_atTop R, eventually_cofinite_ne y] with x hx hxy
    have hxy' : e x - e y ≠ 0 := sub_ne_zero.2 fun h =>
      hxy (Subtype.val_injective (latticeEuclideanEmbedding.injective h))
    have := hR x ⟨e x - e y, hxy'⟩ rfl hx
    simp only [continuumGreen, if_true] at this
    rw [Real.dist_eq, sub_zero]
    exact this.trans_lt (half_lt_self hε)
  have h2 : Tendsto (fun x => a x - greenLog κ x.val) cofinite (𝓝 0) := by
    have := (tendsto_log_norm_sub_sub_log_norm C y).neg.div_const c
    rw [neg_zero, zero_div] at this
    refine this.congr fun x => ?_
    simp only [ha, greenLog, eucl, he, hc]
    ring
  have := (h1.add h2).add_const K
  rw [zero_add, zero_add] at this
  refine this.congr fun x => ?_
  ring

/-- On an open component, `u_f - (Σ f) φ` is a finite sum over the charges of `f` in the
component. -/
theorem potential_sub_mass_mul_eq_sum (C : OpenComponent ω) (G : C → C → ℝ) (f : Vertex 2 → ℤ)
    (hf : (Function.support f).Finite) (φ : ℝ) (x : C) :
    potential C G f x - (mass C f : ℝ) * φ =
      ∑ y ∈ (hf.preimage Subtype.val_injective.injOn).toFinset,
        (f y.val : ℝ) * (G x y - φ) := by
  set F : Finset C := (hf.preimage Subtype.val_injective.injOn).toFinset with hF
  have hsub : (Function.support fun y : C => (f y.val : ℝ) * G x y) ⊆ F := by
    intro y hy
    rw [hF, Set.Finite.coe_toFinset, Set.mem_preimage, Function.mem_support]
    intro h0
    exact hy (by simp [h0])
  have hsupp : (Function.support fun y : C => f y.val) ⊆ F := by
    intro y hy
    rwa [hF, Set.Finite.coe_toFinset, Set.mem_preimage]
  rw [potential, finsum_eq_sum_of_support_subset _ hsub, mass,
    finsum_eq_sum_of_support_subset _ hsupp, Int.cast_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- On an open component, the Green potential of a finitely supported charge minus `(Σ f) Ḡ`
converges at infinity to `Σ_y f(y) K_y` as soon as each Green column does with limit `K_y`. -/
theorem tendsto_potential_sub_mass_mul_greenLog (C : OpenComponent ω) (κ : {a : ℝ // 0 < a})
    (G : C → C → ℝ) (K : C → ℝ) (f : Vertex 2 → ℤ) (hf : (Function.support f).Finite)
    (hcol : ∀ y : C, Tendsto (fun x : C => G x y - greenLog κ x.val) cofinite (𝓝 (K y))) :
    Tendsto (fun x => potential C G f x - (mass C f : ℝ) * greenLog κ x.val) cofinite
      (𝓝 (∑ y ∈ (hf.preimage Subtype.val_injective.injOn).toFinset, (f y.val : ℝ) * K y)) := by
  simp_rw [potential_sub_mass_mul_eq_sum C G f hf]
  exact tendsto_finsetSum _ fun y _ => (hcol y).const_mul _

/-- Potential asymptotics (Dario-Gu Thm 2, `d = 2`), from the quantitative Green input: almost
surely `u_f - (Σ f) Ḡ → Σ_y f(y) K_y` at infinity for every Green family. -/
theorem potentialAsymptotic (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    PotentialAsymptotic p := by
  obtain ⟨κ, hκ, h2, -⟩ := hGQ 2 le_rfl p hp hp1
  obtain ⟨K, -, hK⟩ := h2 rfl
  obtain ⟨Cst, s, -, -, hy⟩ := hK 1 one_pos
  refine ⟨⟨κ, hκ⟩, fun f hf => ?_⟩
  have hae : ∀ y : Vertex 2, ∀ᵐ ω ∂latticeBondLaw 2 p,
      ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
        ∀ g : uniqueInfiniteComponent h → ℝ,
          IsGreenColumn 2 le_rfl (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
          ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
            ∀ x : uniqueInfiniteComponent h,
              ∀ z : {v : EuclideanSpace ℝ (Fin 2) // v ≠ 0},
                z.val = latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y →
                R ≤ ‖latticeEuclideanEmbedding x.val‖ →
                |g x - continuumGreen 2 le_rfl ⟨κ, hκ⟩ z - K y ω| ≤ ε := by
    intro y
    obtain ⟨M, -, -, -, hM⟩ := (hy y).2
    exact hM.mono fun ω hω h hy g hg => (hω h hy g hg).1
  filter_upwards [ae_all_iff.2 hae] with ω hω h
  refine ⟨_, fun G hG => tendsto_potential_sub_mass_mul_greenLog _ _ G
    (fun y => K y.val ω) f hf fun y => ?_⟩
  exact tendsto_column_sub_greenLog _ _ y _ _ (hω y.val h y.prop _ (hG y))

/-- The potential normalized at infinity: for a neutral charge the Green potential converges at
infinity, to a limit independent of the Green family. -/
theorem potentialLimit_of_asymptotic {p : unitInterval} (h : PotentialAsymptotic p) :
    PotentialLimit p := by
  obtain ⟨κ, hκ⟩ := h
  intro f hf
  filter_upwards [hκ f hf] with ω hω h hmass
  obtain ⟨L, hL⟩ := hω h
  exact ⟨L, fun G hG => by simpa [hmass] using hL G hG⟩

/-- `|log a - log b| ≤ 2c / b` when `b / 2 ≤ a` and `|a - b| ≤ c`. -/
theorem abs_log_sub_log_le {a b c : ℝ} (hb : 0 < b) (ha : b / 2 ≤ a) (hc : |a - b| ≤ c) :
    |Real.log a - Real.log b| ≤ 2 * c / b := by
  have ha0 : 0 < a := by linarith
  have hc0 : 0 ≤ c := (abs_nonneg _).trans hc
  rw [← Real.log_div ha0.ne' hb.ne']
  have h1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb)
  have h2 := Real.one_sub_inv_le_log_of_pos (div_pos ha0 hb)
  rw [inv_div] at h2
  rw [abs_le] at hc ⊢
  have e1 : a / b - 1 = (a - b) / b := by field_simp
  have e2 : 1 - b / a = (a - b) / a := by field_simp
  have u1 : (a - b) / b ≤ 2 * c / b := by gcongr; linarith
  have u2 : -c / a ≤ (a - b) / a := by gcongr; linarith
  have u3 : -(2 * c / b) ≤ -c / a := by
    rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ ha0 hb]
    nlinarith
  constructor <;> linarith

/-- Rate for one Green column: beyond the random scale `M`, if `|g - Ḡ(· - y) - K| ≤ C/|x - y|^(1-δ)`
then `|g - Ḡ - K| ≤ (2C + |y|/(πκ)) / |x|^(1-δ)` once `|x| ≥ max(1, M + |y|, 2|y|)`. -/
theorem abs_column_sub_greenLog_sub_le (C : OpenComponent ω) (κ : {a : ℝ // 0 < a}) (y : C)
    (g : C → ℝ) {K M Cst δ : ℝ} (hCst : 0 ≤ Cst) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hg : ∀ x : C, ∀ z : {v : EuclideanSpace ℝ (Fin 2) // v ≠ 0},
      z.val = latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y.val →
      M ≤ ‖z.val‖ → |g x - continuumGreen 2 le_rfl κ z - K| ≤ Cst / Real.rpow ‖z.val‖ (1 - δ))
    (x : C) (hx1 : 1 ≤ ‖latticeEuclideanEmbedding x.val‖)
    (hxM : M + ‖latticeEuclideanEmbedding y.val‖ ≤ ‖latticeEuclideanEmbedding x.val‖)
    (hxy : 2 * ‖latticeEuclideanEmbedding y.val‖ ≤ ‖latticeEuclideanEmbedding x.val‖) :
    |g x - greenLog κ x.val - K| ≤
      (2 * Cst + ‖latticeEuclideanEmbedding y.val‖ / (Real.pi * κ.val)) /
        ‖latticeEuclideanEmbedding x.val‖ ^ (1 - δ) := by
  have hb := abs_norm_sub_norm_le (latticeEuclideanEmbedding x.val -
    latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x.val)
  rw [sub_sub_cancel_left, norm_neg] at hb
  set t := ‖latticeEuclideanEmbedding x.val‖ with ht
  set m := ‖latticeEuclideanEmbedding y.val‖ with hm
  set r := ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y.val‖ with hr
  have hr2 : t / 2 ≤ r := by rw [abs_le] at hb; linarith
  have hrM : M ≤ r := by rw [abs_le] at hb; linarith
  have hr0 : 0 < r := by linarith
  have hxy' : latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y.val ≠ 0 :=
    norm_ne_zero_iff.1 hr0.ne'
  have h1 := hg x ⟨_, hxy'⟩ rfl hrM
  simp only [continuumGreen, if_true, Real.rpow_eq_pow] at h1
  rw [← hr] at h1
  have hlog := abs_log_sub_log_le (by linarith : 0 < t) hr2 hb
  have hexp : 0 ≤ 1 - δ := by linarith
  have htpos : 0 < t ^ (1 - δ) := Real.rpow_pos_of_pos (by linarith) _
  have hrpos : 0 < r ^ (1 - δ) := Real.rpow_pos_of_pos hr0 _
  have htle : t ^ (1 - δ) ≤ t := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : 1 - δ ≤ 1)
  have htr : t ^ (1 - δ) ≤ 2 * r ^ (1 - δ) := by
    calc t ^ (1 - δ) ≤ (2 * r) ^ (1 - δ) := Real.rpow_le_rpow (by linarith) (by linarith) hexp
      _ = 2 ^ (1 - δ) * r ^ (1 - δ) := Real.mul_rpow (by norm_num) hr0.le
      _ ≤ 2 * r ^ (1 - δ) := by
        gcongr
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith : 1 - δ ≤ 1)
  have hκ := κ.prop
  have hc : 0 < 2 * Real.pi * κ.val := by positivity
  have hT1 : Cst / r ^ (1 - δ) ≤ 2 * Cst / t ^ (1 - δ) := by
    rw [div_le_div_iff₀ hrpos htpos]; nlinarith
  have hT2 : |-Real.log r / (2 * Real.pi * κ.val) - -Real.log t / (2 * Real.pi * κ.val)| ≤
      m / (Real.pi * κ.val) / t ^ (1 - δ) := by
    rw [show -Real.log r / (2 * Real.pi * κ.val) - -Real.log t / (2 * Real.pi * κ.val) =
      -(Real.log r - Real.log t) / (2 * Real.pi * κ.val) by ring, abs_div, abs_neg,
      abs_of_pos hc]
    calc |Real.log r - Real.log t| / (2 * Real.pi * κ.val)
        ≤ 2 * m / t / (2 * Real.pi * κ.val) := by gcongr
      _ = m / (Real.pi * κ.val) / t := by field_simp
      _ ≤ m / (Real.pi * κ.val) / t ^ (1 - δ) := by gcongr
  have heq : g x - greenLog κ x.val - K =
      (g x - -Real.log r / (2 * Real.pi * κ.val) - K) +
        (-Real.log r / (2 * Real.pi * κ.val) - -Real.log t / (2 * Real.pi * κ.val)) := by
    simp only [greenLog, eucl]
    rw [← ht]
    ring
  rw [heq, add_div]
  exact (abs_add_le _ _).trans (add_le_add (h1.trans hT1) hT2)

/-- Quantitative potential asymptotics (Dario-Gu Thm 2, `d = 2`): beyond a random scale,
`|u_f - (Σ f) Ḡ - L| ≤ C / |x|^(1-δ)` for every Green family, with a deterministic constant `C`. -/
theorem potentialAsymptotic_rate (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ κ : {a : ℝ // 0 < a}, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ f : Vertex 2 → ℤ,
      (Function.support f).Finite → ∃ Cst : ℝ, ∀ᵐ ω ∂latticeBondLaw 2 p,
        ∀ h : HasUniqueInfiniteOpenComponent ω, ∃ L R : ℝ,
          ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G →
            ∀ x : uniqueInfiniteComponent h, R ≤ eucl x.val →
              |potential (uniqueInfiniteComponent h) G f x -
                (mass (uniqueInfiniteComponent h) f : ℝ) * greenLog κ x.val - L| ≤
                  Cst / eucl x.val ^ (1 - δ) := by
  obtain ⟨κ, hκ, h2, -⟩ := hGQ 2 le_rfl p hp hp1
  obtain ⟨K, -, hK⟩ := h2 rfl
  refine ⟨⟨κ, hκ⟩, fun δ hδ hδ1 f hf => ?_⟩
  obtain ⟨Cin, s, hCin, -, hy⟩ := hK δ hδ
  choose M _ hMnn _ hMae using fun y => (hy y).2
  refine ⟨∑ v ∈ hf.toFinset, |(f v : ℝ)| *
    (2 * Cin + ‖latticeEuclideanEmbedding v‖ / (Real.pi * κ)), ?_⟩
  have hae : ∀ y : Vertex 2, ∀ᵐ ω ∂latticeBondLaw 2 p,
      ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
        ∀ g : uniqueInfiniteComponent h → ℝ,
          IsGreenColumn 2 le_rfl (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
          ∀ x : uniqueInfiniteComponent h,
            ∀ z : {v : EuclideanSpace ℝ (Fin 2) // v ≠ 0},
              z.val = latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y →
              M y ω ≤ ‖z.val‖ →
              |g x - continuumGreen 2 le_rfl ⟨κ, hκ⟩ z - K y ω| ≤
                Cin / Real.rpow ‖z.val‖ (1 - δ) :=
    fun y => (hMae y).mono fun ω hω h hy g hg => (hω h hy g hg).2
  filter_upwards [ae_all_iff.2 hae] with ω hω h
  refine ⟨∑ y ∈ (hf.preimage (f := (Subtype.val : uniqueInfiniteComponent h → Vertex 2))
      Subtype.val_injective.injOn).toFinset, (f y.val : ℝ) * K y.val ω,
    1 + ∑ v ∈ hf.toFinset, (M v ω + 2 * ‖latticeEuclideanEmbedding v‖), fun G hG x hx => ?_⟩
  have hnn : ∀ v, 0 ≤ M v ω + 2 * ‖latticeEuclideanEmbedding v‖ := fun v =>
    add_nonneg (hMnn v ω) (by positivity)
  have hR : ∀ v ∈ hf.toFinset, M v ω + 2 * ‖latticeEuclideanEmbedding v‖ ≤
      ‖latticeEuclideanEmbedding x.val‖ - 1 := fun v hv => by
    have := Finset.single_le_sum (fun v _ => hnn v) hv
    simp only [eucl] at hx
    linarith
  have hx1 : 1 ≤ ‖latticeEuclideanEmbedding x.val‖ := by
    have := Finset.sum_nonneg fun v (_ : v ∈ hf.toFinset) => hnn v
    simp only [eucl] at hx
    linarith
  have hmemF : ∀ y ∈ (hf.preimage (f := (Subtype.val : uniqueInfiniteComponent h → Vertex 2))
      Subtype.val_injective.injOn).toFinset, y.val ∈ hf.toFinset := fun y hy => by
    simpa using hy
  have hpos : 0 < eucl x.val ^ (1 - δ) := Real.rpow_pos_of_pos (by simp only [eucl]; linarith) _
  have hκ0 : 0 < Real.pi * κ := by positivity
  rw [potential_sub_mass_mul_eq_sum _ G f hf, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ y ∈ (hf.preimage (f := (Subtype.val : uniqueInfiniteComponent h → Vertex 2))
          Subtype.val_injective.injOn).toFinset, |(f y.val : ℝ)| *
          ((2 * Cin + ‖latticeEuclideanEmbedding y.val‖ / (Real.pi * κ)) /
            eucl x.val ^ (1 - δ)) := by
        refine Finset.sum_le_sum fun y hy => ?_
        rw [← mul_sub, abs_mul]
        have hRy := hR _ (hmemF y hy)
        have hMy := hMnn y.val ω
        have hny := norm_nonneg (latticeEuclideanEmbedding y.val)
        gcongr
        exact abs_column_sub_greenLog_sub_le _ ⟨κ, hκ⟩ y (fun x => G x y) hCin.le hδ.le hδ1
          (hω y.val h y.prop _ (hG y)) x hx1 (by linarith) (by linarith)
    _ = (∑ v ∈ (hf.preimage (f := (Subtype.val : uniqueInfiniteComponent h → Vertex 2))
          Subtype.val_injective.injOn).toFinset.map (Function.Embedding.subtype _),
          |(f v : ℝ)| * (2 * Cin + ‖latticeEuclideanEmbedding v‖ / (Real.pi * κ))) /
            eucl x.val ^ (1 - δ) := by
        rw [Finset.sum_map, Finset.sum_div]
        exact Finset.sum_congr rfl fun y _ => by simp [mul_div_assoc]
    _ ≤ _ := by
        gcongr
        intro v hv
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hv
        exact hmemF y hy

end Rigidity.Proofs.Section5
