import Rigidity.Proofs.Green.DarioGuFluxInput

/-!
# The energy estimate of Step 2 of the proof of Theorem 5 of Dario–Gu

Step 2 of the proof of Theorem 5 of Dario–Gu (lines 1418-1452 of the source) bounds a function
`v = w - u` on the cylinder `[a, b] × V`, `V ⊆ ℤ²` finite, which vanishes on `∂_a V = V \ int_a(V)`
and at the initial time, by the `L²(H̲^{-1})` norm of `(∂_t - Δ) v`: the discrete integration by
parts (1.29), the sign of `∫ ∂_t v · v`, the duality (1.33) and the Poincaré inequality for
functions vanishing on the boundary. This file proves this step for unit conductances on the open
edges, with the Poincaré inequality and the weak norm bound as hypotheses.

* `clusterDirEnergy ω V g = Σ_{x ∈ V} Σ_{z ∈ V, z ∼ x} (g(z) - g(x))²` (twice the energy over the
  open edges inside `V`) and `clusterGradSq ω V g = Σ_{x ∈ V} |∇g|(x)²` (the square of the
  unnormalized norm (1.31)); `clusterDirEnergy ≤ clusterGradSq ≤ 4 clusterDirEnergy`;
* `sum_neg_openLaplacian_mul`: for `g` vanishing on `∂_a V`,
  `Σ_{x ∈ V} (-Δg)(x) g(x) = clusterDirEnergy ω V g / 2` ((1.29));
* `sum_mul_le_of_weakNormLe`: if `‖g‖_{H̲^{-1}(V)} ≤ B`, `v` vanishes on `∂_a V` and
  `Σ_V v² ≤ P² Σ_V |∇v|²`, then `Σ_V g v ≤ |B| (P + |V|^{1/2}) (Σ_V |∇v|²)^{1/2}`;
* `integral_sum_sq_le_of_energy`: if moreover `v` solves `∂_t v - Δ v = g` at the points of
  `int_a(V)` for `t ∈ (a, b)` and `v(a) = 0`, then
  `∫_a^b Σ_V v² ≤ 64 P² (P + |V|^{1/2})² ∫_a^b B²`.

With `[a, b] = [-r², 0]`, `P = C r` (the Poincaré inequality of Proposition 2.7 for functions
vanishing on `∂(ℤ² ∩ B_r) ∩ 𝒞_∞`) and `|V| ≤ 25 r²`, the last estimate reads
`r^{-1} ‖v‖_{L̲²(I_r × V)} ≤ 8 C (C + 5) r |V|^{-1/2} ‖B‖_{L̲²(I_r)}`, the conclusion of Step 2
(the source has the constant `λ^{-1}` and normalized norms; with `|V| ≥ c r²` the factor
`r |V|^{-1/2}` is bounded). In Step 2 of the source, `v = w - u` is required to vanish on `∂_a V`;
the hypothesis `hbd` below is that requirement.
-/

open scoped Classical
open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Green

/-- `Σ_{x ∈ V} Σ_{z ∈ V, z ∼ x} (g(z) - g(x))²`, twice the energy of `g` on the open edges inside
`V`. -/
noncomputable def clusterDirEnergy (ω : Configuration 2) (V : Finset (Vertex 2))
    (g : Vertex 2 → ℝ) : ℝ :=
  ∑ x ∈ V, ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), (g z - g x) ^ 2

/-- `Σ_{x ∈ V} |∇g|(x)²`, with `|∇g|(x) = Σ_{z ∈ V, z ∼ x} |g(z) - g(x)|` ((1.31), unnormalized). -/
noncomputable def clusterGradSq (ω : Configuration 2) (V : Finset (Vertex 2))
    (g : Vertex 2 → ℝ) : ℝ :=
  ∑ x ∈ V, openGradNorm ω V g x ^ 2

theorem openGradNorm_eq_sum_filter (ω : Configuration 2) (V : Finset (Vertex 2))
    (g : Vertex 2 → ℝ) (x : Vertex 2) :
    openGradNorm ω V g x = ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), |g z - g x| := by
  rw [openGradNorm, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨-, h, hz⟩
    exact ⟨hz, h⟩
  · rintro ⟨hz, h⟩
    exact ⟨LatticeProb.Graph.Zd.mem_nbrFinset.mpr
      (LatticeProb.Graph.Zd.adj_iff.mp (openGraph_le ω h)), h, hz⟩

theorem card_filter_adj_le (ω : Configuration 2) (V : Finset (Vertex 2)) (x : Vertex 2) :
    ((V.filter (fun z => (openGraph ω).Adj x z)).card : ℝ) ≤ 4 := by
  have hsub : V.filter (fun z => (openGraph ω).Adj x z) ⊆ (openGraph ω).neighborFinset x := by
    intro z hz
    rw [SimpleGraph.mem_neighborFinset]
    exact (Finset.mem_filter.1 hz).2
  have h1 := Finset.card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
  have h2 := openGraph_degree_le ω x
  have h3 : (V.filter (fun z => (openGraph ω).Adj x z)).card ≤ 4 := by omega
  exact_mod_cast h3

theorem clusterGradSq_nonneg (ω : Configuration 2) (V : Finset (Vertex 2))
    (g : Vertex 2 → ℝ) : 0 ≤ clusterGradSq ω V g :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem clusterDirEnergy_le_clusterGradSq (ω : Configuration 2) (V : Finset (Vertex 2))
    (g : Vertex 2 → ℝ) : clusterDirEnergy ω V g ≤ clusterGradSq ω V g := by
  unfold clusterDirEnergy clusterGradSq
  refine Finset.sum_le_sum fun x _ => ?_
  rw [openGradNorm_eq_sum_filter]
  set S := V.filter (fun z => (openGraph ω).Adj x z)
  calc ∑ z ∈ S, (g z - g x) ^ 2 = ∑ z ∈ S, |g z - g x| * |g z - g x| := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← sq, sq_abs]
    _ ≤ ∑ z ∈ S, |g z - g x| * ∑ w ∈ S, |g w - g x| := by
        refine Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact Finset.single_le_sum (f := fun w => |g w - g x|) (fun w _ => abs_nonneg _) hz
    _ = (∑ z ∈ S, |g z - g x|) ^ 2 := by rw [← Finset.sum_mul, sq]

theorem clusterGradSq_le_four_mul (ω : Configuration 2) (V : Finset (Vertex 2))
    (g : Vertex 2 → ℝ) : clusterGradSq ω V g ≤ 4 * clusterDirEnergy ω V g := by
  unfold clusterDirEnergy clusterGradSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [openGradNorm_eq_sum_filter]
  set S := V.filter (fun z => (openGraph ω).Adj x z)
  calc (∑ z ∈ S, |g z - g x|) ^ 2 ≤ S.card * ∑ z ∈ S, |g z - g x| ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ = S.card * ∑ z ∈ S, (g z - g x) ^ 2 := by simp only [sq_abs]
    _ ≤ 4 * ∑ z ∈ S, (g z - g x) ^ 2 :=
        mul_le_mul_of_nonneg_right (card_filter_adj_le ω V x)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Exchanging the two endpoints of the open edges inside `V`. -/
theorem sum_filter_adj_comm (ω : Configuration 2) (V : Finset (Vertex 2))
    (F : Vertex 2 → Vertex 2 → ℝ) :
    ∑ x ∈ V, ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), F x z =
      ∑ x ∈ V, ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), F z x := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
  by_cases h : (openGraph ω).Adj x z
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun h' => h h'.symm), if_neg h]

/-- **Discrete integration by parts** (Dario–Gu, (1.29)) for a function vanishing on `∂_a V`:
`Σ_{x ∈ V} (-Δg)(x) g(x) = clusterDirEnergy ω V g / 2`. -/
theorem sum_neg_openLaplacian_mul (ω : Configuration 2) (V : Finset (Vertex 2))
    {g : Vertex 2 → ℝ} (hg : ∀ x ∈ V, x ∉ openInterior ω V → g x = 0) :
    ∑ x ∈ V, -openLaplacian ω g x * g x = clusterDirEnergy ω V g / 2 := by
  have h1 : ∀ x ∈ V, -openLaplacian ω g x * g x =
      ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), (g x - g z) * g x := by
    intro x hx
    by_cases hi : x ∈ openInterior ω V
    · have hN : (openGraph ω).neighborFinset x = V.filter (fun z => (openGraph ω).Adj x z) := by
        ext z
        rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
        exact ⟨fun h => ⟨hi.2 z h, h⟩, fun h => h.2⟩
      rw [openLaplacian, hN, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring
    · rw [hg x hx hi]
      simp
  rw [Finset.sum_congr rfl h1]
  have hswap := sum_filter_adj_comm ω V (fun x z => (g x - g z) * g x)
  have hdouble : ∑ x ∈ V, ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), (g x - g z) * g x +
      ∑ x ∈ V, ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), (g z - g x) * g z =
      clusterDirEnergy ω V g := by
    rw [← Finset.sum_add_distrib, clusterDirEnergy]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  linarith

/-- The `H̲¹` norm (1.32) of a function satisfying the Poincaré inequality
`Σ_V v² ≤ P² Σ_V |∇v|²`: `|V| ‖v‖_{H̲¹(V)} ≤ (P + |V|^{1/2}) (Σ_V |∇v|²)^{1/2}`. -/
theorem card_mul_clusterH1Norm_le (ω : Configuration 2) {V : Finset (Vertex 2)}
    (hV : V.Nonempty) {v : Vertex 2 → ℝ} {P : ℝ} (hP : 0 ≤ P)
    (hpoinc : ∑ x ∈ V, v x ^ 2 ≤ P ^ 2 * clusterGradSq ω V v) :
    (V.card : ℝ) * clusterH1Norm ω V v ≤
      (P + Real.sqrt V.card) * Real.sqrt (clusterGradSq ω V v) := by
  have hc : (0 : ℝ) < V.card := by exact_mod_cast hV.card_pos
  set c : ℝ := (V.card : ℝ) with hcdef
  set G := clusterGradSq ω V v with hGdef
  have hG : 0 ≤ G := clusterGradSq_nonneg ω V v
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hA : Real.sqrt (c⁻¹ * ∑ x ∈ V, v x ^ 2) ≤ P * Real.sqrt (c⁻¹ * G) := by
    rw [← Real.sqrt_sq hP, ← Real.sqrt_mul (sq_nonneg P)]
    refine Real.sqrt_le_sqrt ?_
    calc c⁻¹ * ∑ x ∈ V, v x ^ 2 ≤ c⁻¹ * (P ^ 2 * G) :=
          mul_le_mul_of_nonneg_left hpoinc (inv_nonneg.2 hc.le)
      _ = P ^ 2 * (c⁻¹ * G) := by ring
  have hpow : c ^ (-(1 / 2 : ℝ)) = (Real.sqrt c)⁻¹ := by
    rw [Real.rpow_neg hc.le, Real.sqrt_eq_rpow]
  have hsq : Real.sqrt (c⁻¹ * G) = (Real.sqrt c)⁻¹ * Real.sqrt G := by
    rw [Real.sqrt_mul (inv_nonneg.2 hc.le), Real.sqrt_inv]
  have hcs : c = Real.sqrt c * Real.sqrt c := (Real.mul_self_sqrt hc.le).symm
  have hgrad : clusterH1Norm ω V v ≤
      c ^ (-(1 / 2 : ℝ)) * (P * Real.sqrt (c⁻¹ * G)) + Real.sqrt (c⁻¹ * G) := by
    unfold clusterH1Norm
    rw [← hcdef, ← hGdef.trans (by rfl : clusterGradSq ω V v = ∑ x ∈ V, openGradNorm ω V v x ^ 2)]
    exact add_le_add (mul_le_mul_of_nonneg_left hA (by positivity)) le_rfl
  calc c * clusterH1Norm ω V v
      ≤ c * (c ^ (-(1 / 2 : ℝ)) * (P * Real.sqrt (c⁻¹ * G)) + Real.sqrt (c⁻¹ * G)) :=
        mul_le_mul_of_nonneg_left hgrad hc.le
    _ = (P + Real.sqrt c) * Real.sqrt G := by
        rw [hpow, hsq]
        obtain ⟨σ, hσ⟩ : ∃ σ, σ = Real.sqrt c := ⟨_, rfl⟩
        have hσ0 : σ ≠ 0 := by rw [hσ]; exact hs.ne'
        have hc' : c = σ * σ := by rw [hσ]; exact hcs
        rw [← hσ, hc']
        field_simp

/-- **The duality step** of Step 2: if `‖g‖_{H̲^{-1}(V)} ≤ B` ((1.33)), `v` vanishes on `∂_a V`
and `Σ_V v² ≤ P² Σ_V |∇v|²`, then `Σ_V g v ≤ |B| (P + |V|^{1/2}) (Σ_V |∇v|²)^{1/2}`. -/
theorem sum_mul_le_of_weakNormLe (ω : Configuration 2) {V : Finset (Vertex 2)}
    {g v : Vertex 2 → ℝ} {B P : ℝ} (hP : 0 ≤ P) (hw : WeakNormLe ω V g B)
    (hv : ∀ x ∈ V, x ∉ openInterior ω V → v x = 0)
    (hpoinc : ∑ x ∈ V, v x ^ 2 ≤ P ^ 2 * clusterGradSq ω V v) :
    ∑ x ∈ V, g x * v x ≤ |B| * ((P + Real.sqrt V.card) * Real.sqrt (clusterGradSq ω V v)) := by
  rcases V.eq_empty_or_nonempty with rfl | hV
  · simp only [Finset.sum_empty]
    have : 0 ≤ Real.sqrt (clusterGradSq ω ∅ v) := Real.sqrt_nonneg _
    positivity
  have hc : (0 : ℝ) < V.card := by exact_mod_cast hV.card_pos
  have h1 := hw v hv
  have hH : 0 ≤ clusterH1Norm ω V v := by
    unfold clusterH1Norm
    positivity
  have h2 : ∑ x ∈ V, g x * v x ≤ (V.card : ℝ) * (B * clusterH1Norm ω V v) := by
    have := mul_le_mul_of_nonneg_left h1 hc.le
    rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this
  calc ∑ x ∈ V, g x * v x ≤ (V.card : ℝ) * (B * clusterH1Norm ω V v) := h2
    _ ≤ (V.card : ℝ) * (|B| * clusterH1Norm ω V v) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self B) hH) hc.le
    _ = |B| * ((V.card : ℝ) * clusterH1Norm ω V v) := by ring
    _ ≤ |B| * ((P + Real.sqrt V.card) * Real.sqrt (clusterGradSq ω V v)) :=
        mul_le_mul_of_nonneg_left (card_mul_clusterH1Norm_le ω hV hP hpoinc) (abs_nonneg B)

/-- Comparison of interval integrals from a bound on the open interval. -/
theorem intervalIntegral_mono_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (h : ∀ t ∈ Set.Ioo a b, f t ≤ g t) : ∫ t in a..b, f t ≤ ∫ t in a..b, g t := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_mono_on (hf.1.mono_set Set.Ioo_subset_Ioc_self)
    (hg.1.mono_set Set.Ioo_subset_Ioc_self) measurableSet_Ioo h

theorem continuousOn_clusterGradSq (ω : Configuration 2) {V : Finset (Vertex 2)} {a b : ℝ}
    {v : ℝ → Vertex 2 → ℝ} (hcont : ∀ x ∈ V, ContinuousOn (fun t => v t x) (Set.Icc a b)) :
    ContinuousOn (fun t => clusterGradSq ω V (v t)) (Set.Icc a b) := by
  unfold clusterGradSq
  simp only [openGradNorm_eq_sum_filter]
  refine continuousOn_finsetSum _ fun x hx => ?_
  refine (continuousOn_finsetSum _ fun z hz => ?_).pow 2
  exact ((hcont z (Finset.mem_filter.1 hz).1).sub (hcont x hx)).abs

theorem continuousOn_clusterDirEnergy (ω : Configuration 2) {V : Finset (Vertex 2)} {a b : ℝ}
    {v : ℝ → Vertex 2 → ℝ} (hcont : ∀ x ∈ V, ContinuousOn (fun t => v t x) (Set.Icc a b)) :
    ContinuousOn (fun t => clusterDirEnergy ω V (v t)) (Set.Icc a b) := by
  unfold clusterDirEnergy
  refine continuousOn_finsetSum _ fun x hx => continuousOn_finsetSum _ fun z hz => ?_
  exact ((hcont z (Finset.mem_filter.1 hz).1).sub (hcont x hx)).pow 2

/-- **Step 2 of the proof of Theorem 5 of Dario–Gu** (lines 1418-1452), for unit conductances:
if `v` is continuous in time on `[a, b] × V`, vanishes on `∂_a V` and at the time `a`, solves
`∂_t v - Δ v = g` at the points of `int_a(V)` for `t ∈ (a, b)`, satisfies the Poincaré inequality
`Σ_V v(t)² ≤ P² Σ_V |∇v(t)|²` and `‖g(t)‖_{H̲^{-1}(V)} ≤ B(t)`, then
`∫_a^b Σ_V v² ≤ 64 P² (P + |V|^{1/2})² ∫_a^b B²`. -/
theorem integral_sum_sq_le_of_energy (ω : Configuration 2) {V : Finset (Vertex 2)} {a b P : ℝ}
    (hab : a ≤ b) (hP : 0 ≤ P) {v dv g : ℝ → Vertex 2 → ℝ} {B : ℝ → ℝ}
    (hcont : ∀ x ∈ V, ContinuousOn (fun t => v t x) (Set.Icc a b))
    (hderiv : ∀ x ∈ V, ∀ t ∈ Set.Ioo a b, HasDerivAt (fun s => v s x) (dv t x) t)
    (hdv : ∀ x ∈ V, IntervalIntegrable (fun t => dv t x) volume a b)
    (hbd : ∀ t ∈ Set.Icc a b, ∀ x ∈ V, x ∉ openInterior ω V → v t x = 0)
    (hinit : ∀ x ∈ V, v a x = 0)
    (heq : ∀ t ∈ Set.Ioo a b, ∀ x ∈ openInterior ω V,
      dv t x - openLaplacian ω (v t) x = g t x)
    (hweak : ∀ t ∈ Set.Ioo a b, WeakNormLe ω V (g t) (B t))
    (hB : IntervalIntegrable (fun t => B t ^ 2) volume a b)
    (hpoinc : ∀ t ∈ Set.Ioo a b, ∑ x ∈ V, v t x ^ 2 ≤ P ^ 2 * clusterGradSq ω V (v t)) :
    ∫ t in a..b, ∑ x ∈ V, v t x ^ 2 ≤
      64 * P ^ 2 * (P + Real.sqrt V.card) ^ 2 * ∫ t in a..b, B t ^ 2 := by
  set K := P + Real.sqrt V.card with hK
  have hK0 : 0 ≤ K := add_nonneg hP (Real.sqrt_nonneg _)
  have hIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  set G : ℝ → ℝ := fun t => clusterGradSq ω V (v t) with hGdef
  set E : ℝ → ℝ := fun t => clusterDirEnergy ω V (v t) / 2 with hEdef
  set S : ℝ → ℝ := fun t => ∑ x ∈ V, dv t x * v t x with hSdef
  have hGc : ContinuousOn G (Set.Icc a b) := continuousOn_clusterGradSq ω hcont
  have hEc : ContinuousOn E (Set.Icc a b) := (continuousOn_clusterDirEnergy ω hcont).div_const 2
  have hGi : IntervalIntegrable G volume a b := (hIcc ▸ hGc).intervalIntegrable
  have hEi : IntervalIntegrable E volume a b := (hIcc ▸ hEc).intervalIntegrable
  have hterm : ∀ x ∈ V, IntervalIntegrable (fun t => dv t x * v t x) volume a b :=
    fun x hx => (hdv x hx).mul_continuousOn (hIcc ▸ hcont x hx)
  have hSi : IntervalIntegrable S volume a b := by
    have h := IntervalIntegrable.sum V hterm
    rw [Finset.sum_fn] at h
    exact h
  have hvsq : ContinuousOn (fun t => ∑ x ∈ V, v t x ^ 2) (Set.Icc a b) :=
    continuousOn_finsetSum _ fun x hx => (hcont x hx).pow 2
  have hvi : IntervalIntegrable (fun t => ∑ x ∈ V, v t x ^ 2) volume a b :=
    (hIcc ▸ hvsq).intervalIntegrable
  -- the time derivative term has a nonnegative integral
  have hSint : 0 ≤ ∫ t in a..b, S t := by
    have hx : ∀ x ∈ V, ∫ t in a..b, dv t x * v t x = v b x ^ 2 / 2 - v a x ^ 2 / 2 := by
      intro x hx
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
        (((hcont x hx).pow 2).div_const 2) (fun t ht => ?_) (hterm x hx)
      have h := ((hderiv x hx t ht).pow 2).div_const 2
      refine h.congr_deriv ?_
      rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
      push_cast
      ring
    rw [hSdef, intervalIntegral.integral_finsetSum hterm, Finset.sum_congr rfl hx]
    refine Finset.sum_nonneg fun x hx => ?_
    rw [hinit x hx]
    nlinarith [sq_nonneg (v b x)]
  -- the pointwise bound on the open interval
  have hpt : ∀ t ∈ Set.Ioo a b, E t + S t ≤ G t / 16 + 4 * K ^ 2 * B t ^ 2 := by
    intro t ht
    have htI : t ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ht
    have hv0 : ∀ x ∈ V, x ∉ openInterior ω V → v t x = 0 := hbd t htI
    have hsplit : ∑ x ∈ V, g t x * v t x = S t + E t := by
      have h1 : ∀ x ∈ V, g t x * v t x = dv t x * v t x + -openLaplacian ω (v t) x * v t x := by
        intro x hx
        by_cases hi : x ∈ openInterior ω V
        · rw [← heq t ht x hi]
          ring
        · rw [hv0 x hx hi]
          ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, sum_neg_openLaplacian_mul ω V hv0]
    have hdual := sum_mul_le_of_weakNormLe ω hP (hweak t ht) hv0 (hpoinc t ht)
    have hG0 : 0 ≤ G t := clusterGradSq_nonneg ω V (v t)
    have hsq : Real.sqrt (G t) ^ 2 = G t := Real.sq_sqrt hG0
    have hamgm : |B t| * (K * Real.sqrt (G t)) ≤ G t / 16 + 4 * K ^ 2 * B t ^ 2 := by
      have := sq_nonneg (Real.sqrt (G t) / 4 - 2 * |B t| * K)
      have hB2 : |B t| ^ 2 = B t ^ 2 := sq_abs _
      nlinarith
    calc E t + S t = ∑ x ∈ V, g t x * v t x := by rw [hsplit]; ring
      _ ≤ |B t| * (K * Real.sqrt (G t)) := hdual
      _ ≤ G t / 16 + 4 * K ^ 2 * B t ^ 2 := hamgm
  have hRi : IntervalIntegrable (fun t => G t / 16 + 4 * K ^ 2 * B t ^ 2) volume a b :=
    (hGi.div_const 16).add (hB.const_mul _)
  have hmain := intervalIntegral_mono_Ioo hab (hEi.add hSi) hRi hpt
  rw [intervalIntegral.integral_add hEi hSi, intervalIntegral.integral_add (hGi.div_const 16)
    (hB.const_mul _)] at hmain
  have e1 : ∫ t in a..b, G t / 16 = (∫ t in a..b, G t) / 16 := intervalIntegral.integral_div 16 G
  have e2 : ∫ t in a..b, G t / 8 = (∫ t in a..b, G t) / 8 := intervalIntegral.integral_div 8 G
  have e3 : ∫ t in a..b, 4 * K ^ 2 * B t ^ 2 = 4 * K ^ 2 * ∫ t in a..b, B t ^ 2 :=
    intervalIntegral.integral_const_mul _ _
  -- the energy controls the gradient
  have hEG : ∫ t in a..b, G t / 8 ≤ ∫ t in a..b, E t := by
    refine intervalIntegral.integral_mono_on hab (hGi.div_const 8) hEi fun t _ => ?_
    have := clusterGradSq_le_four_mul ω V (v t)
    simp only [hGdef, hEdef]
    linarith
  have hGbound : ∫ t in a..b, G t ≤ 64 * K ^ 2 * ∫ t in a..b, B t ^ 2 := by linarith
  have hfin : ∫ t in a..b, ∑ x ∈ V, v t x ^ 2 ≤ ∫ t in a..b, P ^ 2 * G t :=
    intervalIntegral_mono_Ioo hab hvi (hGi.const_mul _) hpoinc
  rw [intervalIntegral.integral_const_mul] at hfin
  calc ∫ t in a..b, ∑ x ∈ V, v t x ^ 2 ≤ P ^ 2 * ∫ t in a..b, G t := hfin
    _ ≤ P ^ 2 * (64 * K ^ 2 * ∫ t in a..b, B t ^ 2) :=
        mul_le_mul_of_nonneg_left hGbound (sq_nonneg P)
    _ = 64 * P ^ 2 * K ^ 2 * ∫ t in a..b, B t ^ 2 := by ring

end Rigidity.Green
