import Rigidity.Proofs.Green.ClusterParabolicEnergy

/-!
# Estimates of the weak norm on a finite set of the planar cluster

The estimates of the terms of the two-scale expansion in Step 3 of the proof of Theorem 5 of
Dario–Gu (lines 1488-1501 of the source) use three properties of the norm `H̲^{-1}(V)` of (1.33),
`V ⊆ ℤ²` finite, with unit conductances on the open edges. This file proves them, together with the
linearity of the bound.

* `weakNormLe_sqrt_sum_sq` ((3.27)): `‖A‖_{H̲^{-1}(V)} ≤ (Σ_V A²)^{1/2} = |V|^{1/2} ‖A‖_{L̲²(V)}`
  (the source writes `r ‖A‖_{L̲²}`, with `|V| ≤ C r²`);
* `WeakNormLe.mul_right` ((3.26)): if `‖A‖_{H̲^{-1}(V)} ≤ a`, `|B| ≤ M` and `|∇B| ≤ N` on `V`, then
  `‖A B‖_{H̲^{-1}(V)} ≤ a (M + |V|^{1/2} N)` (the source writes `‖B‖_∞ + r ‖∇B‖_∞`);
* `weakNormLe_sum_antisymm` (the first lines of (3.30) and (3.32)): for an antisymmetric function
  `F` on the open edges inside `V`, `‖Σ_{z ∼ x} F(x, z)‖_{H̲^{-1}(V)} ≤ ‖F‖_{L̲²(V)} / 2`, with
  `‖F‖_{L̲²(V)}² = |V|^{-1} Σ_{x ∈ V} Σ_{z ∈ V, z ∼ x} F(x, z)²`;
* `WeakNormLe.neg`, `WeakNormLe.const_mul`, `WeakNormLe.sum`.
-/

open scoped Classical
open LatticeProb.Percolation

namespace Rigidity.Green

theorem clusterH1Norm_nonneg (ω : Configuration 2) (V : Finset (Vertex 2)) (v : Vertex 2 → ℝ) :
    0 ≤ clusterH1Norm ω V v := by
  unfold clusterH1Norm
  positivity

/-- The `L²` part of the norm (1.32): `|V|^{-1} (Σ_V v²)^{1/2} ≤ ‖v‖_{H̲¹(V)}`. -/
theorem inv_card_mul_sqrt_le_clusterH1Norm (ω : Configuration 2) {V : Finset (Vertex 2)}
    (hV : V.Nonempty) (v : Vertex 2 → ℝ) :
    (V.card : ℝ)⁻¹ * Real.sqrt (∑ x ∈ V, v x ^ 2) ≤ clusterH1Norm ω V v := by
  have hc : (0 : ℝ) < V.card := by exact_mod_cast hV.card_pos
  have hs : 0 < Real.sqrt (V.card : ℝ) := Real.sqrt_pos.2 hc
  have e : (V.card : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt ((V.card : ℝ)⁻¹ * ∑ x ∈ V, v x ^ 2) =
      (V.card : ℝ)⁻¹ * Real.sqrt (∑ x ∈ V, v x ^ 2) := by
    rw [Real.rpow_neg hc.le, ← Real.sqrt_eq_rpow, Real.sqrt_mul (inv_nonneg.2 hc.le),
      Real.sqrt_inv, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hc.le]
  unfold clusterH1Norm
  rw [e]
  exact le_add_of_nonneg_right (Real.sqrt_nonneg _)

/-- The gradient part of the norm (1.32): `|V|^{-1/2} (Σ_V |∇v|²)^{1/2} ≤ ‖v‖_{H̲¹(V)}`. -/
theorem inv_sqrt_card_mul_sqrt_le_clusterH1Norm (ω : Configuration 2) {V : Finset (Vertex 2)}
    (hV : V.Nonempty) (v : Vertex 2 → ℝ) :
    (Real.sqrt V.card)⁻¹ * Real.sqrt (clusterGradSq ω V v) ≤ clusterH1Norm ω V v := by
  have hc : (0 : ℝ) < V.card := by exact_mod_cast hV.card_pos
  have e : Real.sqrt ((V.card : ℝ)⁻¹ * ∑ x ∈ V, openGradNorm ω V v x ^ 2) =
      (Real.sqrt V.card)⁻¹ * Real.sqrt (clusterGradSq ω V v) := by
    rw [Real.sqrt_mul (inv_nonneg.2 hc.le), Real.sqrt_inv]
    rfl
  unfold clusterH1Norm
  rw [e]
  exact le_add_of_nonneg_left (by positivity)

/-- The triangle inequality for the Euclidean norm of finite families. -/
theorem sqrt_sum_sq_add_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    Real.sqrt (∑ i ∈ s, (f i + g i) ^ 2) ≤
      Real.sqrt (∑ i ∈ s, f i ^ 2) + Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have hF : 0 ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hG : 0 ≤ ∑ i ∈ s, g i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfg := Real.sum_mul_le_sqrt_mul_sqrt s f g
  have e : ∑ i ∈ s, (f i + g i) ^ 2 =
      ∑ i ∈ s, f i ^ 2 + ∑ i ∈ s, g i ^ 2 + 2 * ∑ i ∈ s, f i * g i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hle : ∑ i ∈ s, (f i + g i) ^ 2 ≤
      (Real.sqrt (∑ i ∈ s, f i ^ 2) + Real.sqrt (∑ i ∈ s, g i ^ 2)) ^ 2 := by
    rw [e, add_sq, Real.sq_sqrt hF, Real.sq_sqrt hG]
    nlinarith
  calc Real.sqrt (∑ i ∈ s, (f i + g i) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ i ∈ s, f i ^ 2) + Real.sqrt (∑ i ∈ s, g i ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt (∑ i ∈ s, f i ^ 2) + Real.sqrt (∑ i ∈ s, g i ^ 2) :=
        Real.sqrt_sq (by positivity)

/-- **Dario–Gu, (3.27)**: `‖A‖_{H̲^{-1}(V)} ≤ (Σ_V A²)^{1/2}`. -/
theorem weakNormLe_sqrt_sum_sq (ω : Configuration 2) (V : Finset (Vertex 2))
    (A : Vertex 2 → ℝ) : WeakNormLe ω V A (Real.sqrt (∑ x ∈ V, A x ^ 2)) := by
  intro v _
  rcases V.eq_empty_or_nonempty with rfl | hV
  · simp
  have hc : (0 : ℝ) < V.card := by exact_mod_cast hV.card_pos
  calc (V.card : ℝ)⁻¹ * ∑ x ∈ V, A x * v x
      ≤ (V.card : ℝ)⁻¹ * (Real.sqrt (∑ x ∈ V, A x ^ 2) * Real.sqrt (∑ x ∈ V, v x ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (inv_nonneg.2 hc.le)
    _ = Real.sqrt (∑ x ∈ V, A x ^ 2) * ((V.card : ℝ)⁻¹ * Real.sqrt (∑ x ∈ V, v x ^ 2)) := by ring
    _ ≤ Real.sqrt (∑ x ∈ V, A x ^ 2) * clusterH1Norm ω V v :=
        mul_le_mul_of_nonneg_left (inv_card_mul_sqrt_le_clusterH1Norm ω hV v) (Real.sqrt_nonneg _)

/-- The pointwise product rule for `|∇(B v)|`: `|∇(B v)|(x) ≤ M |∇v|(x) + |v(x)| |∇B|(x)` when
`|B| ≤ M` on `V`. -/
theorem openGradNorm_mul_le (ω : Configuration 2) (V : Finset (Vertex 2)) {B v : Vertex 2 → ℝ}
    {M : ℝ} (hM : ∀ x ∈ V, |B x| ≤ M) (x : Vertex 2) :
    openGradNorm ω V (fun y => B y * v y) x ≤
      M * openGradNorm ω V v x + |v x| * openGradNorm ω V B x := by
  simp only [openGradNorm_eq_sum_filter]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z hz => ?_
  have hzV := (Finset.mem_filter.1 hz).1
  have e : B z * v z - B x * v x = B z * (v z - v x) + v x * (B z - B x) := by ring
  rw [e]
  calc |B z * (v z - v x) + v x * (B z - B x)|
      ≤ |B z * (v z - v x)| + |v x * (B z - B x)| := abs_add_le _ _
    _ = |B z| * |v z - v x| + |v x| * |B z - B x| := by rw [abs_mul, abs_mul]
    _ ≤ M * |v z - v x| + |v x| * |B z - B x| :=
        add_le_add_left (mul_le_mul_of_nonneg_right (hM z hzV) (abs_nonneg _)) _

/-- **Dario–Gu, (3.26)**: if `‖A‖_{H̲^{-1}(V)} ≤ a`, `|B| ≤ M` and `|∇B| ≤ N` on `V`, then
`‖A B‖_{H̲^{-1}(V)} ≤ a (M + |V|^{1/2} N)`. -/
theorem WeakNormLe.mul_right {ω : Configuration 2} {V : Finset (Vertex 2)} {A B : Vertex 2 → ℝ}
    {a M N : ℝ} (hA : WeakNormLe ω V A a) (ha : 0 ≤ a) (hM : ∀ x ∈ V, |B x| ≤ M)
    (hN : ∀ x ∈ V, openGradNorm ω V B x ≤ N) :
    WeakNormLe ω V (fun x => A x * B x) (a * (M + Real.sqrt V.card * N)) := by
  intro v hv
  rcases V.eq_empty_or_nonempty with rfl | hV
  · simp [clusterH1Norm]
  have hc : (0 : ℝ) < V.card := by exact_mod_cast hV.card_pos
  obtain ⟨x0, hx0⟩ := hV
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x0 hx0)
  have hN0 : 0 ≤ N := by
    have : 0 ≤ openGradNorm ω V B x0 := by
      rw [openGradNorm_eq_sum_filter]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact this.trans (hN x0 hx0)
  have hV : V.Nonempty := ⟨x0, hx0⟩
  set w : Vertex 2 → ℝ := fun y => B y * v y with hwdef
  have hw : ∀ x ∈ V, x ∉ openInterior ω V → w x = 0 := fun x hx hi => by
    simp only [hwdef, hv x hx hi, mul_zero]
  have h1 := hA w hw
  have hsum : ∑ x ∈ V, A x * B x * v x = ∑ x ∈ V, A x * w x :=
    Finset.sum_congr rfl fun x _ => by simp only [hwdef]; ring
  -- the two parts of the norm of `w`
  set L := Real.sqrt (∑ x ∈ V, v x ^ 2) with hL
  set Gv := Real.sqrt (clusterGradSq ω V v) with hGv
  have hwL : Real.sqrt (∑ x ∈ V, w x ^ 2) ≤ M * L := by
    rw [hL, ← Real.sqrt_sq hM0, ← Real.sqrt_mul (sq_nonneg M), Finset.mul_sum]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun x hx => ?_)
    simp only [hwdef]
    rw [mul_pow]
    have := hM x hx
    have hB2 : B x ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    exact mul_le_mul_of_nonneg_right hB2 (sq_nonneg _)
  have hwG : Real.sqrt (clusterGradSq ω V w) ≤ M * Gv + N * L := by
    have hpt : ∀ x ∈ V, openGradNorm ω V w x ^ 2 ≤
        (M * openGradNorm ω V v x + N * |v x|) ^ 2 := by
      intro x hx
      have h0 : 0 ≤ openGradNorm ω V w x := by
        rw [openGradNorm_eq_sum_filter]
        exact Finset.sum_nonneg fun _ _ => abs_nonneg _
      have h2 := openGradNorm_mul_le ω V (v := v) hM x
      have h3 : |v x| * openGradNorm ω V B x ≤ N * |v x| := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hN x hx) (abs_nonneg _)
      exact pow_le_pow_left₀ h0 (h2.trans (add_le_add le_rfl h3)) 2
    calc Real.sqrt (clusterGradSq ω V w)
        ≤ Real.sqrt (∑ x ∈ V, (M * openGradNorm ω V v x + N * |v x|) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum hpt)
      _ ≤ Real.sqrt (∑ x ∈ V, (M * openGradNorm ω V v x) ^ 2) +
            Real.sqrt (∑ x ∈ V, (N * |v x|) ^ 2) := sqrt_sum_sq_add_le _ _ _
      _ = M * Gv + N * L := by
          simp only [mul_pow, ← Finset.mul_sum, sq_abs]
          rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hM0,
            Real.sqrt_sq hN0]
          rfl
  -- the norm of `w`
  have hs : 0 < Real.sqrt (V.card : ℝ) := Real.sqrt_pos.2 hc
  have hHw : clusterH1Norm ω V w ≤ (M + Real.sqrt V.card * N) * clusterH1Norm ω V v := by
    have eH : ∀ u : Vertex 2 → ℝ, clusterH1Norm ω V u =
        (V.card : ℝ)⁻¹ * Real.sqrt (∑ x ∈ V, u x ^ 2) +
          (Real.sqrt V.card)⁻¹ * Real.sqrt (clusterGradSq ω V u) := by
      intro u
      unfold clusterH1Norm
      rw [Real.rpow_neg hc.le, ← Real.sqrt_eq_rpow, Real.sqrt_mul (inv_nonneg.2 hc.le),
        Real.sqrt_inv, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hc.le,
        Real.sqrt_mul (inv_nonneg.2 hc.le), Real.sqrt_inv]
      rfl
    rw [eH w, eH v, ← hL, ← hGv]
    have hcs : (V.card : ℝ)⁻¹ = (Real.sqrt V.card)⁻¹ * (Real.sqrt V.card)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hc.le]
    have hL0 : 0 ≤ L := Real.sqrt_nonneg _
    have hG0 : 0 ≤ Gv := Real.sqrt_nonneg _
    have hsi : 0 < (Real.sqrt V.card)⁻¹ := inv_pos.2 hs
    calc (V.card : ℝ)⁻¹ * Real.sqrt (∑ x ∈ V, w x ^ 2) +
          (Real.sqrt V.card)⁻¹ * Real.sqrt (clusterGradSq ω V w)
        ≤ (V.card : ℝ)⁻¹ * (M * L) + (Real.sqrt V.card)⁻¹ * (M * Gv + N * L) :=
          add_le_add (mul_le_mul_of_nonneg_left hwL (inv_nonneg.2 hc.le))
            (mul_le_mul_of_nonneg_left hwG hsi.le)
      _ = M * ((V.card : ℝ)⁻¹ * L + (Real.sqrt V.card)⁻¹ * Gv) +
            Real.sqrt V.card * N * ((V.card : ℝ)⁻¹ * L) := by
          rw [hcs]
          field_simp
          ring
      _ ≤ M * ((V.card : ℝ)⁻¹ * L + (Real.sqrt V.card)⁻¹ * Gv) +
            Real.sqrt V.card * N * ((V.card : ℝ)⁻¹ * L + (Real.sqrt V.card)⁻¹ * Gv) := by
          have : 0 ≤ Real.sqrt V.card * N := mul_nonneg hs.le hN0
          nlinarith [mul_nonneg this (mul_nonneg hsi.le hG0)]
      _ = (M + Real.sqrt V.card * N) * ((V.card : ℝ)⁻¹ * L + (Real.sqrt V.card)⁻¹ * Gv) := by
          ring
  calc (V.card : ℝ)⁻¹ * ∑ x ∈ V, A x * B x * v x = (V.card : ℝ)⁻¹ * ∑ x ∈ V, A x * w x := by
        rw [hsum]
    _ ≤ a * clusterH1Norm ω V w := h1
    _ ≤ a * ((M + Real.sqrt V.card * N) * clusterH1Norm ω V v) :=
        mul_le_mul_of_nonneg_left hHw ha
    _ = a * (M + Real.sqrt V.card * N) * clusterH1Norm ω V v := by ring

theorem clusterH1Norm_neg (ω : Configuration 2) (V : Finset (Vertex 2)) (v : Vertex 2 → ℝ) :
    clusterH1Norm ω V (fun x => -v x) = clusterH1Norm ω V v := by
  have hg : ∀ x, openGradNorm ω V (fun y => -v y) x = openGradNorm ω V v x := by
    intro x
    simp only [openGradNorm_eq_sum_filter]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← abs_neg]
    ring_nf
  unfold clusterH1Norm
  simp only [hg, neg_sq]

theorem WeakNormLe.neg {ω : Configuration 2} {V : Finset (Vertex 2)} {g : Vertex 2 → ℝ} {B : ℝ}
    (h : WeakNormLe ω V g B) : WeakNormLe ω V (fun x => -g x) B := by
  intro v hv
  have hv' : ∀ x ∈ V, x ∉ openInterior ω V → (fun y => -v y) x = 0 := fun x hx hi => by
    simp only [hv x hx hi, neg_zero]
  have := h (fun y => -v y) hv'
  rw [clusterH1Norm_neg] at this
  calc (V.card : ℝ)⁻¹ * ∑ x ∈ V, -g x * v x = (V.card : ℝ)⁻¹ * ∑ x ∈ V, g x * -v x := by
        congr 1
        exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ B * clusterH1Norm ω V v := this

theorem WeakNormLe.const_mul {ω : Configuration 2} {V : Finset (Vertex 2)} {g : Vertex 2 → ℝ}
    {B : ℝ} (h : WeakNormLe ω V g B) (κ : ℝ) : WeakNormLe ω V (fun x => κ * g x) (|κ| * B) := by
  have key : ∀ {g' : Vertex 2 → ℝ}, WeakNormLe ω V g' B → ∀ μ : ℝ, 0 ≤ μ →
      WeakNormLe ω V (fun x => μ * g' x) (μ * B) := by
    intro g' h' μ hμ v hv
    have := mul_le_mul_of_nonneg_left (h' v hv) hμ
    calc (V.card : ℝ)⁻¹ * ∑ x ∈ V, μ * g' x * v x =
          μ * ((V.card : ℝ)⁻¹ * ∑ x ∈ V, g' x * v x) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ μ * (B * clusterH1Norm ω V v) := this
      _ = μ * B * clusterH1Norm ω V v := by ring
  rcases le_or_gt 0 κ with hκ | hκ
  · rw [abs_of_nonneg hκ]
    exact key h κ hκ
  · rw [abs_of_neg hκ]
    have := key h.neg (-κ) (by linarith)
    have e : (fun x => κ * g x) = fun x => -κ * -g x := by
      funext x
      ring
    rw [e]
    exact this

theorem weakNormLe_zero (ω : Configuration 2) (V : Finset (Vertex 2)) :
    WeakNormLe ω V (fun _ => 0) 0 := by
  intro v _
  simp

/-- Finite sums: `‖Σ_i g_i‖_{H̲^{-1}(V)} ≤ Σ_i B_i` when `‖g_i‖_{H̲^{-1}(V)} ≤ B_i`. -/
theorem WeakNormLe.sum {ω : Configuration 2} {V : Finset (Vertex 2)} {ι : Type*} (s : Finset ι)
    {g : ι → Vertex 2 → ℝ} {B : ι → ℝ} (h : ∀ i ∈ s, WeakNormLe ω V (g i) (B i)) :
    WeakNormLe ω V (fun x => ∑ i ∈ s, g i x) (∑ i ∈ s, B i) := by
  induction s using Finset.induction_on with
  | empty => simpa using weakNormLe_zero ω V
  | insert a s ha ih =>
      have h' := (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      rw [Finset.sum_insert ha]
      convert h' using 1
      funext x
      rw [Finset.sum_insert ha]
      rfl

/-- **The divergence form** (first lines of (3.30) and (3.32) of Dario–Gu): for a function `F`
antisymmetric on the open edges inside `V`, the divergence `x ↦ Σ_{z ∈ V, z ∼ x} F(x, z)` has
`H̲^{-1}(V)` norm at most `‖F‖_{L̲²(V)} / 2 = |V|^{-1/2} (Σ_x Σ_{z ∼ x} F(x, z)²)^{1/2} / 2`. -/
theorem weakNormLe_sum_antisymm (ω : Configuration 2) (V : Finset (Vertex 2))
    {F : Vertex 2 → Vertex 2 → ℝ}
    (hF : ∀ x ∈ V, ∀ z ∈ V, (openGraph ω).Adj x z → F z x = -F x z) :
    WeakNormLe ω V (fun x => ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), F x z)
      ((Real.sqrt V.card)⁻¹ *
        Real.sqrt (∑ x ∈ V, ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), F x z ^ 2) / 2) := by
  intro v _
  rcases V.eq_empty_or_nonempty with rfl | hV
  · simp
  have hc : (0 : ℝ) < V.card := by exact_mod_cast hV.card_pos
  set T := V.sigma fun x => V.filter (fun z => (openGraph ω).Adj x z) with hT
  have hsig : ∀ H : Vertex 2 → Vertex 2 → ℝ,
      ∑ x ∈ V, ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), H x z =
        ∑ p ∈ T, H p.1 p.2 := fun H =>
    (Finset.sum_sigma V (fun x => V.filter (fun z => (openGraph ω).Adj x z))
      (fun p => H p.1 p.2)).symm
  set S := ∑ x ∈ V, v x * ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), F x z with hS
  have hS1 : S = ∑ x ∈ V, ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), v x * F x z := by
    rw [hS]
    exact Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _
  have hS2 : S = -∑ x ∈ V, ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), v z * F x z := by
    rw [hS1, sum_filter_adj_comm ω V (fun x z => v x * F x z), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' := Finset.mem_filter.1 hz
    rw [hF x hx z hz'.1 hz'.2]
    ring
  have h2S : 2 * S = ∑ p ∈ T, (v p.1 - v p.2) * F p.1 p.2 := by
    rw [← hsig (fun x z => (v x - v z) * F x z)]
    have : 2 * S = S + S := by ring
    rw [this]
    nth_rewrite 1 [hS1]
    rw [hS2, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt T (fun p => v p.1 - v p.2) (fun p => F p.1 p.2)
  have hE : ∑ p ∈ T, (v p.1 - v p.2) ^ 2 ≤ clusterGradSq ω V v := by
    rw [← hsig (fun x z => (v x - v z) ^ 2)]
    have : ∑ x ∈ V, ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), (v x - v z) ^ 2 =
        clusterDirEnergy ω V v := by
      unfold clusterDirEnergy
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => by ring
    rw [this]
    exact clusterDirEnergy_le_clusterGradSq ω V v
  have hgrad := inv_sqrt_card_mul_sqrt_le_clusterH1Norm ω hV v
  have hs : 0 < Real.sqrt (V.card : ℝ) := Real.sqrt_pos.2 hc
  have hQ : 0 ≤ Real.sqrt (∑ p ∈ T, F p.1 p.2 ^ 2) := Real.sqrt_nonneg _
  have hmain : S ≤ Real.sqrt (clusterGradSq ω V v) * Real.sqrt (∑ p ∈ T, F p.1 p.2 ^ 2) / 2 := by
    have := hCS.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hE) hQ)
    linarith
  rw [hsig (fun x z => F x z ^ 2)]
  calc (V.card : ℝ)⁻¹ * ∑ x ∈ V,
        (∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), F x z) * v x
      = (V.card : ℝ)⁻¹ * S := by
        rw [hS]
        congr 1
        exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    _ ≤ (V.card : ℝ)⁻¹ *
          (Real.sqrt (clusterGradSq ω V v) * Real.sqrt (∑ p ∈ T, F p.1 p.2 ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hmain (inv_nonneg.2 hc.le)
    _ = (Real.sqrt V.card)⁻¹ * Real.sqrt (∑ p ∈ T, F p.1 p.2 ^ 2) / 2 *
          ((Real.sqrt V.card)⁻¹ * Real.sqrt (clusterGradSq ω V v)) := by
        have hcs : (V.card : ℝ)⁻¹ = (Real.sqrt V.card)⁻¹ * (Real.sqrt V.card)⁻¹ := by
          rw [← mul_inv, Real.mul_self_sqrt hc.le]
        rw [hcs]
        ring
    _ ≤ (Real.sqrt V.card)⁻¹ * Real.sqrt (∑ p ∈ T, F p.1 p.2 ^ 2) / 2 * clusterH1Norm ω V v :=
        mul_le_mul_of_nonneg_left hgrad (by positivity)

end Rigidity.Green
