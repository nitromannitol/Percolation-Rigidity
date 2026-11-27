import Rigidity.Proofs.Corrector.GeneralStepOneSum
import Rigidity.Proofs.Corrector.GeneralRandomBallSums
import Rigidity.Proofs.Corrector.GeneralCoarseningError

/-!
# Moments of sums over random balls and over bonds of `ℤᵈ`

The moments of Dario's sum (3.18) `W(y) = Σ_e 1{y ∈ B_e} F_e` on `ℤᵈ` are bounded in
`GeneralStepOneW` from four facts proved here, as in the planar file `DarioStepOneGrowth`.

* `lintegral_tsum_rpow_le_of_decay`: Jensen's inequality over a countable family with the
  weights `e^{-a_i/(4qθ)}`: if `E[I_i^q] ≤ M e^{-a_i/(2θ)}` and `Σ_i e^{-a_i/κ} ≤ N (1 + κ)^m`,
  then `E[(Σ_i I_i)^q] ≤ (N (1 + 4qθ)^m)^{q-1} M N (1 + 4θ)^m`.
* `tsum_exp_neg_norm_bondBase_le`: the bonds satisfy the weight bound with `m = d` and
  `N = 2d (2d)^d`, through the presentation `e = {z, z + e_j}` of a bond (`bondEdge`).
* `measure_le_mul_stoppingSize_le`: the exponential tail of `K size(□_𝒫(v))`.
* `lintegral_randomBallSum_rpow_le_of_growth`: moments `(B q^κ)^q` of the summands give moments
  `(A q^{κ+d})^q` of their sum over a ball of random radius with an exponential tail
  (from `lintegral_randomBallSum_le`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped ENNReal

variable {d : ℕ}

/-- **Jensen's inequality over a countable family with decaying moments.** -/
theorem lintegral_tsum_rpow_le_of_decay {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {p : unitInterval} {I : ι → Configuration d → ℝ≥0∞}
    (hI : ∀ i, Measurable (I i)) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {q θ M N : ℝ} {m : ℕ}
    (hq : 1 ≤ q) (hθ : 0 < θ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hW : ∀ κ : ℝ, 0 < κ →
      ∑' i, ENNReal.ofReal (Real.exp (-a i / κ)) ≤ ENNReal.ofReal (N * (1 + κ) ^ m))
    (hmom : ∀ i, ∫⁻ ω, I i ω ^ q ∂latticeBondLaw d p ≤
      ENNReal.ofReal (M * Real.exp (-(a i / (2 * θ))))) :
    ∫⁻ ω, (∑' i, I i ω) ^ q ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((N * (1 + 4 * q * θ) ^ m) ^ (q - 1) * (M * (N * (1 + 4 * θ) ^ m))) := by
  have hq0 : 0 < q := by linarith
  have hκ0 : 0 < 4 * q * θ := by positivity
  have hWle : ∑' i, ENNReal.ofReal (Real.exp (-a i / (4 * q * θ))) ≤
      ENNReal.ofReal (N * (1 + 4 * q * θ) ^ m) := hW _ hκ0
  set w : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (Real.exp (-a i / (4 * q * θ))) with hw
  set g : ι → Configuration d → ℝ≥0∞ := fun i ω =>
    I i ω * ENNReal.ofReal (Real.exp (a i / (4 * q * θ))) with hg
  have hgw : ∀ i ω, g i ω * w i = I i ω := by
    intro i ω
    simp only [hg, hw]
    rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      show a i / (4 * q * θ) + -a i / (4 * q * θ) = 0 by ring, Real.exp_zero, ENNReal.ofReal_one,
      mul_one]
  have hgq : ∀ i ω, g i ω ^ q * w i =
      I i ω ^ q * ENNReal.ofReal (Real.exp ((q - 1) * (a i / (4 * q * θ)))) := by
    intro i ω
    simp only [hg, hw]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hq0.le, ← Real.exp_mul, mul_assoc,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 3
    ring
  have hJ : ∀ ω, (∑' i, I i ω) ^ q ≤
      (∑' i, I i ω ^ q * ENNReal.ofReal (Real.exp ((q - 1) * (a i / (4 * q * θ))))) *
        (∑' i, w i) ^ (q - 1) := by
    intro ω
    have h := lintegral_mul_rpow_le (μ := Measure.count) (g := fun i => g i ω) (w := w)
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
      (fun i => ENNReal.ofReal_ne_top) hq
    simp only [lintegral_count, hgw, hgq] at h
    exact h
  have hterm : ∀ i, ENNReal.ofReal (Real.exp ((q - 1) * (a i / (4 * q * θ)))) *
      ENNReal.ofReal (M * Real.exp (-(a i / (2 * θ)))) ≤
        ENNReal.ofReal M * ENNReal.ofReal (Real.exp (-a i / (4 * θ))) := by
    intro i
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hM]
    refine ENNReal.ofReal_le_ofReal ?_
    have hexp : Real.exp ((q - 1) * (a i / (4 * q * θ))) * Real.exp (-(a i / (2 * θ))) ≤
        Real.exp (-a i / (4 * θ)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hax := ha i
      have h1 : (q - 1) * (a i / (4 * q * θ)) ≤ a i / (4 * θ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, show (4 * q * θ)⁻¹ = q⁻¹ * (4 * θ)⁻¹ by
          rw [mul_comm 4 q, mul_assoc, mul_inv]]
        have hqi : (q - 1) * q⁻¹ ≤ 1 := by
          rw [sub_mul, mul_inv_cancel₀ hq0.ne', one_mul]
          have : 0 < q⁻¹ := inv_pos.2 hq0
          linarith
        have h4 : 0 ≤ a i * (4 * θ)⁻¹ := by positivity
        nlinarith
      have e1 : -a i / (4 * θ) = a i / (4 * θ) - a i / (2 * θ) := by field_simp; ring
      rw [e1]
      linarith
    calc Real.exp ((q - 1) * (a i / (4 * q * θ))) * (M * Real.exp (-(a i / (2 * θ))))
        = M * (Real.exp ((q - 1) * (a i / (4 * q * θ))) * Real.exp (-(a i / (2 * θ)))) := by
          ring
      _ ≤ M * Real.exp (-a i / (4 * θ)) := mul_le_mul_of_nonneg_left hexp hM
  have hsumW := hW (4 * θ) (by positivity)
  have hB0 : 0 ≤ N * (1 + 4 * θ) ^ m := mul_nonneg hN (by positivity)
  calc ∫⁻ ω, (∑' i, I i ω) ^ q ∂latticeBondLaw d p
      ≤ ∫⁻ ω, (∑' i, I i ω ^ q * ENNReal.ofReal (Real.exp ((q - 1) * (a i / (4 * q * θ))))) *
          (∑' i, w i) ^ (q - 1) ∂latticeBondLaw d p := lintegral_mono hJ
    _ = (∑' i, ENNReal.ofReal (Real.exp ((q - 1) * (a i / (4 * q * θ)))) *
          ∫⁻ ω, I i ω ^ q ∂latticeBondLaw d p) * (∑' i, w i) ^ (q - 1) := by
        rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hWle))]
        congr 1
        rw [lintegral_tsum fun i => (((hI i).pow_const q).mul_const _).aemeasurable]
        refine tsum_congr fun i => ?_
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
    _ ≤ (∑' i, ENNReal.ofReal M * ENNReal.ofReal (Real.exp (-a i / (4 * θ)))) *
          ENNReal.ofReal (N * (1 + 4 * q * θ) ^ m) ^ (q - 1) :=
        mul_le_mul' (ENNReal.tsum_le_tsum fun i =>
          (mul_le_mul_right (hmom i) _).trans (hterm i))
          (ENNReal.rpow_le_rpow hWle (by linarith))
    _ ≤ (ENNReal.ofReal M * ENNReal.ofReal (N * (1 + 4 * θ) ^ m)) *
          ENNReal.ofReal (N * (1 + 4 * q * θ) ^ m) ^ (q - 1) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
    _ = ENNReal.ofReal ((N * (1 + 4 * q * θ) ^ m) ^ (q - 1) * (M * (N * (1 + 4 * θ) ^ m))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hN (by positivity)) (by linarith),
          ← ENNReal.ofReal_mul hM, ← ENNReal.ofReal_mul (mul_nonneg hM hB0), mul_comm]

/-- Every bond of `ℤᵈ` is `{z, z + e_j}` for some `z` and `j`. -/
theorem exists_bond_eq_unit (e : Bond d) :
    ∃ a : Vertex d × Fin d, e.1 = s(a.1, a.1 + LatticeProb.unit a.2) := by
  obtain ⟨x, y, hxy, h1⟩ := e.2
  have hadj : (nearestNeighborGraph d).Adj x y := lattice_adj_iff_l1Dist.2 h1
  obtain ⟨j, hj | hj⟩ := hadj
  · exact ⟨(x, j), by rw [hxy, hj]⟩
  · exact ⟨(y, j), by rw [hxy, hj, Sym2.eq_swap]⟩

/-- A presentation `e = {z, z + e_j}` of a bond. -/
noncomputable def bondEdge (e : Bond d) : Vertex d × Fin d :=
  Classical.choose (exists_bond_eq_unit e)

theorem bondEdge_spec (e : Bond d) :
    e.1 = s((bondEdge e).1, (bondEdge e).1 + LatticeProb.unit (bondEdge e).2) :=
  Classical.choose_spec (exists_bond_eq_unit e)

theorem bondEdge_injective : Function.Injective (bondEdge (d := d)) := by
  intro e e' h
  apply Subtype.ext
  rw [bondEdge_spec e, bondEdge_spec e', h]

/-- **The weights over the bonds**: `Σ_e e^{-|a_e - y|/κ} ≤ 2d (2d)^d (1 + κ)^d`, with
`a_e = bondBase e`. -/
theorem tsum_exp_neg_norm_bondBase_le (hd : 0 < d) (y : Vertex d) {κ : ℝ} (hκ : 0 < κ) :
    ∑' e : Bond d, ENNReal.ofReal
        (Real.exp (-‖latticeEuclideanEmbedding (bondBase e - y)‖ / κ)) ≤
      ENNReal.ofReal (2 * d * (2 * d) ^ d * (1 + κ) ^ d) := by
  set f : Vertex d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (x - y)‖ / κ)) with hf
  set g : Vertex d × Fin d → ℝ≥0∞ := fun a => f a.1 + f (a.1 + LatticeProb.unit a.2) with hg
  have hpt : ∀ e : Bond d, f (bondBase e) ≤ g (bondEdge e) := by
    intro e
    have h := bondBase_mem e
    rw [bondEdge_spec e, Sym2.mem_iff] at h
    rcases h with h | h
    · rw [h]
      exact le_self_add
    · rw [h]
      exact le_add_self
  have hsum : ∑' x, f x ≤ ENNReal.ofReal ((2 * (1 + d * κ)) ^ d) :=
    tsum_exp_neg_norm_sub_le y hκ
  have hshift : ∀ j : Fin d, ∑' x, f (x + LatticeProb.unit j) = ∑' x, f x := fun j =>
    (Equiv.addRight (LatticeProb.unit j)).tsum_eq f
  have h0 : (0 : ℝ) ≤ (2 * (1 + d * κ)) ^ d := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase : (2 * (1 + d * κ)) ^ d ≤ (2 * d) ^ d * (1 + κ) ^ d := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    nlinarith
  calc ∑' e : Bond d, f (bondBase e)
      ≤ ∑' e : Bond d, g (bondEdge e) := ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' a : Vertex d × Fin d, g a := ENNReal.tsum_comp_le_tsum_of_injective bondEdge_injective g
    _ = ∑' x, ∑' j : Fin d, (f x + f (x + LatticeProb.unit j)) :=
        ENNReal.tsum_prod (f := fun x j => f x + f (x + LatticeProb.unit j))
    _ = ∑' j : Fin d, ∑' x, (f x + f (x + LatticeProb.unit j)) := ENNReal.tsum_comm
    _ = ∑' j : Fin d, (∑' x, f x + ∑' x, f x) :=
        tsum_congr fun j => by rw [ENNReal.tsum_add, hshift j]
    _ ≤ ∑' j : Fin d, (ENNReal.ofReal ((2 * (1 + d * κ)) ^ d) +
          ENNReal.ofReal ((2 * (1 + d * κ)) ^ d)) :=
        ENNReal.tsum_le_tsum fun j => add_le_add hsum hsum
    _ = ENNReal.ofReal (2 * d * (2 * (1 + d * κ)) ^ d) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← ENNReal.ofReal_add h0 h0, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (2 * d * (2 * d) ^ d * (1 + κ) ^ d) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_assoc (2 * (d : ℝ))]
        exact mul_le_mul_of_nonneg_left hbase (by positivity)

/-- The tail of `K size(□_𝒫(v))` from the exponential moment of the size. -/
theorem measure_le_mul_stoppingSize_le [NeZero d] {p : unitInterval} {θ K : ℝ} (hθ : 0 < θ)
    (hK : 0 < K) (v : Vertex d)
    (hint : Integrable
      (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ))
      (latticeBondLaw d p))
    (hb : ∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ)
      ∂latticeBondLaw d p ≤ 2)
    (t : ℝ) :
    latticeBondLaw d p {ω | t ≤ K * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} ≤
      ENNReal.ofReal (2 * Real.exp (-(t / (K * θ)))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have h := measure_le_stoppingSize_le hθ v hint hb (3 * d * t / K)
  have hset : {ω | t ≤ K * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} =
      {ω | 3 * d * t / K ≤ 3 * d * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [div_le_iff₀ hK]
    constructor
    · intro h'
      nlinarith
    · intro h'
      have h3 : (0 : ℝ) < 3 * d := by positivity
      nlinarith
  rw [hset]
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  congr 3
  field_simp

/-- **Cauchy–Schwarz on an event**: `E[(1_A Z)^q] ≤ P[A]^{1/2} E[Z^{2q}]^{1/2}`. -/
theorem lintegral_indicator_rpow_le {p : unitInterval} {A : Set (Configuration d)}
    (hA : MeasurableSet A) {Z : Configuration d → ℝ≥0∞} (hZ : Measurable Z) {q c m : ℝ}
    (hq : 0 < q) (hc : 0 ≤ c) (hm : 0 ≤ m) (hPA : latticeBondLaw d p A ≤ ENNReal.ofReal c)
    (hZm : ∫⁻ ω, Z ω ^ (2 * q) ∂latticeBondLaw d p ≤ ENNReal.ofReal (m ^ 2)) :
    ∫⁻ ω, A.indicator Z ω ^ q ∂latticeBondLaw d p ≤ ENNReal.ofReal (Real.sqrt c * m) := by
  classical
  have hpt : ∀ ω, A.indicator Z ω ^ q = A.indicator 1 ω * Z ω ^ q := by
    intro ω
    simp only [Set.indicator_apply, Pi.one_apply]
    split_ifs <;> simp [ENNReal.zero_rpow_of_pos hq]
  simp only [hpt]
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (latticeBondLaw d p)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2)
    ((measurable_one.indicator hA).aemeasurable) ((hZ.pow_const q).aemeasurable)
  have h1 : ∫⁻ ω, A.indicator 1 ω ^ (2 : ℝ) ∂latticeBondLaw d p = latticeBondLaw d p A := by
    have : ∀ ω, A.indicator (1 : Configuration d → ℝ≥0∞) ω ^ (2 : ℝ) = A.indicator 1 ω := by
      intro ω
      simp only [Set.indicator_apply, Pi.one_apply]
      split_ifs <;> simp
    simp only [this]
    rw [lintegral_indicator_one hA]
  have h2 : ∫⁻ ω, (Z ω ^ q) ^ (2 : ℝ) ∂latticeBondLaw d p ≤ ENNReal.ofReal (m ^ 2) := by
    have : ∀ ω, (Z ω ^ q) ^ (2 : ℝ) = Z ω ^ (2 * q) := by
      intro ω
      rw [← ENNReal.rpow_mul, mul_comm]
    simp only [this]
    exact hZm
  have hfin : ENNReal.ofReal c ^ (1 / (2 : ℝ)) * ENNReal.ofReal (m ^ 2) ^ (1 / (2 : ℝ)) =
      ENNReal.ofReal (Real.sqrt c * m) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hc (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.sqrt_eq_rpow, ← Real.rpow_two m, ← Real.rpow_mul hm,
      show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
  calc ∫⁻ ω, A.indicator 1 ω * Z ω ^ q ∂latticeBondLaw d p
      ≤ (∫⁻ ω, A.indicator 1 ω ^ (2 : ℝ) ∂latticeBondLaw d p) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, (Z ω ^ q) ^ (2 : ℝ) ∂latticeBondLaw d p) ^ (1 / (2 : ℝ)) := hcs
    _ ≤ ENNReal.ofReal c ^ (1 / (2 : ℝ)) * ENNReal.ofReal (m ^ 2) ^ (1 / (2 : ℝ)) :=
        mul_le_mul' (ENNReal.rpow_le_rpow (h1.le.trans hPA) (by norm_num))
          (ENNReal.rpow_le_rpow h2 (by norm_num))
    _ = _ := hfin

/-- **Moments of a sum over a ball of random radius, in growth form**: if the summands satisfy
`E[Y_x^q] ≤ (B q^κ)^q` for all `q ≥ 1` and the radius has the tail `2 e^{-t/θ}`, then the sum
satisfies `E[(Σ_{|x - v| ≤ ρ} Y_x)^q] ≤ (A q^{κ+d})^q` with
`A = (2 (1 + 8dθ))^d · √2 · B 2^κ`. -/
theorem lintegral_randomBallSum_rpow_le_of_growth {p : unitInterval} (v : Vertex d)
    {ρ : Configuration d → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (htail : ∀ t : ℝ, 0 ≤ t →
      latticeBondLaw d p {ω | t ≤ ρ ω} ≤ ENNReal.ofReal (2 * Real.exp (-(t / θ))))
    (hρ : Measurable ρ) {Y : Vertex d → Configuration d → ℝ≥0∞} (hY : ∀ x, Measurable (Y x))
    {B κ : ℝ} (hB : 0 < B)
    (hYm : ∀ x (q : ℝ), 1 ≤ q →
      ∫⁻ ω, Y x ω ^ q ∂latticeBondLaw d p ≤ ENNReal.ofReal ((B * q ^ κ) ^ q))
    {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ ω, (∑' x, if ‖latticeEuclideanEmbedding (x - v)‖ ≤ ρ ω then Y x ω else 0) ^ q
        ∂latticeBondLaw d p ≤
      ENNReal.ofReal
        (((2 * (1 + 8 * d * θ)) ^ d * Real.sqrt 2 * (B * 2 ^ κ) * q ^ (κ + d)) ^ q) := by
  have hq0 : 0 < q := by linarith
  have hM0 : 0 ≤ (B * (2 * q) ^ κ) ^ q := by positivity
  have hYm' : ∀ x, ∫⁻ ω, Y x ω ^ (2 * q) ∂latticeBondLaw d p ≤
      ENNReal.ofReal (((B * (2 * q) ^ κ) ^ q) ^ 2) := by
    intro x
    refine (hYm x (2 * q) (by linarith)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  refine (lintegral_randomBallSum_le v hθ htail hρ hY hq hM0 hYm').trans
    (ENNReal.ofReal_le_ofReal ?_)
  set X : ℝ := (2 * (1 + 8 * d * θ)) ^ d with hXdef
  have hX1 : 1 ≤ X := one_le_pow₀ (by nlinarith [(by positivity : (0 : ℝ) ≤ 8 * d * θ)])
  have hbase : (2 * (1 + d * (4 * q * θ))) ^ d ≤ X * q ^ d := by
    rw [hXdef, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have h0 : 0 ≤ d * θ := by positivity
    nlinarith
  have hbase1 : (2 * (1 + d * (4 * θ))) ^ d ≤ X := by
    rw [hXdef]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have h0 : 0 ≤ d * θ := by positivity
    nlinarith
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.one_le_sqrt]
    norm_num
  have h2q : (2 * q) ^ κ = 2 ^ κ * q ^ κ := Real.mul_rpow (by norm_num) hq0.le
  have hqk : q ^ (κ + d) = q ^ κ * q ^ d := by
    rw [Real.rpow_add hq0, Real.rpow_natCast]
  have hXq1 : (X * q ^ d) ^ (q - 1) * X ≤ (X * q ^ d) ^ q := by
    have hXq : 0 < X * q ^ d := by positivity
    rw [Real.rpow_sub hXq, Real.rpow_one, div_mul_eq_mul_div, div_le_iff₀ hXq]
    have : 0 ≤ (X * q ^ d) ^ q := by positivity
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity)
      (one_le_pow₀ hq)) this
  have hcq : Real.sqrt 2 ≤ Real.sqrt 2 ^ q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hs2 hq
  calc ((2 * (1 + d * (4 * q * θ))) ^ d) ^ (q - 1) *
        (Real.sqrt 2 * (2 * (1 + d * (4 * θ))) ^ d * (B * (2 * q) ^ κ) ^ q)
      ≤ (X * q ^ d) ^ (q - 1) * (X * (Real.sqrt 2 * (B * (2 * q) ^ κ) ^ q)) := by
        refine mul_le_mul (Real.rpow_le_rpow (by positivity) hbase (by linarith)) ?_
          (by positivity) (by positivity)
        rw [show Real.sqrt 2 * (2 * (1 + d * (4 * θ))) ^ d * (B * (2 * q) ^ κ) ^ q =
          (2 * (1 + d * (4 * θ))) ^ d * (Real.sqrt 2 * (B * (2 * q) ^ κ) ^ q) by ring]
        exact mul_le_mul_of_nonneg_right hbase1 (by positivity)
    _ = ((X * q ^ d) ^ (q - 1) * X) * (Real.sqrt 2 * (B * (2 * q) ^ κ) ^ q) := by ring
    _ ≤ (X * q ^ d) ^ q * (Real.sqrt 2 ^ q * (B * (2 * q) ^ κ) ^ q) :=
        mul_le_mul hXq1 (mul_le_mul_of_nonneg_right hcq (by positivity)) (by positivity)
          (by positivity)
    _ = (X * Real.sqrt 2 * (B * 2 ^ κ) * q ^ (κ + d)) ^ q := by
        rw [← Real.mul_rpow (by positivity) (by positivity),
          ← Real.mul_rpow (by positivity) (by positivity), h2q, hqk]
        congr 1
        ring

end Rigidity.Corrector.GeneralDim
