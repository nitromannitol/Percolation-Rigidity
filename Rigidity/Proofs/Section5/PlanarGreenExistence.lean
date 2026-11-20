import Rigidity.Proofs.Section5.PlanarCrossingEvents
import Rigidity.Proofs.Section5.PlanarPotentialSublinear
import Rigidity.Steps.Section5.FastDecayDichotomy

/-!
# Existence of planar Green columns

For `p_c(2) < p < 1`, almost surely, for every pole `y` of the infinite cluster there is a Green
column: a function `g` with `-Δ g = δ_y` on the cluster, `g(y) = 0` and `g(x) = o(|x|)`.

The construction follows the potential kernel: the truncated potentials
`Σ_{t < n} (p_t(y, y) - p_t(x, y)) / deg y` are bounded by the energy of any unit flow from `y` to
`x` inside the cluster, so a limit point is a Green column as soon as such flows exist with energy
`o(|x|)`. At the dyadic scale `L = 4^m` with `4 |x|_∞ ≤ L < 16 |x|_∞`, the crossing event
`CrossingGood ω (4^m) (m²) (2^m (m² + 1)) (m^q)`, which holds for all large `m` almost surely,
gives such a flow along `2^m` parallel crossings of thin rectangles of width `m²`
(`exists_flow_of_crossings`), with energy at most `624 · 2^m m^{3q+4} = o(4^m)`.

This route bounds the effective resistance between `y` and `x` by `o(|x|)`, which is all that the
Green column needs; it does not use the logarithmic resistance bound.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation LatticeProb.Network Rigidity.External
  Rigidity.Proofs.S3

namespace Rigidity.Proofs.Section5

open Rigidity.Section5

/-- The subcube radius of a cube of radius `N ≥ 1` is at most `N`. -/
theorem wcSubRadius_le_self (d : ℕ) {N : ℕ} (hN : 1 ≤ N) : wcSubRadius d N ≤ N := by
  unfold wcSubRadius
  rw [Nat.ceil_le]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hδ : 1 / (10 * (d : ℝ)) ^ 2 ≤ 1 := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have : (1 : ℝ) ≤ (10 * (d : ℝ)) ^ 2 := by nlinarith
      exact (div_le_one (by positivity)).2 this
  have := Real.rpow_le_rpow_of_exponent_le hN1 hδ
  rw [Real.rpow_one] at this
  linarith

/-- The energy bound of the flow at the dyadic scale `m`. -/
theorem crossFlowBound_le {q m : ℕ} (hm : 1 ≤ m) :
    crossFlowBound (4 ^ m) (m ^ 2) (2 ^ m) (m ^ q) ≤ 624 * 2 ^ m * (m : ℝ) ^ (3 * q + 4) := by
  have hn : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hNq : 1 ≤ m ^ q := Nat.one_le_pow _ _ hm
  have hM' : (wcSubRadius 2 (m ^ q) : ℝ) ≤ (m : ℝ) ^ q := by
    exact_mod_cast wcSubRadius_le_self 2 hNq
  have hM0 : (0 : ℝ) ≤ wcSubRadius 2 (m ^ q) := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ (m : ℝ) ^ q := one_le_pow₀ hn
  have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have h4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  have hpow : ∀ j ≤ 3 * q + 4, (m : ℝ) ^ j ≤ (m : ℝ) ^ (3 * q + 4) :=
    fun j hj => pow_le_pow_right₀ hn hj
  have hn2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ hn
  have hN3 : ((m : ℝ) ^ q) ^ 3 = (m : ℝ) ^ (3 * q) := by rw [← pow_mul, mul_comm]
  have hn4 : (m : ℝ) ^ 4 = ((m : ℝ) ^ 2) ^ 2 := by ring
  -- the three terms
  have hT1 : ((4 * (m : ℝ) ^ q + 1) * (2 * (wcSubRadius 2 (m ^ q) : ℝ) + 1) ^ 2 + 1) ≤
      46 * (m : ℝ) ^ (3 * q) := by
    rw [← hN3]
    set N := (m : ℝ) ^ q
    have h1 : (2 * (wcSubRadius 2 (m ^ q) : ℝ) + 1) ^ 2 ≤ (3 * N) ^ 2 := by
      have : 2 * (wcSubRadius 2 (m ^ q) : ℝ) + 1 ≤ 3 * N := by linarith
      exact pow_le_pow_left₀ (by positivity) this 2
    have h2' : 4 * N + 1 ≤ 5 * N := by linarith
    have h3 : (4 * N + 1) * (2 * (wcSubRadius 2 (m ^ q) : ℝ) + 1) ^ 2 ≤ 5 * N * (3 * N) ^ 2 :=
      mul_le_mul h2' h1 (by positivity) (by positivity)
    have h4' : (1 : ℝ) ≤ N ^ 3 := one_le_pow₀ hN1
    nlinarith
  have hT2 : ((m : ℝ) ^ 2 + 1) * (2 ^ m * ((m : ℝ) ^ 2 + 1) + 1) ≤
      8 * 2 ^ m * (m : ℝ) ^ 4 := by
    rw [hn4]
    set w := (m : ℝ) ^ 2
    have ha : w + 1 ≤ 2 * w := by linarith
    have hb : 2 ^ m * (w + 1) + 1 ≤ 4 * 2 ^ m * w := by nlinarith
    calc (w + 1) * (2 ^ m * (w + 1) + 1) ≤ (2 * w) * (4 * 2 ^ m * w) :=
          mul_le_mul ha hb (by positivity) (by positivity)
      _ = 8 * 2 ^ m * w ^ 2 := by ring
  have hT3 : 8 * (2 * (4 : ℝ) ^ m + 1) * ((m : ℝ) ^ 2 + 1) / 2 ^ m ≤
      48 * 2 ^ m * (m : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity), h4]
    have ha : 2 * (2 ^ m * 2 ^ m) + 1 ≤ 3 * (2 ^ m * (2 : ℝ) ^ m) := by nlinarith
    have hb : (m : ℝ) ^ 2 + 1 ≤ 2 * (m : ℝ) ^ 2 := by linarith
    have := mul_le_mul ha hb (by positivity) (by positivity)
    nlinarith
  unfold crossFlowBound
  push_cast
  have e1 := hpow (3 * q) (by omega)
  have e2 := hpow 4 (by omega)
  have e3 := hpow 2 (by omega)
  have hmpos : (0 : ℝ) ≤ (m : ℝ) ^ (3 * q + 4) := by positivity
  have hmq : (m : ℝ) ^ (3 * q) ≤ 2 ^ m * (m : ℝ) ^ (3 * q + 4) := by nlinarith
  nlinarith

/-- The flow energy at the dyadic scale `m` is eventually at most `ε 4^m`. -/
theorem eventually_crossFlowBound_le (q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, crossFlowBound (4 ^ m) (m ^ 2) (2 ^ m) (m ^ q) ≤ ε * 4 ^ m := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt (3 * q + 4) (show (1 : ℝ) < 2 by norm_num)
  filter_upwards [(ht.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 624 by positivity))),
    eventually_ge_atTop 1] with m hm hm1
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_lt_iff₀ h2] at hm
  have h4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  calc crossFlowBound (4 ^ m) (m ^ 2) (2 ^ m) (m ^ q) ≤ 624 * 2 ^ m * (m : ℝ) ^ (3 * q + 4) :=
        crossFlowBound_le hm1
    _ ≤ 624 * 2 ^ m * (ε / 624 * 2 ^ m) := by gcongr
    _ = ε * 4 ^ m := by rw [h4]; ring

/-- Eventually `m^q < 2^m`. -/
theorem eventually_pow_lt_two_pow (q : ℕ) : ∀ᶠ m : ℕ in atTop, m ^ q < 2 ^ m := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt q (show (1 : ℝ) < 2 by norm_num)
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with m hm
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_lt_iff₀ h2, one_mul] at hm
  exact_mod_cast hm

/-- Eventually `4 · 2^m (m² + 1) ≤ 4^m`. -/
theorem eventually_band_le : ∀ᶠ m : ℕ in atTop, 4 * (2 ^ m * (m ^ 2 + 1)) ≤ 4 ^ m := by
  filter_upwards [eventually_pow_lt_two_pow 3, eventually_ge_atTop 8] with m hm h8
  have hsq : 8 * m ^ 2 ≤ m ^ 3 := by
    have : 8 * m ^ 2 ≤ m * m ^ 2 := Nat.mul_le_mul_right _ h8
    calc 8 * m ^ 2 ≤ m * m ^ 2 := this
      _ = m ^ 3 := by ring
  have h4 : 4 ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  have h1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [h4]
  calc 4 * (2 ^ m * (m ^ 2 + 1)) = 2 ^ m * (4 * (m ^ 2 + 1)) := by ring
    _ ≤ 2 ^ m * 2 ^ m := by
      apply Nat.mul_le_mul_left
      omega

/-- The absolute value of an integer, as a real number, is its natural absolute value. -/
theorem abs_intCast_eq_natAbs (a : ℤ) : |(a : ℝ)| = (a.natAbs : ℝ) := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]

/-- The Euclidean norm of a planar lattice point is at most twice its largest coordinate. -/
theorem eucl_le_two_mul_max (x : Vertex 2) :
    eucl x ≤ 2 * (max (x 0).natAbs (x 1).natAbs : ℕ) := by
  have h := Rigidity.Steps.Section5.eucl_le_l1 x
  simp only [l1, Fin.sum_univ_two, abs_intCast_eq_natAbs] at h
  have h0 : ((x 0).natAbs : ℝ) ≤ (max (x 0).natAbs (x 1).natAbs : ℕ) := by
    exact_mod_cast le_max_left (x 0).natAbs (x 1).natAbs
  have h1 : ((x 1).natAbs : ℝ) ≤ (max (x 0).natAbs (x 1).natAbs : ℕ) := by
    exact_mod_cast le_max_right (x 0).natAbs (x 1).natAbs
  linarith

/-- The largest coordinate of a planar lattice point is at most its Euclidean norm. -/
theorem max_le_eucl (x : Vertex 2) : ((max (x 0).natAbs (x 1).natAbs : ℕ) : ℝ) ≤ eucl x := by
  have h0 := Rigidity.Steps.Section5.abs_coord_le_eucl x 0
  have h1 := Rigidity.Steps.Section5.abs_coord_le_eucl x 1
  rw [abs_intCast_eq_natAbs] at h0 h1
  push_cast
  exact max_le h0 h1

/-- **Existence of planar Green columns.** For supercritical planar bond percolation, almost
surely every vertex of the infinite cluster is the pole of a Green column. -/
theorem planar_greenColumn_exists : Rigidity.External.SupercriticalBondGreenColumnExistsTwo := by
  intro p hp hp1 y
  obtain ⟨q, hq2, hgood⟩ := ae_eventually_crossingGood hp hp1
  filter_upwards [hgood] with ω hω h hy
  have hC := uniqueInfiniteComponent_infinite h
  apply exists_greenColumn_of_sublinear_finite_flows (uniqueInfiniteComponent h) hC ⟨y, hy⟩
  intro ε hε
  set ny := max (y 0).natAbs (y 1).natAbs with hny
  have hev : ∀ᶠ m : ℕ in atTop, CrossingGood ω (4 ^ m) (m ^ 2) (2 ^ m * (m ^ 2 + 1)) (m ^ q) ∧
      crossFlowBound (4 ^ m) (m ^ 2) (2 ^ m) (m ^ q) ≤ ε / 8 * 4 ^ m ∧ m ^ q < 2 ^ m ∧
      4 * (2 ^ m * (m ^ 2 + 1)) ≤ 4 ^ m ∧ 1 ≤ m ∧ 4 * ny ≤ 4 ^ m := by
    have hy4 : ∀ᶠ m : ℕ in atTop, 4 * ny ≤ 4 ^ m := by
      filter_upwards [eventually_ge_atTop (4 * ny)] with m hm
      exact hm.trans (Nat.lt_pow_self (by norm_num)).le
    filter_upwards [hω, eventually_crossFlowBound_le q (show 0 < ε / 8 by positivity),
      eventually_pow_lt_two_pow q, eventually_band_le, eventually_ge_atTop 1, hy4]
      with m h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 hev
  refine ⟨2 * 4 ^ m₀ + 2, fun x hx => ?_⟩
  set nx := max (x.val 0).natAbs (x.val 1).natAbs with hnx
  have hxe := eucl_le_two_mul_max x.val
  have hxe' := max_le_eucl x.val
  rw [← hnx] at hxe hxe'
  have hnx0 : 4 ^ m₀ < nx := by
    have : (4 : ℝ) ^ m₀ < nx := by linarith
    exact_mod_cast this
  have hex : ∃ m, 4 * nx ≤ 4 ^ m :=
    ⟨4 * nx, (Nat.lt_pow_self (by norm_num)).le⟩
  classical
  set m := Nat.find hex with hmdef
  have hm_spec : 4 * nx ≤ 4 ^ m := Nat.find_spec hex
  have hm_gt : m₀ < m := by
    by_contra hle
    push Not at hle
    have : 4 ^ m ≤ 4 ^ m₀ := Nat.pow_le_pow_right (by norm_num) hle
    omega
  have hm_upper : 4 ^ m < 16 * nx := by
    have hm1 : 1 ≤ m := by omega
    have hmin := Nat.find_min hex (show m - 1 < m by omega)
    push Not at hmin
    have : 4 ^ m = 4 * 4 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  obtain ⟨hgoodm, hbound, hNH, hHL, hm1, hyL⟩ := hm₀ m hm_gt.le
  obtain ⟨hrowG, hcolG, hcubeG⟩ := hgoodm
  -- integer bookkeeping
  have hK0 : 2 ^ m * (m ^ 2 + 1) ≤ 4 ^ m := by omega
  have hwK : m ^ 2 ≤ 2 ^ m * (m ^ 2 + 1) := by
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    nlinarith
  have hyc : ∀ i : Fin 2, 4 * (y i).natAbs ≤ 4 ^ m := fun i => by
    fin_cases i
    · exact (Nat.mul_le_mul_left 4 (le_max_left _ _)).trans hyL
    · exact (Nat.mul_le_mul_left 4 (le_max_right _ _)).trans hyL
  have hxc : ∀ i : Fin 2, 4 * (x.val i).natAbs ≤ 4 ^ m := fun i => by
    fin_cases i
    · exact (Nat.mul_le_mul_left 4 (le_max_left _ _)).trans hm_spec
    · exact (Nat.mul_le_mul_left 4 (le_max_right _ _)).trans hm_spec
  have hyZ : ∀ i : Fin 2, -((4 ^ m : ℕ) : ℤ) ≤ 4 * y i ∧ 4 * y i ≤ ((4 ^ m : ℕ) : ℤ) := by
    intro i
    have := hyc i
    omega
  have hxZ : ∀ i : Fin 2, -((4 ^ m : ℕ) : ℤ) ≤ 4 * x.val i ∧ 4 * x.val i ≤ ((4 ^ m : ℕ) : ℤ) := by
    intro i
    have := hxc i
    omega
  have hKZ : 4 * (((2 ^ m : ℕ) : ℤ) * (((m ^ 2 : ℕ) : ℤ) + 1)) ≤ ((4 ^ m : ℕ) : ℤ) := by
    exact_mod_cast hHL
  have hwKZ : ((m ^ 2 : ℕ) : ℤ) ≤ ((2 ^ m : ℕ) : ℤ) * (((m ^ 2 : ℕ) : ℤ) + 1) := by
    exact_mod_cast hwK
  have hiK : ∀ i : Fin (2 ^ m), (0 : ℤ) ≤ ((i : ℕ) : ℤ) * (((m ^ 2 : ℕ) : ℤ) + 1) ∧
      ((i : ℕ) : ℤ) * (((m ^ 2 : ℕ) : ℤ) + 1) ≤ ((2 ^ m : ℕ) : ℤ) * (((m ^ 2 : ℕ) : ℤ) + 1) := by
    intro i
    refine ⟨by positivity, ?_⟩
    have := Nat.mul_le_mul_right (m ^ 2 + 1) i.isLt.le
    exact_mod_cast this
  have hy0 := hyZ 0
  have hy1 := hyZ 1
  have hx0 := hxZ 0
  have hx1 := hxZ 1
  have hyCube : y ∈ cubeFinset (0 : Vertex 2) (4 ^ m) := by
    rw [mem_cubeFinset]
    intro i
    have := hyZ i
    simp only [Pi.zero_apply, sub_zero, abs_le]
    omega
  have hxCube : x.val ∈ cubeFinset (0 : Vertex 2) (4 ^ m) := by
    rw [mem_cubeFinset]
    intro i
    have := hxZ i
    simp only [Pi.zero_apply, sub_zero, abs_le]
    omega
  have hpos : (0 : ℤ) ≤ ((m ^ 2 : ℕ) : ℤ) := Nat.cast_nonneg _
  obtain ⟨V, hV, hyV, hxV, θ, hθ, hdiv, hE⟩ := exists_flow_of_crossings
    (uniqueInfiniteComponent h) hC ⟨y, hy⟩ x (L := 4 ^ m) (w := m ^ 2) (k := 2 ^ m)
    (N := m ^ q) (Nat.two_pow_pos m) (Nat.one_le_pow _ _ hm1)
    (Nat.pow_le_pow_right hm1 hq2) (hNH.trans_le (Nat.le_mul_of_pos_right _ (by omega)))
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (hcubeG y hyCube).2.2 (hcubeG x.val hxCube).2.2
    (fun i => hrowG _ (Finset.mem_Icc.2 ⟨by linarith [hiK i], by linarith [hiK i]⟩))
    (fun j => hcolG _ (Finset.mem_Icc.2 ⟨by linarith [hiK j], by linarith [hiK j]⟩))
    (hcubeG y hyCube).1 (hcubeG x.val hxCube).2.1
  refine ⟨V, hV, hyV, hxV, θ, hθ, hdiv, hE.trans ?_⟩
  have hup : ((4 ^ m : ℕ) : ℝ) ≤ 16 * nx := by exact_mod_cast hm_upper.le
  push_cast at hup
  calc crossFlowBound (4 ^ m) (m ^ 2) (2 ^ m) (m ^ q) ≤ ε / 8 * 4 ^ m := hbound
    _ ≤ ε / 8 * (16 * nx) := by gcongr
    _ = 2 * (ε * nx) := by ring
    _ ≤ 2 * (ε * eucl x.val) := by gcongr

end Rigidity.Proofs.Section5
