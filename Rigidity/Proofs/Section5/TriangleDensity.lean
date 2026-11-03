import Rigidity.Steps.Section5.GoodEventDensity
import Rigidity.Proofs.Section5.GoodEventBasics
import Rigidity.Proofs.Ergodic.TranslateDensity
import LatticeProb.Prob.AkcogluKrengelAE.BoxTiling

/-!
# Lemma 5.26: the ergodic theorem on the triangles `T_L`

Step `TriangleDensityStep` of the carving of Lemma 5.26 (`Rigidity.Steps.Section5`, eq.
`spreads-evenly` of the corrected draft): for every
null-measurable event `A`, almost surely `L⁻² |{y ∈ T_L : τ_{-y} ω ∈ A}| → P[A]`. No literature
input is used.

* Anchored boxes (`ae_tendsto_boxAvg_integral`): for a measure-preserving additive `ℤ²`-action
  with an ergodic generator, the box iteration of Lattice-Probability
  (`exists_ae_tendsto_boxAvg`) gives a limit `G` of the averages over the boxes
  `[0, m₀) × [0, m₁)` along every sequence of sides tending to infinity; along the cubes it is
  `∫ h` (`Rigidity.Proofs.Ergodic.ae_tendsto_gridAvg_integral`), so `G = ∫ h` almost surely.
* Rectangles (`ae_tendsto_upperRect`, `ae_tendsto_lowerRect`): applied to `z ↦ τ_{-z}` and to the
  reflected action `z ↦ τ_{-(z₀, -z₁)}`, for every sequence `n_L → ∞` and integers `a, b ≥ 0`,
  almost surely the number of sites `y` of `[0, a n_L) × [0, b n_L)` (resp.
  `[0, a n_L) × [-b n_L, 0)`) with `τ_{-y} ω ∈ A` is `a b n_L² P[A] + o(n_L²)`.
* Staircases (`sum_inner_le`, `le_sum_outer`): with `q + 1` columns of width `n`, `T_L` contains
  the strips `[k n, (k+1) n) × [-k n, k n)` when `(q + 1) n ≤ L + 1`, and is covered by the strips
  `[k n, (k+1) n) × [-(k+1) n, (k+1) n)` when `L + 1 ≤ (q + 1) n`. With
  `n = ⌊(L + 1)/(q + 1)⌋` and `n + 1`, the density on `T_L` lies asymptotically between
  `P[A] q / (q + 1)` and `P[A] (q + 2) / (q + 1)` (`tendsto_triangle_of_rect`).
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

/-! ### Anchored boxes of arbitrary sides -/

section Boxes

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}

/-- **Pointwise ergodic theorem along anchored boxes.** For a measure-preserving additive
`ℤ^d`-action `σ` such that `σ_{e_i}` is ergodic for some `i`, bounded measurable `h`, and boxes
`[0, m_N)` whose sides all tend to infinity, almost surely the averages of `h ∘ σ_z` over the boxes
tend to `∫ h`. -/
theorem ae_tendsto_boxAvg_integral [IsProbabilityMeasure μ] {σ : Site d → Ω → Ω}
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    (i : Fin d) (hErg : Ergodic (σ (Pi.single i 1)) μ) {h : Ω → ℝ} (hh : Measurable h)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M) {m : ℕ → Fin d → ℕ}
    (hm : ∀ i, Tendsto (fun N => m N i) atTop atTop) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => boxAvg σ h Finset.univ (m N) ω) atTop (𝓝 (∫ ω, h ω ∂μ)) := by
  obtain ⟨G, -, -, hconv, -⟩ := exists_ae_tendsto_boxAvg hσ hσadd hh hM hb Finset.univ
  filter_upwards [hconv (fun N _ => N) (fun _ _ => tendsto_id), hconv m (fun i _ => hm i),
    Rigidity.Proofs.Ergodic.ae_tendsto_gridAvg_integral hσ hσadd i hErg hh hb] with ω h1 h2 h3
  simp only [boxAvg_univ_const_eq_gridAvg] at h1
  rw [tendsto_nhds_unique h1 h3] at h2
  exact h2

end Boxes

/-! ### Rectangles of `ℤ²` -/

/-- The rectangle `[a₀, a₁) × [b₀, b₁)` of `ℤ²`. -/
noncomputable def rect (a₀ a₁ b₀ b₁ : ℤ) : Finset (Vertex 2) :=
  Fintype.piFinset ![Finset.Ico a₀ a₁, Finset.Ico b₀ b₁]

theorem mem_rect {a₀ a₁ b₀ b₁ : ℤ} {x : Vertex 2} :
    x ∈ rect a₀ a₁ b₀ b₁ ↔ (a₀ ≤ x 0 ∧ x 0 < a₁) ∧ b₀ ≤ x 1 ∧ x 1 < b₁ := by
  simp [rect, Fintype.mem_piFinset, Fin.forall_fin_two]

theorem rect_eq_empty {a₀ a₁ b₀ b₁ : ℤ} (h : a₁ ≤ a₀ ∨ b₁ ≤ b₀) : rect a₀ a₁ b₀ b₁ = ∅ := by
  ext x
  simp only [mem_rect, Finset.notMem_empty, iff_false]
  omega

/-- A rectangle splits along a vertical line. -/
theorem sum_rect_split (g : Vertex 2 → ℝ) {a₀ a₁ a₂ : ℤ} (b₀ b₁ : ℤ) (h₁ : a₀ ≤ a₁)
    (h₂ : a₁ ≤ a₂) :
    ∑ x ∈ rect a₀ a₂ b₀ b₁, g x = ∑ x ∈ rect a₀ a₁ b₀ b₁, g x + ∑ x ∈ rect a₁ a₂ b₀ b₁, g x := by
  rw [← Finset.sum_union (Finset.disjoint_left.mpr fun x hx hx' => by
    rw [mem_rect] at hx hx'
    omega)]
  congr 1
  ext x
  simp only [Finset.mem_union, mem_rect]
  omega

/-- Sums over the anchored boxes of `ℕ²` are sums over rectangles of `ℤ²`. -/
theorem sum_boxGridSet_natToSite (g : Vertex 2 → ℝ) (m : Fin 2 → ℕ) :
    ∑ w ∈ boxGridSet Finset.univ m, g (natToSite w) = ∑ x ∈ rect 0 (m 0) 0 (m 1), g x := by
  have hbox : ∀ w : Fin 2 → ℕ, w ∈ boxGridSet Finset.univ m ↔ w 0 < m 0 ∧ w 1 < m 1 := by
    intro w
    simp [boxGridSet, Fintype.mem_piFinset, Fin.forall_fin_two]
  refine Finset.sum_nbij' natToSite (fun x i => (x i).toNat) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro w hw
    rw [hbox] at hw
    rw [mem_rect]
    simp only [natToSite]
    omega
  · intro x hx
    rw [mem_rect] at hx
    rw [hbox]
    omega
  · intro w _
    funext i
    simp [natToSite]
  · intro x hx
    rw [mem_rect] at hx
    funext i
    fin_cases i <;> simp [natToSite] <;> omega

/-- The reflection `(x₀, x₁) ↦ (x₀, -1 - x₁)`, exchanging `[0, b)` and `[-b, 0)`. -/
def lowerReflect (x : Vertex 2) : Vertex 2 := ![x 0, -1 - x 1]

theorem sum_rect_lowerReflect (g : Vertex 2 → ℝ) (a b : ℤ) :
    ∑ x ∈ rect 0 a 0 b, g (lowerReflect x) = ∑ x ∈ rect 0 a (-b) 0, g x := by
  have hinv : ∀ x, lowerReflect (lowerReflect x) = x := fun x => by
    funext i
    fin_cases i <;> simp [lowerReflect]
  refine Finset.sum_nbij' lowerReflect lowerReflect ?_ ?_ (fun x _ => hinv x)
    (fun x _ => hinv x) (fun _ _ => rfl)
  · intro x hx
    rw [mem_rect] at hx ⊢
    simp only [lowerReflect, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · intro x hx
    rw [mem_rect] at hx ⊢
    simp only [lowerReflect, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

/-! ### The ergodic theorem on rectangles -/

variable {p : unitInterval}

/-- The indicator `1_A(τ_{-y} ω)` of the event `A` seen from the site `y`. -/
noncomputable def seenFrom (A : Set (Configuration 2)) (ω : Configuration 2) (y : Vertex 2) : ℝ :=
  A.indicator 1 (configurationTranslation (-y) ω)

theorem seenFrom_nonneg (A : Set (Configuration 2)) (ω : Configuration 2) (y : Vertex 2) :
    0 ≤ seenFrom A ω y :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- The ergodic theorem on the anchored boxes of the action `z ↦ τ_{-ρ z}`, for an additive `ρ`
with `ρ e₁ ≠ 0`, applied to `1_A ∘ τ_c`. -/
theorem ae_tendsto_translate_box {A : Set (Configuration 2)} (hA : MeasurableSet A)
    {ρ : Vertex 2 → Vertex 2} (hρadd : ∀ z w, ρ (z + w) = ρ z + ρ w)
    (hρ : ρ (Pi.single 0 1) ≠ 0) (c : Vertex 2) {m : ℕ → Fin 2 → ℕ}
    (hm : ∀ i, Tendsto (fun N => m N i) atTop atTop) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, Tendsto (fun N =>
        (∑ w ∈ boxGridSet Finset.univ (m N), seenFrom A ω (ρ (natToSite w) - c)) /
          ((m N 0 : ℝ) * m N 1)) atTop (𝓝 (latticeBondLaw 2 p A).toReal) := by
  set μ := latticeBondLaw 2 p
  have hσ : ∀ z, MeasurePreserving (fun ω => configurationTranslation (-ρ z) ω) μ μ :=
    fun z => measurePreserving_configurationTranslation p _
  have hσadd : ∀ z w ω, configurationTranslation (-ρ (z + w)) ω =
      configurationTranslation (-ρ z) (configurationTranslation (-ρ w) ω) := by
    intro z w ω
    rw [configurationTranslation_add, hρadd, neg_add]
  have hτc := measurePreserving_configurationTranslation p c
  have hind : Measurable (A.indicator (1 : Configuration 2 → ℝ)) := measurable_one.indicator hA
  have hconv := ae_tendsto_boxAvg_integral (σ := fun z ω => configurationTranslation (-ρ z) ω)
    hσ hσadd 0 (ergodic_configurationTranslation p (neg_ne_zero.mpr hρ))
    (hind.comp hτc.measurable) zero_le_one
    (fun ω => by by_cases hω : configurationTranslation c ω ∈ A <;> simp [hω]) hm
  have hint : ∫ ω, (A.indicator 1 ∘ configurationTranslation c) ω ∂μ = (μ A).toReal := by
    rw [Function.comp_def, Rigidity.Proofs.Ergodic.integral_comp_of_measurePreserving hτc hind,
      integral_indicator_one hA, measureReal_def]
  rw [hint] at hconv
  filter_upwards [hconv] with ω hω
  refine hω.congr fun N => ?_
  simp only [boxAvg, Fin.prod_univ_two]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [seenFrom, Function.comp_apply, configurationTranslation_add]
  rw [neg_sub, sub_eq_add_neg]

/-- The reflection `z ↦ (z₀, -z₁)`. -/
def flipSecond (z : Vertex 2) : Vertex 2 := ![z 0, -z 1]

theorem flipSecond_add (z w : Vertex 2) : flipSecond (z + w) = flipSecond z + flipSecond w := by
  funext i
  fin_cases i
  · simp [flipSecond]
  · simp only [flipSecond, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      Pi.add_apply]
    ring

theorem flipSecond_single_ne_zero : flipSecond (Pi.single 0 1) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [flipSecond] at this

/-- The rectangle `[0, a n_L) × [0, b n_L)`: almost surely the proportion of its sites `y` with
`τ_{-y} ω ∈ A`, normalized by `n_L²`, tends to `a b P[A]`. -/
theorem ae_tendsto_upperRect {A : Set (Configuration 2)} (hA : MeasurableSet A) {n : ℕ → ℕ}
    (hn : Tendsto n atTop atTop) (a b : ℕ) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, Tendsto (fun L =>
        (∑ x ∈ rect 0 ((a : ℤ) * n L) 0 ((b : ℤ) * n L), seenFrom A ω x) / (n L : ℝ) ^ 2)
      atTop (𝓝 (a * b * (latticeBondLaw 2 p A).toReal)) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine Eventually.of_forall fun ω => ?_
    simp [rect_eq_empty]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · refine Eventually.of_forall fun ω => ?_
    simp [rect_eq_empty]
  set m : ℕ → Fin 2 → ℕ := fun L => ![a * n L, b * n L]
  have hm : ∀ i, Tendsto (fun L => m L i) atTop atTop := by
    intro i
    fin_cases i
    · exact tendsto_atTop_mono (fun L => Nat.le_mul_of_pos_left _ ha) hn
    · exact tendsto_atTop_mono (fun L => Nat.le_mul_of_pos_left _ hb) hn
  filter_upwards [ae_tendsto_translate_box (p := p) hA (ρ := id) (fun _ _ => rfl)
    (fun h => by simpa using congrFun h 0) 0 hm] with ω hω
  refine ((hω.const_mul ((a : ℝ) * b)).congr' ?_)
  filter_upwards [hn.eventually_gt_atTop 0] with L hL
  simp only [id, sub_zero]
  rw [sum_boxGridSet_natToSite]
  simp only [m, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  have hL' : (n L : ℝ) ≠ 0 := by positivity
  field_simp

/-- The rectangle `[0, a n_L) × [-b n_L, 0)`: almost surely the proportion of its sites `y` with
`τ_{-y} ω ∈ A`, normalized by `n_L²`, tends to `a b P[A]`. -/
theorem ae_tendsto_lowerRect {A : Set (Configuration 2)} (hA : MeasurableSet A) {n : ℕ → ℕ}
    (hn : Tendsto n atTop atTop) (a b : ℕ) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, Tendsto (fun L =>
        (∑ x ∈ rect 0 ((a : ℤ) * n L) (-((b : ℤ) * n L)) 0, seenFrom A ω x) / (n L : ℝ) ^ 2)
      atTop (𝓝 (a * b * (latticeBondLaw 2 p A).toReal)) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine Eventually.of_forall fun ω => ?_
    simp [rect_eq_empty]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · refine Eventually.of_forall fun ω => ?_
    simp [rect_eq_empty]
  set m : ℕ → Fin 2 → ℕ := fun L => ![a * n L, b * n L]
  have hm : ∀ i, Tendsto (fun L => m L i) atTop atTop := by
    intro i
    fin_cases i
    · exact tendsto_atTop_mono (fun L => Nat.le_mul_of_pos_left _ ha) hn
    · exact tendsto_atTop_mono (fun L => Nat.le_mul_of_pos_left _ hb) hn
  filter_upwards [ae_tendsto_translate_box (p := p) hA flipSecond_add flipSecond_single_ne_zero
    ![0, 1] hm] with ω hω
  refine ((hω.const_mul ((a : ℝ) * b)).congr' ?_)
  filter_upwards [hn.eventually_gt_atTop 0] with L hL
  have hrefl : ∀ w : Fin 2 → ℕ, flipSecond (natToSite w) - ![0, 1] =
      lowerReflect (natToSite w) := fun w => by
    funext i
    fin_cases i
    · simp [flipSecond, lowerReflect]
    · simp only [flipSecond, lowerReflect, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_zero, Pi.sub_apply]
      ring
  simp only [hrefl]
  rw [sum_boxGridSet_natToSite (fun x => seenFrom A ω (lowerReflect x)),
    sum_rect_lowerReflect]
  simp only [m, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  have hL' : (n L : ℝ) ≠ 0 := by positivity
  field_simp

/-! ### Staircases in the triangle -/

/-- The triangle `T_L` as a finite set. -/
noncomputable def triangleFinset (L : ℕ) : Finset (Vertex 2) :=
  (rect 0 (L + 1) (-L) (L + 1)).filter fun x => |x 1| ≤ x 0

theorem mem_triangleFinset {L : ℕ} {x : Vertex 2} :
    x ∈ triangleFinset L ↔ x ∈ triangle L := by
  simp only [triangleFinset, Finset.mem_filter, mem_rect, triangle, Set.mem_setOf_eq, abs_le]
  omega

/-- The upper strip `[k n, (k+1) n) × [0, j n)`. -/
noncomputable def upperPiece (k j n : ℕ) : Finset (Vertex 2) :=
  rect ((k : ℤ) * n) (((k + 1 : ℕ) : ℤ) * n) 0 ((j : ℤ) * n)

/-- The lower strip `[k n, (k+1) n) × [-j n, 0)`. -/
noncomputable def lowerPiece (k j n : ℕ) : Finset (Vertex 2) :=
  rect ((k : ℤ) * n) (((k + 1 : ℕ) : ℤ) * n) (-((j : ℤ) * n)) 0

/-- A strip is the difference of two anchored rectangles. -/
theorem sum_rect_strip (g : Vertex 2 → ℝ) (k n : ℕ) (b₀ b₁ : ℤ) :
    ∑ x ∈ rect ((k : ℤ) * n) (((k + 1 : ℕ) : ℤ) * n) b₀ b₁, g x =
      ∑ x ∈ rect 0 (((k + 1 : ℕ) : ℤ) * n) b₀ b₁, g x - ∑ x ∈ rect 0 ((k : ℤ) * n) b₀ b₁, g x := by
  rw [sum_rect_split g b₀ b₁ (a₀ := 0) (a₁ := (k : ℤ) * n) (a₂ := ((k + 1 : ℕ) : ℤ) * n)
    (by positivity) (by push_cast; nlinarith)]
  ring

theorem mem_piece_fst {k j n : ℕ} {x : Vertex 2} (hx : x ∈ upperPiece k j n ∪ lowerPiece k j n) :
    (k : ℤ) * n ≤ x 0 ∧ x 0 < ((k : ℤ) + 1) * n := by
  rcases Finset.mem_union.mp hx with h | h <;>
    · rw [upperPiece, lowerPiece, mem_rect] at *
      push_cast at h
      exact h.1

theorem pairwiseDisjoint_pieces (J : ℕ → ℕ) (n : ℕ) (s : Finset ℕ) :
    (s : Set ℕ).PairwiseDisjoint fun k => upperPiece k (J k) n ∪ lowerPiece k (J k) n := by
  intro k _ k' _ hkk'
  refine Finset.disjoint_left.mpr fun x hx hx' => ?_
  obtain ⟨h1, h2⟩ := mem_piece_fst hx
  obtain ⟨h1', h2'⟩ := mem_piece_fst hx'
  rcases lt_or_gt_of_ne hkk' with h | h
  · have : ((k : ℤ) + 1) * n ≤ (k' : ℤ) * n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast h) (by positivity)
    linarith
  · have : ((k' : ℤ) + 1) * n ≤ (k : ℤ) * n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast h) (by positivity)
    linarith

theorem disjoint_upperPiece_lowerPiece (k j n : ℕ) :
    Disjoint (upperPiece k j n) (lowerPiece k j n) :=
  Finset.disjoint_left.mpr fun x hx hx' => by
    rw [upperPiece, mem_rect] at hx
    rw [lowerPiece, mem_rect] at hx'
    omega

theorem sum_pieces_eq (f : Vertex 2 → ℝ) (J : ℕ → ℕ) (n : ℕ) (s : Finset ℕ) :
    ∑ k ∈ s, (∑ x ∈ upperPiece k (J k) n, f x + ∑ x ∈ lowerPiece k (J k) n, f x) =
      ∑ x ∈ s.biUnion (fun k => upperPiece k (J k) n ∪ lowerPiece k (J k) n), f x := by
  rw [Finset.sum_biUnion (pairwiseDisjoint_pieces J n s)]
  exact Finset.sum_congr rfl fun k _ =>
    (Finset.sum_union (disjoint_upperPiece_lowerPiece k (J k) n)).symm

/-- The inner staircase: if `(q + 1) n ≤ L + 1`, the strips `[k n, (k+1) n) × [-k n, k n)`,
`k ≤ q`, lie in `T_L`. -/
theorem sum_inner_le {f : Vertex 2 → ℝ} (hf : ∀ x, 0 ≤ f x) {q n L : ℕ}
    (h : (q + 1) * n ≤ L + 1) :
    ∑ k ∈ Finset.range (q + 1), (∑ x ∈ upperPiece k k n, f x + ∑ x ∈ lowerPiece k k n, f x) ≤
      ∑ x ∈ triangleFinset L, f x := by
  rw [sum_pieces_eq f fun k => k]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun x _ _ => hf x
  obtain ⟨k, hk, hx⟩ := Finset.mem_biUnion.mp hx
  have hkq : ((k : ℤ) + 1) * n ≤ L + 1 := by
    have : ((k : ℤ) + 1) * n ≤ ((q : ℤ) + 1) * n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.mem_range.mp hk) (by positivity)
    have h' : (((q + 1) * n : ℕ) : ℤ) ≤ ((L + 1 : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    linarith
  rw [mem_triangleFinset, triangle, Set.mem_setOf_eq, abs_le]
  rcases Finset.mem_union.mp hx with h' | h' <;>
    · simp only [upperPiece, lowerPiece, mem_rect] at h'
      push_cast at h'
      refine ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-- The outer staircase: if `L + 1 ≤ (q + 1) n`, the strips `[k n, (k+1) n) × [-(k+1) n,
(k+1) n)`, `k ≤ q`, cover `T_L`. -/
theorem le_sum_outer {f : Vertex 2 → ℝ} (hf : ∀ x, 0 ≤ f x) {q n L : ℕ} (hn : 0 < n)
    (h : L + 1 ≤ (q + 1) * n) :
    ∑ x ∈ triangleFinset L, f x ≤ ∑ k ∈ Finset.range (q + 1),
      (∑ x ∈ upperPiece k (k + 1) n, f x + ∑ x ∈ lowerPiece k (k + 1) n, f x) := by
  rw [sum_pieces_eq f (fun k => k + 1)]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun x _ _ => hf x
  rw [mem_triangleFinset, triangle, Set.mem_setOf_eq, abs_le] at hx
  obtain ⟨⟨hx1, hx1'⟩, hxL⟩ := hx
  set t := (x 0).toNat
  have ht : (t : ℤ) = x 0 := Int.toNat_of_nonneg (by linarith)
  set k := t / n
  have hdiv := Nat.div_add_mod t n
  have hmod := Nat.mod_lt t hn
  have hdiv' : (n : ℤ) * k + ((t % n : ℕ) : ℤ) = x 0 := by rw [← ht]; exact_mod_cast hdiv
  have hmod' : ((t % n : ℕ) : ℤ) < n := by exact_mod_cast hmod
  have hmod0 : (0 : ℤ) ≤ ((t % n : ℕ) : ℤ) := Nat.cast_nonneg _
  have hlo : (k : ℤ) * n ≤ x 0 := by linarith
  have hhi : x 0 < ((k : ℤ) + 1) * n := by linarith
  have hkq : k < q + 1 := by
    have h' : (((L + 1 : ℕ) : ℤ)) ≤ (((q + 1) * n : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    have : (k : ℤ) * n < ((q : ℤ) + 1) * n := by linarith
    exact_mod_cast lt_of_mul_lt_mul_right this (by positivity)
  refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hkq, ?_⟩
  rcases le_or_gt 0 (x 1) with h1 | h1
  · refine Finset.mem_union_left _ ?_
    rw [upperPiece, mem_rect]
    push_cast
    refine ⟨⟨hlo, hhi⟩, h1, by linarith⟩
  · refine Finset.mem_union_right _ ?_
    rw [lowerPiece, mem_rect]
    push_cast
    refine ⟨⟨hlo, hhi⟩, by linarith, h1⟩

/-! ### The deterministic squeeze -/

/-- The column width `⌊(L + 1)/(q + 1)⌋ + e`. -/
def columnWidth (q e L : ℕ) : ℕ := (L + 1) / (q + 1) + e

theorem tendsto_columnWidth (q e : ℕ) : Tendsto (columnWidth q e) atTop atTop := by
  refine tendsto_atTop_mono (fun L => Nat.le_add_right _ _) ?_
  refine (Nat.tendsto_div_const_atTop (Nat.succ_ne_zero q)).comp ?_
  exact tendsto_add_atTop_nat 1

theorem tendsto_columnWidth_div (q e : ℕ) :
    Tendsto (fun L : ℕ => (columnWidth q e L : ℝ) / L) atTop (𝓝 (1 / (q + 1))) := by
  have hq : (0 : ℝ) < q + 1 := by positivity
  have hlim : ∀ c : ℝ, Tendsto (fun L : ℕ => ((L + 1 : ℝ) / (q + 1) + c) / L) atTop
      (𝓝 (1 / (q + 1))) := by
    intro c
    have := (tendsto_const_div_atTop_nhds_zero_nat ((1 : ℝ) / (q + 1) + c)).const_add
      ((1 : ℝ) / (q + 1))
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with L hL
    have hL' : (L : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (e - 1)) (hlim e) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with L hL
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg L)
    have h1 := Nat.sub_one_lt_floor ((L + 1 : ℝ) / (q + 1))
    rw [show ((L + 1 : ℝ) / (q + 1)) = ((L + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ) by push_cast; rfl,
      Nat.floor_div_eq_div] at h1
    simp only [columnWidth]
    push_cast at h1 ⊢
    linarith
  · filter_upwards [eventually_gt_atTop 0] with L hL
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg L)
    have h1 : (((L + 1) / (q + 1) : ℕ) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ) :=
      Nat.cast_div_le
    simp only [columnWidth]
    push_cast at h1 ⊢
    linarith

/-- The staircase sums, normalized by the squared column width, converge. -/
theorem tendsto_pieces {f : Vertex 2 → ℝ} {P : ℝ}
    (hU : ∀ q e a b : ℕ, Tendsto (fun L =>
      (∑ x ∈ rect 0 ((a : ℤ) * columnWidth q e L) 0 ((b : ℤ) * columnWidth q e L), f x) /
        (columnWidth q e L : ℝ) ^ 2) atTop (𝓝 (a * b * P)))
    (hD : ∀ q e a b : ℕ, Tendsto (fun L =>
      (∑ x ∈ rect 0 ((a : ℤ) * columnWidth q e L) (-((b : ℤ) * columnWidth q e L)) 0, f x) /
        (columnWidth q e L : ℝ) ^ 2) atTop (𝓝 (a * b * P)))
    (q e : ℕ) (J : ℕ → ℕ) :
    Tendsto (fun L => (∑ k ∈ Finset.range (q + 1),
        (∑ x ∈ upperPiece k (J k) (columnWidth q e L), f x +
          ∑ x ∈ lowerPiece k (J k) (columnWidth q e L), f x)) / (columnWidth q e L : ℝ) ^ 2)
      atTop (𝓝 (∑ k ∈ Finset.range (q + 1), 2 * (J k : ℝ) * P)) := by
  simp only [Finset.sum_div]
  refine tendsto_finsetSum _ fun k _ => ?_
  have h := (((hU q e (k + 1) (J k)).sub (hU q e k (J k))).add
    ((hD q e (k + 1) (J k)).sub (hD q e k (J k))))
  convert h using 1
  · funext L
    rw [upperPiece, lowerPiece, sum_rect_strip, sum_rect_strip]
    ring
  · push_cast
    ring_nf

theorem sum_range_two_mul (q : ℕ) (P : ℝ) :
    ∑ k ∈ Finset.range (q + 1), 2 * (k : ℝ) * P = q * (q + 1) * P := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_range_two_mul_succ (q : ℕ) (P : ℝ) :
    ∑ k ∈ Finset.range (q + 1), 2 * ((k + 1 : ℕ) : ℝ) * P = (q + 1) * (q + 2) * P := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- **The deterministic squeeze.** If the counts on the anchored rectangles of the four
column widths have densities `P`, the counts on the triangles `T_L` have density `P`. -/
theorem tendsto_triangle_of_rect {f : Vertex 2 → ℝ} (hf : ∀ x, 0 ≤ f x) {P : ℝ}
    (hU : ∀ q e a b : ℕ, Tendsto (fun L =>
      (∑ x ∈ rect 0 ((a : ℤ) * columnWidth q e L) 0 ((b : ℤ) * columnWidth q e L), f x) /
        (columnWidth q e L : ℝ) ^ 2) atTop (𝓝 (a * b * P)))
    (hD : ∀ q e a b : ℕ, Tendsto (fun L =>
      (∑ x ∈ rect 0 ((a : ℤ) * columnWidth q e L) (-((b : ℤ) * columnWidth q e L)) 0, f x) /
        (columnWidth q e L : ℝ) ^ 2) atTop (𝓝 (a * b * P))) :
    Tendsto (fun L : ℕ => (∑ x ∈ triangleFinset L, f x) / (L : ℝ) ^ 2) atTop (𝓝 P) := by
  -- rescaling from the column width to `L`
  have hscale : ∀ (q e : ℕ) (J : ℕ → ℕ), Tendsto (fun L : ℕ => (∑ k ∈ Finset.range (q + 1),
      (∑ x ∈ upperPiece k (J k) (columnWidth q e L), f x +
        ∑ x ∈ lowerPiece k (J k) (columnWidth q e L), f x)) / (L : ℝ) ^ 2) atTop
      (𝓝 ((∑ k ∈ Finset.range (q + 1), 2 * (J k : ℝ) * P) * (1 / (q + 1)) ^ 2)) := by
    intro q e J
    refine ((tendsto_pieces hU hD q e J).mul ((tendsto_columnWidth_div q e).pow 2)).congr' ?_
    filter_upwards [eventually_gt_atTop 0, (tendsto_columnWidth q e).eventually_gt_atTop 0]
      with L hL hw
    have hL' : (L : ℝ) ≠ 0 := by positivity
    have hw' : (columnWidth q e L : ℝ) ≠ 0 := by positivity
    field_simp
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨q, hq⟩ := exists_nat_gt (P / (P - a))
    have hq' : P < (P - a) * (q + 1) := by
      rw [div_lt_iff₀ (by linarith)] at hq
      nlinarith
    have hlim : a < (∑ k ∈ Finset.range (q + 1), 2 * (k : ℝ) * P) * (1 / (q + 1)) ^ 2 := by
      rw [sum_range_two_mul]
      have hq1 : (0 : ℝ) < q + 1 := by positivity
      rw [show (q : ℝ) * (q + 1) * P * (1 / (q + 1)) ^ 2 = P - P / (q + 1) by field_simp; ring,
        lt_sub_comm, div_lt_iff₀ hq1]
      linarith
    filter_upwards [(hscale q 0 fun k => k).eventually (lt_mem_nhds hlim)] with L hL
    refine hL.trans_le (div_le_div_of_nonneg_right (sum_inner_le hf ?_) (by positivity))
    simp only [columnWidth, add_zero]
    rw [mul_comm]
    exact Nat.div_mul_le_self _ _
  · obtain ⟨q, hq⟩ := exists_nat_gt (P / (b - P))
    have hlim : (∑ k ∈ Finset.range (q + 1), 2 * ((k + 1 : ℕ) : ℝ) * P) *
        (1 / (q + 1)) ^ 2 < b := by
      rw [sum_range_two_mul_succ]
      have hq1 : (0 : ℝ) < q + 1 := by positivity
      rw [show ((q : ℝ) + 1) * (q + 2) * P * (1 / (q + 1)) ^ 2 = P + P / (q + 1) by
        field_simp; ring, ← lt_sub_iff_add_lt', div_lt_iff₀ hq1]
      rw [div_lt_iff₀ (by linarith)] at hq
      nlinarith
    filter_upwards [(hscale q 1 fun k => k + 1).eventually (gt_mem_nhds hlim)] with L hL
    refine lt_of_le_of_lt (div_le_div_of_nonneg_right (le_sum_outer hf (by
      simp [columnWidth]) ?_) (by positivity)) hL
    simp only [columnWidth]
    have := Nat.lt_div_mul_add (a := L + 1) (Nat.succ_pos q)
    nlinarith

/-! ### The step -/

/-- **Step `TriangleDensityStep`** (eq. `spreads-evenly`, the ergodic theorem on the triangles
`T_L`): for every null-measurable event `A`, almost surely `L⁻² |{y ∈ T_L : τ_{-y} ω ∈ A}| → P[A]`.
-/
theorem triangleDensityStep (p : unitInterval) : TriangleDensityStep p := by
  classical
  intro A hA
  set μ := latticeBondLaw 2 p
  set A' := toMeasurable μ A
  have hA' : MeasurableSet A' := measurableSet_toMeasurable μ A
  have hAA' : ∀ᵐ x ∂μ, x ∈ A' ↔ x ∈ A := Filter.eventuallyEq_set.mp hA.toMeasurable_ae_eq
  have hmem : ∀ᵐ ω ∂μ, ∀ y : Vertex 2,
      (configurationTranslation (-y) ω ∈ A' ↔ configurationTranslation (-y) ω ∈ A) :=
    ae_all_iff.mpr fun y =>
      (measurePreserving_configurationTranslation p (-y)).quasiMeasurePreserving.ae hAA'
  have hrect : ∀ᵐ ω ∂μ, ∀ q e a b : ℕ,
      Tendsto (fun L =>
        (∑ x ∈ rect 0 ((a : ℤ) * columnWidth q e L) 0 ((b : ℤ) * columnWidth q e L),
          seenFrom A' ω x) / (columnWidth q e L : ℝ) ^ 2) atTop (𝓝 (a * b * (μ A').toReal)) ∧
      Tendsto (fun L =>
        (∑ x ∈ rect 0 ((a : ℤ) * columnWidth q e L) (-((b : ℤ) * columnWidth q e L)) 0,
          seenFrom A' ω x) / (columnWidth q e L : ℝ) ^ 2) atTop (𝓝 (a * b * (μ A').toReal)) := by
    refine ae_all_iff.mpr fun q => ae_all_iff.mpr fun e => ae_all_iff.mpr fun a =>
      ae_all_iff.mpr fun b => ?_
    exact (ae_tendsto_upperRect hA' (tendsto_columnWidth q e) a b).and
      (ae_tendsto_lowerRect hA' (tendsto_columnWidth q e) a b)
  filter_upwards [hrect, hmem] with ω hω hω'
  have hlim := tendsto_triangle_of_rect (seenFrom_nonneg A' ω)
    (fun q e a b => (hω q e a b).1) (fun q e a b => (hω q e a b).2)
  rw [measure_toMeasurable] at hlim
  refine hlim.congr fun L => ?_
  congr 1
  have hset : {y | y ∈ triangle L ∧ configurationTranslation (-y) ω ∈ A} =
      ↑((triangleFinset L).filter fun y => configurationTranslation (-y) ω ∈ A') := by
    ext y
    simp only [Set.mem_setOf_eq, Finset.coe_filter, mem_triangleFinset, hω' y]
  rw [hset, Set.ncard_coe_finset, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [seenFrom, Set.indicator_apply, Pi.one_apply]

/-- Lemma 5.26 from the null-measurability of the good event alone. -/
theorem goodEventDensity_of_measurableStep (p : unitInterval) (hM : GoodEventMeasurableStep p) :
    GoodEventDensityStmt p :=
  goodEventDensity_of_steps hM goodEventTranslationStep (triangleDensityStep p)

end Rigidity.Proofs.Section5
