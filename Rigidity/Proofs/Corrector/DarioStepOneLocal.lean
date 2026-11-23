import Rigidity.Proofs.Corrector.DarioResamplePartition
import Rigidity.Proofs.Corrector.DarioFiniteEnergyGrowth
import Rigidity.Proofs.Corrector.DarioCoarseHeatField
import Rigidity.Proofs.Poincare.BoxMaximal

/-!
# Step 1 of the proof of Lemma 3.3 of Dario: the change of partition is local

The term (3.15)-(i) of Dario is `Φ_{r²} * (∇[w]_{𝒫} - ∇[w]_{𝒫^e})(0)` for one function `w`, the
coarsenings being taken with the partitions of two configurations `ω₀, ω₁` equal off a bond `e`.
Its summand at `y` in direction `j` is `partitionChange ω₀ ω₁ w j y`. Step 1 uses Lemma 3.5 through
`ResampleLocal ρ M ω₀ ω₁ x`: inside the box `|· - x|_∞ < ρ` the partition cubes of both
configurations have side at most `M`, and outside it their anchors agree. Lemma 3.5
(`ResamplePartitionBound C₀ C`) gives it with `ρ = C₀ s₀`, `M = C s₀`, `s₀` the side of the
partition cube of `ω₀` at the endpoint `x` of `e` (`resampleLocal_of_bound`). Then

* `partitionChange_eq_zero`: the summand vanishes unless `y` or `y + e_j` lies in the box;
* `abs_partitionChange_le`: otherwise it is at most the sum of the total variations of `w` over the
  open edges of `ω₀` and of `ω₁` in the box of radius `(ρ + 1) + 5M` around `x`, since the coarse
  gradient across neighbouring cubes is controlled by the total variation over the square of side
  `9s` of the smaller cube (`abs_coarseAnchor_sub_le_supBox`);
* `sq_tsum_partitionChange_le`: `|Σ_y Φ(y) partitionChange(y)|² ≤ |B| (Σ_{y ∈ B} Φ(y)²) (V₀ + V₁)²`
  with `B` the box of radius `ρ` around `x`, by the Cauchy–Schwarz inequality over `B`.

This is (3.16) of Dario in the flip form, with the Cauchy–Schwarz inequality over the ball in place
of the supremum of the heat kernel over the ball; the latter is then not needed.
-/

namespace Rigidity.Corrector

open LatticeProb.Percolation Rigidity.Percolation Rigidity.Poincare
open scoped Classical

/-- The square of side `9s` around a cube of side `s ≤ M` containing a point within `L` of `x`
lies in the box of radius `L + 5M` around `x`. -/
theorem ninefold_subset_supBox {Q : TriadicCube 2} {x y : Vertex 2} {L M : ℕ}
    (hy : y ∈ Q.vertices) (hyx : ∀ i, |y i - x i| ≤ L) (hM : 3 ^ Q.scale ≤ M) :
    Q.ninefold.vertices ⊆ supBox x (L + 5 * M) := by
  intro v hv
  have hv' := TriadicCube.mem_ninefold.1 (Finset.mem_coe.2 hv)
  rw [mem_supBox]
  intro i
  have h1 := hv' i
  have h2 := Q.abs_sub_center_le hy i
  have h3 := Q.two_mul_ninefoldRadius
  have h4 := hyx i
  have hM' : (3 : ℤ) ^ Q.scale ≤ M := by exact_mod_cast hM
  have t1 := abs_sub_le (v i) (Q.center i) (x i)
  have t2 := abs_sub_le (Q.center i) (y i) (x i)
  have t3 : |Q.center i - y i| = |y i - Q.center i| := abs_sub_comm _ _
  push_cast
  linarith

/-- The total variation over open edges grows with the region. -/
theorem edgeVariationIn_mono {ω : Configuration 2} {S T : Finset (Vertex 2)} (h : S ⊆ T)
    (w : Vertex 2 → ℝ) : edgeVariationIn ω S w ≤ edgeVariationIn ω T w := by
  set f : Vertex 2 → Vertex 2 → ℝ := fun a b =>
    if (openGraph ω).Adj a b then |w a - w b| else 0 with hf
  have hnn : ∀ a b, 0 ≤ f a b := fun a b => by
    simp only [hf]
    split_ifs <;> positivity
  show ∑ a ∈ S, ∑ b ∈ S, f a b ≤ ∑ a ∈ T, ∑ b ∈ T, f a b
  calc ∑ a ∈ S, ∑ b ∈ S, f a b ≤ ∑ a ∈ S, ∑ b ∈ T, f a b :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum_of_subset_of_nonneg h fun b _ _ => hnn a b
    _ ≤ ∑ a ∈ T, ∑ b ∈ T, f a b :=
        Finset.sum_le_sum_of_subset_of_nonneg h fun a _ _ => Finset.sum_nonneg fun b _ => hnn a b

/-- **Coarse gradient in a box**: across neighbouring points `y, y'` within `L` of `x`, one of
whose partition cubes has side at most `M`, the coarsening of `w` changes by at most the total
variation of `w` over the open edges of the box of radius `L + 5M` around `x`. -/
theorem abs_coarseAnchor_sub_le_supBox {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {x y y' : Vertex 2} (hnear : ∀ i, |y i - y' i| ≤ 1) {L M : ℕ}
    (hM : 3 ^ (planarPartCube ω y).scale ≤ M ∨ 3 ^ (planarPartCube ω y').scale ≤ M)
    (hy : ∀ i, |y i - x i| ≤ L) (hy' : ∀ i, |y' i - x i| ≤ L) (w : Vertex 2 → ℝ) :
    |w (planarCoarseAnchor ω y) - w (planarCoarseAnchor ω y')| ≤
      edgeVariationIn ω (supBox x (L + 5 * M)) w := by
  rcases le_total (planarPartCube ω y).scale (planarPartCube ω y').scale with h | h
  · have hMy : 3 ^ (planarPartCube ω y).scale ≤ M :=
      hM.elim id fun h' => (Nat.pow_le_pow_right (by norm_num) h).trans h'
    exact (abs_coarseAnchor_sub_le hP hnear h w).trans
      (edgeVariationIn_mono (ninefold_subset_supBox (planarPartCube_spec hP y).1 hy hMy) w)
  · have hMy' : 3 ^ (planarPartCube ω y').scale ≤ M :=
      hM.elim (fun h' => (Nat.pow_le_pow_right (by norm_num) h).trans h') id
    rw [abs_sub_comm]
    exact (abs_coarseAnchor_sub_le hP (fun i => by rw [abs_sub_comm]; exact hnear i) h w).trans
      (edgeVariationIn_mono (ninefold_subset_supBox (planarPartCube_spec hP y').1 hy' hMy') w)

/-- The summand of the term (3.15)-(i) of Dario: the change of the coarse gradient
`∇_j[w]_𝒫(y)` when the partition of `ω₀` is replaced by that of `ω₁`. -/
noncomputable def partitionChange (ω₀ ω₁ : Configuration 2) (w : Vertex 2 → ℝ) (j : Fin 2)
    (y : Vertex 2) : ℝ :=
  (w (planarCoarseAnchor ω₁ (y + LatticeProb.unit j)) - w (planarCoarseAnchor ω₁ y)) -
    (w (planarCoarseAnchor ω₀ (y + LatticeProb.unit j)) - w (planarCoarseAnchor ω₀ y))

/-- **The change of partition is local** (the form of Lemma 3.5 used in Step 1): inside the box
`|z - x|_∞ < ρ` the partition cubes of `ω₀` and `ω₁` have side at most `M`, and outside it the
anchors of `ω₀` and `ω₁` agree. -/
def ResampleLocal (ρ M : ℕ) (ω₀ ω₁ : Configuration 2) (x : Vertex 2) : Prop :=
  ∀ z : Vertex 2, ((∀ i, |z i - x i| < (ρ : ℤ)) →
      3 ^ (planarPartCube ω₀ z).scale ≤ M ∧ 3 ^ (planarPartCube ω₁ z).scale ≤ M) ∧
    (¬ (∀ i, |z i - x i| < (ρ : ℤ)) → planarCoarseAnchor ω₁ z = planarCoarseAnchor ω₀ z)

/-- Lemma 3.5 (`ResamplePartitionBound C₀ C`) gives the locality with `ρ = C₀ s₀` and `M = C s₀`,
`s₀` the side of the partition cube of `ω₀` at the endpoint `x` of `e`. -/
theorem resampleLocal_of_bound {C₀ C : ℕ} (hres : ResamplePartitionBound C₀ C) {e : Bond 2}
    {ω₀ ω₁ : Configuration 2} (hagree : ∀ b, b ≠ e → ω₁ b = ω₀ b)
    (hP₀ : PlanarPartitionEvent ω₀) (hP₁ : PlanarPartitionEvent ω₁) {x : Vertex 2}
    (hx : x ∈ e.1) :
    ResampleLocal (C₀ * 3 ^ (planarPartCube ω₀ x).scale) (C * 3 ^ (planarPartCube ω₀ x).scale)
      ω₀ ω₁ x := by
  intro z
  have hiff : (∀ i, |z i - x i| < ((C₀ * 3 ^ (planarPartCube ω₀ x).scale : ℕ) : ℤ)) ↔
      InResampleBall C₀ ω₀ x z := by
    unfold InResampleBall
    push_cast
    exact Iff.rfl
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · exact ⟨(hres e ω₀ ω₀ (fun _ _ => rfl) hP₀ hP₀ x hx z).1 (hiff.1 hz),
      (hres e ω₀ ω₁ hagree hP₀ hP₁ x hx z).1 (hiff.1 hz)⟩
  · exact ((hres e ω₀ ω₁ hagree hP₀ hP₁ x hx z).2 fun h => hz (hiff.2 h)).2

section Resample

variable {ρ M : ℕ} {ω₀ ω₁ : Configuration 2} {x : Vertex 2} (hloc : ResampleLocal ρ M ω₀ ω₁ x)
include hloc

/-- Away from the box of the locality the change of partition does not change the coarse
gradient. -/
theorem partitionChange_eq_zero (w : Vertex 2 → ℝ) (j : Fin 2) {y : Vertex 2}
    (hy : ¬ (∀ i, |y i - x i| < (ρ : ℤ)))
    (hy' : ¬ (∀ i, |(y + LatticeProb.unit j) i - x i| < (ρ : ℤ))) :
    partitionChange ω₀ ω₁ w j y = 0 := by
  have h1 := (hloc y).2 hy
  have h2 := (hloc (y + LatticeProb.unit j)).2 hy'
  simp only [partitionChange, h1, h2, sub_self]

/-- **Step 1, the summand**: near the box of the locality the change of the coarse gradient is at
most the total variations of `w` over the open edges of `ω₀` and of `ω₁` in the box of radius
`(ρ + 1) + 5M` around `x`. -/
theorem abs_partitionChange_le (hP₀ : PlanarPartitionEvent ω₀) (hP₁ : PlanarPartitionEvent ω₁)
    (w : Vertex 2 → ℝ) (j : Fin 2) {y : Vertex 2}
    (hy : (∀ i, |y i - x i| < (ρ : ℤ)) ∨ (∀ i, |(y + LatticeProb.unit j) i - x i| < (ρ : ℤ))) :
    |partitionChange ω₀ ω₁ w j y| ≤
      edgeVariationIn ω₀ (supBox x ((ρ + 1) + 5 * M)) w +
        edgeVariationIn ω₁ (supBox x ((ρ + 1) + 5 * M)) w := by
  have hnear : ∀ i, |y i - (y + LatticeProb.unit j) i| ≤ 1 := fun i => (abs_sub_add_unit_le y j i).1
  have hnear' : ∀ i, |(y + LatticeProb.unit j) i - y i| ≤ 1 := fun i =>
    (abs_sub_add_unit_le y j i).2
  -- both points lie within `ρ + 1` of `x`
  have hL : (∀ i, |y i - x i| ≤ ((ρ + 1 : ℕ) : ℤ)) ∧
      (∀ i, |(y + LatticeProb.unit j) i - x i| ≤ ((ρ + 1 : ℕ) : ℤ)) := by
    push_cast
    rcases hy with hb | hb
    · refine ⟨fun i => ?_, fun i => ?_⟩
      · have := hb i
        linarith
      · have t := abs_sub_le ((y + LatticeProb.unit j) i) (y i) (x i)
        have h2 := Int.add_one_le_iff.mpr (hb i)
        have := hnear' i
        linarith
    · refine ⟨fun i => ?_, fun i => ?_⟩
      · have t := abs_sub_le (y i) ((y + LatticeProb.unit j) i) (x i)
        have h2 := Int.add_one_le_iff.mpr (hb i)
        have := hnear i
        linarith
      · have := hb i
        linarith
  -- one of the two cubes has side at most `M`, for both configurations
  have hM₀ : 3 ^ (planarPartCube ω₀ y).scale ≤ M ∨
      3 ^ (planarPartCube ω₀ (y + LatticeProb.unit j)).scale ≤ M :=
    hy.elim (fun hb => Or.inl ((hloc y).1 hb).1)
      (fun hb => Or.inr ((hloc (y + LatticeProb.unit j)).1 hb).1)
  have hM₁ : 3 ^ (planarPartCube ω₁ y).scale ≤ M ∨
      3 ^ (planarPartCube ω₁ (y + LatticeProb.unit j)).scale ≤ M :=
    hy.elim (fun hb => Or.inl ((hloc y).1 hb).2)
      (fun hb => Or.inr ((hloc (y + LatticeProb.unit j)).1 hb).2)
  have h0 : |w (planarCoarseAnchor ω₀ (y + LatticeProb.unit j)) - w (planarCoarseAnchor ω₀ y)| ≤
      edgeVariationIn ω₀ (supBox x ((ρ + 1) + 5 * M)) w := by
    rw [abs_sub_comm]
    exact abs_coarseAnchor_sub_le_supBox hP₀ hnear hM₀ hL.1 hL.2 w
  have h1 : |w (planarCoarseAnchor ω₁ (y + LatticeProb.unit j)) - w (planarCoarseAnchor ω₁ y)| ≤
      edgeVariationIn ω₁ (supBox x ((ρ + 1) + 5 * M)) w := by
    rw [abs_sub_comm]
    exact abs_coarseAnchor_sub_le_supBox hP₁ hnear hM₁ hL.1 hL.2 w
  exact (abs_sub _ _).trans ((add_le_add h1 h0).trans_eq (add_comm _ _))

end Resample

/-- **Cauchy–Schwarz over a box**: for weights `φ ≥ 0` and a function `g` vanishing off a finite
set `B` and bounded by `V` on it, `(Σ_y φ(y) g(y))² ≤ |B| (Σ_{y ∈ B} φ(y)²) V²`. -/
theorem sq_tsum_mul_le_of_support {φ g : Vertex 2 → ℝ} {B : Finset (Vertex 2)} {V : ℝ}
    (hsupp : ∀ y ∉ B, g y = 0) (hg : ∀ y ∈ B, |g y| ≤ V) :
    (∑' y, φ y * g y) ^ 2 ≤ B.card * (∑ y ∈ B, φ y ^ 2) * V ^ 2 := by
  rw [tsum_eq_sum (s := B) fun y hy => by rw [hsupp y hy, mul_zero]]
  calc (∑ y ∈ B, φ y * g y) ^ 2 ≤ B.card * ∑ y ∈ B, (φ y * g y) ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ B.card * ∑ y ∈ B, φ y ^ 2 * V ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y hy => ?_) (by positivity)
        rw [mul_pow]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact sq_le_sq' (abs_le.mp (hg y hy)).1 (abs_le.mp (hg y hy)).2
    _ = B.card * (∑ y ∈ B, φ y ^ 2) * V ^ 2 := by rw [← Finset.sum_mul, mul_assoc]

/-- **Step 1 of Dario's proof, (3.16) in flip form**: if the change of partition from `ω₀` to `ω₁`
is local around `x` (`ResampleLocal ρ M`, given by Lemma 3.5 with `ρ = C₀ s₀`, `M = C s₀`), then for
weights `φ`, `|Σ_y φ(y) partitionChange(y)|² ≤ |B| (Σ_{y ∈ B} φ(y)²) (V₀ + V₁)²`, with `B` the box
of radius `ρ` around `x` and `V_b` the total variation of `w` over the open edges of `ω_b` in the
box of radius `(ρ + 1) + 5M`. -/
theorem sq_tsum_partitionChange_le {ρ M : ℕ} {ω₀ ω₁ : Configuration 2} {x : Vertex 2}
    (hloc : ResampleLocal ρ M ω₀ ω₁ x) (hP₀ : PlanarPartitionEvent ω₀)
    (hP₁ : PlanarPartitionEvent ω₁) (φ w : Vertex 2 → ℝ) (j : Fin 2) :
    (∑' y, φ y * partitionChange ω₀ ω₁ w j y) ^ 2 ≤
      (supBox x ρ).card * (∑ y ∈ supBox x ρ, φ y ^ 2) *
        (edgeVariationIn ω₀ (supBox x ((ρ + 1) + 5 * M)) w +
          edgeVariationIn ω₁ (supBox x ((ρ + 1) + 5 * M)) w) ^ 2 := by
  refine sq_tsum_mul_le_of_support (fun y hy => ?_) (fun y _ => ?_)
  · refine partitionChange_eq_zero hloc w j (fun hb => hy ?_) (fun hb => hy ?_)
    · rw [mem_supBox]
      exact fun i => (hb i).le
    · rw [mem_supBox]
      intro i
      have t := abs_sub_le (y i) ((y + LatticeProb.unit j) i) (x i)
      have h1 := (abs_sub_add_unit_le y j i).1
      have h2 := Int.add_one_le_iff.mpr (hb i)
      linarith
  · by_cases hb : (∀ i, |y i - x i| < (ρ : ℤ)) ∨
        (∀ i, |(y + LatticeProb.unit j) i - x i| < (ρ : ℤ))
    · exact abs_partitionChange_le hloc hP₀ hP₁ w j hb
    · rw [not_or] at hb
      rw [partitionChange_eq_zero hloc w j hb.1 hb.2, abs_zero]
      exact add_nonneg (edgeVariationIn_nonneg _ _ _) (edgeVariationIn_nonneg _ _ _)

end Rigidity.Corrector
