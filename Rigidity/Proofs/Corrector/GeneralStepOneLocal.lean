import Rigidity.Proofs.Corrector.GeneralResamplePartition
import Rigidity.Proofs.Corrector.GeneralCaseFiniteEnergy
import Rigidity.Proofs.Corrector.GeneralCaseHeatField
import Rigidity.Proofs.Poincare.GeneralBoxMaximal

/-!
# Step 1 of the proof of Lemma 3.3 of Dario on `ℤᵈ`: the change of partition is local

The term (3.15)-(i) of Dario is `Φ_{r²} * (∇[w]_{𝒫} - ∇[w]_{𝒫^e})(0)` for one function `w`, the
coarsenings being taken with the partitions into good cubes of two configurations `ω₀, ω₁` equal
off a bond `e`. Its summand at `y` in direction `j` is `partitionChange ω₀ ω₁ w j y`. Step 1 uses
Lemma 3.5 through `ResampleLocal ρ M ω₀ ω₁ x`: inside the box `|· - x|_∞ < ρ` the partition cubes
of both configurations have side at most `M`, and outside it their anchors agree. Lemma 3.5
(`ResamplePartitionBound C₀ C`) gives it with `ρ = C₀ s₀`, `M = C s₀`, `s₀` the side of the
partition cube of `ω₀` at the endpoint `x` of `e` (`resampleLocal_of_bound`). Then

* `partitionChange_eq_zero`: the summand vanishes unless `y` or `y + e_j` lies in the box;
* `abs_partitionChange_le`: otherwise it is at most the sum of the total variations of `w` over
  the open edges of `ω₀` and of `ω₁` in the box of radius `(ρ + 1) + 3M` around `x`, since the
  anchors of neighbouring partition cubes are joined inside the union of the two cubes (Armstrong
  and Dario, Corollary 2.10) and neighbouring partition cubes differ by at most one scale
  (`abs_partitionAnchor_sub_le_supBox`);
* `sq_tsum_partitionChange_le`: `|Σ_y Φ(y) partitionChange(y)|² ≤ |B| (Σ_{y ∈ B} Φ(y)²) (V₀ + V₁)²`
  with `B` the box of radius `ρ` around `x`, by the Cauchy–Schwarz inequality over `B`.

This is (3.16) of Dario in the flip form, with the Cauchy–Schwarz inequality over the ball in place
of the supremum of the heat kernel over the ball; it is the planar argument of
`Rigidity.Corrector.sq_tsum_partitionChange_le` for the partition into good cubes of `ℤᵈ`.
-/

namespace Rigidity.Corrector.GeneralDim

open LatticeProb.Percolation Rigidity.Percolation Rigidity.Poincare.GeneralDim
open scoped Classical

variable {d : ℕ}

theorem supBox_eq_boxFinset (x : Vertex d) (r : ℕ) : supBox x r = LatticeProb.boxFinset x r :=
  rfl

/-- The total variation over open edges grows with the region. -/
theorem edgeVariationIn_mono {ω : Configuration d} {S T : Finset (Vertex d)} (h : S ⊆ T)
    (w : Vertex d → ℝ) : edgeVariationIn ω S w ≤ edgeVariationIn ω T w := by
  set f : Vertex d → Vertex d → ℝ := fun a b =>
    if (openGraph ω).Adj a b then |w a - w b| else 0 with hf
  have hnn : ∀ a b, 0 ≤ f a b := fun a b => by
    simp only [hf]
    split_ifs <;> positivity
  show ∑ a ∈ S, ∑ b ∈ S, f a b ≤ ∑ a ∈ T, ∑ b ∈ T, f a b
  calc ∑ a ∈ S, ∑ b ∈ S, f a b ≤ ∑ a ∈ S, ∑ b ∈ T, f a b :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum_of_subset_of_nonneg h fun b _ _ => hnn a b
    _ ≤ ∑ a ∈ T, ∑ b ∈ T, f a b :=
        Finset.sum_le_sum_of_subset_of_nonneg h fun a _ _ => Finset.sum_nonneg fun b _ => hnn a b

/-- **Coarse gradient in a box**: across `y` and `y + e_j` within `L` of `x`, one of whose partition
cubes has side at most `M`, the coarsening of `w` changes by at most the total variation of `w`
over the open edges of the box of radius `L + 3M` around `x`. -/
theorem abs_partitionAnchor_sub_le_supBox (hd : 0 < d) {ω : Configuration d}
    (hP : PartitionEvent ω) {x y : Vertex d} {j : Fin d} {L M : ℕ}
    (hM : 3 ^ (partitionCube ω y).scale ≤ M ∨
      3 ^ (partitionCube ω (y + LatticeProb.unit j)).scale ≤ M)
    (hy : ∀ i, |y i - x i| ≤ L) (w : Vertex d → ℝ) :
    |w (partitionAnchor ω y) - w (partitionAnchor ω (y + LatticeProb.unit j))| ≤
      edgeVariationIn ω (supBox x (L + 3 * M)) w := by
  obtain ⟨h1, h2⟩ := partitionCube_scales_close hP fun i => (abs_sub_add_unit_le y j i).1
  have h3 : ∀ {a b : ℕ}, a ≤ b + 1 → 3 ^ b ≤ M → 3 ^ a ≤ 3 * M := fun {a b} hab hb =>
    calc 3 ^ a ≤ 3 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) hab
      _ = 3 * 3 ^ b := by ring
      _ ≤ 3 * M := Nat.mul_le_mul_left 3 hb
  have hM3 : 3 ^ (partitionCube ω y).scale ≤ 3 * M ∧
      3 ^ (partitionCube ω (y + LatticeProb.unit j)).scale ≤ 3 * M := by
    rcases hM with hb | hb
    · exact ⟨hb.trans (by omega), h3 h2 hb⟩
    · exact ⟨h3 h1 hb, hb.trans (by omega)⟩
  have hadj : (nearestNeighborGraph d).Adj y (y + LatticeProb.unit j) := ⟨j, Or.inl rfl⟩
  refine (abs_partitionAnchor_sub_le hd hP hadj hM3.1 hM3.2 w).trans
    (edgeVariationIn_mono (fun v hv => ?_) w)
  rw [← supBox_eq_boxFinset, mem_supBox] at hv
  rw [mem_supBox]
  intro i
  have t := abs_sub_le (v i) (y i) (x i)
  have := hv i
  have := hy i
  push_cast at *
  linarith

/-- The summand of the term (3.15)-(i) of Dario: the change of the coarse gradient
`∇_j[w]_𝒫(y)` when the partition of `ω₀` is replaced by that of `ω₁`. -/
noncomputable def partitionChange (ω₀ ω₁ : Configuration d) (w : Vertex d → ℝ) (j : Fin d)
    (y : Vertex d) : ℝ :=
  (w (guardAnchor ω₁ (y + LatticeProb.unit j)) - w (guardAnchor ω₁ y)) -
    (w (guardAnchor ω₀ (y + LatticeProb.unit j)) - w (guardAnchor ω₀ y))

/-- **The change of partition is local** (the form of Lemma 3.5 used in Step 1): inside the box
`|z - x|_∞ < ρ` the partition cubes of `ω₀` and `ω₁` have side at most `M`, and outside it the
anchors of `ω₀` and `ω₁` agree. -/
def ResampleLocal (ρ M : ℕ) (ω₀ ω₁ : Configuration d) (x : Vertex d) : Prop :=
  ∀ z : Vertex d, ((∀ i, |z i - x i| < (ρ : ℤ)) →
      3 ^ (partitionCube ω₀ z).scale ≤ M ∧ 3 ^ (partitionCube ω₁ z).scale ≤ M) ∧
    (¬ (∀ i, |z i - x i| < (ρ : ℤ)) → guardAnchor ω₁ z = guardAnchor ω₀ z)

/-- Lemma 3.5 (`ResamplePartitionBound C₀ C`) gives the locality with `ρ = C₀ s₀` and `M = C s₀`,
`s₀` the side of the partition cube of `ω₀` at the endpoint `x` of `e`. -/
theorem resampleLocal_of_bound {C₀ C : ℕ} (hres : ResamplePartitionBound (d := d) C₀ C)
    {e : Bond d} {ω₀ ω₁ : Configuration d} (hagree : ∀ b, b ≠ e → ω₁ b = ω₀ b)
    (hP₀ : PartitionEvent ω₀) (hP₁ : PartitionEvent ω₁) {x : Vertex d} (hx : x ∈ e.1) :
    ResampleLocal (C₀ * 3 ^ (partitionCube ω₀ x).scale) (C * 3 ^ (partitionCube ω₀ x).scale)
      ω₀ ω₁ x := by
  intro z
  have hiff : (∀ i, |z i - x i| < ((C₀ * 3 ^ (partitionCube ω₀ x).scale : ℕ) : ℤ)) ↔
      InResampleBall C₀ ω₀ x z := by
    unfold InResampleBall
    push_cast
    exact Iff.rfl
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · exact ⟨(hres e ω₀ ω₀ (fun _ _ => rfl) hP₀ hP₀ x hx z).1 (hiff.1 hz),
      (hres e ω₀ ω₁ hagree hP₀ hP₁ x hx z).1 (hiff.1 hz)⟩
  · have h := ((hres e ω₀ ω₁ hagree hP₀ hP₁ x hx z).2 fun h => hz (hiff.2 h)).2
    rw [guardAnchor_of_event hP₀, guardAnchor_of_event hP₁, h]

section Resample

variable {ρ M : ℕ} {ω₀ ω₁ : Configuration d} {x : Vertex d} (hloc : ResampleLocal ρ M ω₀ ω₁ x)
include hloc

/-- Away from the box of the locality the change of partition does not change the coarse
gradient. -/
theorem partitionChange_eq_zero (w : Vertex d → ℝ) (j : Fin d) {y : Vertex d}
    (hy : ¬ (∀ i, |y i - x i| < (ρ : ℤ)))
    (hy' : ¬ (∀ i, |(y + LatticeProb.unit j) i - x i| < (ρ : ℤ))) :
    partitionChange ω₀ ω₁ w j y = 0 := by
  have h1 := (hloc y).2 hy
  have h2 := (hloc (y + LatticeProb.unit j)).2 hy'
  simp only [partitionChange, h1, h2, sub_self]

/-- **Step 1, the summand**: near the box of the locality the change of the coarse gradient is at
most the total variations of `w` over the open edges of `ω₀` and of `ω₁` in the box of radius
`(ρ + 1) + 3M` around `x`. -/
theorem abs_partitionChange_le (hd : 0 < d) (hP₀ : PartitionEvent ω₀) (hP₁ : PartitionEvent ω₁)
    (w : Vertex d → ℝ) (j : Fin d) {y : Vertex d}
    (hy : (∀ i, |y i - x i| < (ρ : ℤ)) ∨ (∀ i, |(y + LatticeProb.unit j) i - x i| < (ρ : ℤ))) :
    |partitionChange ω₀ ω₁ w j y| ≤
      edgeVariationIn ω₀ (supBox x ((ρ + 1) + 3 * M)) w +
        edgeVariationIn ω₁ (supBox x ((ρ + 1) + 3 * M)) w := by
  have hL : ∀ i, |y i - x i| ≤ ((ρ + 1 : ℕ) : ℤ) := by
    push_cast
    rcases hy with hb | hb
    · intro i
      have := hb i
      linarith
    · intro i
      have t := abs_sub_le (y i) ((y + LatticeProb.unit j) i) (x i)
      have h2 := Int.add_one_le_iff.mpr (hb i)
      have := (abs_sub_add_unit_le y j i).1
      linarith
  have hM₀ : 3 ^ (partitionCube ω₀ y).scale ≤ M ∨
      3 ^ (partitionCube ω₀ (y + LatticeProb.unit j)).scale ≤ M :=
    hy.elim (fun hb => Or.inl ((hloc y).1 hb).1)
      (fun hb => Or.inr ((hloc (y + LatticeProb.unit j)).1 hb).1)
  have hM₁ : 3 ^ (partitionCube ω₁ y).scale ≤ M ∨
      3 ^ (partitionCube ω₁ (y + LatticeProb.unit j)).scale ≤ M :=
    hy.elim (fun hb => Or.inl ((hloc y).1 hb).2)
      (fun hb => Or.inr ((hloc (y + LatticeProb.unit j)).1 hb).2)
  have h0 : |w (guardAnchor ω₀ (y + LatticeProb.unit j)) - w (guardAnchor ω₀ y)| ≤
      edgeVariationIn ω₀ (supBox x ((ρ + 1) + 3 * M)) w := by
    rw [abs_sub_comm, guardAnchor_of_event hP₀, guardAnchor_of_event hP₀]
    exact abs_partitionAnchor_sub_le_supBox hd hP₀ hM₀ hL w
  have h1 : |w (guardAnchor ω₁ (y + LatticeProb.unit j)) - w (guardAnchor ω₁ y)| ≤
      edgeVariationIn ω₁ (supBox x ((ρ + 1) + 3 * M)) w := by
    rw [abs_sub_comm, guardAnchor_of_event hP₁, guardAnchor_of_event hP₁]
    exact abs_partitionAnchor_sub_le_supBox hd hP₁ hM₁ hL w
  exact (abs_sub _ _).trans ((add_le_add h1 h0).trans_eq (add_comm _ _))

end Resample

/-- **Cauchy–Schwarz over a box**: for weights `φ` and a function `g` vanishing off a finite set
`B` and bounded by `V` on it, `(Σ_y φ(y) g(y))² ≤ |B| (Σ_{y ∈ B} φ(y)²) V²`. -/
theorem sq_tsum_mul_le_of_support {φ g : Vertex d → ℝ} {B : Finset (Vertex d)} {V : ℝ}
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

/-- **Step 1 of Dario's proof, (3.16) in flip form, on `ℤᵈ`**: if the change of partition from
`ω₀` to `ω₁` is local around `x` (`ResampleLocal ρ M`, given by Lemma 3.5 with `ρ = C₀ s₀`,
`M = C s₀`), then for weights `φ`, `|Σ_y φ(y) partitionChange(y)|² ≤ |B| (Σ_{y ∈ B} φ(y)²) (V₀ + V₁)²`,
with `B` the box of radius `ρ` around `x` and `V_b` the total variation of `w` over the open edges of
`ω_b` in the box of radius `(ρ + 1) + 3M`. -/
theorem sq_tsum_partitionChange_le (hd : 0 < d) {ρ M : ℕ} {ω₀ ω₁ : Configuration d}
    {x : Vertex d} (hloc : ResampleLocal ρ M ω₀ ω₁ x) (hP₀ : PartitionEvent ω₀)
    (hP₁ : PartitionEvent ω₁) (φ w : Vertex d → ℝ) (j : Fin d) :
    (∑' y, φ y * partitionChange ω₀ ω₁ w j y) ^ 2 ≤
      (supBox x ρ).card * (∑ y ∈ supBox x ρ, φ y ^ 2) *
        (edgeVariationIn ω₀ (supBox x ((ρ + 1) + 3 * M)) w +
          edgeVariationIn ω₁ (supBox x ((ρ + 1) + 3 * M)) w) ^ 2 := by
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
    · exact abs_partitionChange_le hloc hd hP₀ hP₁ w j hb
    · rw [not_or] at hb
      rw [partitionChange_eq_zero hloc w j hb.1 hb.2, abs_zero]
      exact add_nonneg (edgeVariationIn_nonneg _ _ _) (edgeVariationIn_nonneg _ _ _)

end Rigidity.Corrector.GeneralDim
