import Rigidity.Proofs.Partition.LambdaMinimalScale

/-!
# The quantity `Λ_t` of Armstrong and Dario

For a finite set `U`, Armstrong and Dario (display before Lemma 2.2) set
`Λ_t(U) = |U|⁻¹ ∑_{x ∈ cl(U)} size(𝒫(x))^t`, where the closure `cl(U)` is the union of the
partition cubes of the points of `U`. Each partition cube `Q ⊆ cl(U)` contains a point of `U` and
contributes `size(Q)^{d + t}`, so `∑_{x ∈ cl(U)} size^t ≤ ∑_{z ∈ U} size(𝒫(z))^{t + d}`. With the
bound of `exists_scale_sum_pow_partitionCube_le` for `τ = t + d` this gives Proposition 2.4 (the
first bound) in the form of the source: `Λ_t(Q_m) ≤ C` above a random scale with a
stretched-exponential moment.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- A sum of nonnegative terms over a finite union is at most the sum of the sums over the
pieces. -/
theorem sum_biUnion_le_sum_of_nonneg {α β : Type*} [DecidableEq β] (s : Finset α)
    (g : α → Finset β) (f : β → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion g, f x ≤ ∑ a ∈ s, ∑ x ∈ g a, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h := Finset.sum_union_inter (s₁ := g a) (s₂ := s.biUnion g) (f := f)
    have hinter : 0 ≤ ∑ x ∈ g a ∩ s.biUnion g, f x := Finset.sum_nonneg fun x _ => hf x
    linarith

open scoped Classical in
/-- The closure `cl(U)` of a finite set of vertices: the union of the partition cubes of its
points. -/
noncomputable def partitionClosure (ω : Configuration d) (U : Finset (Vertex d)) :
    Finset (Vertex d) :=
  U.biUnion fun z => (partitionCube ω z).toIntegerCube.vertices

theorem mem_partitionClosure {ω : Configuration d} {U : Finset (Vertex d)} {x : Vertex d} :
    x ∈ partitionClosure ω U ↔ ∃ z ∈ U, x ∈ (partitionCube ω z).vertices := by
  classical
  unfold partitionClosure
  simp only [Finset.mem_biUnion, TriadicCube.mem_toIntegerCube_vertices]

/-- `∑_{x ∈ cl(U)} 3^{t n(x)} ≤ ∑_{z ∈ U} 3^{(t + d) n(z)}`, `n(x)` the scale of the partition
cube of `x`. -/
theorem sum_partitionClosure_le {ω : Configuration d} (hP : PartitionEvent ω)
    (U : Finset (Vertex d)) (t : ℕ) :
    ∑ x ∈ partitionClosure ω U, (3 : ℝ) ^ (t * (partitionCube ω x).scale) ≤
      ∑ z ∈ U, (3 : ℝ) ^ ((t + d) * (partitionCube ω z).scale) := by
  classical
  unfold partitionClosure
  refine (sum_biUnion_le_sum_of_nonneg _ _ _ fun _ => by positivity).trans
    (Finset.sum_le_sum fun z _ => le_of_eq ?_)
  have hconst : ∀ x ∈ (partitionCube ω z).toIntegerCube.vertices,
      (3 : ℝ) ^ (t * (partitionCube ω x).scale) = 3 ^ (t * (partitionCube ω z).scale) := by
    intro x hx
    rw [partitionCube_eq_of_mem hP ((TriadicCube.mem_toIntegerCube_vertices _ x).1 hx)]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, IntegerCube.card_vertices]
  change ((((3 ^ (partitionCube ω z).scale) ^ d : ℕ)) : ℝ) * _ = _
  push_cast
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

/-- **Armstrong and Dario, Proposition 2.4, the first bound**, in the form of the source: for
supercritical bond percolation on `ℤᵈ`, `d ≥ 2`, and every `t ∈ ℕ`, there are `C`, `s > 0` and a
measurable random scale `M` with a stretched-exponential moment of order `s` such that, almost
surely, `Λ_t(Q_m) = 3^{-d m} ∑_{x ∈ cl(Q_m)} 3^{t n(x)} ≤ C` whenever `M < 3ᵐ`. -/
theorem exists_scale_lambda_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (t : ℕ) :
    ∃ C s : ℝ, 0 < s ∧ ∃ M : Configuration d → ℝ≥0∞, Measurable M ∧
      (∃ θ : ℝ, 0 < θ ∧
        Integrable (fun ω => Real.exp (((M ω).toReal / θ) ^ s)) (latticeBondLaw d p) ∧
        (∫ ω, Real.exp (((M ω).toReal / θ) ^ s) ∂(latticeBondLaw d p)) ≤ 2) ∧
      ∀ᵐ ω ∂(latticeBondLaw d p), ∀ m : ℕ, M ω < 3 ^ m →
        (∑ x ∈ partitionClosure ω (originCube d m).toIntegerCube.vertices,
          (3 : ℝ) ^ (t * (partitionCube ω x).scale)) / 3 ^ (d * m) ≤ C := by
  obtain ⟨C, s, hs, M, hM, hmom, hae⟩ := exists_scale_sum_pow_partitionCube_le hd hpc (t + d)
  refine ⟨C, s, hs, M, hM, hmom, ?_⟩
  filter_upwards [hae, ae_partitionEvent hd hpc] with ω hω hP m hm
  rw [div_le_iff₀ (by positivity)]
  exact (sum_partitionClosure_le hP _ t).trans (hω m hm)

end Rigidity.Percolation
