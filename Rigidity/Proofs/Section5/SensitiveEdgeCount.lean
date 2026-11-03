import Rigidity.Steps.Section5.LevelSetDensity
import Rigidity.Steps.Section5.FastDecayDichotomy
import Rigidity.Steps.Section5.LongPathRenormalized

/-!
# Proposition 5.11: counting the sensitive edges

The counting lemmas of `step:5.11-count` (Proposition 5.11, corrected draft L2423-2429), consumed
by its `∀ᶠ` form `sensitiveEdgeCountEventuallyStep`
(`Rigidity/Steps/Section5/LevelSetDensityEventual.lean`; the draft Proposition 5.11 has a lower
limit, [C29]). Each site `x₀` of `Q_L` within `ℓ¹`-distance `C₀` of an oriented edge `(a, b)` of
the cluster with `∇u ≠ 0` and `∇ℓ ≠ 0` is charged to that edge through the pair
`(a, a - x₀) ∈ ℤ² × Q_N`, `N = ⌈C₀⌉`, which determines `x₀`; so at most `|Q_N|` sites are charged
to an edge (`ncard_cube_inter_sensitiveSites_le`). The charged edges lie in `B_r` once
`2L + N + 1 < r`, and `r = 2^k ∈ (4L, 8L]` gives `|B_{2^k}| = π 4^k ≤ 64 π L²`.
-/

open Filter LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

variable {ω : Configuration 2}

/-- The oriented edges of the ball `B_r` with `∇u ≠ 0` and `∇ℓ ≠ 0` form a finite set. -/
theorem activeEdges_finite (C : OpenComponent ω) (u ℓ : C → ℝ) (r : ℝ) :
    (activeEdges C u ℓ r).Finite := by
  have hB : {x : Vertex 2 | eucl x < r}.Finite := by
    refine (cube_finite ⌈r⌉₊).subset fun x hx i => ?_
    have h : |(x i : ℝ)| ≤ ((⌈r⌉₊ : ℤ) : ℝ) := by
      have := abs_coord_le_eucl x i
      push_cast
      exact this.trans ((le_of_lt hx).trans (Nat.le_ceil r))
    exact_mod_cast h
  refine ((hB.prod hB).preimage
    (Subtype.val_injective.prodMap Subtype.val_injective).injOn).subset ?_
  rintro e ⟨-, h1, h2, -⟩
  exact ⟨h1, h2⟩

/-- Counting: a site of `Q_L` within `ℓ¹`-distance `C₀ ≤ N` of a sensitive edge is charged to an
oriented edge of `B_r` (for `2L + N + 1 < r`) with `∇u ≠ 0` and `∇ℓ ≠ 0`, and each such edge is
charged by at most `|Q_N|` sites. -/
theorem ncard_cube_inter_sensitiveSites_le (C : OpenComponent ω) (u ℓ : C → ℝ) {C₀ r : ℝ}
    {L N : ℕ} (hN : C₀ ≤ N) (hr : 2 * (L : ℝ) + N + 1 < r) :
    (cube L ∩ sensitiveSites C u ℓ C₀).ncard ≤ (activeEdges C u ℓ r).ncard * (cube N).ncard := by
  classical
  set S := sensitiveSites C u ℓ C₀
  set A := activeEdges C u ℓ r
  let tail : Vertex 2 → Vertex 2 := fun x₀ =>
    if h : x₀ ∈ S then (Classical.choose h).val else 0
  have key : ∀ x₀ ∈ cube L ∩ S,
      tail x₀ ∈ (fun e : C × C => e.1.val) '' A ∧ tail x₀ - x₀ ∈ cube N := by
    rintro x₀ ⟨hx, hs⟩
    have ht : tail x₀ = (Classical.choose hs).val := dif_pos hs
    obtain ⟨b, hadj, hl1, hℓ, hu⟩ := Classical.choose_spec hs
    set a := Classical.choose hs
    rw [ht]
    have hx0 : |(x₀ 0 : ℝ)| ≤ L := by exact_mod_cast hx 0
    have hx1 : |(x₀ 1 : ℝ)| ≤ L := by exact_mod_cast hx 1
    have hl1' := hl1
    simp only [l1, Fin.sum_univ_two, Pi.sub_apply, Int.cast_sub] at hl1'
    have hab : |(a.val 0 : ℝ) - b.val 0| + |(a.val 1 : ℝ) - b.val 1| = 1 := by
      exact_mod_cast abs_sub_add_abs_sub_eq_one_of_adj hadj
    have ea := eucl_le_l1 a.val
    have eb := eucl_le_l1 b.val
    simp only [l1, Fin.sum_univ_two] at ea eb
    have t0 := abs_sub_abs_le_abs_sub (a.val 0 : ℝ) (x₀ 0)
    have t1 := abs_sub_abs_le_abs_sub (a.val 1 : ℝ) (x₀ 1)
    have s0 := abs_sub_abs_le_abs_sub (b.val 0 : ℝ) (a.val 0)
    have s1 := abs_sub_abs_le_abs_sub (b.val 1 : ℝ) (a.val 1)
    rw [abs_sub_comm (b.val 0 : ℝ)] at s0
    rw [abs_sub_comm (b.val 1 : ℝ)] at s1
    refine ⟨⟨(a, b), ⟨hadj, by linarith, by linarith, hu, hℓ⟩, rfl⟩, fun i => ?_⟩
    have hi : |(((a.val - x₀) i : ℤ) : ℝ)| ≤ N := by
      refine le_trans ?_ (hl1.trans hN)
      exact Finset.single_le_sum (f := fun j => |(((a.val - x₀) j : ℤ) : ℝ)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    exact_mod_cast hi
  calc (cube L ∩ S).ncard
      ≤ (((fun e : C × C => e.1.val) '' A) ×ˢ cube N).ncard := by
        refine Set.ncard_le_ncard_of_injOn (fun x₀ => (tail x₀, tail x₀ - x₀))
          (fun x₀ hx₀ => key x₀ hx₀) ?_
          ((((activeEdges_finite C u ℓ r).image _)).prod (cube_finite N))
        intro x _ y _ hxy
        obtain ⟨h1, h2⟩ := Prod.mk.inj hxy
        calc x = tail x - (tail x - x) := (sub_sub_cancel _ _).symm
          _ = tail y - (tail y - y) := by rw [h2, h1]
          _ = y := sub_sub_cancel _ _
    _ = ((fun e : C × C => e.1.val) '' A).ncard * (cube N).ncard := Set.ncard_prod
    _ ≤ A.ncard * (cube N).ncard :=
        Nat.mul_le_mul_right _ (Set.ncard_image_le (activeEdges_finite C u ℓ r))

end Rigidity.Proofs.Section5
