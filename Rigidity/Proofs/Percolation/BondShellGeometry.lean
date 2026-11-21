import Rigidity.Proofs.Percolation.BondCounting

/-!
# Separation of bonds from lattice cubes

A bond outside an enlarged cube is separated from the original cube in a common coordinate.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- A bond outside an enlarged cube is coordinate-separated from the inner cube. -/
theorem bond_outside_cube_separated {d : ℕ} (z : Vertex d) (R n : ℕ) (e : Bond d)
    (he : e ∉ bondsIncidentTo d (Rigidity.Proofs.S3.cubeFinset z (R + n))) :
    ∃ i : Fin d, ∀ x ∈ cubeAt z R, ∀ y ∈ e.val,
      (n : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)| := by
  obtain ⟨v, w, hevw, hdist⟩ := e.property
  have hv : v ∈ e.val := by rw [hevw]; exact Sym2.mem_mk_left v w
  have hvout : v ∉ cubeAt z (R + n) := by
    intro hv'
    apply he
    exact (mem_bondsIncidentTo d _ e).2 ⟨v, Rigidity.Proofs.S3.mem_cubeFinset.mpr hv', hv⟩
  change ¬ ∀ i, |v i - z i| ≤ ((R + n : ℕ) : ℤ) at hvout
  obtain ⟨i, hi⟩ := not_forall.mp hvout
  have hfar : ((R + n : ℕ) : ℤ) < |v i - z i| := lt_of_not_ge hi
  have hadj : (nearestNeighborGraph d).Adj v w := lattice_adj_iff_l1Dist.mpr hdist
  have hnear : |w i - v i| ≤ 1 := Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj hadj i
  refine ⟨i, fun x hx y hy => ?_⟩
  have hxy : |y i - v i| ≤ 1 := by
    rw [hevw, Sym2.mem_iff] at hy
    rcases hy with rfl | rfl
    · simp
    · exact hnear
  have hxin : |x i - z i| ≤ (R : ℤ) := hx i
  have ht1 := abs_sub_le (v i) (y i) (z i)
  have ht2 := abs_sub_le (y i) (x i) (z i)
  rw [abs_sub_comm (v i) (y i)] at ht1
  rw [abs_sub_comm (y i) (x i)] at ht2
  have h' : (n : ℤ) ≤ |x i - y i| := by
    simp only [Nat.cast_add] at hfar
    omega
  exact_mod_cast h'

end Rigidity.Percolation
