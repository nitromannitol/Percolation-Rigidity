import Rigidity.Proofs.Percolation.BondShellGeometry

/-!
# Finite bond shells around lattice cubes

Finite bond boxes exhaust all bonds, and their successive differences have polynomial size.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- Bonds incident to a lattice cube. -/
noncomputable def bondBox (d : ℕ) (z : Vertex d) (R : ℕ) : Finset (Bond d) :=
  bondsIncidentTo d (Rigidity.Proofs.S3.cubeFinset z R)

/-- The bonds entering the next layer of a lattice cube. -/
noncomputable def bondShell (d : ℕ) (z : Vertex d) (R n : ℕ) : Finset (Bond d) :=
  bondBox d z (R + n + 1) \ bondBox d z (R + n)

/-- Bond boxes are increasing in their radius. -/
theorem bondBox_mono (d : ℕ) (z : Vertex d) {R T : ℕ} (hRT : R ≤ T) :
    bondBox d z R ⊆ bondBox d z T := by
  intro e he
  obtain ⟨v, hv, hev⟩ := (mem_bondsIncidentTo d _ e).1 he
  apply (mem_bondsIncidentTo d _ e).2
  refine ⟨v, Rigidity.Proofs.S3.mem_cubeFinset.mpr ?_, hev⟩
  have hv' := Rigidity.Proofs.S3.mem_cubeFinset.mp hv
  intro i
  exact (hv' i).trans (by exact_mod_cast hRT)

/-- Every bond belongs to a sufficiently large bond box. -/
theorem exists_mem_bondBox (d : ℕ) (z : Vertex d) (e : Bond d) :
    ∃ R : ℕ, e ∈ bondBox d z R := by
  classical
  obtain ⟨v, w, he, _⟩ := e.property
  let R := ∑ i : Fin d, (v i - z i).natAbs
  refine ⟨R, (mem_bondsIncidentTo d _ e).2 ⟨v, ?_, ?_⟩⟩
  · apply Rigidity.Proofs.S3.mem_cubeFinset.mpr
    intro i
    have h := Finset.single_le_sum (f := fun j : Fin d => (v j - z j).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h' : (v i - z i).natAbs ≤ R := h
    rw [← Int.natCast_natAbs]
    exact_mod_cast h'
  · rw [he]
    exact Sym2.mem_mk_left v w

/-- A bond shell is controlled by the volume of its enclosing cube. -/
theorem card_bondShell_le (d : ℕ) (z : Vertex d) (R n : ℕ) :
    (bondShell d z R n).card ≤ 2 * d * (2 * (R + n + 1) + 1) ^ d := by
  apply card_bonds_incident_cube_le d _ z (R + n + 1)
  intro e he
  have he' : e ∈ bondBox d z (R + n + 1) := (Finset.mem_sdiff.mp he).1
  obtain ⟨v, hv, hev⟩ := (mem_bondsIncidentTo d _ e).1 he'
  exact ⟨v, Rigidity.Proofs.S3.mem_cubeFinset.mp hv, hev⟩

/-- Every bond in a shell has a separating coordinate for the inner cube. -/
theorem bondShell_separated {d : ℕ} (z : Vertex d) (R n : ℕ) (e : Bond d)
    (he : e ∈ bondShell d z R n) :
    ∃ i : Fin d, ∀ x ∈ cubeAt z R, ∀ y ∈ e.val,
      (n : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)| :=
  bond_outside_cube_separated z R n e (Finset.mem_sdiff.mp he).2

end Rigidity.Percolation
