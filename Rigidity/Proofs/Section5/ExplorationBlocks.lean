import Rigidity.Steps.Section5.LargeGradientSensitive

/-! # Step 1 of Lemma 5.27: the blocks of `𝒢` and the holes of its complement

Proofs of `ExplorationBlockStep` and `ExplorationHolesStep` (step:5.27-graph, L2485-2491 of the
corrected draft).

* The points of `𝒢` are endpoints of paths in `L_{u(x₀)}` and the edges of `𝒢` are edges of
  `𝒞_∞`, so a block of `𝒢` lies in `L_{u(x₀)}` and is biconnected in `𝒞_∞`.
* Along a path defining `𝒢`, `ℓ` increases from `x₁` on, so `ℓ ≥ ℓ(x₁) > ℓ(x₀)` on `𝒢`. If `ℓ`
  is smaller than `ℓ(x₀)` on `𝒞_∞ ∩ (Q_r ∪ L_-)`, then `Q_r ∪ L_-` avoids every `S ⊆ 𝒢`; it is
  connected in `ℤ²` (a vertical segment of `Q_r` leads to the axis, the axis to `L_-`) and
  infinite, so a finite connected component of `ℤ² \ S` does not meet `Q_r ⊇ supp f`. -/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

section Exploration

variable {ω : Configuration 2} (C : OpenComponent ω)

/-- A point of `𝒢` lies in the level set `L_{u(x₀)}`. -/
theorem explorationSet_subset_levelSet (u ℓ : C → ℝ) (x₀ x₁ : C) :
    explorationSet C u ℓ x₀ x₁ ⊆ levelSet u (u x₀) := by
  rintro y ⟨n, -, γ, -, hu, -, -, hy, -⟩
  rw [← hy]
  exact hu _

/-- `ℓ` is at least `ℓ(x₁)` on `𝒢`: it increases along the paths defining `𝒢` from `x₁` on. -/
theorem le_of_mem_explorationSet {u ℓ : C → ℝ} {x₀ x₁ y : C}
    (hy : y ∈ explorationSet C u ℓ x₀ x₁) : ℓ x₁ ≤ ℓ y := by
  obtain ⟨n, hn, γ, -, -, -, h1, hy, hinc⟩ := hy
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmono : ∀ k (hk : k ≤ m), ℓ (γ 1) ≤ ℓ (γ ⟨k + 1, by omega⟩) := by
    intro k
    induction k with
    | zero => exact fun _ => le_of_eq (congrArg ℓ (congrArg γ (Fin.ext (by simp))))
    | succ k ih =>
      intro hk
      exact (ih (by omega)).trans (hinc ⟨k + 1, by omega⟩ (by simp)).le
  subst h1 hy
  exact hmono m le_rfl

/-- An edge of `𝒢` is an edge of `𝒞_∞`. -/
theorem explorationGraph_le_componentGraph (u ℓ : C → ℝ) (x₀ x₁ : C) :
    explorationGraph C u ℓ x₀ x₁ ≤ componentGraph C := fun _ _ h => h.2.2.1

/-- A set connected in `𝒢` is connected in `𝒞_∞`. -/
theorem isConnectedSet_of_connectedIn {u ℓ : C → ℝ} {x₀ x₁ : C} {S : Set C}
    (hS : ConnectedIn C (explorationGraph C u ℓ x₀ x₁) S) : IsConnectedSet C S := by
  intro x hx y hy
  obtain ⟨hx', hy', hr⟩ := hS x hx y hy
  exact ⟨hx', hy', hr.mono fun a b h => explorationGraph_le_componentGraph C u ℓ x₀ x₁ h⟩

end Exploration

/-- **step:5.27-graph** (Step 1, L2485-2491): a block of `𝒢` lies in `L_{u(x₀)}` and is
biconnected in `𝒞_∞`. -/
theorem explorationBlockStep : ExplorationBlockStep := by
  intro ω C u ℓ x₀ x₁ S hS
  obtain ⟨⟨hSV, hconn, hcut⟩, -⟩ := hS
  exact ⟨hSV.trans (explorationSet_subset_levelSet C u ℓ x₀ x₁),
    isConnectedSet_of_connectedIn C hconn, fun x hx => isConnectedSet_of_connectedIn C (hcut x hx)⟩

/-! ### Connectedness of `Q_r ∪ L_-` in `ℤ²` -/

/-- `x` and `y` are joined by a nearest-neighbour path inside `A` (the relation defining the
connected components of `A` in `IsLatticeComponentOf`). -/
private def LatticeJoined (A : Set (Vertex 2)) (x y : Vertex 2) : Prop :=
  ∃ hx : x ∈ A, ∃ hy : y ∈ A, ((nearestNeighborGraph 2).induce A).Reachable ⟨x, hx⟩ ⟨y, hy⟩

private theorem LatticeJoined.trans {A : Set (Vertex 2)} {x y z : Vertex 2}
    (h₁ : LatticeJoined A x y) (h₂ : LatticeJoined A y z) : LatticeJoined A x z := by
  obtain ⟨hx, hy, r₁⟩ := h₁
  obtain ⟨hy', hz, r₂⟩ := h₂
  exact ⟨hx, hz, r₁.trans r₂⟩

private theorem LatticeJoined.symm {A : Set (Vertex 2)} {x y : Vertex 2}
    (h : LatticeJoined A x y) : LatticeJoined A y x := by
  obtain ⟨hx, hy, r⟩ := h
  exact ⟨hy, hx, r.symm⟩

/-- Along a lattice line inside `A`, the endpoints are joined in `A`. -/
private theorem latticeJoined_of_line {A : Set (Vertex 2)} (f : ℤ → Vertex 2)
    (hf : ∀ t, (nearestNeighborGraph 2).Adj (f t) (f (t + 1))) {m n : ℤ}
    (hA : ∀ t, (m ≤ t ∧ t ≤ n) ∨ (n ≤ t ∧ t ≤ m) → f t ∈ A) : LatticeJoined A (f m) (f n) := by
  have key : ∀ a b, a ≤ b → (∀ t, a ≤ t → t ≤ b → f t ∈ A) → LatticeJoined A (f a) (f b) := by
    intro a b hab
    induction b, hab using Int.leInduction with
    | base => exact fun h => ⟨h a le_rfl le_rfl, h a le_rfl le_rfl, .refl _⟩
    | succ b hab ih =>
      intro h
      have hb : f b ∈ A := h b hab (by omega)
      have hb' : f (b + 1) ∈ A := h (b + 1) (by omega) le_rfl
      refine (ih fun t h1 h2 => h t h1 (by omega)).trans ⟨hb, hb', ?_⟩
      exact (show ((nearestNeighborGraph 2).induce A).Adj ⟨f b, hb⟩ ⟨f (b + 1), hb'⟩ from
        hf b).reachable
  rcases le_total m n with h | h
  · exact key m n h fun t h1 h2 => hA t (Or.inl ⟨h1, h2⟩)
  · exact (key n m h fun t h1 h2 => hA t (Or.inr ⟨h1, h2⟩)).symm

private theorem adj_vertical (a t : ℤ) : (nearestNeighborGraph 2).Adj ![a, t] ![a, t + 1] :=
  show ∃ i : Fin 2, _ = _ + LatticeProb.unit i ∨ _ from
    ⟨1, Or.inl (by funext j; fin_cases j <;> simp [LatticeProb.unit])⟩

private theorem adj_horizontal (t : ℤ) : (nearestNeighborGraph 2).Adj ![t, 0] ![t + 1, 0] :=
  show ∃ i : Fin 2, _ = _ + LatticeProb.unit i ∨ _ from
    ⟨0, Or.inl (by funext j; fin_cases j <;> simp [LatticeProb.unit])⟩

/-- Inside every `A ⊇ Q_r ∪ L_-`, each point of `Q_r` is joined to each point of `L_-`: a
vertical segment of `Q_r` leads to the axis, and the axis to `L_-`. -/
private theorem latticeJoined_cube_negativeLine {A : Set (Vertex 2)} {r : ℕ}
    (hA : cube r ∪ negativeLine ⊆ A) {x y : Vertex 2} (hx : x ∈ cube r)
    (hy : y ∈ negativeLine) : LatticeJoined A x y := by
  obtain ⟨hx0l, hx0r⟩ := abs_le.1 (hx 0)
  obtain ⟨hx1l, hx1r⟩ := abs_le.1 (hx 1)
  obtain ⟨hy0, hy1⟩ := hy
  have ex : x = ![x 0, x 1] := by funext j; fin_cases j <;> rfl
  have ey : y = ![y 0, 0] := by funext j; fin_cases j <;> simp [hy1]
  have hv : LatticeJoined A ![x 0, x 1] ![x 0, 0] :=
    latticeJoined_of_line (fun t => ![x 0, t]) (adj_vertical (x 0)) fun t ht => hA <| Or.inl <| by
      intro i
      fin_cases i
      · exact hx 0
      · exact abs_le.2 (by simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
                           constructor <;> omega)
  have hh : LatticeJoined A ![x 0, 0] ![y 0, 0] :=
    latticeJoined_of_line (fun t => ![t, 0]) adj_horizontal fun t ht => hA <| by
      rcases le_or_gt t 0 with h0 | h0
      · exact Or.inr ⟨by simpa using h0, by simp⟩
      · refine Or.inl fun i => ?_
        fin_cases i
        · exact abs_le.2 (by simp only [Fin.zero_eta, Matrix.cons_val_zero]
                             constructor <;> omega)
        · simp
  rw [ex, ey]
  exact hv.trans hh

/-- **step:5.27-graph** (Step 1, third point, L2487-2490): if `supp f ⊆ Q_r` and `ℓ(x₀)` exceeds
`ℓ` on `𝒞_∞ ∩ (Q_r ∪ L_-)`, then the finite connected components of `ℤ² \ S`, `S ⊆ 𝒢`, avoid
`supp f`. -/
theorem explorationHolesStep : ExplorationHolesStep := by
  intro ω C f r u ℓ x₀ x₁ hf h01 hlow S hS T hT hTfin x hxT
  by_contra hfx
  have hA : cube r ∪ negativeLine ⊆ (Subtype.val '' S)ᶜ := by
    rintro z hz ⟨y, hyS, rfl⟩
    have h1 := le_of_mem_explorationSet C (hS hyS)
    have h2 := hlow y hz
    linarith
  obtain ⟨x', -, rfl⟩ := hT
  have hxj : LatticeJoined (Subtype.val '' S)ᶜ x' x := hxT
  have hsub : negativeLine ⊆ {y | LatticeJoined (Subtype.val '' S)ᶜ x' y} := fun y hy =>
    hxj.trans (latticeJoined_cube_negativeLine hA (hf x hfx) hy)
  have hinf : negativeLine.Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (![-(k : ℤ), 0] : Vertex 2))
      (fun k k' hkk' => by simpa using congrFun hkk' 0) fun k => ⟨by simp, by simp⟩
  exact hinf.mono hsub hTfin

end Rigidity.Proofs.Section5
