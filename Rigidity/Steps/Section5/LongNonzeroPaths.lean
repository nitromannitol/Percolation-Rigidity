import Rigidity.Steps.Section5.PolesSuperLevelSets

/-! # Lemma 5.18: long paths avoiding the zero set

Proof of Lemma 5.18 (`LongNonzeroPathsStmt`, corrected draft L1992-1997) from Lemma 5.17. Since
`supp u` is infinite and `Q_{R'}` is finite, there is a vertex `x` of `𝒞_∞` outside `Q_{R'}` with
`u(x) ≠ 0`. If `u(x) > 0`, the connected component of `{u > 0}` through `x` meets a pole
`y ∈ supp f ⊆ Q_R` (Lemma 5.17 for `f`); a path from `y` to `x` inside it avoids the zero set of
`u`. If `u(x) < 0`, the same argument applies to `-u`, the potential of `-f` normalized at infinity
(Lemma 5.17 for `-f`).

The printed proof uses the component of `{u ≥ u(x)}`; the strict superlevel set `{u > 0}` serves
equally well and is the form in which Lemma 5.17 is stated. -/

open MeasureTheory LatticeProb.Percolation Filter Topology

namespace Rigidity.Steps.Section5

open Rigidity.Section5

variable {ω : Configuration 2}

/-- The cube `Q_r` is finite. -/
theorem cube_finite (r : ℕ) : (cube r).Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin 2 => Set.Icc (-(r : ℤ)) r)
    (fun _ => Set.finite_Icc _ _)).subset ?_
  intro x hx i _
  exact abs_le.mp (hx i)

/-- Two vertices joined inside `S` are joined by a finite path of `𝒞_∞` inside `S`. -/
theorem exists_path_of_joinedIn {C : OpenComponent ω} {S : Set C} {x y : C}
    (hxy : JoinedIn C S x y) :
    ∃ n : ℕ, ∃ γ : Fin (n + 1) → C,
      (∀ i : Fin n, (componentGraph C).Adj (γ i.castSucc) (γ i.succ)) ∧
      γ 0 = x ∧ γ (Fin.last n) = y ∧ ∀ i, γ i ∈ S := by
  obtain ⟨_, _, ⟨w⟩⟩ := hxy
  refine ⟨w.length, fun i => (w.getVert i).val, fun i => ?_, by simp [w.getVert_zero],
    by simp [w.getVert_length], fun i => (w.getVert i).2⟩
  have h := w.adj_getVert_succ (i := i) i.isLt
  simpa [Fin.val_succ] using h

/-- Being joined inside `S` is symmetric. -/
theorem joinedIn_symm {C : OpenComponent ω} {S : Set C} {x y : C} (hxy : JoinedIn C S x y) :
    JoinedIn C S y x := by
  obtain ⟨hx, hy, hr⟩ := hxy
  exact ⟨hy, hx, hr.symm⟩

/-- The Laplacian of `𝒞_∞` commutes with negation. -/
theorem componentLaplacian_neg (C : OpenComponent ω) (u : C → ℝ) (x : C) :
    componentLaplacian C (-u) x = -componentLaplacian C u x := by
  simp only [componentLaplacian, Pi.neg_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- `-u` is the potential of `-f` normalized at infinity. -/
theorem isDecayingPotential_neg {C : OpenComponent ω} {f : Vertex 2 → ℤ} {u : C → ℝ}
    (hu : IsDecayingPotential C f u) : IsDecayingPotential C (-f) (-u) := by
  have hlim := hu.2.neg
  rw [neg_zero] at hlim
  refine ⟨fun x => ?_, hlim⟩
  rw [componentLaplacian_neg, neg_neg, Pi.neg_apply, Int.cast_neg, ← hu.1 x, neg_neg]

/-- Lemma 5.18 on a fixed component: if every connected component of `{u > 0}` and of `{-u > 0}`
meets a pole, `supp f ⊆ Q_R` and `supp u` is infinite, then some path of `𝒞_∞` from `Q_R` to the
complement of `Q_{R'}` avoids the zero set of `u`. -/
theorem exists_nonzero_path_of_poles {C : OpenComponent ω} {f : Vertex 2 → ℤ} {u : C → ℝ}
    (hP : ∀ T, IsComponentOf C {x | 0 < u x} T → ∃ y ∈ T, f y.val ≠ 0)
    (hP' : ∀ T, IsComponentOf C {x | 0 < (-u) x} T → ∃ y ∈ T, (-f) y.val ≠ 0)
    (R : ℕ) (hR : ∀ x, f x ≠ 0 → x ∈ cube R) (R' : ℕ) (hsupp : (Function.support u).Infinite) :
    ∃ n : ℕ, ∃ γ : Fin (n + 1) → C,
      (∀ i : Fin n, (componentGraph C).Adj (γ i.castSucc) (γ i.succ)) ∧
      (γ 0).val ∈ cube R ∧ (γ (Fin.last n)).val ∉ cube R' ∧ ∀ i, u (γ i) ≠ 0 := by
  have hfin : {x : C | x.val ∈ cube R'}.Finite :=
    (cube_finite R').preimage Subtype.val_injective.injOn
  obtain ⟨x, hx, hxR'⟩ := (hsupp.sdiff hfin).nonempty
  rcases lt_or_gt_of_ne (hx : u x ≠ 0) with hneg | hpos
  · have hxS : x ∈ {z | 0 < (-u) z} := by simpa using hneg
    obtain ⟨y, hyT, hfy⟩ := hP' {z | JoinedIn C {z | 0 < (-u) z} x z} ⟨x, hxS, rfl⟩
    obtain ⟨n, γ, hadj, h0, hlast, hS⟩ := exists_path_of_joinedIn (joinedIn_symm hyT)
    refine ⟨n, γ, hadj, h0 ▸ hR _ (by simpa using hfy), hlast ▸ hxR', fun i => ?_⟩
    have := hS i
    simp only [Set.mem_setOf_eq, Pi.neg_apply, neg_pos] at this
    exact this.ne
  · obtain ⟨y, hyT, hfy⟩ := hP {z | JoinedIn C {z | 0 < u z} x z} ⟨x, hpos, rfl⟩
    obtain ⟨n, γ, hadj, h0, hlast, hS⟩ := exists_path_of_joinedIn (joinedIn_symm hyT)
    exact ⟨n, γ, hadj, h0 ▸ hR _ hfy, hlast ▸ hxR', fun i => (hS i).ne'⟩

/-- Lemma 5.18 follows from Lemma 5.17 for `f` and for `-f`. -/
theorem longNonzeroPaths_of_polesSuperLevelSets {p : unitInterval} {f : Vertex 2 → ℤ}
    (h517 : PolesSuperLevelSetsStmt p f) (h517' : PolesSuperLevelSetsStmt p (-f)) :
    LongNonzeroPathsStmt p f := by
  intro hf
  have hf' : (Function.support (-f)).Finite := by simpa using hf
  filter_upwards [h517 hf, h517' hf'] with ω ⟨h, hP⟩ ⟨_, hP'⟩
  refine ⟨h, fun u hu R _ hR R' _ hsupp => ?_⟩
  exact exists_nonzero_path_of_poles (fun T hT => hP u hu hsupp 0 T hT)
    (fun T hT => hP' (-u) (isDecayingPotential_neg hu) (by simpa using hsupp) 0 T hT)
    R hR R' hsupp

/-- Lemma 5.18 follows from the finite maximum principle and Lemma 5.16, through Lemma 5.17. -/
theorem longNonzeroPaths_of_steps {p : unitInterval} (hF : FiniteMaxPrinciple)
    (h516 : StrongMaxPrincipleStmt p) (f : Vertex 2 → ℤ) : LongNonzeroPathsStmt p f :=
  longNonzeroPaths_of_polesSuperLevelSets (polesSuperLevelSets_of_steps hF h516 f)
    (polesSuperLevelSets_of_steps hF h516 (-f))

end Rigidity.Steps.Section5
