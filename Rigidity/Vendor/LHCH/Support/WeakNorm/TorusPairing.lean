/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/TorusPairing.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.WeakNorm.Reflection
import Rigidity.Vendor.LHCH.Support.Lattice.Membership

/-!
# Face-weighted pairings on a cube are pairings on the torus

Step 3 of the proof of `p:finite-range`:
"face-weighted pairings on `□_n` are then pairings on the torus". Let `N ≥ 1`. The fold maps
every edge of the periodicity box `{0, …, 2N − 1}^d` onto an edge of the cube `{0, …, N}^d`, and
the reflected edge fields are
`±` the original fields at the folded edge, so the product of two reflected fields is the product
of the fields at the folded edge. An edge `(y, j)` of the cube has `2` preimages in its own
direction and, in each other direction `i`, one preimage if `y_i ∈ {0, N}` and two otherwise: in
total `2^{d − k(e)}`, where `k(e)` is the number of faces of the cube containing `e`. Hence
`Σ_{torus} F̃ G̃ = 2^d Σ_{e ⊂ □} w_□(e) F(e) G(e)`.
-/

namespace LatticeHC

open LatticeProb

noncomputable section

variable {d : ℕ}

/-- The periodicity box `{0, …, 2N − 1}^d`, a fundamental domain of the torus of side `2N`. -/
def torusBox (d N : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ : Fin d => Finset.Ico (0 : ℤ) (2 * N)

/-- The fold of an edge: `(x, j)` goes to `(fold x, j)` below the midpoint of the period in
direction `j`, and to `(fold (x + e_j), j)` above it. -/
def foldEdge (N : ℕ) (e : Edge d) : Edge d :=
  if e.1 e.2 % (2 * N) < N then (foldSite N e.1, e.2) else (foldSite N (e.1 + unit e.2), e.2)

/-- The product of two reflected edge fields is the product of the fields at the folded edge. -/
theorem reflectEdgeField_mul (N : ℕ) (F G : Edge d → ℝ) (e : Edge d) :
    reflectEdgeField N F e * reflectEdgeField N G e = F (foldEdge N e) * G (foldEdge N e) := by
  unfold reflectEdgeField foldEdge
  split_ifs <;> ring

/-- The fold of an integer lies in `[0, N]`. -/
theorem foldCoord_mem (N : ℕ) (hN : 0 < N) (a : ℤ) : 0 ≤ foldCoord N a ∧ foldCoord N a ≤ N := by
  have h0 := Int.emod_nonneg a (by positivity : (2 * (N : ℤ)) ≠ 0)
  have h1 := Int.emod_lt_of_pos a (by positivity : (0 : ℤ) < 2 * N)
  unfold foldCoord
  generalize a % (2 * (N : ℤ)) = r at *
  split_ifs <;> omega

/-- On the periodicity interval `[0, 2N)` the fold is `s` below `N` and `2N − s` above. -/
theorem foldCoord_of_mem_Ico (N : ℕ) (s : ℤ) (hs0 : 0 ≤ s) (hs : s < 2 * N) :
    foldCoord N s = if s ≤ N then s else 2 * N - s := by
  unfold foldCoord
  rw [Int.emod_eq_of_lt hs0 hs]

/-- The fold maps every edge into the edges of the cube `{0, …, N}^d`. -/
theorem foldEdge_mem_edgesOf (N : ℕ) (hN : 0 < N) (e : Edge d) :
    foldEdge N e ∈ edgesOf 0 N := by
  obtain ⟨x, j⟩ := e
  rw [mem_edgesOf_iff_coord]
  intro i
  unfold foldEdge
  split_ifs with h <;> dsimp only at h ⊢
  · by_cases hij : i = j
    · subst hij
      left
      refine ⟨rfl, ?_⟩
      have h0 := Int.emod_nonneg (x i) (by positivity : (2 * (N : ℤ)) ≠ 0)
      simp only [Pi.zero_apply, foldSite, zero_add, foldCoord]
      rw [if_pos (by omega)]
      omega
    · right
      have := foldCoord_mem N hN (x i)
      exact ⟨hij, by simpa [foldSite] using this.1, by simpa [foldSite] using this.2⟩
  · by_cases hij : i = j
    · subst hij
      left
      refine ⟨rfl, ?_⟩
      have hrel := foldCoord_eq_add_one_of_le N hN (x i) (not_lt.mp h)
      have hm := foldCoord_mem N hN (x i + 1)
      have hm' := foldCoord_mem N hN (x i)
      simp only [Pi.zero_apply, foldSite, zero_add, Pi.add_apply, unit, Pi.single_eq_same]
      omega
    · right
      have := foldCoord_mem N hN (x i)
      refine ⟨hij, ?_, ?_⟩ <;>
        simp only [Pi.zero_apply, zero_add, foldSite_add_unit_of_ne N x j i hij] <;>
        simp only [foldSite] <;> omega

/-- The admissible values of the coordinate `i` of a preimage of the cube edge `(y, j)`: in the
direction `j` of the edge, `y_j` itself (below the midpoint) or `2N − 1 − y_j` (above it); in the
other directions, the preimages of `y_i` under the fold. -/
def foldFibre (N : ℕ) (y : Site d) (j i : Fin d) : Finset ℤ :=
  if i = j then
    (Finset.Ico (0 : ℤ) (2 * N)).filter fun s => (s < N ∧ s = y j) ∨ (N ≤ s ∧ 2 * N - 1 - s = y j)
  else (Finset.Ico (0 : ℤ) (2 * N)).filter fun s => foldCoord N s = y i

/-- The sites of the periodicity box whose edge in direction `j` folds onto `(y, j)` are exactly
those whose coordinates lie in `foldFibre`. -/
theorem filter_foldEdge_eq_piFinset (N : ℕ) (hN : 0 < N) (y : Site d) (j : Fin d) :
    (torusBox d N).filter (fun x => foldEdge N (x, j) = (y, j)) =
      Fintype.piFinset (foldFibre N y j) := by
  ext x
  simp only [torusBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Ico, foldFibre]
  constructor
  · rintro ⟨hbox, hfold⟩ i
    have hxj := hbox j
    unfold foldEdge at hfold
    rw [Int.emod_eq_of_lt hxj.1 hxj.2] at hfold
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, Finset.mem_filter, Finset.mem_Ico]
      refine ⟨hbox i, ?_⟩
      split_ifs at hfold with hlt
      · left
        refine ⟨hlt, ?_⟩
        have := congrArg (fun e : Edge d => e.1 i) hfold
        simp only [foldSite] at this
        rw [foldCoord_of_mem_Ico N _ hxj.1 hxj.2, if_pos hlt.le] at this
        exact this
      · right
        refine ⟨not_lt.mp hlt, ?_⟩
        have := congrArg (fun e : Edge d => e.1 i) hfold
        simp only [foldSite, Pi.add_apply, unit, Pi.single_eq_same] at this
        have hrel := foldCoord_eq_add_one_of_le N hN (x i)
          (by rw [Int.emod_eq_of_lt hxj.1 hxj.2]; exact not_lt.mp hlt)
        rw [foldCoord_of_mem_Ico N _ hxj.1 hxj.2] at hrel
        split_ifs at hrel <;> omega
    · rw [if_neg hij, Finset.mem_filter, Finset.mem_Ico]
      refine ⟨hbox i, ?_⟩
      have := congrArg (fun e : Edge d => e.1 i) hfold
      split_ifs at this
      · exact this
      · rw [show (foldSite N (x + unit j), j).1 i = foldSite N x i from
          foldSite_add_unit_of_ne N x j i hij] at this
        exact this
  · intro h
    have hbox : ∀ i, 0 ≤ x i ∧ x i < 2 * N := fun i => by
      have := h i
      split_ifs at this <;> exact Finset.mem_Ico.mp (Finset.mem_filter.mp this).1
    refine ⟨hbox, ?_⟩
    have hj := h j
    rw [if_pos rfl, Finset.mem_filter] at hj
    unfold foldEdge
    rw [Int.emod_eq_of_lt (hbox j).1 (hbox j).2]
    split_ifs with hlt
    · refine Prod.ext (funext fun i => ?_) rfl
      by_cases hij : i = j
      · subst hij
        simp only [foldSite]
        rw [foldCoord_of_mem_Ico N _ (hbox i).1 (hbox i).2, if_pos hlt.le]
        omega
      · have hi := h i
        rw [if_neg hij, Finset.mem_filter] at hi
        exact hi.2
    · refine Prod.ext (funext fun i => ?_) rfl
      by_cases hij : i = j
      · subst hij
        have hrel := foldCoord_eq_add_one_of_le N hN (x i)
          (by rw [Int.emod_eq_of_lt (hbox i).1 (hbox i).2]; exact not_lt.mp hlt)
        rw [foldCoord_of_mem_Ico N _ (hbox i).1 (hbox i).2] at hrel
        simp only [foldSite, Pi.add_apply, unit, Pi.single_eq_same]
        split_ifs at hrel <;> omega
      · have hi := h i
        rw [if_neg hij, Finset.mem_filter] at hi
        show foldSite N (x + unit j) i = y i
        rw [foldSite_add_unit_of_ne N x j i hij]
        exact hi.2

/-- Membership in a fibre of the fold, unfolded on the periodicity interval. -/
theorem mem_filter_foldCoord_iff (N : ℕ) (b s : ℤ) :
    s ∈ (Finset.Ico (0 : ℤ) (2 * N)).filter (fun s => foldCoord N s = b) ↔
      0 ≤ s ∧ s < 2 * N ∧ (if s ≤ N then s else 2 * N - s) = b := by
  rw [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h0, h1⟩, h⟩
    exact ⟨h0, h1, by rwa [foldCoord_of_mem_Ico N s h0 h1] at h⟩
  · rintro ⟨h0, h1, h⟩
    exact ⟨⟨h0, h1⟩, by rwa [foldCoord_of_mem_Ico N s h0 h1]⟩

/-- In the direction of the edge there are two preimages, `y_j` and `2N − 1 − y_j`. -/
theorem card_foldFibre_self (N : ℕ) (y : Site d) (j : Fin d) (hy0 : 0 ≤ y j)
    (hy1 : y j + 1 ≤ N) : (foldFibre N y j j).card = 2 := by
  rw [Finset.card_eq_two]
  refine ⟨y j, 2 * N - 1 - y j, by omega, ?_⟩
  ext s
  rw [foldFibre, if_pos rfl, Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert,
    Finset.mem_singleton]
  omega

/-- In a direction `i ≠ j` there is one preimage on a face (`y_i ∈ {0, N}`) and two otherwise. -/
theorem card_foldFibre_of_ne (N : ℕ) (hN : 0 < N) (y : Site d) {j i : Fin d} (hij : i ≠ j)
    (hy0 : 0 ≤ y i) (hy1 : y i ≤ N) :
    (foldFibre N y j i).card = if y i = 0 ∨ y i = N then 1 else 2 := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  simp only [foldFibre, if_neg hij]
  split_ifs with hface
  · rw [Finset.card_eq_one]
    refine ⟨y i, ?_⟩
    ext s
    rw [mem_filter_foldCoord_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨h0, h1, h⟩
      split_ifs at h <;> omega
    · rintro rfl
      exact ⟨hy0, by omega, by rw [if_pos hy1]⟩
  · rw [Finset.card_eq_two]
    refine ⟨y i, 2 * N - y i, by omega, ?_⟩
    ext s
    rw [mem_filter_foldCoord_iff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h0, h1, h⟩
      split_ifs at h <;> omega
    · rintro (rfl | rfl)
      · exact ⟨hy0, by omega, by rw [if_pos hy1]⟩
      · exact ⟨by omega, by omega, by rw [if_neg (by omega)]; ring⟩

/-- **The fibres of the fold**: an edge `e` of the cube `{0, …, N}^d` has `2^d w_□(e)` preimages
in the periodicity box, in its own direction. -/
theorem card_filter_foldEdge (N : ℕ) (hN : 0 < N) (e : Edge d) (he : e ∈ edgesOf 0 N) :
    (((torusBox d N).filter (fun x => foldEdge N (x, e.2) = e)).card : ℝ) =
      2 ^ d * faceWeight 0 N e := by
  obtain ⟨y, j⟩ := e
  have hcoord := (mem_edgesOf_iff_coord 0 N (y, j)).1 he
  rw [filter_foldEdge_eq_piFinset N hN y j, Fintype.card_piFinset]
  have hfac : ∀ i, ((foldFibre N y j i).card : ℝ) =
      2 * (1 / 2 : ℝ) ^ (if i ≠ j ∧ (y i = 0 ∨ y i = N) then 1 else 0) := by
    intro i
    by_cases hij : i = j
    · subst hij
      rcases hcoord i with ⟨-, h0, h1⟩ | ⟨hne, -, -⟩
      · simp only [Pi.zero_apply, zero_add] at h0 h1
        rw [card_foldFibre_self N y i h0 h1]
        simp
      · exact absurd rfl hne
    · rcases hcoord i with ⟨hji, -, -⟩ | ⟨-, h0, h1⟩
      · exact absurd hji hij
      · simp only [Pi.zero_apply, zero_add] at h0 h1
        rw [card_foldFibre_of_ne N hN y hij h0 h1]
        by_cases hface : y i = 0 ∨ y i = N
        · rw [if_pos hface, if_pos ⟨hij, hface⟩]
          norm_num
        · rw [if_neg hface, if_neg (fun h => hface h.2)]
          norm_num
  push_cast
  rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
  congr 1
  unfold faceWeight faceCount
  congr 1
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.zero_apply, zero_add]

/-- **Face-weighted pairings on a cube are pairings on the torus** (Step 3 of the proof of
`p:finite-range`): for `N ≥ 1` and edge fields `F`, `G`,
`Σ_{x ∈ {0,…,2N−1}^d} Σ_j F̃(x,j) G̃(x,j) = 2^d Σ_{e ⊂ □} w_□(e) F(e) G(e)`, where `□ = {0,…,N}^d`.
The products of reflected fields are products at the folded edge (`reflectEdgeField_mul`), and
each edge of the cube has `2^d w_□(e)` preimages (`card_filter_foldEdge`). -/
theorem sum_torusBox_reflectEdgeField_mul (N : ℕ) (hN : 0 < N) (F G : Edge d → ℝ) :
    ∑ x ∈ torusBox d N, ∑ j : Fin d, reflectEdgeField N F (x, j) * reflectEdgeField N G (x, j) =
      2 ^ d * ∑ e ∈ edgesOf 0 N, faceWeight 0 N e * F e * G e := by
  classical
  simp only [reflectEdgeField_mul]
  rw [Finset.sum_comm]
  have hdir : ∀ j : Fin d, ∑ x ∈ torusBox d N, F (foldEdge N (x, j)) * G (foldEdge N (x, j)) =
      ∑ e ∈ (edgesOf 0 N).filter (fun e => e.2 = j),
        (((torusBox d N).filter (fun x => foldEdge N (x, e.2) = e)).card : ℝ) * (F e * G e) := by
    intro j
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun x => foldEdge N (x, j))
      (t := (edgesOf 0 N).filter (fun e => e.2 = j))]
    · refine Finset.sum_congr rfl fun e he => ?_
      have hej : e.2 = j := (Finset.mem_filter.1 he).2
      rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]),
        Finset.sum_const, nsmul_eq_mul, hej]
    · intro x _
      refine Finset.mem_filter.2 ⟨foldEdge_mem_edgesOf N hN (x, j), ?_⟩
      unfold foldEdge
      split_ifs <;> rfl
  rw [Finset.sum_congr rfl fun j _ => hdir j, Finset.sum_fiberwise, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [card_filter_foldEdge N hN e he]
  ring

end

end LatticeHC
