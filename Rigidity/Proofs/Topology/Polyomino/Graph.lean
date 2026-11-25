import Rigidity.Proofs.Topology.Polyomino.Cells
import Mathlib.Combinatorics.SimpleGraph.Matching

/-! # The boundary graph of a finite union of lattice cells

The corners of the cells are indexed by `ℤ²`: the corner `m` is the point `mpt m`, the upper right
corner of `Cell m`. Two corners are adjacent in the boundary graph if they are the two ends of a
side between a cell of `S` and a cell not in `S` (`BAdj`). At the corner `m` the four cells are
`m`, `m + (1, 0)`, `m + (0, 1)` and `m + (1, 1)`, and the side from `m` in the direction `d` lies
between the cells `eA m d` and `eB m d` (`badj_iff`). Without checkerboard corners every corner
with a neighbour has exactly two (`bGraph_isCycles`), so every component of the boundary graph
with an edge is a cycle (Mathlib's `SimpleGraph.IsCycles`), whose corners form a closed lattice
polygon without repeated corner (`exists_polygon`).
-/

open Set Function LatticeProb

namespace Rigidity.Proofs.Topology.Polyomino

open Rigidity.Proofs.Section5.JordanLoop

instance : Fintype Dir where
  elems := {.E, .N, .W, .S}
  complete d := by cases d <;> decide

/-- The first cell along the side from the corner `m` in the direction `d`. -/
def eA (m : ℤ × ℤ) : Dir → ℤ × ℤ
  | .E => (m.1 + 1, m.2) | .N => (m.1, m.2 + 1) | .W => m | .S => m

/-- The second cell along the side from the corner `m` in the direction `d`. -/
def eB (m : ℤ × ℤ) : Dir → ℤ × ℤ
  | .E => (m.1 + 1, m.2 + 1) | .N => (m.1 + 1, m.2 + 1) | .W => (m.1, m.2 + 1)
  | .S => (m.1 + 1, m.2)

variable {S : Set (ℤ × ℤ)}

/-- The corners `a, b` are the two ends of a side between a cell of `S` and a cell not in `S`. -/
def BAdj (S : Set (ℤ × ℤ)) (a b : ℤ × ℤ) : Prop :=
  ∃ c ∈ S, ∃ n : Dir, c + n.v ∉ S ∧ s(a, b) = s(sideStart c n, sideEnd c n)

theorem BAdj.symm {a b : ℤ × ℤ} (h : BAdj S a b) : BAdj S b a := by
  obtain ⟨c, hc, n, hn, h⟩ := h
  exact ⟨c, hc, n, hn, Sym2.eq_swap.trans h⟩

theorem sideStart_ne_sideEnd (c : ℤ × ℤ) (n : Dir) : sideStart c n ≠ sideEnd c n := by
  rw [sideEnd_eq]
  intro h
  exact add_v_ne (sideStart c n) n.rot h.symm

theorem BAdj.ne {a b : ℤ × ℤ} (h : BAdj S a b) : a ≠ b := by
  obtain ⟨c, -, n, -, h⟩ := h
  rintro rfl
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact sideStart_ne_sideEnd c n (h1.symm.trans h2)
  · exact sideStart_ne_sideEnd c n (h2.symm.trans h1)

/-- The corner equalities of the boundary graph. -/
local macro "pe" : tactic =>
  `(tactic| ((try simp only [eA, eB, sideStart, sideEnd, Dir.v, Prod.ext_iff, Prod.fst_add,
    Prod.snd_add, true_and, and_true]); all_goals omega))

/-- The neighbours of a corner `m` in the boundary graph. -/
theorem badj_iff {m w : ℤ × ℤ} :
    BAdj S m w ↔ ∃ d : Dir, w = m + d.v ∧ ¬ (eA m d ∈ S ↔ eB m d ∈ S) := by
  constructor
  · rintro ⟨c, hc, n, hcn, h⟩
    have key1 : ∀ x y : ℤ × ℤ, x = c → y = c + n.v → ¬ (x ∈ S ↔ y ∈ S) := by
      rintro x y rfl rfl; tauto
    have key2 : ∀ x y : ℤ × ℤ, x = c + n.v → y = c → ¬ (x ∈ S ↔ y ∈ S) := by
      rintro x y rfl rfl; tauto
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases n
      · refine ⟨.N, by pe, key1 _ _ ?_ ?_⟩ <;> pe
      · refine ⟨.W, by pe, key1 _ _ ?_ ?_⟩ <;> pe
      · refine ⟨.S, by pe, key2 _ _ ?_ ?_⟩ <;> pe
      · refine ⟨.E, by pe, key2 _ _ ?_ ?_⟩ <;> pe
    · cases n
      · refine ⟨.S, by pe, key1 _ _ ?_ ?_⟩ <;> pe
      · refine ⟨.E, by pe, key1 _ _ ?_ ?_⟩ <;> pe
      · refine ⟨.N, by pe, key2 _ _ ?_ ?_⟩ <;> pe
      · refine ⟨.W, by pe, key2 _ _ ?_ ?_⟩ <;> pe
  · rintro ⟨d, rfl, hp⟩
    cases d
    · by_cases h : eA m .E ∈ S
      · refine ⟨eA m .E, h, .N, ?_, Sym2.eq_iff.2 (Or.inr ⟨by pe, by pe⟩)⟩
        rw [show eA m .E + Dir.N.v = eB m .E by pe]; tauto
      · refine ⟨eB m .E, by tauto, .S, ?_, Sym2.eq_iff.2 (Or.inl ⟨by pe, by pe⟩)⟩
        rw [show eB m .E + Dir.S.v = eA m .E by pe]; exact h
    · by_cases h : eA m .N ∈ S
      · refine ⟨eA m .N, h, .E, ?_, Sym2.eq_iff.2 (Or.inl ⟨by pe, by pe⟩)⟩
        rw [show eA m .N + Dir.E.v = eB m .N by pe]; tauto
      · refine ⟨eB m .N, by tauto, .W, ?_, Sym2.eq_iff.2 (Or.inr ⟨by pe, by pe⟩)⟩
        rw [show eB m .N + Dir.W.v = eA m .N by pe]; exact h
    · by_cases h : eA m .W ∈ S
      · refine ⟨eA m .W, h, .N, ?_, Sym2.eq_iff.2 (Or.inl ⟨by pe, by pe⟩)⟩
        rw [show eA m .W + Dir.N.v = eB m .W by pe]; tauto
      · refine ⟨eB m .W, by tauto, .S, ?_, Sym2.eq_iff.2 (Or.inr ⟨by pe, by pe⟩)⟩
        rw [show eB m .W + Dir.S.v = eA m .W by pe]; exact h
    · by_cases h : eA m .S ∈ S
      · refine ⟨eA m .S, h, .E, ?_, Sym2.eq_iff.2 (Or.inr ⟨by pe, by pe⟩)⟩
        rw [show eA m .S + Dir.E.v = eB m .S by pe]; tauto
      · refine ⟨eB m .S, by tauto, .W, ?_, Sym2.eq_iff.2 (Or.inl ⟨by pe, by pe⟩)⟩
        rw [show eB m .S + Dir.W.v = eA m .S by pe]; exact h

theorem add_v_injective (m : ℤ × ℤ) : Injective fun d : Dir => m + d.v := by
  intro d d' h
  have h' : d.v = d'.v := add_left_cancel h
  cases d <;> cases d' <;> first | rfl | simp [Dir.v] at h'

theorem ncard_dirs (p : Dir → Prop) [DecidablePred p] :
    {d | p d}.ncard = (if p .E then 1 else 0) + (if p .N then 1 else 0) +
      (if p .W then 1 else 0) + (if p .S then 1 else 0) := by
  have : {d | p d} = ↑(Finset.univ.filter p) := by ext; simp
  rw [this, Set.ncard_coe_finset, Finset.card_filter,
    show (Finset.univ : Finset Dir) = {.E, .N, .W, .S} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- Four sides at a corner: if they are not all boundary sides, an even number of them are, and
one of them is, then exactly two of them are. -/
theorem ncard_eq_two_of (p : Dir → Prop) (h4 : ¬ (p .E ∧ p .N ∧ p .W ∧ p .S))
    (hne : p .E ∨ p .N ∨ p .W ∨ p .S) (hpar : (p .E ↔ p .N) ↔ (p .W ↔ p .S)) :
    {d | p d}.ncard = 2 := by
  classical
  rw [ncard_dirs]
  by_cases h1 : p .E <;> by_cases h2 : p .N <;> by_cases h3 : p .W <;> by_cases h5 : p .S <;>
    simp_all

/-- The corners with a neighbour in the boundary graph. -/
def Corner (S : Set (ℤ × ℤ)) : Set (ℤ × ℤ) := {m | ∃ w, BAdj S m w}

theorem corner_finite (hS : S.Finite) : (Corner S).Finite := by
  refine (((hS.prod (Set.finite_univ (α := Dir))).image fun x => sideStart x.1 x.2).union
    ((hS.prod (Set.finite_univ (α := Dir))).image fun x => sideEnd x.1 x.2)).subset ?_
  rintro m ⟨w, c, hc, n, -, h⟩
  rcases Sym2.eq_iff.1 h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl ⟨(c, n), ⟨hc, trivial⟩, rfl⟩
  · exact Or.inr ⟨(c, n), ⟨hc, trivial⟩, rfl⟩

/-- The boundary graph on the corners with a neighbour. -/
def bGraph (S : Set (ℤ × ℤ)) : SimpleGraph (Corner S) where
  Adj a b := BAdj S a.1 b.1
  symm := ⟨fun a b (h : BAdj S a.1 b.1) => h.symm⟩
  loopless := ⟨fun a (h : BAdj S a.1 a.1) => h.ne rfl⟩

theorem bGraph_adj {a b : Corner S} : (bGraph S).Adj a b ↔ BAdj S a.1 b.1 := Iff.rfl

theorem image_val_neighborSet (v : Corner S) :
    Subtype.val '' (bGraph S).neighborSet v = {w | BAdj S v.1 w} := by
  ext w
  constructor
  · rintro ⟨w', hw', rfl⟩
    rw [SimpleGraph.mem_neighborSet] at hw'
    exact hw'
  · intro hw
    exact ⟨⟨w, v.1, BAdj.symm hw⟩, (SimpleGraph.mem_neighborSet _ _ _).2 hw, rfl⟩

/-- Without checkerboard corners the boundary graph is a union of cycles. -/
theorem bGraph_isCycles (hNC : NoChecker S) : (bGraph S).IsCycles := by
  intro v hv
  have hset : {w | BAdj S v.1 w} =
      (fun d : Dir => v.1 + d.v) '' {d | ¬ (eA v.1 d ∈ S ↔ eB v.1 d ∈ S)} := by
    ext w
    rw [mem_setOf_eq, badj_iff]
    constructor
    · rintro ⟨d, rfl, hd⟩
      exact ⟨d, hd, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d, rfl, hd⟩
  obtain ⟨w, hw⟩ := hv
  rw [SimpleGraph.mem_neighborSet] at hw
  obtain ⟨d₀, -, hd₀⟩ := (badj_iff (S := S) (m := v.1) (w := w.1)).1 hw
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, image_val_neighborSet, hset,
    Set.ncard_image_of_injective _ (add_v_injective v.1)]
  have hc := hNC v.1 (v.1.1 + 1, v.1.2 + 1) (by simp) (by simp)
  simp only at hc
  refine ncard_eq_two_of _ ?_ ?_ ?_
  · rintro ⟨hE, hN, hW, hS⟩
    simp only [eA, eB] at hE hN hW hS
    tauto
  · cases d₀
    exacts [Or.inl hd₀, Or.inr (Or.inl hd₀), Or.inr (Or.inr (Or.inl hd₀)),
      Or.inr (Or.inr (Or.inr hd₀))]
  · simp only [eA, eB]
    tauto

/-- A boundary edge joins lattice neighbours. -/
theorem BAdj.lattice_adj {a b : ℤ × ℤ} (h : BAdj S a b) : (lattice 2).Adj (toV a) (toV b) := by
  obtain ⟨c, -, n, -, h⟩ := h
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact adj_of_dir (d := n.rot) (by rw [pr_toV, pr_toV, sideEnd_eq])
  · exact (adj_of_dir (d := n.rot) (by rw [pr_toV, pr_toV, sideEnd_eq])).symm

/-- The side between two adjacent corners lies in `bdry S`. -/
theorem BAdj.segment_subset {a b : ℤ × ℤ} (h : BAdj S a b) :
    segment ℝ (mpt a) (mpt b) ⊆ bdry S := by
  obtain ⟨c, hc, n, hn, h⟩ := h
  have hside : segment ℝ (mpt a) (mpt b) = segment ℝ (mpt (sideStart c n)) (mpt (sideEnd c n)) := by
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact segment_symm ℝ _ _
  rw [hside, side_eq_inter]
  exact fun p hp => ⟨c, hc, n, hn, hp⟩

/-- Every point of `bdry S` lies on the side between two adjacent corners. -/
theorem exists_badj_of_mem_bdry {p : E2} (hp : p ∈ bdry S) :
    ∃ a b, BAdj S a b ∧ p ∈ segment ℝ (mpt a) (mpt b) := by
  obtain ⟨c, hc, n, hn, hpc⟩ := hp
  exact ⟨sideStart c n, sideEnd c n, ⟨c, hc, n, hn, rfl⟩, by rw [side_eq_inter]; exact hpc⟩

end Rigidity.Proofs.Topology.Polyomino
