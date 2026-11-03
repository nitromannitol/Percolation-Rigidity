import Rigidity.Steps.S3.NotLipschitz
import Rigidity.Proofs.S3.ChemicalDistance

/-!
# Short paths around the removed horizontal edges (`step:3.2-short-paths`)

The step `ShortPathsStep` of Proposition 3.2 (corrected draft L986-1062, eq. (short-paths)).

**Choice of the removable horizontal edges.** With `α = 1/(10d)` and `δ = α²`, the centre plane is
cut into cells of side `s = ⌊N^α⌋` in the `d - 1` transverse directions (the medium cubes), and
`w = ⌈N^δ⌉` is the radius of the small cubes. A horizontal edge `(y, y + e₁)`, `y ∈ center(Q_N)`, is
removable (`y ∈ removablePoints`) if `y ∈ Q_{N - N^{1/d}}` and every transverse coordinate of `y`
has residue at least `2w + 1` modulo `s`: the walls of width `2w + 1` along the boundaries of the
cells (the boundary layers of small blue cubes) are never touched. The number of centre points
outside `removablePoints` is at most `C N^{d-1} (w/s + N^{1/d - 1})`.

**Short paths.** Let `x` be a removable point whose edge was removed. Around the edge
`(x, x + e₁)` consider the box `D_x` (`alteredLo`, `alteredHi`): `-w ≤ y₁ ≤ w + 1`, and the
transverse coordinates within `w` of the cell of `x` minus its walls; and the box `A_x ⊇ D_x`
(`shellLo`, `shellHi`) one step larger in every direction. The proof below replaces the case
analysis of the printed argument (geodesic `γ`, the cases `|γ| ≤ 2N^{1/5}`, the vertex `z`) by a
direct construction, with the same two ingredients (the walls and the small cubes far from the
centre plane are untouched):
* (`not_mem_cubeAt_of_shell`) for a centre `y ∈ A_x \ D_x`, the cube `y + Q_w` contains no
  removable edge, so its open edges are the same before and after the removal and it is a good
  subcube for the modified environment (`isGoodCluster_closeBonds`);
* (`exists_exit_reachable`) an open path of the infinite cluster from `x` (or `x + e₁`) leaves
  `D_x` at a point `z ∈ A_x \ D_x`, which lies in the largest cluster of the good cube `z + Q_w`;
* (`reachable_of_shell`) the faces of `A_x` are boxes of centres in `A_x \ D_x`, any two of which
  are linked through the top face `{y₁ = w + 2}`; chaining the good cubes along a face connects the
  largest clusters of any two of them inside `x + Q_{s + 2w + 2}`.
Hence `x` and `x + e₁` are joined by open edges inside `x + Q_{s + 2w + 2}`, at distance less than
`(2s + 4w + 5)^d ≤ 15^d N^{1/10}` in the modified cluster (`shortPathsStep`, with `K = 34 d 15^d`).
Only the well-connectedness of `Q_N` is used (no literature input beyond its definition).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation Rigidity.External
  Rigidity.Section3 Rigidity.Steps.S3

namespace Rigidity.Proofs.S3

variable {d : ℕ}

/-! ### Boxes of centres and chaining of good cubes -/

/-- The box `{y : lo i ≤ y i ≤ hi i for every i}`. -/
def coordBox (lo hi : Vertex d) : Set (Vertex d) := {y | ∀ i, lo i ≤ y i ∧ y i ≤ hi i}

theorem openIn_le_openIn {ω : Configuration d} {S S' : Set (Vertex d)} (h : S ⊆ S') :
    openIn ω S ≤ openIn ω S' := fun _ _ hxy => ⟨hxy.1, h hxy.2.1, h hxy.2.2⟩

/-- Closing bonds none of which has both endpoints in `S` does not change the open edges in `S`. -/
theorem openIn_closeBonds_eq {ω : Configuration d} {B : Finset (Bond d)} {S : Set (Vertex d)}
    (hB : ∀ e ∈ B, ¬ ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ S) :
    openIn (closeBonds B ω) S = openIn ω S := by
  ext x y
  constructor
  · rintro ⟨h, hx, hy⟩
    exact ⟨adj_of_adj_closeBonds h, hx, hy⟩
  · rintro ⟨h, hx, hy⟩
    refine ⟨adj_closeBonds_of_adj h fun e he hexy => hB e he ?_, hx, hy⟩
    intro z hz
    rw [hexy] at hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact hx
    · exact hy

/-- A good cube containing no closed bond is a good cube of the modified environment. -/
theorem isGoodCluster_closeBonds {ω : Configuration d} {B : Finset (Bond d)} {z : Vertex d}
    {M : ℕ} {V : Set (Vertex d)} (hB : ∀ e ∈ B, ¬ ∀ y ∈ (e : Sym2 (Vertex d)), y ∈ cubeAt z M)
    (hV : IsGoodCluster ω z M V) : IsGoodCluster (closeBonds B ω) z M V := by
  have h := openIn_closeBonds_eq (ω := ω) hB
  unfold IsGoodCluster IsLargestClusterIn at hV ⊢
  rw [h]
  exact hV

/-- A largest cluster is nonempty. -/
theorem nonempty_of_isLargestClusterIn {ω : Configuration d} {S V : Set (Vertex d)}
    (hV : IsLargestClusterIn ω S V) : V.Nonempty := by
  obtain ⟨⟨x, -, rfl⟩, -⟩ := hV
  exact ⟨x, SimpleGraph.Reachable.refl x⟩

/-- Chaining good cubes along a box of centres: the largest clusters of two good cubes centred in
a box of good cubes contained in `W` are joined by open edges inside `W`. -/
theorem reachable_of_isGoodCluster_box {ω : Configuration d} {M : ℕ} (hM : 1 ≤ M)
    {W : Set (Vertex d)} (V : Vertex d → Set (Vertex d)) {lo hi : Vertex d}
    (hV : ∀ z ∈ coordBox lo hi, IsGoodCluster ω z M (V z) ∧ cubeAt z M ⊆ W) (n : ℕ) :
    ∀ z ∈ coordBox lo hi, ∀ z' ∈ coordBox lo hi, ∑ i, (z i - z' i).natAbs = n →
      ∀ a ∈ V z, ∀ b ∈ V z', (openIn ω W).Reachable a b := by
  induction n with
  | zero =>
    intro z hz z' _ hzz a ha b hb
    obtain rfl : z = z' := funext fun i => by
      have := (Finset.sum_eq_zero_iff.mp hzz) i (Finset.mem_univ i)
      omega
    exact (reachable_of_isLargestClusterIn (hV z hz).1.1 ha hb).mono
      (openIn_le_openIn (hV z hz).2)
  | succ n ih =>
    intro z hz z' hz' hzz a ha b hb
    obtain ⟨j, hj⟩ : ∃ j, z j ≠ z' j := by
      by_contra hcon
      push Not at hcon
      have : ∑ i, (z i - z' i).natAbs = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hcon i]; simp
      omega
    have hunit : ∀ k, (unit j : Vertex d) k = if k = j then 1 else 0 := fun k => by
      simp only [unit, Pi.single_apply]
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · -- step from `z` to `y = z + e_j`
      have hy : z + unit j ∈ coordBox lo hi := fun k => by
        have := hz k
        have := hz' k
        simp only [Pi.add_apply, hunit k]
        split_ifs with hk
        · subst hk; omega
        · omega
      have hsum : ∑ i, ((z + unit j) i - z' i).natAbs = n := by
        have := sum_natAbs_sub_succ (z := z) (z' := z + unit j) (w := z') j
          (fun k hk => by simp [hunit k, hk])
          (by rw [show (z + unit j) j = z j + 1 by simp [hunit j]]; omega)
        omega
      obtain ⟨c, hcz, hcy⟩ := exists_mem_inter_of_isGoodCluster hM j (hV z hz).1
        (hV _ hy).1
      exact ((reachable_of_isLargestClusterIn (hV z hz).1.1 ha hcz).mono
        (openIn_le_openIn (hV z hz).2)).trans (ih _ hy z' hz' hsum c hcy b hb)
    · -- step from `z` to `y = z - e_j`, so that `z = y + e_j`
      have hy : z - unit j ∈ coordBox lo hi := fun k => by
        have := hz k
        have := hz' k
        simp only [Pi.sub_apply, hunit k]
        split_ifs with hk
        · subst hk; omega
        · omega
      have hyz : z - unit j + unit j = z := by abel
      have hsum : ∑ i, ((z - unit j) i - z' i).natAbs = n := by
        have := sum_natAbs_sub_succ (z := z) (z' := z - unit j) (w := z') j
          (fun k hk => by simp [hunit k, hk])
          (by rw [show (z - unit j) j = z j - 1 by simp [hunit j]]; omega)
        omega
      obtain ⟨c, hcy, hcz⟩ := exists_mem_inter_of_isGoodCluster hM j (hV _ hy).1
        (by rw [hyz]; exact (hV z hz).1)
      exact ((reachable_of_isLargestClusterIn (hV z hz).1.1 ha hcz).mono
        (openIn_le_openIn (hV z hz).2)).trans (ih _ hy z' hz' hsum c hcy b hb)

/-- Two good cubes centred in a box of good cubes inside `W`: their largest clusters are joined
inside `W`. -/
theorem reachable_of_mem_coordBox {ω : Configuration d} {M : ℕ} (hM : 1 ≤ M)
    {W : Set (Vertex d)} (V : Vertex d → Set (Vertex d)) {lo hi : Vertex d}
    (hV : ∀ z ∈ coordBox lo hi, IsGoodCluster ω z M (V z) ∧ cubeAt z M ⊆ W)
    {z z' : Vertex d} (hz : z ∈ coordBox lo hi) (hz' : z' ∈ coordBox lo hi) :
    ∀ a ∈ V z, ∀ b ∈ V z', (openIn ω W).Reachable a b :=
  reachable_of_isGoodCluster_box hM V hV _ z hz z' hz' rfl

/-- An open walk from a point of `D` to a point outside `D` leaves `D` at a point `z` of `A`
(every neighbour of `D` lies in `A`), reached from the start by open edges inside `W ⊇ D ∪ A`. -/
theorem exists_exit_reachable {ω : Configuration d} {W D A : Set (Vertex d)} (hDW : D ⊆ W)
    (hAW : A ⊆ W) (hDA : ∀ y y', y ∈ D → (openGraph ω).Adj y y' → y' ∈ A) {v u : Vertex d}
    (p : (openGraph ω).Walk v u) (hv : v ∈ D) (hu : u ∉ D) :
    ∃ z ∈ A, z ∉ D ∧ (openIn ω W).Reachable v z := by
  induction p with
  | nil => exact absurd hv hu
  | @cons a b c hab q ih =>
    by_cases hb : b ∈ D
    · obtain ⟨z, hzA, hzD, hz⟩ := ih hb hu
      exact ⟨z, hzA, hzD,
        (SimpleGraph.Adj.reachable (G := openIn ω W) ⟨hab, hDW hv, hDW hb⟩).trans hz⟩
    · exact ⟨b, hDA a b hv hab, hb,
        SimpleGraph.Adj.reachable (G := openIn ω W) ⟨hab, hDW hv, hAW (hDA a b hv hab)⟩⟩

/-- The face `{y ∈ [lo, hi] : y_j = c}` of a box, itself a box. -/
def coordFace (lo hi : Vertex d) (j : Fin d) (c : ℤ) : Set (Vertex d) :=
  coordBox (Function.update lo j c) (Function.update hi j c)

theorem mem_coordFace {lo hi y : Vertex d} {j : Fin d} {c : ℤ} (hy : y ∈ coordBox lo hi)
    (hyj : y j = c) : y ∈ coordFace lo hi j c := fun k => by
  by_cases hk : k = j
  · subst hk; simp only [Function.update_self]; omega
  · simp only [Function.update_of_ne hk]; exact hy k

/-- A face `{y_j = Dlo_j - 1}` or `{y_j = Dhi_j + 1}` of the box `[Dlo - 1, Dhi + 1]` avoids the
inner box `[Dlo, Dhi]`. -/
theorem coordFace_subset {lo hi Dlo Dhi : Vertex d} (hlo : ∀ i, lo i = Dlo i - 1)
    (hhi : ∀ i, hi i = Dhi i + 1) (hle : ∀ i, lo i ≤ hi i) {j : Fin d} {c : ℤ}
    (hc : c = lo j ∨ c = hi j) :
    coordFace lo hi j c ⊆ coordBox lo hi \ coordBox Dlo Dhi := by
  intro y hy
  have hyj := hy j
  simp only [Function.update_self] at hyj
  refine ⟨fun k => ?_, fun hD => ?_⟩
  · by_cases hk : k = j
    · subst hk; have := hle k; omega
    · have := hy k
      simp only [Function.update_of_ne hk] at this
      exact this
  · have := hD j
    have := hlo j
    have := hhi j
    omega

/-- The good cubes centred in the shell `[Dlo - 1, Dhi + 1] \ [Dlo, Dhi]` (`d ≥ 2`) have their
largest clusters joined inside `W`: every face is a box of centres, and every face meets the top
face `{y₁ = Dhi₁ + 1}`, directly or through the face `{y₂ = Dhi₂ + 1}`. -/
theorem reachable_of_shell [NeZero d] (hd : 2 ≤ d) {ω : Configuration d} {M : ℕ} (hM : 1 ≤ M)
    {W : Set (Vertex d)} (V : Vertex d → Set (Vertex d)) {lo hi Dlo Dhi : Vertex d}
    (hlo : ∀ i, lo i = Dlo i - 1) (hhi : ∀ i, hi i = Dhi i + 1) (hle : ∀ i, lo i ≤ hi i)
    (hV : ∀ z ∈ coordBox lo hi, z ∉ coordBox Dlo Dhi →
      IsGoodCluster ω z M (V z) ∧ cubeAt z M ⊆ W)
    {z z' : Vertex d} (hz : z ∈ coordBox lo hi) (hzD : z ∉ coordBox Dlo Dhi)
    (hz' : z' ∈ coordBox lo hi) (hz'D : z' ∉ coordBox Dlo Dhi) :
    ∀ a ∈ V z, ∀ b ∈ V z', (openIn ω W).Reachable a b := by
  let R : Vertex d → Vertex d → Prop := fun z z' =>
    ∀ a ∈ V z, ∀ b ∈ V z', (openIn ω W).Reachable a b
  have htrans : ∀ z p z', p ∈ coordBox lo hi → p ∉ coordBox Dlo Dhi → R z p → R p z' →
      R z z' := fun z p z' hp hpD h1 h2 a ha b hb => by
    obtain ⟨c, hc⟩ := nonempty_of_isLargestClusterIn (hV p hp hpD).1.1
    exact (h1 a ha c hc).trans (h2 c hc b hb)
  have hface : ∀ j c, (c = lo j ∨ c = hi j) → ∀ y ∈ coordFace lo hi j c,
      ∀ y' ∈ coordFace lo hi j c, R y y' := fun j c hc y hy y' hy' =>
    reachable_of_mem_coordBox hM V (fun u hu => hV u (coordFace_subset hlo hhi hle hc hu).1
      (coordFace_subset hlo hhi hle hc hu).2) hy hy'
  have hqA : hi ∈ coordBox lo hi := fun i => ⟨hle i, le_rfl⟩
  have hqD : hi ∉ coordBox Dlo Dhi := fun h => by have := (h 0).2; have := hhi 0; omega
  -- the top face
  have htop : ∀ y ∈ coordBox lo hi, y 0 = hi 0 → R y hi := fun y hy hy0 =>
    hface 0 (hi 0) (Or.inr rfl) y (mem_coordFace hy hy0) hi (mem_coordFace hqA rfl)
  -- the transverse faces, through the top face
  have hside : ∀ y ∈ coordBox lo hi, ∀ j ≠ 0, (y j = lo j ∨ y j = hi j) → R y hi := by
    intro y hy j hj hyj
    set p := Function.update y 0 (hi 0)
    have hpA : p ∈ coordBox lo hi := fun k => by
      by_cases hk : k = 0
      · subst hk; simp only [p, Function.update_self]; exact ⟨hle _, le_rfl⟩
      · simp only [p, Function.update_of_ne hk]; exact hy k
    have hpj : p j = y j := by simp only [p, Function.update_of_ne hj]
    have hp0 : p 0 = hi 0 := by simp only [p, Function.update_self]
    refine htrans y p hi hpA (coordFace_subset hlo hhi hle hyj (mem_coordFace hpA hpj)).2
      (hface j (y j) hyj y (mem_coordFace hy rfl) p (mem_coordFace hpA hpj)) (htop p hpA hp0)
  -- the bottom face, through the face `{y₂ = Dhi₂ + 1}`
  have hall : ∀ y ∈ coordBox lo hi, y ∉ coordBox Dlo Dhi → R y hi := by
    intro y hy hyD
    simp only [coordBox, Set.mem_setOf_eq, not_forall] at hyD
    obtain ⟨i, hi'⟩ := hyD
    have hyi := hy i
    have hloi := hlo i
    have hhii := hhi i
    rcases (show y i = lo i ∨ y i = hi i by omega) with hyl | hyh
    · by_cases hi0 : i = 0
      · subst hi0
        set j : Fin d := ⟨1, by omega⟩
        have hj : j ≠ 0 := fun h => by
          have := congrArg Fin.val h
          simp [j] at this
        set p := Function.update y j (hi j)
        have hpA : p ∈ coordBox lo hi := fun k => by
          by_cases hk : k = j
          · subst hk; simp only [p, Function.update_self]; exact ⟨hle _, le_rfl⟩
          · simp only [p, Function.update_of_ne hk]; exact hy k
        have hp0 : p 0 = y 0 := by simp only [p, Function.update_of_ne hj.symm]
        have hpj : p j = hi j := by simp only [p, Function.update_self]
        exact htrans y p hi hpA
          (coordFace_subset hlo hhi hle (c := lo 0) (Or.inl rfl)
            (mem_coordFace hpA (hp0.trans hyl))).2
          (hface 0 (lo 0) (Or.inl rfl) y (mem_coordFace hy hyl) p
            (mem_coordFace hpA (hp0.trans hyl)))
          (hside p hpA j hj (Or.inr hpj))
      · exact hside y hy i hi0 (Or.inl hyl)
    · by_cases hi0 : i = 0
      · subst hi0; exact htop y hy hyh
      · exact hside y hy i hi0 (Or.inr hyh)
  exact htrans z hi z' hqA hqD (hall z hz hzD)
    (fun a ha b hb => (hall z' hz' hz'D b hb a ha).symm)

/-! ### The altered box `D_x` and its shell `A_x` -/

section Geometry

variable [NeZero d]

/-- Lower corner of `D_x`: `-w` in the horizontal direction, `b_i + w + 1` in the transverse
directions, where `b_i = s ⌊x_i / s⌋` is the corner of the cell of `x`. -/
def alteredLo (s w : ℕ) (x : Vertex d) : Vertex d :=
  fun i => if i = 0 then -(w : ℤ) else s * (x i / s) + w + 1

/-- Upper corner of `D_x`: `w + 1` in the horizontal direction, `b_i + s - 1 + w` in the
transverse directions. -/
def alteredHi (s w : ℕ) (x : Vertex d) : Vertex d :=
  fun i => if i = 0 then (w : ℤ) + 1 else s * (x i / s) + s - 1 + w

/-- Lower corner of the shell box `A_x`. -/
def shellLo (s w : ℕ) (x : Vertex d) : Vertex d := fun i => alteredLo s w x i - 1

/-- Upper corner of the shell box `A_x`. -/
def shellHi (s w : ℕ) (x : Vertex d) : Vertex d := fun i => alteredHi s w x i + 1

/-- For a centre `y ∈ A_x \ D_x`, the cube `y + Q_w` contains no horizontal edge `(y', y' + e₁)`
starting at a removable point `y'` (transverse residues at least `2w + 1` modulo `s`): either `y`
is too far from the centre plane, or `y` lies in a wall of width `2w + 1` between two cells. -/
theorem not_mem_cubeAt_of_shell {s w : ℕ} (hs : 0 < s) {x y y' : Vertex d}
    (hyA : y ∈ coordBox (shellLo s w x) (shellHi s w x))
    (hyD : y ∉ coordBox (alteredLo s w x) (alteredHi s w x)) (hy'0 : y' 0 = 0)
    (hy' : ∀ i ≠ 0, ((2 * w + 1 : ℕ) : ℤ) ≤ y' i % s) (h1 : y' ∈ cubeAt y w)
    (h2 : y' + unit 0 ∈ cubeAt y w) : False := by
  simp only [coordBox, Set.mem_setOf_eq, not_forall] at hyA hyD
  obtain ⟨i, hi⟩ := hyD
  have ha := hyA i
  have c1 := abs_le.mp (h1 i)
  have c2 := abs_le.mp (h2 i)
  by_cases hi0 : i = 0
  · subst hi0
    simp only [shellLo, shellHi, alteredLo, alteredHi, ↓reduceIte] at hi ha
    simp only [Pi.add_apply, unit, Pi.single_eq_same, hy'0] at c1 c2
    omega
  · simp only [shellLo, shellHi, alteredLo, alteredHi, if_neg hi0] at hi ha
    simp only [Pi.add_apply, unit, Pi.single_apply, if_neg hi0, add_zero] at c2
    have hs' : (0 : ℤ) < s := by exact_mod_cast hs
    have hr := Int.emod_add_mul_ediv (y' i) s
    have hr1 := Int.emod_lt_of_pos (y' i) hs'
    have hrt := hy' i hi0
    have hdvd : (s : ℤ) ∣ s * (y' i / s) - s * (x i / s) := ⟨y' i / s - x i / s, by ring⟩
    push_cast at hrt
    rcases (show y i = s * (x i / s) + w ∨ y i = s * (x i / s) + s + w by omega) with hlow | hhigh
    · have hneg : 0 < -(s * (y' i / s) - s * (x i / s)) := by omega
      have := Int.le_of_dvd hneg ((dvd_neg).mpr hdvd)
      omega
    · have hpos : 0 < s * (y' i / s) - s * (x i / s) := by omega
      have := Int.le_of_dvd hpos hdvd
      omega

/-- The shell box `A_x` lies in `x + Q_{s + w + 2}`. -/
theorem abs_sub_le_of_mem_shell {s w : ℕ} (hs : 0 < s) {x z : Vertex d} (hx0 : x 0 = 0)
    (hz : z ∈ coordBox (shellLo s w x) (shellHi s w x)) (i : Fin d) :
    |z i - x i| ≤ (s + w + 2 : ℕ) := by
  have h := hz i
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  have hr := Int.emod_add_mul_ediv (x i) s
  have hr0 := Int.emod_nonneg (x i) hs'.ne'
  have hr1 := Int.emod_lt_of_pos (x i) hs'
  rw [abs_le]
  push_cast
  by_cases hi0 : i = 0
  · subst hi0
    simp only [shellLo, shellHi, alteredLo, alteredHi, ↓reduceIte] at h
    rw [hx0]
    constructor <;> omega
  · simp only [shellLo, shellHi, alteredLo, alteredHi, if_neg hi0] at h
    constructor <;> omega

/-- `D_x ⊆ A_x`. -/
theorem altered_subset_shell {s w : ℕ} {x : Vertex d} :
    coordBox (alteredLo s w x) (alteredHi s w x) ⊆ coordBox (shellLo s w x) (shellHi s w x) :=
  fun y hy i => by
    have := hy i
    simp only [shellLo, shellHi]
    omega

/-- A lattice neighbour of a point of `D_x` lies in `A_x`. -/
theorem mem_shell_of_adj {s w : ℕ} {x y y' : Vertex d}
    (hy : y ∈ coordBox (alteredLo s w x) (alteredHi s w x))
    (h : (nearestNeighborGraph d).Adj y y') :
    y' ∈ coordBox (shellLo s w x) (shellHi s w x) := fun i => by
  have h1 := hy i
  have h2 := abs_le.mp (abs_coord_sub_le_one_of_adj h i)
  simp only [shellLo, shellHi]
  omega

/-- The endpoints `x` and `x + e₁` of a removable edge lie in `D_x`. -/
theorem mem_altered {s w : ℕ} (hs : 0 < s) {x v : Vertex d}
    (hxi : ∀ i ≠ 0, ((2 * w + 1 : ℕ) : ℤ) ≤ x i % s) (hv0 : v 0 = 0 ∨ v 0 = 1)
    (hvi : ∀ i ≠ 0, v i = x i) : v ∈ coordBox (alteredLo s w x) (alteredHi s w x) := fun i => by
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  have hr := Int.emod_add_mul_ediv (x i) s
  have hr1 := Int.emod_lt_of_pos (x i) hs'
  by_cases hi0 : i = 0
  · subst hi0
    simp only [alteredLo, alteredHi, ↓reduceIte]
    omega
  · simp only [alteredLo, alteredHi, if_neg hi0]
    have := hxi i hi0
    have := hvi i hi0
    push_cast at *
    omega

/-- **Short path around a removed horizontal edge.** Let `x` be a removable point (`x₁ = 0`,
transverse residues at least `2w + 1` modulo `s`), and close a set `B` of horizontal edges at
removable points. If every cube `z + Q_w` centred in `A_x` is a good subcube of `ω` and `x`,
`x + e₁` lie in an infinite cluster of the modified environment, then they are joined by open
edges of the modified environment inside `x + Q_{s + 2w + 2}`. -/
theorem reachable_center_of_isGoodSubcube (hd : 2 ≤ d) {ω : Configuration d}
    {B : Finset (Bond d)} {s w : ℕ} (hs : 0 < s) (hw : 1 ≤ w) {x : Vertex d} (hx0 : x 0 = 0)
    (hxi : ∀ i ≠ 0, ((2 * w + 1 : ℕ) : ℤ) ≤ x i % s)
    (hB : ∀ e ∈ B, ∃ y', y' 0 = 0 ∧ (∀ i ≠ 0, ((2 * w + 1 : ℕ) : ℤ) ≤ y' i % s) ∧
      e = centerBond y')
    (hgood : ∀ z ∈ coordBox (shellLo s w x) (shellHi s w x), IsGoodSubcube ω z w)
    (C' : OpenComponent (closeBonds B ω)) (hC' : C'.supp.Infinite) (hx : x ∈ C'.supp)
    (hy : x + unit 0 ∈ C'.supp) :
    (openIn (closeBonds B ω) (cubeAt x (s + 2 * w + 2))).Reachable x (x + unit 0) := by
  classical
  set W := cubeAt x (s + 2 * w + 2)
  set A := coordBox (shellLo s w x) (shellHi s w x)
  set D := coordBox (alteredLo s w x) (alteredHi s w x)
  let V : Vertex d → Set (Vertex d) := fun z =>
    if h : IsGoodSubcube ω z w then Classical.choose h else ∅
  have hVz : ∀ z ∈ A, IsGoodCluster ω z w (V z) := fun z hz => by
    simp only [V, dif_pos (hgood z hz)]
    exact Classical.choose_spec (hgood z hz)
  have hAW' : ∀ z ∈ A, cubeAt z w ⊆ W := fun z hz y hy i => by
    have h1 := abs_le.mp (abs_sub_le_of_mem_shell hs hx0 hz i)
    have h2 := abs_le.mp (hy i)
    push_cast at h1 h2 ⊢
    rw [abs_le]
    constructor <;> omega
  have hAW : A ⊆ W := fun z hz => hAW' z hz (fun i => by simp)
  have hG : ∀ z ∈ A, z ∉ D → IsGoodCluster (closeBonds B ω) z w (V z) ∧ cubeAt z w ⊆ W := by
    intro z hz hzD
    refine ⟨isGoodCluster_closeBonds (fun e he hcube => ?_) (hVz z hz), hAW' z hz⟩
    obtain ⟨y', hy'0, hy', rfl⟩ := hB e he
    exact not_mem_cubeAt_of_shell hs hz hzD hy'0 hy'
      (hcube y' (Sym2.mem_mk_left _ _)) (hcube (y' + unit 0) (Sym2.mem_mk_right _ _))
  -- a point of `C'` far away
  obtain ⟨u, huC, huW⟩ : ∃ u ∈ C'.supp, u ∉ W := (hC'.sdiff (finite_cubeAt x _)).nonempty
  have huD : u ∉ D := fun h => huW (hAW (altered_subset_shell h))
  -- leaving `D_x` from a vertex of `C'` in `D_x`
  have hexit : ∀ v ∈ D, v ∈ C'.supp →
      ∃ z ∈ A, z ∉ D ∧ (openIn (closeBonds B ω) W).Reachable v z ∧ z ∈ V z := by
    intro v hvD hvC
    have hvu : (openGraph (closeBonds B ω)).Reachable v u :=
      SimpleGraph.ConnectedComponent.exact
        (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hvC).trans
          ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp huC).symm)
    obtain ⟨q⟩ := hvu
    obtain ⟨z, hzA, hzD, hvz⟩ := exists_exit_reachable (fun y hy => hAW (altered_subset_shell hy))
      hAW (fun y y' hy hadj => mem_shell_of_adj hy (openGraph_le (closeBonds B ω) hadj)) q hvD huD
    refine ⟨z, hzA, hzD, hvz, mem_of_isGoodCluster_of_infinite (hG z hzA hzD).1 ?_⟩
    have hmk : (openGraph (closeBonds B ω)).connectedComponentMk z = C' :=
      (SimpleGraph.ConnectedComponent.sound (hvz.mono (openIn_le (closeBonds B ω) W))).symm.trans hvC
    rw [hmk]
    exact hC'
  have hle : ∀ i, shellLo s w x i ≤ shellHi s w x i := fun i => by
    by_cases hi0 : i = 0
    · subst hi0
      simp only [shellLo, shellHi, alteredLo, alteredHi, ↓reduceIte]
      omega
    · simp only [shellLo, shellHi, alteredLo, alteredHi, if_neg hi0]
      omega
  obtain ⟨z₁, hz₁A, hz₁D, hxz₁, hz₁V⟩ :=
    hexit x (mem_altered hs hxi (Or.inl hx0) fun _ _ => rfl) hx
  obtain ⟨z₂, hz₂A, hz₂D, hxz₂, hz₂V⟩ := hexit (x + unit 0)
    (mem_altered hs hxi (Or.inr (by simp [unit, hx0]))
      fun i hi => by simp [unit, hi]) hy
  exact hxz₁.trans ((reachable_of_shell hd hw V (fun _ => rfl) (fun _ => rfl) hle hG hz₁A hz₁D
    hz₂A hz₂D z₁ hz₁V z₂ hz₂V).trans hxz₂.symm)

end Geometry

/-! ### The removable horizontal edges and the count of the remaining ones -/

/-- Integers `a ∈ [-N, N]` with `N < |a| + y`: at most `2y + 2` of them. -/
theorem card_filter_lt_abs_add_le (N : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ((((Finset.Icc (-(N : ℤ)) N).filter fun a => (N : ℝ) < ((|a| : ℤ) : ℝ) + y).card : ℕ) : ℝ)
      ≤ 2 * y + 2 := by
  set m := ⌊y⌋₊
  have hm : y < m + 1 := Nat.lt_floor_add_one y
  have hmy : (m : ℝ) ≤ y := Nat.floor_le hy
  have hsub : ((Finset.Icc (-(N : ℤ)) N).filter fun a => (N : ℝ) < ((|a| : ℤ) : ℝ) + y) ⊆
      Finset.Icc (-(N : ℤ)) (-N + m) ∪ Finset.Icc ((N : ℤ) - m) N := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    simp only [Finset.mem_union, Finset.mem_Icc]
    obtain ⟨⟨h1, h2⟩, h3⟩ := ha
    rcases le_or_gt 0 a with h0 | h0
    · refine Or.inr ⟨?_, h2⟩
      by_contra hc
      have h4 : a + m + 1 ≤ N := by omega
      have h5 : ((a + m + 1 : ℤ) : ℝ) ≤ N := by exact_mod_cast h4
      rw [abs_of_nonneg h0] at h3
      push_cast at h5
      linarith
    · refine Or.inl ⟨h1, ?_⟩
      by_contra hc
      have h4 : -a + m + 1 ≤ N := by omega
      have h5 : ((-a + m + 1 : ℤ) : ℝ) ≤ N := by exact_mod_cast h4
      rw [abs_of_neg h0] at h3
      push_cast at h5 h3
      linarith
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simp only [Int.card_Icc] at hcard
  have e1 : (-(N : ℤ) + m + 1 - -(N : ℤ)).toNat = m + 1 := by omega
  have e2 : ((N : ℤ) + 1 - (N - m)).toNat = m + 1 := by omega
  rw [e1, e2] at hcard
  have hc : ((((Finset.Icc (-(N : ℤ)) N).filter fun a =>
      (N : ℝ) < ((|a| : ℤ) : ℝ) + y).card : ℕ) : ℝ) ≤ (m : ℝ) + 1 + ((m : ℝ) + 1) := by
    exact_mod_cast hcard
  linarith

/-- Integers `a ∈ [-N, N]` with residue less than `t` modulo `s`: at most `t (2N + 2s) / s`. -/
theorem card_filter_emod_lt_mul_le (N s t : ℕ) (hs : 0 < s) :
    ((Finset.Icc (-(N : ℤ)) N).filter fun a => a % (s : ℤ) < t).card * s ≤
      t * (2 * N + 2 * s) := by
  set T := (Finset.Icc (-(N : ℤ)) N).filter fun a => a % (s : ℤ) < t
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  have h1 : T.card ≤ t * (T.image fun a => a / (s : ℤ)).card := by
    apply Finset.card_le_mul_card_image
    intro q _
    calc _ ≤ (Finset.range t).card := by
          apply Finset.card_le_card_of_injOn (fun a => (a % (s : ℤ)).toNat)
          · intro a ha
            simp only [T, Finset.mem_filter, Finset.coe_filter, Set.mem_setOf_eq] at ha
            simp only [Finset.coe_range, Set.mem_Iio]
            have := Int.emod_nonneg a hs'.ne'
            omega
          · intro a ha b hb hab
            simp only [T, Finset.mem_filter, Finset.coe_filter, Set.mem_setOf_eq] at ha hb
            have ha' := Int.emod_add_mul_ediv a s
            have hb' := Int.emod_add_mul_ediv b s
            have h0a := Int.emod_nonneg a hs'.ne'
            have h0b := Int.emod_nonneg b hs'.ne'
            simp only at hab
            rw [ha.2, hb.2] at *
            omega
      _ = t := Finset.card_range t
  have h2 : (T.image fun a => a / (s : ℤ)) ⊆ Finset.Icc ((-(N : ℤ)) / s) ((N : ℤ) / s) := by
    intro q hq
    simp only [Finset.mem_image] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    have := (Finset.mem_filter.mp ha).1
    rw [Finset.mem_Icc] at this
    exact Finset.mem_Icc.mpr ⟨Int.ediv_le_ediv hs' this.1, Int.ediv_le_ediv hs' this.2⟩
  have h3 := Finset.card_le_card h2
  rw [Int.card_Icc] at h3
  have q1 := Int.emod_add_mul_ediv (N : ℤ) s
  have q2 := Int.emod_add_mul_ediv (-(N : ℤ)) s
  have r1 := Int.emod_nonneg (N : ℤ) hs'.ne'
  have r2 := Int.emod_lt_of_pos (-(N : ℤ)) hs'
  have hmono : (-(N : ℤ)) / s ≤ (N : ℤ) / s := Int.ediv_le_ediv hs' (by omega)
  have h4 : (((T.image fun a => a / (s : ℤ)).card : ℕ) : ℤ) ≤ (N : ℤ) / s + 1 - (-(N : ℤ)) / s := by
    have := Int.toNat_of_nonneg (show 0 ≤ (N : ℤ) / s + 1 - (-(N : ℤ)) / s by omega)
    omega
  have h5 : (((T.image fun a => a / (s : ℤ)).card * s : ℕ) : ℤ) ≤ ((2 * N + 2 * s : ℕ) : ℤ) := by
    push_cast
    have e : ((N : ℤ) / s + 1 - (-(N : ℤ)) / s) * s = s * ((N : ℤ) / s) + s - s * ((-(N : ℤ)) / s) := by
      ring
    nlinarith
  have h6 : (T.image fun a => a / (s : ℤ)).card * s ≤ 2 * N + 2 * s := by exact_mod_cast h5
  calc T.card * s ≤ t * (T.image fun a => a / (s : ℤ)).card * s := Nat.mul_le_mul_right _ h1
    _ = t * ((T.image fun a => a / (s : ℤ)).card * s) := by ring
    _ ≤ t * (2 * N + 2 * s) := Nat.mul_le_mul_left _ h6

section Count

variable [NeZero d]

/-- The centre points of `Q_N` whose `i`-th coordinate (`i ≠ 0`) satisfies `P`: at most
`(2N + 1)^{d-2}` times the number of `a ∈ [-N, N]` satisfying `P`. -/
theorem card_filter_centerFace_le {N : ℕ} {i : Fin d} (hi : i ≠ 0) (P : ℤ → Prop)
    [DecidablePred P] :
    ((centerFace d N).filter fun x => P (x i)).card ≤
      (2 * N + 1) ^ (d - 2) * ((Finset.Icc (-(N : ℤ)) N).filter P).card := by
  classical
  let f : Fin d → Finset ℤ := fun j =>
    if j = 0 then {0} else if j = i then (Finset.Icc (-(N : ℤ)) N).filter P
    else Finset.Icc (-(N : ℤ)) N
  have hsub : ((centerFace d N).filter fun x => P (x i)) ⊆ Fintype.piFinset f := by
    intro x hx
    simp only [centerFace, latticeCube, Finset.mem_filter, Fintype.mem_piFinset] at hx
    rw [Fintype.mem_piFinset]
    intro j
    simp only [f]
    split_ifs with h0 hji
    · subst h0; simp [hx.1.2]
    · subst hji; exact Finset.mem_filter.mpr ⟨hx.1.1 j, hx.2⟩
    · exact hx.1.1 j
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  have h0 : (0 : Fin d) ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hi.symm, Finset.mem_univ _⟩
  rw [Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ h0]
  have hrest : ∀ j ∈ (Finset.univ.erase i).erase 0, (f j).card = 2 * N + 1 := by
    intro j hj
    obtain ⟨hj0, hj'⟩ := Finset.mem_erase.mp hj
    have hji := Finset.ne_of_mem_erase hj'
    simp only [f, if_neg hj0, if_neg hji, Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl hrest, Finset.prod_const]
  have hcard : ((Finset.univ.erase i).erase (0 : Fin d)).card = d - 2 := by
    rw [Finset.card_erase_of_mem h0, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
    omega
  simp only [f, hcard, if_neg hi, ↓reduceIte, Finset.card_singleton]
  ring

/-- The removable points: the centre points of `Q_{N - N^{1/d}}` whose transverse coordinates have
residues at least `2w + 1` modulo `s`, i.e. which lie outside the walls (boundary layers of small
blue cubes) of the cells of side `s`. -/
noncomputable def removablePoints (d N s w : ℕ) [NeZero d] : Finset (Vertex d) :=
  (centerInner d N).filter fun y => ∀ i : Fin d, i ≠ 0 → ((2 * w + 1 : ℕ) : ℤ) ≤ y i % (s : ℤ)

/-- The removable horizontal edges `H_N`: the edges `(y, y + e₁)` at removable points `y`. -/
noncomputable def removableBonds (d N s w : ℕ) [NeZero d] : Finset (Bond d) :=
  (removablePoints d N s w).image centerBond

theorem centerBond_mem_removableBonds {N s w : ℕ} {x : Vertex d} :
    centerBond x ∈ removableBonds d N s w ↔ x ∈ removablePoints d N s w :=
  centerBond_injective.mem_finset_image

/-- The centre points of `Q_N` that are not removable: at most
`(d - 1)(2N + 1)^{d-2} (2N^{1/d} + 2 + (2w + 1)(2N + 2s)/s)`. -/
theorem card_kept_le (hd : 2 ≤ d) (N s w : ℕ) (hs : 0 < s) :
    ((((centerFace d N).filter fun x => centerBond x ∉ removableBonds d N s w).card : ℕ) : ℝ) ≤
      ((d : ℝ) - 1) * (2 * (N : ℝ) + 1) ^ (d - 2) * (2 * (N : ℝ) ^ (1 / (d : ℝ)) + 2 +
        (2 * (w : ℝ) + 1) * (2 * N + 2 * s) / s) := by
  classical
  let Bad : ℤ → Prop := fun a =>
    (N : ℝ) < ((|a| : ℤ) : ℝ) + (N : ℝ) ^ (1 / (d : ℝ)) ∨ a % (s : ℤ) < ((2 * w + 1 : ℕ) : ℤ)
  have hsub : ((centerFace d N).filter fun x => centerBond x ∉ removableBonds d N s w) ⊆
      (Finset.univ.erase (0 : Fin d)).biUnion fun i =>
        (centerFace d N).filter fun x => Bad (x i) := by
    intro x hx
    obtain ⟨hxF, hxR⟩ := Finset.mem_filter.mp hx
    rw [centerBond_mem_removableBonds] at hxR
    by_contra hcon
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_filter, not_exists, not_and] at hcon
    apply hxR
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxF, fun i hi => ?_⟩, fun i hi => ?_⟩
    · have := hcon i hi hxF
      simp only [Bad, not_or, not_lt] at this
      exact this.1
    · have := hcon i hi hxF
      simp only [Bad, not_or, not_lt] at this
      exact this.2
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hterm : ∀ i ∈ Finset.univ.erase (0 : Fin d),
      ((centerFace d N).filter fun x => Bad (x i)).card ≤
        (2 * N + 1) ^ (d - 2) * ((Finset.Icc (-(N : ℤ)) N).filter Bad).card :=
    fun i hi => card_filter_centerFace_le (Finset.ne_of_mem_erase hi) Bad
  have hsum := (Finset.sum_le_sum hterm).trans_eq' rfl
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum
  have hT : ((Finset.Icc (-(N : ℤ)) N).filter Bad).card ≤
      ((Finset.Icc (-(N : ℤ)) N).filter fun a =>
        (N : ℝ) < ((|a| : ℤ) : ℝ) + (N : ℝ) ^ (1 / (d : ℝ))).card +
      ((Finset.Icc (-(N : ℤ)) N).filter fun a => a % (s : ℤ) < ((2 * w + 1 : ℕ) : ℤ)).card := by
    simp only [Bad]
    rw [Finset.filter_or]
    exact Finset.card_union_le _ _
  have h1 := card_filter_lt_abs_add_le N (Real.rpow_nonneg (Nat.cast_nonneg N) (1 / (d : ℝ)))
  have h2 := card_filter_emod_lt_mul_le N s (2 * w + 1) hs
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h2' : ((((Finset.Icc (-(N : ℤ)) N).filter fun a =>
      a % (s : ℤ) < ((2 * w + 1 : ℕ) : ℤ)).card : ℕ) : ℝ) ≤
      (2 * (w : ℝ) + 1) * (2 * N + 2 * s) / s := by
    rw [le_div_iff₀ hs']
    exact_mod_cast h2
  have hT' : ((((Finset.Icc (-(N : ℤ)) N).filter Bad).card : ℕ) : ℝ) ≤
      2 * (N : ℝ) ^ (1 / (d : ℝ)) + 2 + (2 * (w : ℝ) + 1) * (2 * N + 2 * s) / s := by
    have : ((((Finset.Icc (-(N : ℤ)) N).filter Bad).card : ℕ) : ℝ) ≤
        ((((Finset.Icc (-(N : ℤ)) N).filter fun a =>
          (N : ℝ) < ((|a| : ℤ) : ℝ) + (N : ℝ) ^ (1 / (d : ℝ))).card : ℕ) : ℝ) +
        ((((Finset.Icc (-(N : ℤ)) N).filter fun a =>
          a % (s : ℤ) < ((2 * w + 1 : ℕ) : ℤ)).card : ℕ) : ℝ) := by
      exact_mod_cast hT
    linarith
  have htot : ((((centerFace d N).filter fun x => centerBond x ∉ removableBonds d N s w).card
      : ℕ) : ℝ) ≤ ((d - 1 : ℕ) : ℝ) * (((2 * N + 1) ^ (d - 2) : ℕ) : ℝ) *
        ((((Finset.Icc (-(N : ℤ)) N).filter Bad).card : ℕ) : ℝ) := by
    have := hcard.trans hsum
    rw [← mul_assoc] at this
    exact_mod_cast this
  have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hd1] at htot
  push_cast at htot
  refine htot.trans (mul_le_mul_of_nonneg_left hT' ?_)
  have : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have : (0 : ℝ) ≤ d - 1 := by linarith
  positivity

end Count

/-! ### The scales `s = ⌊N^{1/(10d)}⌋` and `w = ⌈N^{1/(10d)²}⌉` -/

/-- The side `s = ⌊N^{1/(10d)}⌋` of the cells (the medium cubes). -/
noncomputable def cellSide (d N : ℕ) : ℕ := ⌊(N : ℝ) ^ (1 / (10 * (d : ℝ)))⌋₊

/-- The radius `w = ⌈N^{1/(10d)²}⌉` of the small cubes. -/
noncomputable def smallRadius (d N : ℕ) : ℕ := ⌈(N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2)⌉₊

theorem scale_bounds (hd : 2 ≤ d) {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ cellSide d N ∧ 1 ≤ smallRadius d N ∧
    (cellSide d N : ℝ) ≤ (N : ℝ) ^ (1 / (10 * (d : ℝ))) ∧
    (N : ℝ) ^ (1 / (10 * (d : ℝ))) ≤ 2 * cellSide d N ∧
    (N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) ≤ smallRadius d N ∧
    (smallRadius d N : ℝ) ≤ (N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) + 1 ∧
    1 ≤ (N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) ∧
    (N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) ≤ (N : ℝ) ^ (1 / (10 * (d : ℝ))) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hα : (0 : ℝ) ≤ 1 / (10 * (d : ℝ)) := by positivity
  have hδ : (0 : ℝ) ≤ 1 / (10 * (d : ℝ)) ^ 2 := by positivity
  have hδα : 1 / (10 * (d : ℝ)) ^ 2 ≤ 1 / (10 * (d : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have ha1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / (10 * (d : ℝ))) := Real.one_le_rpow hN' hα
  have hb1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) := Real.one_le_rpow hN' hδ
  have hs1 : 1 ≤ cellSide d N := Nat.le_floor (by simpa using ha1)
  have hfl := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / (10 * (d : ℝ))))
  have hs1' : (1 : ℝ) ≤ cellSide d N := by exact_mod_cast hs1
  refine ⟨hs1, ?_, Nat.floor_le (by linarith), ?_, Nat.le_ceil _,
    (Nat.ceil_lt_add_one (by linarith)).le, hb1,
    Real.rpow_le_rpow_of_exponent_le hN' hδα⟩
  · have := Nat.le_ceil ((N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2))
    have h : (1 : ℝ) ≤ smallRadius d N := hb1.trans this
    exact_mod_cast h
  · unfold cellSide at hs1' ⊢
    linarith

/-- `(2(s + 2w + 2) + 1)^d ≤ 15^d N^{1/10} ≤ 15^d N^{1/2}`. -/
theorem pow_shell_le (hd : 2 ≤ d) {N : ℕ} (hN : 1 ≤ N) :
    (((2 * (cellSide d N + 2 * smallRadius d N + 2) + 1) ^ d : ℕ) : ℝ) ≤
      15 ^ d * (N : ℝ) ^ (1 / 2 : ℝ) := by
  obtain ⟨-, -, hs, -, -, hw, -, hba⟩ := scale_bounds hd hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ha1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / (10 * (d : ℝ))) :=
    Real.one_le_rpow hN' (by positivity)
  have h1 : ((2 * (cellSide d N + 2 * smallRadius d N + 2) + 1 : ℕ) : ℝ) ≤
      15 * (N : ℝ) ^ (1 / (10 * (d : ℝ))) := by
    push_cast
    linarith
  have hd0 : (d : ℝ) ≠ 0 := by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                               linarith
  calc (((2 * (cellSide d N + 2 * smallRadius d N + 2) + 1) ^ d : ℕ) : ℝ)
      ≤ (15 * (N : ℝ) ^ (1 / (10 * (d : ℝ)))) ^ d := by
        push_cast at h1 ⊢
        exact pow_le_pow_left₀ (by positivity) h1 d
    _ = 15 ^ d * (N : ℝ) ^ (1 / 10 : ℝ) := by
        rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
        congr 2
        field_simp
    _ ≤ 15 ^ d * (N : ℝ) ^ (1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN' (by norm_num))
          (by positivity)

/-- Eventually `s + w + 2 ≤ N^{1/d}`: the shell boxes around removable points stay in `Q_N`. -/
theorem eventually_scale_le_rpow (hd : 2 ≤ d) : ∀ᶠ N : ℕ in atTop,
    (cellSide d N : ℝ) + smallRadius d N + 2 ≤ (N : ℝ) ^ (1 / (d : ℝ)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : 0 < 1 / (d : ℝ) - 1 / (10 * (d : ℝ)) := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have ht := (tendsto_rpow_atTop hpos).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop 5, eventually_ge_atTop 1] with N h5 hN
  obtain ⟨-, -, hs, -, -, hw, -, hba⟩ := scale_bounds hd hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have ha1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / (10 * (d : ℝ))) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  simp only [Function.comp_apply] at h5
  have hsplit : (N : ℝ) ^ (1 / (d : ℝ)) = (N : ℝ) ^ (1 / (10 * (d : ℝ))) *
      (N : ℝ) ^ (1 / (d : ℝ) - 1 / (10 * (d : ℝ))) := by
    rw [← Real.rpow_add hN']
    ring_nf
  rw [hsplit]
  nlinarith

/-- The count of the non-removable centre points, eq. (horizontal-flux-small):
`(d - 1)(2N + 1)^{d-2}(2N^{1/d} + 2 + (2w + 1)(2N + 2s)/s) ≤ 34 d 3^{d-2} N^{d-1-1/(10d)+1/(10d)²}`. -/
theorem count_bound_le (hd : 2 ≤ d) {N : ℕ} (hN : 1 ≤ N) :
    ((d : ℝ) - 1) * (2 * (N : ℝ) + 1) ^ (d - 2) * (2 * (N : ℝ) ^ (1 / (d : ℝ)) + 2 +
      (2 * (smallRadius d N : ℝ) + 1) * (2 * N + 2 * cellSide d N) / cellSide d N) ≤
    34 * d * 3 ^ (d - 2) *
      (N : ℝ) ^ ((d : ℝ) - 1 - 1 / (10 * (d : ℝ)) + 1 / (10 * (d : ℝ)) ^ 2) := by
  obtain ⟨-, -, -, hs2, -, hw, hb1, hba⟩ := scale_bounds hd hN
  set α := 1 / (10 * (d : ℝ))
  set δ := 1 / (10 * (d : ℝ)) ^ 2
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hα : 0 ≤ α := by positivity
  have hα1 : α ≤ 1 / 20 := by
    simp only [α]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hδ0 : 0 ≤ δ := by positivity
  have ha1 : (1 : ℝ) ≤ (N : ℝ) ^ α := Real.one_le_rpow hN1 hα
  set a := (N : ℝ) ^ α
  set b := (N : ℝ) ^ δ
  set s := (cellSide d N : ℝ)
  set w := (smallRadius d N : ℝ)
  have hs0 : 0 < s := by linarith
  -- the exponent `1 - α + δ`
  have hc1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 - α) := Real.one_le_rpow hN1 (by linarith)
  have hNa : (N : ℝ) / a = (N : ℝ) ^ (1 - α) := by
    rw [Real.rpow_sub hN0, Real.rpow_one]
  have hprod : b * (N : ℝ) ^ (1 - α) = (N : ℝ) ^ (1 - α + δ) := by
    rw [Real.rpow_add hN0, mul_comm]
  have hdinv : (1 : ℝ) / d ≤ 1 - α + δ := by
    have : (1 : ℝ) / d ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hroot : (N : ℝ) ^ (1 / (d : ℝ)) ≤ (N : ℝ) ^ (1 - α + δ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hdinv
  have hroot1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / (d : ℝ)) := Real.one_le_rpow hN1 (by positivity)
  -- `(2N + 2s)/s ≤ 6 N^{1-α}`
  have hfrac : (2 * (N : ℝ) + 2 * s) / s ≤ 6 * (N : ℝ) ^ (1 - α) := by
    rw [div_le_iff₀ hs0]
    have : (N : ℝ) ≤ s * (2 * (N : ℝ) ^ (1 - α)) := by
      rw [← hNa]
      have : (N : ℝ) / a * a = N := div_mul_cancel₀ _ (by linarith)
      nlinarith [div_nonneg hN0.le (show (0 : ℝ) ≤ a by linarith)]
    nlinarith
  have hinner : 2 * (N : ℝ) ^ (1 / (d : ℝ)) + 2 + (2 * w + 1) * (2 * N + 2 * s) / s ≤
      34 * (N : ℝ) ^ (1 - α + δ) := by
    have h5 : 2 * w + 1 ≤ 5 * b := by linarith
    have : (2 * w + 1) * (2 * N + 2 * s) / s ≤ 5 * b * (6 * (N : ℝ) ^ (1 - α)) := by
      rw [mul_div_assoc]
      exact mul_le_mul h5 hfrac (div_nonneg (by positivity) hs0.le) (by positivity)
    nlinarith
  have hpow : (2 * (N : ℝ) + 1) ^ (d - 2) ≤ 3 ^ (d - 2) * (N : ℝ) ^ (d - 2) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hsplit : (N : ℝ) ^ ((d : ℝ) - 1 - α + δ) = (N : ℝ) ^ (d - 2) * (N : ℝ) ^ (1 - α + δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN0, Nat.cast_sub hd]
    push_cast
    ring_nf
  rw [hsplit]
  calc ((d : ℝ) - 1) * (2 * (N : ℝ) + 1) ^ (d - 2) *
        (2 * (N : ℝ) ^ (1 / (d : ℝ)) + 2 + (2 * w + 1) * (2 * N + 2 * s) / s)
      ≤ (d : ℝ) * (3 ^ (d - 2) * (N : ℝ) ^ (d - 2)) * (34 * (N : ℝ) ^ (1 - α + δ)) := by
        apply mul_le_mul (mul_le_mul (by linarith) hpow (by positivity) (by positivity)) hinner
          (by positivity) (by positivity)
    _ = 34 * d * 3 ^ (d - 2) * ((N : ℝ) ^ (d - 2) * (N : ℝ) ^ (1 - α + δ)) := by ring

/-! ### `step:3.2-short-paths` -/

/-- **`step:3.2-short-paths`** (corrected draft L986-1062, eqs. (short-paths) and
(horizontal-flux-small)), with `H_N = removableBonds d N s w`, `s = ⌊N^{1/(10d)}⌋`,
`w = ⌈N^{1/(10d)²}⌉` and `K = 34 d 15^d`. -/
theorem shortPathsStep (d : ℕ) [NeZero d] : ShortPathsStep d := by
  intro hd
  refine ⟨34 * d * 15 ^ d, by positivity,
    fun N => removableBonds d N (cellSide d N) (smallRadius d N), ?_⟩
  filter_upwards [eventually_ge_atTop 12, eventually_scale_le_rpow hd] with N hN12 hscale
  have hN : 1 ≤ N := by omega
  obtain ⟨hs1, hw1, -, -, hwlo, hwhi, -, -⟩ := scale_bounds hd hN
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hK : (1 : ℝ) ≤ 34 * d := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩
  · refine (card_kept_le hd N _ _ hs1).trans ((count_bound_le hd hN).trans ?_)
    have h3 : (3 : ℝ) ^ (d - 2) ≤ 15 ^ d :=
      (pow_le_pow_left₀ (by norm_num) (by norm_num) _).trans
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le d 2))
    have := Real.rpow_nonneg (Nat.cast_nonneg N)
      ((d : ℝ) - 1 - 1 / (10 * (d : ℝ)) + 1 / (10 * (d : ℝ)) ^ 2)
    gcongr
  · intro ω hwc C hCinf B hBH hBC hBconn x hxB C' hx hy
    set s := cellSide d N
    set w := smallRadius d N
    have hxR : x ∈ removablePoints d N s w := centerBond_mem_removableBonds.mp (hBH hxB)
    obtain ⟨hxI, hxi⟩ := Finset.mem_filter.mp hxR
    obtain ⟨hxF, hxbd⟩ := Finset.mem_filter.mp hxI
    have hx0 : x 0 = 0 := (Finset.mem_filter.mp hxF).2
    have hB' : ∀ e ∈ B, ∃ y', y' 0 = 0 ∧ (∀ i ≠ 0, ((2 * w + 1 : ℕ) : ℤ) ≤ y' i % s) ∧
        e = centerBond y' := by
      intro e he
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp (hBH he)
      obtain ⟨hy'I, hy'i⟩ := Finset.mem_filter.mp hy'
      exact ⟨y', (Finset.mem_filter.mp (Finset.mem_filter.mp hy'I).1).2, hy'i, rfl⟩
    -- every cube `z + Q_w` centred in the shell box is a good subcube
    obtain ⟨hsmall, -, hgoodN⟩ := hwc
    have hN' : (12 : ℝ) ≤ N := by exact_mod_cast hN12
    have hroot : (N : ℝ) ^ (1 / (d : ℝ)) ≤ N := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ N by linarith)
        (show 1 / (d : ℝ) ≤ 1 by rw [div_le_one (by linarith)]; exact hd1)
      rwa [Real.rpow_one] at this
    have hgood : ∀ z ∈ coordBox (shellLo s w x) (shellHi s w x), IsGoodSubcube ω z w := by
      intro z hz
      have hδ := Real.rpow_nonneg (Nat.cast_nonneg N) (1 / (10 * (d : ℝ)) ^ 2)
      refine hgoodN z w (by linarith) (by linarith) ⟨z, fun i => by simp, fun i => ?_⟩
      have h1 := abs_sub_le_of_mem_shell hs1 hx0 hz i
      have h1' : ((|z i - x i| : ℤ) : ℝ) ≤ (s : ℝ) + w + 2 := by exact_mod_cast h1
      have h2 : ((|z i| : ℤ) : ℝ) ≤ ((|z i - x i| : ℤ) : ℝ) + ((|x i| : ℤ) : ℝ) := by
        have := abs_sub_abs_le_abs_sub (z i) (x i)
        have : |z i| ≤ |z i - x i| + |x i| := by linarith
        exact_mod_cast this
      have h3 : ((|z i| : ℤ) : ℝ) ≤ N := by
        by_cases hi0 : i = 0
        · subst hi0
          rw [hx0, sub_zero] at h1'
          linarith
        · have := hxbd i hi0
          linarith
      simp only [Pi.zero_apply, sub_zero]
      exact_mod_cast h3
    -- the modified cluster `C'` contains `C`, hence is infinite
    have hxC : x ∈ C.supp := (hBC _ hxB).2 x (Sym2.mem_mk_left _ _)
    have hCsub : C.supp ⊆ C'.supp := fun y hyC =>
      (SimpleGraph.ConnectedComponent.sound (hBconn x hxC y hyC)).symm.trans hx
    have hreach := reachable_center_of_isGoodSubcube hd hs1 hw1 hx0 hxi hB' hgood C'
      (hCinf.mono hCsub) hx hy
    obtain ⟨q, hq⟩ := exists_walk_length_lt_of_reachable_openIn
      (fun i => by simp only [sub_self, abs_zero]; positivity) hreach
    have hdist := componentGraph_dist_le C' ⟨x, hx⟩ ⟨x + unit 0, hy⟩ q
    have h15 := pow_shell_le hd hN
    have hdist' : (((componentGraph C').dist ⟨x, hx⟩ ⟨x + unit 0, hy⟩ : ℕ) : ℝ) ≤
        (((2 * (s + 2 * w + 2) + 1) ^ d : ℕ) : ℝ) := by
      exact_mod_cast hdist.trans hq.le
    refine hdist'.trans (h15.trans ?_)
    have := Real.rpow_nonneg (Nat.cast_nonneg N) (1 / 2 : ℝ)
    have : (0 : ℝ) ≤ 15 ^ d * (N : ℝ) ^ (1 / 2 : ℝ) := by positivity
    nlinarith

end Rigidity.Proofs.S3
