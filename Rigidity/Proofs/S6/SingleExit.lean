import Rigidity.Steps.S6.SlowMixing
import Rigidity.External.WellConnected
import LatticeProb.Prob.Percolation.FiniteCylinder
import LatticeProb.Prob.Percolation.LatticeBondProbability
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Section 6: a site of the largest box cluster with a single exit

`SingleExitStep` (repair of the gap of step:6.5-upper, paper L2948-2951 of the corrected draft;
not in the paper): almost surely, for every large `n`, every largest open cluster `V` of
`Q_n = [-n, n]^d` contains a site with exactly one open edge leaving `V`.

Route. Let `F` be the sites `y` of the face `{y_0 = n}` of `Q_n` with `|y_i| < n` for `i ≠ 0`.
The only lattice neighbour of `y ∈ F` outside `Q_n` is `y + e_0`, and the open neighbours of
`y ∈ V` inside `Q_n` lie in `V`; so `y ∈ V ∩ F` is a single-exit site as soon as the bond
`{y, y + e_0}` is open.

* Geometry (Proposition 2.3, `Rigidity.External.WellConnectedInput`). If `Q_n` is well-connected,
  every cube of radius `m` or `2m` meeting `Q_n` is a good subcube, for `n^{1/(10d)²}/2 ≤ m` and
  `20 m ≤ n`. A crossing cluster of a cube of radius `m` inside a good cube of radius `2m` is
  joined to the cluster of the larger cube (its crossing path has length `2m ≥ 2m/100`). Chaining
  unit translates of the radius-`m` cubes of centre in `[-(n-2m), n-2m]^d` joins all their
  clusters inside `Q_n`; the radius-`m` cubes touching the face `{y_0 = n}` at
  `K = ⌊(2(n-2m)+1)/(2m+1)⌋` disjoint places then give `K` sites of `F` in one open cluster `W`
  of `Q_n`. A largest cluster `V` has at least `K > (2m+1)^d` sites, so it contains an open path
  of length `m`; this path lies in a good cube of radius `2m` inside `Q_n`, hence `V = W`.
* Probability. The open clusters of `Q_n` depend only on the bonds inside `Q_n`, and the bonds
  `{y, y + e_0}`, `y ∈ F`, are outside; by independence, the probability that some open cluster
  of `Q_n` has at least `K` sites in `F` whose outward bonds are all closed is at most
  `(2n+1)^d (1-p)^K`.
* Borel-Cantelli: with `m ≈ n^{1/(100d²)}` both `C exp(-c n^s)` and `(2n+1)^d (1-p)^K` are
  summable. -/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Classical Filter Rigidity.Section6
open Rigidity.External (cubeAt openIn IsGoodSubcube IsWellConnected WellConnectedInput)

namespace Rigidity.Proofs.S6

namespace SingleExit

variable {d : ℕ}

/-! ### Walks in the lattice -/

/-- An open edge changes every coordinate by at most one. -/
theorem abs_sub_le_one_of_adj {ω : Configuration d} {x y : Vertex d}
    (h : (openGraph ω).Adj x y) (i : Fin d) : |y i - x i| ≤ 1 := by
  obtain ⟨⟨j, hj | hj⟩, -⟩ := h <;> subst hj <;>
    by_cases hij : i = j <;> simp [LatticeProb.unit, hij]

/-- Along a walk whose steps change the `i`-th coordinate by at most one, the `j`-th vertex is
within `j` of the start in that coordinate. -/
theorem abs_getVert_sub_le {G : SimpleGraph (Vertex d)} {i : Fin d}
    (hG : ∀ a b, G.Adj a b → |b i - a i| ≤ 1) {u v : Vertex d} (p : G.Walk u v) (j : ℕ) :
    |p.getVert j i - u i| ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rcases lt_or_ge j p.length with hj | hj
    · have h1 := hG _ _ (p.adj_getVert_succ hj)
      have h2 := abs_sub_le (p.getVert (j + 1) i) (p.getVert j i) (u i)
      push_cast
      linarith
    · rw [p.getVert_of_length_le (by omega)]
      rw [p.getVert_of_length_le hj] at ih
      push_cast
      linarith

/-- A walk is at least as long as the displacement of any coordinate. -/
theorem abs_sub_le_length {G : SimpleGraph (Vertex d)} {i : Fin d}
    (hG : ∀ a b, G.Adj a b → |b i - a i| ≤ 1) {u v : Vertex d} (p : G.Walk u v) :
    |v i - u i| ≤ p.length := by
  simpa [p.getVert_length] using abs_getVert_sub_le hG p p.length

/-! ### Open clusters of cubes -/

theorem openIn_mono {ω : Configuration d} {B B' : Set (Vertex d)} (h : B ⊆ B') :
    openIn ω B ≤ openIn ω B' := fun _ _ hxy => ⟨hxy.1, h hxy.2.1, h hxy.2.2⟩

theorem openIn_cube (ω : Configuration d) (n : ℕ) : openIn ω (cube d n) = boxOpenGraph ω n := by
  ext; rfl

theorem openIn_adj_le_one {ω : Configuration d} {B : Set (Vertex d)} (i : Fin d) :
    ∀ a b, (openIn ω B).Adj a b → |b i - a i| ≤ 1 :=
  fun _ _ h => abs_sub_le_one_of_adj h.1 i

theorem mem_of_reachable_openIn {ω : Configuration d} {B : Set (Vertex d)} {x y : Vertex d}
    (hx : x ∈ B) (h : (openIn ω B).Reachable x y) : y ∈ B := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hx
  | cons hadj _ ih => exact ih hadj.2.2

theorem cubeAt_subset_cubeAt {z z' : Vertex d} {M M' : ℕ}
    (h : ∀ i, |z' i - z i| + M' ≤ M) : cubeAt z' M' ⊆ cubeAt z M := by
  intro y hy i
  have h1 := hy i
  have h2 := h i
  have h3 := abs_sub_le (y i) (z' i) (z i)
  linarith

theorem cubeAt_subset_cube {z : Vertex d} {M n : ℕ} (h : ∀ i, |z i| + M ≤ n) :
    cubeAt z M ⊆ cube d n := by
  intro y hy i
  have h1 := hy i
  have h2 := h i
  have h3 := abs_sub_le (y i) (z i) 0
  simp only [sub_zero] at h3
  linarith

/-- The largest cluster chosen by the definition of a good subcube. -/
noncomputable def goodCluster (ω : Configuration d) (z : Vertex d) (M : ℕ) : Set (Vertex d) :=
  if h : IsGoodSubcube ω z M then h.choose else ∅

theorem goodCluster_spec {ω : Configuration d} {z : Vertex d} {M : ℕ}
    (h : IsGoodSubcube ω z M) :
    Rigidity.External.IsLargestClusterIn ω (cubeAt z M) (goodCluster ω z M) ∧
      Rigidity.External.CrossesCube z M (goodCluster ω z M) ∧
      ∀ (n : ℕ) (γ : Fin (n + 1) → Vertex d), Function.Injective γ →
        (∀ i : Fin n, (openIn ω (cubeAt z M)).Adj (γ i.castSucc) (γ i.succ)) →
        (M : ℝ) / 100 ≤ n → ∃ y ∈ goodCluster ω z M, (openIn ω (cubeAt z M)).Reachable (γ 0) y := by
  simp only [goodCluster, dif_pos h]
  exact h.choose_spec

theorem reachable_of_mem_goodCluster {ω : Configuration d} {z : Vertex d} {M : ℕ}
    (h : IsGoodSubcube ω z M) {y y' : Vertex d} (hy : y ∈ goodCluster ω z M)
    (hy' : y' ∈ goodCluster ω z M) : (openIn ω (cubeAt z M)).Reachable y y' := by
  obtain ⟨⟨x, -, hV⟩, -⟩ := (goodCluster_spec h).1
  rw [hV] at hy hy'
  exact hy.symm.trans hy'

theorem goodCluster_subset {ω : Configuration d} {z : Vertex d} {M : ℕ}
    (h : IsGoodSubcube ω z M) : goodCluster ω z M ⊆ cubeAt z M := by
  obtain ⟨⟨x, hx, hV⟩, -⟩ := (goodCluster_spec h).1
  intro y hy
  rw [hV] at hy
  exact mem_of_reachable_openIn hx hy

theorem goodCluster_nonempty [NeZero d] {ω : Configuration d} {z : Vertex d} {M : ℕ}
    (h : IsGoodSubcube ω z M) : (goodCluster ω z M).Nonempty := by
  obtain ⟨⟨y, hy, -⟩, -⟩ := (goodCluster_spec h).2.1 0
  exact ⟨y, hy⟩

/-- A crossing cluster of a cube of radius `M'` inside a good cube of radius `M ≤ 200 M'` is
joined, inside the larger cube, to the cluster of the larger cube: its crossing path has length
at least `2M' ≥ M/100`. -/
theorem reachable_goodCluster_of_subset [NeZero d] {ω : Configuration d} {z z' : Vertex d}
    {M M' : ℕ} (h : IsGoodSubcube ω z M) (h' : IsGoodSubcube ω z' M')
    (hsub : cubeAt z' M' ⊆ cubeAt z M) (hM : (M : ℝ) / 100 ≤ 2 * M') {y' y : Vertex d}
    (hy' : y' ∈ goodCluster ω z' M') (hy : y ∈ goodCluster ω z M) :
    (openIn ω (cubeAt z M)).Reachable y' y := by
  obtain ⟨⟨a, ha, ha0⟩, ⟨b, hb, hb0⟩⟩ := (goodCluster_spec h').2.1 0
  have hab := (reachable_of_mem_goodCluster h' ha hb).mono (openIn_mono hsub)
  obtain ⟨p⟩ := hab
  set q := p.bypass with hq
  have hqp : q.IsPath := p.bypass_isPath
  have hlen : 2 * M' ≤ q.length := by
    have := abs_sub_le_length (openIn_adj_le_one 0) q
    rw [hb0, ha0] at this
    have h2 : |(z' 0 + M') - (z' 0 - M')| = 2 * (M' : ℤ) := by
      rw [show (z' 0 + M') - (z' 0 - M') = 2 * (M' : ℤ) by ring]
      exact abs_of_nonneg (by positivity)
    rw [h2] at this
    exact_mod_cast this
  let γ : Fin (q.length + 1) → Vertex d := fun j => q.getVert j
  have hinj : Function.Injective γ := by
    intro j k hjk
    exact Fin.ext (hqp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hjk)
  have hadj : ∀ j : Fin q.length, (openIn ω (cubeAt z M)).Adj (γ j.castSucc) (γ j.succ) :=
    fun j => q.adj_getVert_succ j.2
  have hL : (M : ℝ) / 100 ≤ q.length := by
    refine hM.trans ?_
    exact_mod_cast hlen
  obtain ⟨y₀, hy₀, hreach⟩ := (goodCluster_spec h).2.2 q.length γ hinj hadj hL
  have hγ0 : γ 0 = a := by simp [γ]
  rw [hγ0] at hreach
  exact (((reachable_of_mem_goodCluster h' hy' ha).mono (openIn_mono hsub)).trans hreach).trans
    (reachable_of_mem_goodCluster h hy₀ hy)

/-! ### The deterministic geometry on a well-connected cube -/

/-- Every cube of radius `m` or `2m` with centre in `Q_n` is a good subcube. -/
def CubesGood (ω : Configuration d) (n m : ℕ) : Prop :=
  ∀ z : Vertex d, (∀ i, |z i| ≤ n) → IsGoodSubcube ω z m ∧ IsGoodSubcube ω z (2 * m)

/-- The sites of the face `{y_0 = n}` of `Q_n` off its lower-dimensional faces. -/
noncomputable def faceSites (d : ℕ) [NeZero d] (n : ℕ) : Finset (Vertex d) :=
  (Steps.S6.cubeFinset d n).filter fun y => y 0 = n ∧ ∀ i, i ≠ 0 → |y i| < n

/-- The clusters of two good cubes of radius `m` with centres at distance at most `m`, the first
centre in `[-(n-2m), n-2m]^d`, are joined inside `Q_n` (through the cube of radius `2m`). -/
theorem reachable_of_near [NeZero d] {ω : Configuration d} {n m : ℕ} (hg : CubesGood ω n m)
    {z z' : Vertex d} (hz : ∀ i, |z i| ≤ (n : ℤ) - 2 * m) (hz' : ∀ i, |z' i - z i| ≤ m)
    {y y' : Vertex d} (hy : y ∈ goodCluster ω z m) (hy' : y' ∈ goodCluster ω z' m) :
    (boxOpenGraph ω n).Reachable y y' := by
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have hzn : ∀ i, |z i| ≤ n := fun i => by linarith [hz i]
  have hz'n : ∀ i, |z' i| ≤ n := fun i => by
    have h3 := abs_sub_le (z' i) (z i) 0
    simp only [sub_zero] at h3
    linarith [hz i, hz' i]
  obtain ⟨h1, h2⟩ := hg z hzn
  have h1' := (hg z' hz'n).1
  obtain ⟨w, hw⟩ := goodCluster_nonempty h2
  have hM : ((2 * m : ℕ) : ℝ) / 100 ≤ 2 * (m : ℝ) := by
    push_cast; linarith [show (0 : ℝ) ≤ m by positivity]
  have hs : cubeAt z m ⊆ cubeAt z (2 * m) :=
    cubeAt_subset_cubeAt fun i => by simp only [sub_self, abs_zero, zero_add]; push_cast; omega
  have hs' : cubeAt z' m ⊆ cubeAt z (2 * m) :=
    cubeAt_subset_cubeAt fun i => by push_cast; linarith [hz' i]
  have hbox : cubeAt z (2 * m) ⊆ cube d n :=
    cubeAt_subset_cube fun i => by push_cast; linarith [hz i]
  have hr := ((reachable_goodCluster_of_subset h2 h1 hs hM hy hw).trans
    (reachable_goodCluster_of_subset h2 h1' hs' hM hy' hw).symm).mono (openIn_mono hbox)
  rwa [openIn_cube] at hr

/-- Chaining unit translates: the clusters of all good cubes of radius `m` with centre in
`[-(n-2m), n-2m]^d` lie in one open cluster of `Q_n`. -/
theorem reachable_chain [NeZero d] {ω : Configuration d} {n m : ℕ} (hg : CubesGood ω n m)
    (hm : 1 ≤ m) (hnm : 2 * m ≤ n) {x₀ : Vertex d} (hx₀ : x₀ ∈ goodCluster ω 0 m) :
    ∀ (N : ℕ) (z : Vertex d), ∑ i, (z i).natAbs = N → (∀ i, |z i| ≤ (n : ℤ) - 2 * m) →
      ∀ y ∈ goodCluster ω z m, (boxOpenGraph ω n).Reachable x₀ y := by
  have h0 : ∀ i, |(0 : Vertex d) i| ≤ (n : ℤ) - 2 * m := fun i => by simp; omega
  intro N
  induction N with
  | zero =>
    intro z hN hz y hy
    have hz0 : z = 0 := funext fun i => by
      have := (Finset.sum_eq_zero_iff.mp hN) i (Finset.mem_univ i)
      simpa using this
    subst hz0
    exact reachable_of_near hg h0 (fun i => by simp) hx₀ hy
  | succ N ih =>
    intro z hN hz y hy
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra! hcon
      simp [hcon] at hN
    set z' : Vertex d := Function.update z i (if 0 < z i then z i - 1 else z i + 1) with hz'def
    have hz'i : z' i = if 0 < z i then z i - 1 else z i + 1 := Function.update_self _ _ _
    have hz'j : ∀ j, j ≠ i → z' j = z j := fun j hj => Function.update_of_ne hj _ _
    have hsum : ∑ j, (z' j).natAbs = N := by
      have key : ∀ j, (z' j).natAbs + (if j = i then 1 else 0) = (z j).natAbs := by
        intro j
        by_cases hj : j = i
        · subst hj; rw [hz'i, if_pos rfl]; split_ifs <;> omega
        · rw [hz'j j hj, if_neg hj, add_zero]
      have := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => key j)
      rw [Finset.sum_add_distrib] at this
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      omega
    have hz' : ∀ j, |z' j| ≤ (n : ℤ) - 2 * m := by
      intro j
      by_cases hj : j = i
      · subst hj
        have := hz j
        rw [hz'i]
        rw [abs_le] at this ⊢
        split_ifs <;> constructor <;> omega
      · rw [hz'j j hj]; exact hz j
    have hzz' : ∀ j, |z j - z' j| ≤ m := by
      intro j
      by_cases hj : j = i
      · subst hj; rw [hz'i]; rw [abs_le]; split_ifs <;> constructor <;> omega
      · rw [hz'j j hj, sub_self, abs_zero]; positivity
    have hz'n : ∀ j, |z' j| ≤ n := fun j => by linarith [hz' j, show (0 : ℤ) ≤ m by positivity]
    obtain ⟨y', hy'⟩ := goodCluster_nonempty (hg z' hz'n).1
    exact (ih z' hsum hz' y' hy').trans (reachable_of_near hg hz' hzz' hy' hy)

/-- The `K = ⌊(2(n-2m)+1)/(2m+1)⌋` radius-`m` cubes touching the face `{y_0 = n}` give `K`
distinct face sites in the open cluster of `Q_n` joining the good cubes. -/
theorem le_card_faceSites [NeZero d] (hd : 2 ≤ d) {ω : Configuration d} {n m : ℕ}
    (hg : CubesGood ω n m) (hm : 1 ≤ m) (hnm : 2 * m ≤ n) {x₀ : Vertex d}
    (hx₀ : x₀ ∈ goodCluster ω 0 m) :
    (2 * (n - 2 * m) + 1) / (2 * m + 1) ≤
      ((faceSites d n).filter fun y => (boxOpenGraph ω n).Reachable x₀ y).card := by
  set K := (2 * (n - 2 * m) + 1) / (2 * m + 1) with hK
  have hKle : K * (2 * m + 1) ≤ 2 * (n - 2 * m) + 1 := Nat.div_mul_le_self _ _
  let i1 : Fin d := ⟨1, by omega⟩
  have hi01 : i1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [i1] at this
  let a : Fin K → ℤ := fun j => -((n : ℤ) - 2 * m) + (j : ℤ) * (2 * m + 1)
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have ha : ∀ j : Fin K, |a j| ≤ (n : ℤ) - 2 * m := by
    intro j
    have hj : ((j : ℕ) + 1) * (2 * m + 1) ≤ 2 * (n - 2 * m) + 1 :=
      le_trans (Nat.mul_le_mul_right _ j.2) hKle
    have hj' : ((j : ℤ) + 1) * (2 * m + 1) ≤ 2 * ((n : ℤ) - 2 * m) + 1 := by
      zify [hnm] at hj; linarith
    have hj0 : (0 : ℤ) ≤ (j : ℤ) * (2 * m + 1) := by positivity
    rw [abs_le]; constructor <;> simp only [a] <;> nlinarith
  let zf : Fin K → Vertex d := fun j i => if i = 0 then (n : ℤ) - m else if i = i1 then a j else 0
  let wf : Fin K → Vertex d :=
    fun j i => if i = 0 then (n : ℤ) - 2 * m else if i = i1 then a j else 0
  have hwf : ∀ j i, |wf j i| ≤ (n : ℤ) - 2 * m := by
    intro j i
    simp only [wf]
    split_ifs
    · rw [abs_of_nonneg (by omega)]
    · exact ha j
    · simp; omega
  have hzw : ∀ j i, |zf j i - wf j i| ≤ m := by
    intro j i
    simp only [zf, wf]
    split_ifs
    · rw [show (n : ℤ) - m - (n - 2 * m) = m by ring, abs_of_nonneg hm0]
    · simp
    · simp
  have hzn : ∀ j i, |zf j i| ≤ n := fun j i => by
    have h3 := abs_sub_le (zf j i) (wf j i) 0
    simp only [sub_zero] at h3
    linarith [hzw j i, hwf j i]
  choose y hyΓ hy0 using fun j => ((goodCluster_spec (hg (zf j) (hzn j)).1).2.1 0).2
  have hyc : ∀ j i, |y j i - zf j i| ≤ m := fun j =>
    goodCluster_subset (hg (zf j) (hzn j)).1 (hyΓ j)
  have hyn : ∀ j, y j 0 = n := fun j => by rw [hy0 j]; simp [zf]
  have hyi1 : ∀ j, |y j i1 - a j| ≤ m := fun j => by
    have := hyc j i1
    simpa [zf, hi01] using this
  have hface : ∀ j, y j ∈ faceSites d n := by
    intro j
    have hlt : ∀ i, i ≠ 0 → |y j i| < n := by
      intro i hi
      have h1 := hyc j i
      by_cases hi1 : i = i1
      · subst hi1
        have h3 := abs_sub_le (y j i1) (a j) 0
        simp only [sub_zero] at h3
        linarith [hyi1 j, ha j]
      · simp only [zf, if_neg hi, if_neg hi1, sub_zero] at h1
        omega
    refine Finset.mem_filter.mpr ⟨Steps.S6.mem_cubeFinset.mpr fun i => ?_, hyn j, hlt⟩
    by_cases hi : i = 0
    · subst hi; rw [hyn j, abs_of_nonneg (by positivity)]
    · exact (hlt i hi).le
  have hreach : ∀ j, (boxOpenGraph ω n).Reachable x₀ (y j) := by
    intro j
    obtain ⟨y', hy'⟩ := goodCluster_nonempty (hg (wf j) fun i => by linarith [hwf j i]).1
    exact (reachable_chain hg hm hnm hx₀ _ (wf j) rfl (hwf j) y' hy').trans
      (reachable_of_near hg (hwf j) (hzw j) hy' (hyΓ j))
  have hinj : Function.Injective y := by
    intro j k hjk
    by_contra hne
    have h1 := hyi1 j
    have h2 := hyi1 k
    rw [hjk] at h1
    have hdiff : a j - a k = ((j : ℤ) - k) * (2 * m + 1) := by simp only [a]; ring
    have h3 : |a j - a k| ≤ 2 * m := by
      have := abs_sub_le (a j) (y k i1) (a k)
      rw [abs_sub_comm] at h1
      linarith
    rw [hdiff, abs_le] at h3
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have : (j : ℤ) + 1 ≤ k := by exact_mod_cast hlt
      nlinarith
    · have : (k : ℤ) + 1 ≤ j := by exact_mod_cast hlt
      nlinarith
  have := Finset.card_le_card_of_injOn y (s := Finset.univ)
    (t := (faceSites d n).filter fun y => (boxOpenGraph ω n).Reachable x₀ y)
    (fun j _ => Finset.mem_filter.mpr ⟨hface j, hreach j⟩) hinj.injOn
  simpa using this

/-- On a cube all of whose radius-`m` and radius-`2m` subcubes are good, with
`(2m+1)^d < K`, every largest open cluster of `Q_n` is the cluster joining the good cubes. -/
theorem reachable_of_isLargestBoxCluster [NeZero d] (hd : 2 ≤ d) {ω : Configuration d}
    {n m : ℕ} (hg : CubesGood ω n m) (hm : 1 ≤ m) (hnm : 2 * m ≤ n)
    (hK : (2 * m + 1) ^ d < (2 * (n - 2 * m) + 1) / (2 * m + 1)) {x₀ : Vertex d}
    (hx₀ : x₀ ∈ goodCluster ω 0 m) {V : Finset (Vertex d)} (hV : IsLargestBoxCluster ω n V)
    {v₀ : Vertex d} (hv₀ : v₀ ∈ cube d n) (hVv : (V : Set (Vertex d)) = boxCluster ω n v₀) :
    (boxOpenGraph ω n).Reachable x₀ v₀ := by
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have h0n : ∀ i, |(0 : Vertex d) i| ≤ n := fun i => by simp
  have hx₀c : x₀ ∈ cube d n :=
    cubeAt_subset_cube (z := 0) (M := m) (fun i => by simp; omega)
      (goodCluster_subset (hg 0 h0n).1 hx₀)
  have hcard : (2 * m + 1) ^ d < V.card := by
    refine hK.trans_le ((le_card_faceSites hd hg hm hnm hx₀).trans ?_)
    refine le_trans ?_ (hV.2 x₀ hx₀c)
    rw [← Set.ncard_coe_finset]
    apply Set.ncard_le_ncard
    · intro y hy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy
      exact hy.2
    · exact (Steps.S6.cubeFinset d n).finite_toSet.subset
        (fun y hy => Steps.S6.mem_cubeFinset.mpr (Steps.S6.mem_cube_of_reachable hx₀c hy))
  obtain ⟨u, huV, i, hui⟩ : ∃ u ∈ V, ∃ i, (m : ℤ) < |u i - v₀ i| := by
    by_contra! hcon
    have hsub : V ⊆ Fintype.piFinset fun i => Finset.Icc (v₀ i - m) (v₀ i + m) := by
      intro u hu
      rw [Fintype.mem_piFinset]
      intro i
      have := hcon u hu i
      rw [abs_le] at this
      rw [Finset.mem_Icc]
      constructor <;> linarith
    have hc : ∀ i, (Finset.Icc (v₀ i - m) (v₀ i + m)).card = 2 * m + 1 := fun i => by
      rw [Int.card_Icc]; omega
    have := Finset.card_le_card hsub
    simp only [Fintype.card_piFinset, hc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at this
    omega
  have hu : (boxOpenGraph ω n).Reachable v₀ u := by
    have : u ∈ (V : Set (Vertex d)) := huV
    rw [hVv] at this
    exact this
  obtain ⟨p⟩ := hu
  set q := p.bypass
  have hqp : q.IsPath := p.bypass_isPath
  have hG : ∀ j, ∀ a b, (boxOpenGraph ω n).Adj a b → |b j - a j| ≤ 1 :=
    fun j _ _ h => abs_sub_le_one_of_adj h.1 j
  have hlen : m < q.length := by
    have := abs_sub_le_length (hG i) q
    exact_mod_cast hui.trans_le this
  let w : Vertex d := fun j => max (-((n : ℤ) - 2 * m)) (min ((n : ℤ) - 2 * m) (v₀ j))
  have hw : ∀ j, |w j| ≤ (n : ℤ) - 2 * m := by
    intro j
    simp only [w]
    rw [abs_le]
    constructor <;> simp only [max_def, min_def] <;> split_ifs <;> omega
  have hwn : ∀ j, |w j| ≤ n := fun j => by linarith [hw j]
  have hwc : cubeAt w (2 * m) ⊆ cube d n :=
    cubeAt_subset_cube fun j => by push_cast; linarith [hw j]
  have hγ : ∀ k ≤ m, q.getVert k ∈ cubeAt w (2 * m) := by
    intro k hk j
    have h1 : |q.getVert k j - v₀ j| ≤ k := abs_getVert_sub_le (hG j) q k
    have h2 : q.getVert k ∈ cube d n := (q.adj_getVert_succ (by omega : k < q.length)).2.1
    have h3 := h2 j
    have h4 := hv₀ j
    have hk' : (k : ℤ) ≤ m := by exact_mod_cast hk
    simp only [w]
    rw [abs_le] at h1 h3 h4 ⊢
    push_cast
    constructor <;> simp only [max_def, min_def] <;> split_ifs <;> omega
  let γ : Fin (m + 1) → Vertex d := fun k => q.getVert k
  have hinj : Function.Injective γ := by
    intro j k hjk
    exact Fin.ext (hqp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hjk)
  have hadj : ∀ k : Fin m, (openIn ω (cubeAt w (2 * m))).Adj (γ k.castSucc) (γ k.succ) :=
    fun k => ⟨(q.adj_getVert_succ (by omega : (k : ℕ) < q.length)).1,
      hγ _ (by simp), hγ _ (by simp)⟩
  have hgw := (hg w hwn).2
  obtain ⟨y₀, hy₀, hr⟩ := (goodCluster_spec hgw).2.2 m γ hinj hadj
    (by push_cast; linarith [show (0 : ℝ) ≤ m by positivity])
  have hγ0 : γ 0 = v₀ := by simp [γ]
  rw [hγ0] at hr
  obtain ⟨y₁, hy₁⟩ := goodCluster_nonempty (hg w hwn).1
  have hM : ((2 * m : ℕ) : ℝ) / 100 ≤ 2 * (m : ℝ) := by
    push_cast; linarith [show (0 : ℝ) ≤ m by positivity]
  have h10 := reachable_goodCluster_of_subset hgw (hg w hwn).1
    (cubeAt_subset_cubeAt fun j => by simp only [sub_self, abs_zero, zero_add]; push_cast; omega)
    hM hy₁ hy₀
  have hloc := (h10.trans hr.symm).mono (openIn_mono hwc)
  rw [openIn_cube] at hloc
  exact (reachable_chain hg hm hnm hx₀ _ w rfl hw y₁ hy₁).trans hloc

/-- Every largest open cluster of `Q_n` contains at least `K` face sites. -/
theorem le_card_faceSites_of_isLargestBoxCluster [NeZero d] (hd : 2 ≤ d) {ω : Configuration d}
    {n m : ℕ} (hg : CubesGood ω n m) (hm : 1 ≤ m) (hnm : 2 * m ≤ n)
    (hK : (2 * m + 1) ^ d < (2 * (n - 2 * m) + 1) / (2 * m + 1)) {V : Finset (Vertex d)}
    (hV : IsLargestBoxCluster ω n V) :
    ∃ v₀ ∈ cube d n, (V : Set (Vertex d)) = boxCluster ω n v₀ ∧
      (2 * (n - 2 * m) + 1) / (2 * m + 1) ≤
        ((faceSites d n).filter fun y => y ∈ boxCluster ω n v₀).card := by
  obtain ⟨v₀, hv₀, hVv⟩ := hV.1
  have h0n : ∀ i, |(0 : Vertex d) i| ≤ n := fun i => by simp
  obtain ⟨x₀, hx₀⟩ := goodCluster_nonempty (hg 0 h0n).1
  have hr := reachable_of_isLargestBoxCluster hd hg hm hnm hK hx₀ hV hv₀ hVv
  refine ⟨v₀, hv₀, hVv, (le_card_faceSites hd hg hm hnm hx₀).trans_eq ?_⟩
  congr 1
  apply Finset.filter_congr
  intro y _
  exact ⟨fun h => hr.symm.trans h, fun h => hr.trans h⟩

/-! ### Single exits at face sites -/

/-- At a face site `y` of an open cluster `V` of `Q_n`, the only open edge that can leave `V` is
the outward edge `{y, y + e_0}`. -/
theorem exitNeighbors_eq_of_mem_faceSites [NeZero d] {ω : Configuration d} {n : ℕ} (hn : 1 ≤ n)
    {V : Finset (Vertex d)} {v₀ : Vertex d} (hv₀ : v₀ ∈ cube d n)
    (hVv : (V : Set (Vertex d)) = boxCluster ω n v₀) {y : Vertex d} (hyF : y ∈ faceSites d n)
    (hyV : y ∈ V) (hopen : (openGraph ω).Adj y (y + LatticeProb.unit 0)) :
    Steps.S6.exitNeighbors ω V y = {y + LatticeProb.unit 0} := by
  obtain ⟨hyc, hy0, hyi⟩ := Finset.mem_filter.mp hyF
  have hyc' := Steps.S6.mem_cubeFinset.mp hyc
  have hyB : (boxOpenGraph ω n).Reachable v₀ y := by
    have : y ∈ (V : Set (Vertex d)) := hyV
    rw [hVv] at this
    exact this
  have hout : y + LatticeProb.unit 0 ∉ cube d n := by
    intro h
    have := h 0
    simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same, hy0] at this
    rw [abs_le] at this
    omega
  ext z
  simp only [Steps.S6.exitNeighbors, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hz, hzV⟩
    have hzc : z ∉ cube d n := by
      intro hzc
      apply hzV
      have : z ∈ (V : Set (Vertex d)) := by
        rw [hVv]
        exact hyB.trans (SimpleGraph.Adj.reachable ⟨hz, hyc', hzc⟩)
      exact this
    obtain ⟨⟨j, hj | hj⟩, -⟩ := hz
    · by_cases hj0 : j = 0
      · subst hj0; exact hj
      · exfalso
        apply hzc
        intro i
        rw [hj]
        by_cases hij : i = j
        · subst hij
          have := abs_lt.mp (hyi i hj0)
          simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]
          rw [abs_le]; constructor <;> omega
        · simpa [LatticeProb.unit, hij] using hyc' i
    · exfalso
      apply hzc
      intro i
      have hz' : z = y - LatticeProb.unit j := by rw [hj]; abel
      rw [hz']
      by_cases hij : i = j
      · subst hij
        simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_same]
        by_cases hi0 : i = 0
        · subst hi0; rw [hy0, abs_le]; constructor <;> omega
        · have := abs_lt.mp (hyi i hi0)
          rw [abs_le]; constructor <;> omega
      · simpa [LatticeProb.unit, hij] using hyc' i
  · rintro rfl
    refine ⟨hopen, fun h => hout ?_⟩
    have : y + LatticeProb.unit 0 ∈ (V : Set (Vertex d)) := h
    rw [hVv] at this
    exact Steps.S6.mem_cube_of_reachable hv₀ this

/-! ### Independence of the outward bonds of the face sites -/

/-- The bonds with both endpoints in `Q_n`. -/
noncomputable def insideBonds (d n : ℕ) : Finset (Bond d) :=
  ((Steps.S6.cubeFinset d n ×ˢ Steps.S6.cubeFinset d n).image fun xy => s(xy.1, xy.2)).subtype
    fun e => ∃ x y : Vertex d, e = s(x, y) ∧ (∑ i, |x i - y i|) = 1

theorem bondOfAdjacent_mem_insideBonds {n : ℕ} {x y : Vertex d}
    (h : (nearestNeighborGraph d).Adj x y) (hx : x ∈ cube d n) (hy : y ∈ cube d n) :
    bondOfAdjacent h ∈ insideBonds d n := by
  rw [insideBonds, Finset.mem_subtype]
  exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr
    ⟨Steps.S6.mem_cubeFinset.mpr hx, Steps.S6.mem_cubeFinset.mpr hy⟩, rfl⟩

/-- The open graph of `Q_n` depends only on the bonds inside `Q_n`. -/
theorem boxOpenGraph_congr {ω ω' : Configuration d} {n : ℕ}
    (h : ∀ e ∈ insideBonds d n, ω e = ω' e) : boxOpenGraph ω n = boxOpenGraph ω' n := by
  ext x y
  change (openGraph ω).Adj x y ∧ x ∈ cube d n ∧ y ∈ cube d n ↔
    (openGraph ω').Adj x y ∧ x ∈ cube d n ∧ y ∈ cube d n
  constructor
  · rintro ⟨⟨hxy, ho⟩, hx, hy⟩
    exact ⟨⟨hxy, by rw [← h _ (bondOfAdjacent_mem_insideBonds hxy hx hy)]; exact ho⟩, hx, hy⟩
  · rintro ⟨⟨hxy, ho⟩, hx, hy⟩
    exact ⟨⟨hxy, by rw [h _ (bondOfAdjacent_mem_insideBonds hxy hx hy)]; exact ho⟩, hx, hy⟩

theorem boxCluster_congr {ω ω' : Configuration d} {n : ℕ}
    (h : ∀ e ∈ insideBonds d n, ω e = ω' e) (x : Vertex d) :
    boxCluster ω n x = boxCluster ω' n x := by
  simp only [boxCluster, boxOpenGraph_congr h]

/-- The outward bond `{y, y + e_0}`. -/
def topBond [NeZero d] (y : Vertex d) : Bond d :=
  bondOfAdjacent (show (nearestNeighborGraph d).Adj y (y + LatticeProb.unit 0) from
    ⟨0, Or.inl rfl⟩)

theorem openGraph_adj_top_iff [NeZero d] (ω : Configuration d) (y : Vertex d) :
    (openGraph ω).Adj y (y + LatticeProb.unit 0) ↔ ω (topBond y) = true :=
  ⟨fun ⟨_, ho⟩ => ho, fun ho => ⟨⟨0, Or.inl rfl⟩, ho⟩⟩

theorem topBond_injective [NeZero d] : Function.Injective (topBond (d := d)) := by
  intro y y' h
  have h' := congrArg Subtype.val h
  simp only [topBond, bondOfAdjacent, Sym2.eq_iff] at h'
  rcases h' with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have := congrFun (h1.trans (congrArg (· + LatticeProb.unit 0) h2.symm)) 0
    simp [LatticeProb.unit] at this
    omega

theorem topBond_notMem_insideBonds [NeZero d] {n : ℕ} {y : Vertex d} (hy : y ∈ faceSites d n) :
    topBond y ∉ insideBonds d n := by
  intro h
  rw [insideBonds, Finset.mem_subtype, Finset.mem_image] at h
  obtain ⟨⟨a, b⟩, hab, he⟩ := h
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  have hout : y + LatticeProb.unit 0 ∈ Steps.S6.cubeFinset d n := by
    simp only [topBond, bondOfAdjacent, Sym2.eq_iff] at he
    rcases he with ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact hb
    · exact ha
  have := Steps.S6.mem_cubeFinset.mp hout 0
  have hy0 := (Finset.mem_filter.mp hy).2.1
  simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same, hy0] at this
  rw [abs_le] at this
  omega

/-- The outward bonds of the face sites. -/
noncomputable def topBonds (d : ℕ) [NeZero d] (n : ℕ) : Finset (Bond d) :=
  (faceSites d n).image topBond

theorem disjoint_insideBonds_topBonds [NeZero d] (n : ℕ) :
    Disjoint (insideBonds d n) (topBonds d n) := by
  rw [Finset.disjoint_right]
  intro e he
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he
  exact topBond_notMem_insideBonds hy

/-- The open cluster of `x` in `Q_n` has at least `k` face sites, all of whose outward bonds are
closed. -/
def closedFaceEvent [NeZero d] (n k : ℕ) (x : Vertex d) : Set (Configuration d) :=
  {ω | k ≤ ((faceSites d n).filter fun y => y ∈ boxCluster ω n x).card ∧
    ∀ y ∈ faceSites d n, y ∈ boxCluster ω n x → ω (topBond y) = false}

/-- Conditionally on the bonds inside `Q_n`, the outward bonds of the face sites are independent
and closed with probability `1 - p`. -/
theorem measure_closedFaceEvent_le [NeZero d] (p : unitInterval) (n k : ℕ) (x : Vertex d) :
    latticeBondLaw d p (closedFaceEvent n k x) ≤ ENNReal.ofReal (1 - p) ^ k := by
  set S := insideBonds d n
  set T := topBonds d n
  set μ := latticeBondLaw d p
  let f : Configuration d → (S → Bool) := fun ω e => ω e
  let g : Configuration d → (T → Bool) := fun ω e => ω e
  have hind : IndepFun f g μ := (latticeBondLaw_iIndepFun p).indepFun_finset S T
    (disjoint_insideBonds_topBonds n) (fun e => measurable_pi_apply e)
  have hf : Measurable f := measurable_pi_lambda _ fun e => measurable_pi_apply _
  let ext : (S → Bool) → Configuration d := fun η e => if h : e ∈ S then η ⟨e, h⟩ else false
  let C : (S → Bool) → Finset (Vertex d) :=
    fun η => (faceSites d n).filter fun y => y ∈ boxCluster (ext η) n x
  have hC : ∀ ω, (faceSites d n).filter (fun y => y ∈ boxCluster ω n x) = C (f ω) := by
    intro ω
    have : boxCluster ω n x = boxCluster (ext (f ω)) n x :=
      boxCluster_congr (fun e he => by
        change ω e = (if h : e ∈ S then ω e else false)
        rw [dif_pos he]) x
    simp only [C, this]
  let Z : (S → Bool) → Set (T → Bool) :=
    fun η => {t | ∀ e : T, (∃ y ∈ C η, topBond y = e.1) → t e = false}
  have hcover : closedFaceEvent n k x ⊆
      ⋃ η ∈ (Finset.univ.filter fun η => k ≤ (C η).card), f ⁻¹' {η} ∩ g ⁻¹' Z η := by
    rintro ω ⟨hk, hcl⟩
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨f ω, by rw [← hC]; exact hk, rfl, ?_⟩
    rintro e ⟨y, hy, hye⟩
    rw [← hC] at hy
    obtain ⟨hyF, hyB⟩ := Finset.mem_filter.mp hy
    change ω e = false
    rw [← hye]
    exact hcl y hyF hyB
  have hr1 : ENNReal.ofReal (1 - p) ≤ 1 := ENNReal.ofReal_le_one.mpr (by linarith [p.2.1])
  have hZ : ∀ η, μ (g ⁻¹' Z η) = ENNReal.ofReal (1 - p) ^ (C η).card := by
    intro η
    have hset : g ⁻¹' Z η =
        {ω | ∀ e ∈ (C η).image topBond, ω e = (fun _ => false) e} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Z, g, Finset.mem_image]
      constructor
      · rintro h e ⟨y, hy, rfl⟩
        have hyT : topBond y ∈ T :=
          Finset.mem_image.mpr ⟨y, (Finset.mem_filter.mp hy).1, rfl⟩
        exact h ⟨topBond y, hyT⟩ ⟨y, hy, rfl⟩
      · rintro h ⟨e, he⟩ ⟨y, hy, hye⟩
        exact h e ⟨y, hy, hye⟩
    rw [hset, show μ = Measure.infinitePi (fun _ : Bond d => bernoulliMeasure true false p) from rfl,
      LatticeProb.Prob.Percolation.FiniteCylinder.measure_pattern p _ (fun _ => false)]
    simp [Finset.prod_const, Finset.card_image_of_injective _ topBond_injective]
  calc μ (closedFaceEvent n k x)
      ≤ μ (⋃ η ∈ (Finset.univ.filter fun η => k ≤ (C η).card), f ⁻¹' {η} ∩ g ⁻¹' Z η) :=
        measure_mono hcover
    _ ≤ ∑ η ∈ Finset.univ.filter fun η => k ≤ (C η).card, μ (f ⁻¹' {η} ∩ g ⁻¹' Z η) :=
        measure_biUnion_finset_le _ _
    _ = ∑ η ∈ Finset.univ.filter fun η => k ≤ (C η).card, μ (f ⁻¹' {η}) * μ (g ⁻¹' Z η) :=
        Finset.sum_congr rfl fun η _ => indepFun_iff_measure_inter_preimage_eq_mul.mp hind _ _
          (measurableSet_singleton η) (Set.toFinite _).measurableSet
    _ ≤ ∑ η ∈ Finset.univ.filter fun η => k ≤ (C η).card,
          μ (f ⁻¹' {η}) * ENNReal.ofReal (1 - p) ^ k := by
        refine Finset.sum_le_sum fun η hη => ?_
        rw [hZ]
        exact mul_le_mul' le_rfl (pow_le_pow_of_le_one zero_le hr1 (Finset.mem_filter.mp hη).2)
    _ ≤ ∑ η, μ (f ⁻¹' {η}) * ENNReal.ofReal (1 - p) ^ k :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ENNReal.ofReal (1 - p) ^ k := by
        rw [← Finset.sum_mul, sum_measure_preimage_singleton _
          (fun η _ => hf (measurableSet_singleton η)), Finset.coe_univ, Set.preimage_univ,
          measure_univ, one_mul]

/-! ### The scale and Borel-Cantelli -/

/-- `(2n+1)^a exp(-c n^s)` is summable for `c, s > 0`. -/
theorem summable_pow_mul_exp_neg_rpow (a : ℕ) {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    Summable fun n : ℕ => (2 * (n : ℝ) + 1) ^ a * Real.exp (-(c * (n : ℝ) ^ s)) := by
  set b : ℝ := -((a : ℝ) + 2) / s with hb
  have h1 : (fun n : ℕ => Real.exp (-c * (n : ℝ) ^ s)) =o[atTop]
      fun n : ℕ => ((n : ℝ) ^ s) ^ b :=
    (isLittleO_exp_neg_mul_rpow_atTop hc b).comp_tendsto
      ((tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop)
  have h3 : (fun n : ℕ => (2 * (n : ℝ) + 1) ^ a) =O[atTop] fun n : ℕ => (n : ℝ) ^ (a : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (3 ^ a) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), Real.rpow_natCast, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) a
  have h4 := h3.mul h1.isBigO
  refine summable_of_isBigO_nat (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)) ?_
  refine h4.congr' (Eventually.of_forall fun n => by simp only [neg_mul]) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_mul hn'.le, ← Real.rpow_add hn']
  congr 1
  rw [hb]
  field_simp
  ring

/-- The arithmetic of the scale: if `m ≥ 22` and `(m-1)^q < n` with `q = 100 d²`, then
`20 m ≤ n` and `(2m+1)^d < ⌊(2(n-2m)+1)/(2m+1)⌋`. -/
theorem scale_conditions {d q n m : ℕ} (hd : 2 ≤ d) (hq : q = 100 * d ^ 2) (hm : 22 ≤ m)
    (hlow : (m - 1) ^ q < n) :
    20 * m ≤ n ∧ (2 * m + 1) ^ d < (2 * (n - 2 * m) + 1) / (2 * m + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlow
  have hr : 21 ≤ r := by omega
  have hrpos : 0 < r := by omega
  have hq2 : 2 * (d + 1) ≤ q := by subst hq; nlinarith
  have hr2q : r ^ 2 ≤ r ^ q := Nat.pow_le_pow_right hrpos (by omega)
  have h20 : 20 * (r + 1) ≤ r ^ 2 := by nlinarith
  have hA : 2 * (r + 1) + 1 ≤ r ^ 2 := by nlinarith
  have h6 : 6 * (r + 1) + 1 ≤ r ^ 2 := by nlinarith
  have hAd : (2 * (r + 1) + 1) ^ (d + 1) ≤ r ^ q :=
    (Nat.pow_le_pow_left hA _).trans (by rw [← pow_mul]; exact Nat.pow_le_pow_right hrpos hq2)
  have hn20 : 20 * (r + 1) ≤ n := (h20.trans hr2q).trans hlow.le
  refine ⟨hn20, ?_⟩
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega)]
  have hexp : ((2 * (r + 1) + 1) ^ d + 1) * (2 * (r + 1) + 1) =
      (2 * (r + 1) + 1) ^ (d + 1) + (2 * (r + 1) + 1) := by ring
  rw [hexp]
  generalize (2 * (r + 1) + 1) ^ (d + 1) = P at hAd ⊢
  generalize r ^ q = R at hAd hr2q hlow
  generalize r ^ 2 = R2 at hr2q h6
  omega

end SingleExit

open SingleExit in
/-- `SingleExitStep` (repair of the gap of step:6.5-upper; not in the paper): almost surely, for
every large `n`, every largest open cluster `V` of `Q_n` contains a site with exactly one open edge
leaving `V`, namely a site of the face `{y_0 = n}` off the lower-dimensional faces whose outward
bond is open. Inputs: Proposition 2.3 (`WellConnectedInput`) and `p_c < p < 1`. -/
theorem singleExitStep {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hwc : WellConnectedInput) :
    Steps.S6.SingleExitStep d p := by
  obtain ⟨c, C, s, hc, hC, hs, hbound⟩ := hwc d hd p hpc hp1
  have hp0 : 0 < (p : ℝ) := lt_of_le_of_lt (criticalProbability_nonneg d) hpc
  set q := 100 * d ^ 2 with hqdef
  have hq : q ≠ 0 := by positivity
  have hex : ∀ n : ℕ, ∃ m, n ≤ m ^ q := fun n => ⟨n, Nat.le_self_pow hq n⟩
  let mOf : ℕ → ℕ := fun n => Nat.find (hex n)
  let KOf : ℕ → ℕ := fun n => (2 * (n - 2 * mOf n) + 1) / (2 * mOf n + 1)
  let bad : ℕ → Set (Configuration d) := fun n =>
    {ω | ¬ IsWellConnected ω 0 n} ∪ ⋃ x ∈ Steps.S6.cubeFinset d n, closedFaceEvent n (KOf n) x
  have hscale : ∀ n, 22 ^ q ≤ n → 1 ≤ mOf n ∧ 20 * mOf n ≤ n ∧
      (2 * mOf n + 1) ^ d < KOf n ∧ (n : ℝ) ^ ((q : ℝ)⁻¹) ≤ mOf n := by
    intro n hn
    have hspec : n ≤ mOf n ^ q := Nat.find_spec (hex n)
    have h22 : 22 ≤ mOf n := by
      by_contra h
      push Not at h
      exact absurd (hn.trans hspec) (not_le.mpr (Nat.pow_lt_pow_left h hq))
    have hlow : (mOf n - 1) ^ q < n := by
      have := Nat.find_min (hex n) (show mOf n - 1 < mOf n by omega)
      push Not at this
      exact this
    obtain ⟨h20, hK⟩ := scale_conditions hd hqdef h22 hlow
    refine ⟨by omega, h20, hK, ?_⟩
    calc (n : ℝ) ^ ((q : ℝ)⁻¹) ≤ ((mOf n : ℝ) ^ q) ^ ((q : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hspec) (by positivity)
      _ = mOf n := Real.pow_rpow_inv_natCast (by positivity) hq
  have hδ : (1 / (10 * (d : ℝ)) ^ 2) = (q : ℝ)⁻¹ := by
    rw [hqdef]; push_cast; ring
  have hdet : ∀ n, 22 ^ q ≤ n → ∀ ω, ω ∉ bad n → ∀ V : Finset (Vertex d),
      IsLargestBoxCluster ω n V → ∃ x ∈ V, (Steps.S6.exitNeighbors ω V x).card = 1 := by
    intro n hn ω hω V hV
    obtain ⟨hm1, h20, hK, hnm⟩ := hscale n hn
    have hWC : IsWellConnected ω 0 n := by
      by_contra h
      exact hω (Or.inl h)
    have hcl : ∀ x ∈ Steps.S6.cubeFinset d n, ω ∉ closedFaceEvent n (KOf n) x :=
      fun x hx h => hω (Or.inr (Set.mem_iUnion₂.mpr ⟨x, hx, h⟩))
    have hg : CubesGood ω n (mOf n) := by
      intro z hz
      have hmem : ∀ M : ℕ, (cubeAt z M ∩ cubeAt 0 n).Nonempty := fun M =>
        ⟨z, fun i => by simp, fun i => by simpa using hz i⟩
      have h20' : (20 : ℝ) * mOf n ≤ n := by exact_mod_cast h20
      have hpos : 0 ≤ (n : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) := by positivity
      have hlo : (n : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) ≤ mOf n := by rw [hδ]; exact hnm
      refine ⟨hWC.2.2 z _ (by linarith) (by linarith) (hmem _),
        hWC.2.2 z _ (by push_cast; linarith) (by push_cast; linarith) (hmem _)⟩
    obtain ⟨v₀, hv₀, hVv, hcard⟩ :=
      le_card_faceSites_of_isLargestBoxCluster hd hg hm1 (by omega) hK hV
    by_contra hcon
    push Not at hcon
    apply hcl v₀ (Steps.S6.mem_cubeFinset.mpr hv₀)
    refine ⟨hcard, fun y hyF hyB => ?_⟩
    by_contra hy
    simp only [Bool.not_eq_false] at hy
    have hyV : y ∈ V := by
      have : y ∈ (V : Set (Vertex d)) := by rw [hVv]; exact hyB
      exact this
    exact hcon y hyV (by
      rw [exitNeighbors_eq_of_mem_faceSites (by omega) hv₀ hVv hyF hyV
        ((openGraph_adj_top_iff ω y).mpr hy), Finset.card_singleton])
  let f : ℕ → ℝ := fun n =>
    C * Real.exp (-(c * (n : ℝ) ^ s)) + (2 * (n : ℝ) + 1) ^ d * (1 - p) ^ KOf n
  have hq1 : 0 ≤ 1 - (p : ℝ) := by linarith
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hμbad : ∀ n, latticeBondLaw d p (bad n) ≤ ENNReal.ofReal (f n) := by
    intro n
    calc latticeBondLaw d p (bad n)
        ≤ latticeBondLaw d p {ω | ¬ IsWellConnected ω 0 n} +
            latticeBondLaw d p (⋃ x ∈ Steps.S6.cubeFinset d n, closedFaceEvent n (KOf n) x) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (C * Real.exp (-(c * (n : ℝ) ^ s))) +
            ∑ x ∈ Steps.S6.cubeFinset d n, ENNReal.ofReal (1 - p) ^ KOf n :=
          add_le_add (hbound 0 n) ((measure_biUnion_finset_le _ _).trans
            (Finset.sum_le_sum fun x _ => measure_closedFaceEvent_le p n _ x))
      _ = ENNReal.ofReal (f n) := by
          rw [Finset.sum_const, Steps.S6.card_cubeFinset, nsmul_eq_mul,
            ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hq1,
            show (2 * (n : ℝ) + 1) ^ d = (((2 * n + 1) ^ d : ℕ) : ℝ) by push_cast; ring,
            ENNReal.ofReal_natCast]
  have hfs : Summable f := by
    refine Summable.add ?_ ?_
    · simpa using (summable_pow_mul_exp_neg_rpow 0 hc hs).mul_left C
    · set c' := -Real.log (1 - p) with hc'def
      have hc' : 0 < c' := neg_pos.mpr (Real.log_neg (by linarith) (by linarith))
      refine (summable_pow_mul_exp_neg_rpow d hc' (s := (q : ℝ)⁻¹)
        (by positivity)).of_norm_bounded_eventually_nat ?_
      filter_upwards [eventually_ge_atTop (22 ^ q)] with n hn
      obtain ⟨-, -, hK, hnm⟩ := hscale n hn
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hmK : mOf n ≤ KOf n :=
        ((Nat.le_succ_of_le (Nat.le_mul_of_pos_left _ (by norm_num))).trans
          (Nat.le_self_pow (NeZero.ne d) _)).trans hK.le
      have hKm : (n : ℝ) ^ ((q : ℝ)⁻¹) ≤ KOf n := hnm.trans (by exact_mod_cast hmK)
      calc (1 - (p : ℝ)) ^ KOf n = Real.exp (KOf n * Real.log (1 - p)) := by
            rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
        _ = Real.exp (-(c' * KOf n)) := by rw [hc'def]; ring_nf
        _ ≤ Real.exp (-(c' * (n : ℝ) ^ ((q : ℝ)⁻¹))) :=
            Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hKm hc'.le))
  have hsum : ∑' n, latticeBondLaw d p (bad n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hμbad)
    rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hfs]
    exact ENNReal.ofReal_ne_top
  unfold Steps.S6.SingleExitStep
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  intro _
  filter_upwards [hω, eventually_ge_atTop (22 ^ q)] with n hn hn'
  intro V hV
  exact hdet n hn' ω hn V hV.1

end Rigidity.Proofs.S6
