import Rigidity.Vendor.BonannoPerc.ExclusiveMain
import Rigidity.Vendor.BonannoPerc.Peierls

/-!
# Good paths in a rectangle of sites

Sites of the rectangle `[0, K) × [0, L)` of `ℤ²` are good or bad. A site is attached to the four
sides when good paths inside the rectangle join it to each side. Two attached sites are joined
by a good path: the left–right crossing through the first and the top–bottom crossing through the
second meet. A left–right crossing of a band contains a left–right crossing of every initial
sub-rectangle of the band. Transposition and the reflections of the rectangle preserve all these
notions.
-/

namespace Rigidity.Percolation

open LQGMetric

/-- A good path inside the `K × L` grid from the good site `a` to `b`. -/
def GridConn (K L : ℤ) (G : Set (ℤ × ℤ)) (a b : ℤ × ℤ) : Prop :=
  percInGrid K L a ∧ a ∈ G ∧ Relation.ReflTransGen (PercGoodStep K L (· ∈ G)) a b

namespace GridConn

variable {K L : ℤ} {G : Set (ℤ × ℤ)} {a b c : ℤ × ℤ}

theorem refl (ha : percInGrid K L a) (hG : a ∈ G) : GridConn K L G a a :=
  ⟨ha, hG, Relation.ReflTransGen.refl⟩

theorem mem (h : GridConn K L G a b) : percInGrid K L b ∧ b ∈ G :=
  PercExcl.goodStep_end h.2.2 ⟨h.1, h.2.1⟩

theorem symm (h : GridConn K L G a b) : GridConn K L G b a :=
  ⟨h.mem.1, h.mem.2, PercExcl.goodStep_rtg_symm h.2.2⟩

theorem trans (h₁ : GridConn K L G a b) (h₂ : GridConn K L G b c) : GridConn K L G a c :=
  ⟨h₁.1, h₁.2.1, h₁.2.2.trans h₂.2.2⟩

/-- Good paths in a smaller grid are good paths in a larger one. -/
theorem mono {K' L' : ℤ} (hK : K ≤ K') (hL : L ≤ L') (h : GridConn K L G a b) :
    GridConn K' L' G a b := by
  have hg : ∀ z, percInGrid K L z → percInGrid K' L' z := fun z hz => by
    unfold percInGrid at hz ⊢
    omega
  refine ⟨hg a h.1, h.2.1, Relation.ReflTransGen.mono (fun x y hxy => ?_) _ _ h.2.2⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hxy
  exact ⟨hg x h1, h2, hg y h3, h4, h5⟩

end GridConn

/-- Nearest neighbours are `*`-neighbours. -/
theorem percAdjK_of_percAdj4 {x y : ℤ × ℤ} (h : PercAdj4 x y) : PercAdjK x y := by
  unfold PercAdj4 at h
  unfold PercAdjK
  omega

/-- The site is joined inside the grid to each of the four sides. -/
def Att4 (K L : ℤ) (G : Set (ℤ × ℤ)) (a : ℤ × ℤ) : Prop :=
  (∃ c, c.1 = 0 ∧ GridConn K L G a c) ∧ (∃ c, c.1 = K - 1 ∧ GridConn K L G a c) ∧
    (∃ c, c.2 = 0 ∧ GridConn K L G a c) ∧ (∃ c, c.2 = L - 1 ∧ GridConn K L G a c)

/-- A good path from `a` stays among the sites joined to `a`. -/
theorem rtg_cluster {K L : ℤ} {G : Set (ℤ × ℤ)} {a : ℤ × ℤ} (ha : percInGrid K L a) (haG : a ∈ G) :
    ∀ {b : ℤ × ℤ}, Relation.ReflTransGen (PercGoodStep K L (· ∈ G)) a b →
      Relation.ReflTransGen (PercGoodStep K L (· ∈ {z | GridConn K L G a z})) a b := by
  intro b h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z hay hyz ih =>
    refine ih.tail ⟨hyz.1, ⟨ha, haG, hay⟩, hyz.2.2.1, ⟨ha, haG, hay.tail hyz⟩, hyz.2.2.2.2⟩

/-- Two sites, one joined to the left and right sides and the other to the bottom and top sides,
are joined by a good path. -/
theorem gridConn_of_crossings {K L : ℤ} {G : Set (ℤ × ℤ)} {a b c d e f : ℤ × ℤ}
    (hc : c.1 = 0) (hd : d.1 = K - 1) (hac : GridConn K L G a c) (had : GridConn K L G a d)
    (he : e.2 = 0) (hf : f.2 = L - 1) (hbe : GridConn K L G b e) (hbf : GridConn K L G b f) :
    GridConn K L G a b := by
  set A := {z | GridConn K L G a z} with hA
  set C := {z | GridConn K L G b z} with hC
  have hLR : PercGoodLR K L (· ∈ A) := by
    have hcd : GridConn K L G c d := hac.symm.trans had
    refine ⟨c, d, hc, hd, hcd.1, hac, ?_⟩
    have h1 := rtg_cluster hac.mem.1 hac.mem.2 hcd.2.2
    refine Relation.ReflTransGen.mono (fun x y hxy => ?_) _ _ h1
    obtain ⟨h1, h2, h3, h4, h5⟩ := hxy
    exact ⟨h1, hac.trans h2, h3, hac.trans h4, h5⟩
  have hTB : PercBadTB K L (· ∉ C) := by
    have hfe : GridConn K L G f e := hbf.symm.trans hbe
    refine ⟨f, e, hf, he, hfe.1, not_not.2 hbf, ?_⟩
    have h1 := rtg_cluster hfe.1 hfe.2.1 hfe.2.2
    refine Relation.ReflTransGen.mono (fun x y hxy => ?_) _ _ h1
    obtain ⟨h1, h2, h3, h4, h5⟩ := hxy
    exact ⟨h1, not_not.2 (hbf.trans h2), h3, not_not.2 (hbf.trans h4), percAdjK_of_percAdj4 h5⟩
  obtain ⟨z, -, hzA, hzC⟩ := percGoodLR_meets_percBadTB A C hLR hTB
  exact hzA.trans hzC.symm

/-- **Two attached sites are joined.** -/
theorem gridConn_of_att4 {K L : ℤ} {G : Set (ℤ × ℤ)} {a b : ℤ × ℤ} (ha : Att4 K L G a)
    (hb : Att4 K L G b) : GridConn K L G a b := by
  obtain ⟨⟨c, hc, hac⟩, ⟨d, hd, had⟩, -, -⟩ := ha
  obtain ⟨-, -, ⟨e, he, hbe⟩, ⟨f, hf, hbf⟩⟩ := hb
  exact gridConn_of_crossings hc hd hac had he hf hbe hbf

/-- **Initial sub-crossings.** A good path from a site of column at most `K' - 1` to a site of
column at least `K' - 1` contains a good path inside the first `K'` columns to column `K' - 1`. -/
theorem exists_subcrossing {K L K' : ℤ} {G : Set (ℤ × ℤ)} {z w : ℤ × ℤ}
    (h : Relation.ReflTransGen (PercGoodStep K L (· ∈ G)) z w) (hw : K' - 1 ≤ w.1) :
    percInGrid K L z → z ∈ G → z.1 ≤ K' - 1 → ∃ w', w'.1 = K' - 1 ∧ GridConn K' L G z w' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hz hzG hz1
    refine ⟨_, by omega, GridConn.refl ?_ hzG⟩
    unfold percInGrid at hz ⊢
    omega
  | @head z z' hzz' _ ih =>
    intro hz hzG hz1
    by_cases heq : z.1 = K' - 1
    · refine ⟨z, heq, GridConn.refl ?_ hzG⟩
      unfold percInGrid at hz ⊢
      omega
    · obtain ⟨-, -, hz'g, hz'G, hadj⟩ := hzz'
      have hz'1 : z'.1 ≤ K' - 1 := by
        unfold PercAdj4 at hadj
        omega
      obtain ⟨w', hw', hconn⟩ := ih hz'g hz'G hz'1
      refine ⟨w', hw', ?_⟩
      have hzg' : percInGrid K' L z := by
        unfold percInGrid at hz ⊢
        omega
      have hstep : GridConn K' L G z z' :=
        ⟨hzg', hzG, Relation.ReflTransGen.single ⟨hzg', hzG, hconn.1, hz'G, hadj⟩⟩
      exact GridConn.trans hstep hconn

/-! ### Transposition and reflections -/

/-- Exchanging the two coordinates. -/
def swapSite (z : ℤ × ℤ) : ℤ × ℤ := (z.2, z.1)

/-- Reflection of the columns of the `K`-wide grid. -/
def reflCol (K : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (K - 1 - z.1, z.2)

/-- Reflection of the rows of the `L`-high grid. -/
def reflRow (L : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (z.1, L - 1 - z.2)

/-- A site map carrying grid steps to grid steps carries good paths to good paths. -/
theorem gridConn_map {K L K' L' : ℤ} (φ : ℤ × ℤ → ℤ × ℤ)
    (hgrid : ∀ z, percInGrid K L z → percInGrid K' L' (φ z))
    (hadj : ∀ x y, PercAdj4 x y → PercAdj4 (φ x) (φ y)) {G G' : Set (ℤ × ℤ)}
    (hG : ∀ z, z ∈ G → φ z ∈ G') {a b : ℤ × ℤ} (h : GridConn K L G a b) :
    GridConn K' L' G' (φ a) (φ b) := by
  refine ⟨hgrid a h.1, hG a h.2.1, ?_⟩
  refine Relation.ReflTransGen.lift φ (fun x y hxy => ?_) _ _ h.2.2
  obtain ⟨h1, h2, h3, h4, h5⟩ := hxy
  exact ⟨hgrid x h1, hG x h2, hgrid y h3, hG y h4, hadj x y h5⟩

theorem gridConn_swap {K L : ℤ} {G : Set (ℤ × ℤ)} {a b : ℤ × ℤ} (h : GridConn K L G a b) :
    GridConn L K (swapSite ⁻¹' G) (swapSite a) (swapSite b) :=
  gridConn_map swapSite (fun z hz => by unfold percInGrid swapSite at *; omega)
    (fun x y h => by unfold PercAdj4 swapSite at *; omega)
    (fun z hz => by simpa [swapSite] using hz) h

theorem gridConn_reflCol {K L : ℤ} {G : Set (ℤ × ℤ)} {a b : ℤ × ℤ} (h : GridConn K L G a b) :
    GridConn K L (reflCol K ⁻¹' G) (reflCol K a) (reflCol K b) :=
  gridConn_map (reflCol K) (fun z hz => by unfold percInGrid reflCol at *; omega)
    (fun x y h => by unfold PercAdj4 reflCol at *; omega)
    (fun z hz => by simpa [reflCol] using hz) h

theorem gridConn_reflRow {K L : ℤ} {G : Set (ℤ × ℤ)} {a b : ℤ × ℤ} (h : GridConn K L G a b) :
    GridConn K L (reflRow L ⁻¹' G) (reflRow L a) (reflRow L b) :=
  gridConn_map (reflRow L) (fun z hz => by unfold percInGrid reflRow at *; omega)
    (fun x y h => by unfold PercAdj4 reflRow at *; omega)
    (fun z hz => by simpa [reflRow] using hz) h

theorem reflCol_reflCol (K : ℤ) (z : ℤ × ℤ) : reflCol K (reflCol K z) = z := by
  simp [reflCol]

theorem reflRow_reflRow (L : ℤ) (z : ℤ × ℤ) : reflRow L (reflRow L z) = z := by
  simp [reflRow]

/-- Attachment is invariant under the reflection of the columns. -/
theorem att4_reflCol {K L : ℤ} {G : Set (ℤ × ℤ)} {a : ℤ × ℤ}
    (h : Att4 K L (reflCol K ⁻¹' G) (reflCol K a)) : Att4 K L G a := by
  have hG : reflCol K ⁻¹' (reflCol K ⁻¹' G) = G := by
    ext z
    simp [reflCol_reflCol]
  obtain ⟨⟨c1, h1, g1⟩, ⟨c2, h2, g2⟩, ⟨c3, h3, g3⟩, ⟨c4, h4, g4⟩⟩ := h
  have t : ∀ c, GridConn K L (reflCol K ⁻¹' G) (reflCol K a) c →
      GridConn K L G a (reflCol K c) := fun c g => by
    have := gridConn_reflCol g
    rwa [hG, reflCol_reflCol] at this
  refine ⟨⟨_, ?_, t _ g2⟩, ⟨_, ?_, t _ g1⟩, ⟨_, ?_, t _ g3⟩, ⟨_, ?_, t _ g4⟩⟩ <;>
    simp [reflCol] <;> omega

/-- Attachment is invariant under the reflection of the rows. -/
theorem att4_reflRow {K L : ℤ} {G : Set (ℤ × ℤ)} {a : ℤ × ℤ}
    (h : Att4 K L (reflRow L ⁻¹' G) (reflRow L a)) : Att4 K L G a := by
  have hG : reflRow L ⁻¹' (reflRow L ⁻¹' G) = G := by
    ext z
    simp [reflRow_reflRow]
  obtain ⟨⟨c1, h1, g1⟩, ⟨c2, h2, g2⟩, ⟨c3, h3, g3⟩, ⟨c4, h4, g4⟩⟩ := h
  have t : ∀ c, GridConn K L (reflRow L ⁻¹' G) (reflRow L a) c →
      GridConn K L G a (reflRow L c) := fun c g => by
    have := gridConn_reflRow g
    rwa [hG, reflRow_reflRow] at this
  refine ⟨⟨_, ?_, t _ g1⟩, ⟨_, ?_, t _ g2⟩, ⟨_, ?_, t _ g4⟩, ⟨_, ?_, t _ g3⟩⟩ <;>
    simp [reflRow] <;> omega

theorem swapSite_swapSite (z : ℤ × ℤ) : swapSite (swapSite z) = z := rfl

/-- A top–bottom crossing of the `K × L` grid by a good path. -/
def GridTB (K L : ℤ) (G : Set (ℤ × ℤ)) : Prop :=
  ∃ e f, e.2 = 0 ∧ f.2 = L - 1 ∧ GridConn K L G e f

/-- **The quadrant step.** A site attached inside the lower left `K' × L'` sub-grid is attached
inside the `K × L` grid when the lower band `K × L'` has a left–right crossing and the left band
`K' × L` has a top–bottom crossing. -/
theorem att4_of_quadrant {K L K' L' : ℤ} (hK' : K' ≤ K) (hL' : L' ≤ L) {G : Set (ℤ × ℤ)}
    {a : ℤ × ℤ} (ha : Att4 K' L' G a) (hLR : PercGoodLR K L' (· ∈ G)) (hTB : GridTB K' L G) :
    Att4 K L G a := by
  obtain ⟨⟨c1, h1, g1⟩, ⟨c2, h2, g2⟩, ⟨c3, h3, g3⟩, ⟨c4, h4, g4⟩⟩ := ha
  refine ⟨⟨c1, h1, g1.mono hK' hL'⟩, ?_, ⟨c3, h3, g3.mono hK' hL'⟩, ?_⟩
  · obtain ⟨c, d, hc0, hd, hcg, hcG, hcd⟩ := hLR
    have hK1 : 0 ≤ K' - 1 := by
      have := g1.1
      unfold percInGrid at this
      omega
    obtain ⟨w', hw', hcw'⟩ := exists_subcrossing (K' := K') hcd (by omega) hcg hcG (by omega)
    have hca : GridConn K' L' G c a :=
      gridConn_of_crossings hc0 hw' (GridConn.refl hcw'.1 hcw'.2.1) hcw' h3 h4 g3 g4
    have hcd' : GridConn K L G c d := (show GridConn K L' G c d from ⟨hcg, hcG, hcd⟩).mono le_rfl hL'
    exact ⟨d, hd, (hca.mono hK' hL').symm.trans hcd'⟩
  · obtain ⟨e, f, he0, hf, hef⟩ := hTB
    have hL1 : 0 ≤ L' - 1 := by
      have := g1.1
      unfold percInGrid at this
      omega
    have hs := gridConn_swap hef
    obtain ⟨w', hw', hew'⟩ := exists_subcrossing (K' := L') hs.2.2
      (by simp only [swapSite]; omega) hs.1 hs.2.1 (by simp only [swapSite]; omega)
    have hback := gridConn_swap hew'
    have hpre : swapSite ⁻¹' (swapSite ⁻¹' G) = G := rfl
    rw [hpre, swapSite_swapSite] at hback
    have hae : GridConn K' L' G a e :=
      gridConn_of_crossings h1 h2 g1 g2 he0 (by simpa [swapSite] using hw')
        (GridConn.refl hback.1 hback.2.1) hback
    exact ⟨f, hf, (hae.mono hK' hL').trans (hef.mono hK' le_rfl)⟩

/-- In an all-good grid, a site is joined to the sites to its right in its row. -/
theorem gridConn_row_of_all {K L : ℤ} {G : Set (ℤ × ℤ)} (hall : ∀ z, percInGrid K L z → z ∈ G)
    (a : ℤ × ℤ) (ha : percInGrid K L a) :
    ∀ n : ℕ, a.1 + n < K → GridConn K L G a (a.1 + n, a.2) := by
  intro n
  induction n with
  | zero =>
    intro _
    simpa using GridConn.refl ha (hall a ha)
  | succ n ih =>
    intro hn
    have h1 := ih (by push_cast at hn; omega)
    have hg : percInGrid K L (a.1 + (n + 1 : ℕ), a.2) := by
      unfold percInGrid at ha ⊢
      push_cast
      omega
    refine h1.trans ⟨h1.mem.1, h1.mem.2, Relation.ReflTransGen.single
      ⟨h1.mem.1, h1.mem.2, hg, hall _ hg, ?_⟩⟩
    unfold PercAdj4
    push_cast
    omega

/-- In an all-good grid, a site is joined to the sites above it in its column. -/
theorem gridConn_col_of_all {K L : ℤ} {G : Set (ℤ × ℤ)} (hall : ∀ z, percInGrid K L z → z ∈ G)
    (a : ℤ × ℤ) (ha : percInGrid K L a) :
    ∀ n : ℕ, a.2 + n < L → GridConn K L G a (a.1, a.2 + n) := by
  intro n
  induction n with
  | zero =>
    intro _
    simpa using GridConn.refl ha (hall a ha)
  | succ n ih =>
    intro hn
    have h1 := ih (by push_cast at hn; omega)
    have hg : percInGrid K L (a.1, a.2 + (n + 1 : ℕ)) := by
      unfold percInGrid at ha ⊢
      push_cast
      omega
    refine h1.trans ⟨h1.mem.1, h1.mem.2, Relation.ReflTransGen.single
      ⟨h1.mem.1, h1.mem.2, hg, hall _ hg, ?_⟩⟩
    unfold PercAdj4
    push_cast
    omega

/-- In an all-good grid every site is attached to the four sides. -/
theorem att4_of_all {K L : ℤ} {G : Set (ℤ × ℤ)} (hall : ∀ z, percInGrid K L z → z ∈ G)
    {a : ℤ × ℤ} (ha : percInGrid K L a) : Att4 K L G a := by
  have hg := ha
  unfold percInGrid at hg
  have hl : percInGrid K L (0, a.2) := by unfold percInGrid; simp only; omega
  have hb : percInGrid K L (a.1, 0) := by unfold percInGrid; simp only; omega
  have e1 := gridConn_row_of_all hall (0, a.2) hl a.1.toNat (by simp only; omega)
  have e2 := gridConn_row_of_all hall a ha (K - 1 - a.1).toNat (by omega)
  have e3 := gridConn_col_of_all hall (a.1, 0) hb a.2.toNat (by simp only; omega)
  have e4 := gridConn_col_of_all hall a ha (L - 1 - a.2).toNat (by omega)
  refine ⟨⟨(0, a.2), rfl, ?_⟩, ⟨_, ?_, e2⟩, ⟨(a.1, 0), rfl, ?_⟩, ⟨_, ?_, e4⟩⟩
  · have : ((0 : ℤ) + ((a.1.toNat : ℕ) : ℤ), a.2) = a := Prod.ext (by simp; omega) rfl
    simpa only [this] using e1.symm
  · simp only
    omega
  · have : (a.1, (0 : ℤ) + ((a.2.toNat : ℕ) : ℤ)) = a := Prod.ext rfl (by simp; omega)
    simpa only [this] using e3.symm
  · simp only
    omega

end Rigidity.Percolation
