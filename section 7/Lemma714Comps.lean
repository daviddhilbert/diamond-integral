import «section 7».Lemma714RecodeW

/-! Lemma 7.14, part 22: the sets of a witness schema.

Freezing makes the rows of finitely many definable sets constant on key
classes. This file lists the sets of each kind of schema (`comps`), each as a
set of tuples `(z, row)` (two-block sets are reassociated, `Comp.of2`), and
shows that constant rows of all listed sets give the row constancy needed for
recoding (`WitnessSchema.rowConst_of`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks
open IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

/-- A definable set of tuples `(z, row)` with parameter sorts `sp`. -/
structure Comp (B : Base (M := M)) (sp : Fin p → SortTag) where
  n : ℕ
  D : Set (Fin (p + n) → M)
  hD : DefinableOverBase B (Fin.append sp (rvs n)) D

/-- Reassociation `(z, u, y) ↦ (z, (u, y))`. -/
def assocIdx (p n m : ℕ) : Fin ((p + n) + m) → Fin (p + (n + m)) :=
  Fin.append (Fin.append (Fin.castAdd (n + m)) (fun i => Fin.natAdd p (Fin.castAdd m i)))
    (fun j => Fin.natAdd p (Fin.natAdd n j))

omit hM in
theorem append_assocIdx {n m : ℕ} (z : Fin p → M) (u : Fin n → M) (y : Fin m → M) :
    Fin.append z (Fin.append u y) ∘ assocIdx p n m = Fin.append (Fin.append z u) y := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;> simp [assocIdx]
  · simp [assocIdx]

/-- A two-block set as a component. -/
def Comp.of2 {n m : ℕ} (D : Set (Fin ((p + n) + m) → M))
    (hD : DefinableOverBase B (Fin.append (Fin.append sp (rvs n)) (rvs m)) D) : Comp B sp where
  n := n + m
  D := {w | w ∘ assocIdx p n m ∈ D ∧ w ∈ sortedUniverse (Fin.append sp (rvs (n + m)))}
  hD := hD.preimage_real _ _

namespace KeyRel
variable (K : KeyRel B sq sp)

theorem rel_sorted {x : Fin q → M} {z : Fin p → M} (h : K.R x z) : ∀ i, sortEval (sp i) (z i) := by
  intro i
  have := K.rel_definable.proper _ h (Fin.natAdd q i)
  simpa only [Fin.append_right] using this

theorem rowConst2_of {n m : ℕ} {D : Set (Fin ((p + n) + m) → M)}
    (hD : DefinableOverBase B (Fin.append (Fin.append sp (rvs n)) (rvs m)) D) {x : Fin q → M}
    (h : K.RowConst (Comp.of2 D hD).D x) : K.RowConst2 D x := by
  intro z z' hz hz' u y
  have hzs := K.rel_sorted hz
  have hzs' := K.rel_sorted hz'
  have key : ∀ w : Fin p → M, (∀ i, sortEval (sp i) (w i)) →
      (Fin.append (Fin.append w u) y ∈ D ↔ Fin.append w (Fin.append u y) ∈ (Comp.of2 D hD).D) := by
    intro w hw
    constructor
    · intro hm
      refine ⟨by rw [append_assocIdx]; exact hm, ?_⟩
      have hs := hD.proper _ hm
      intro j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simp only [Fin.append_left]
        exact hw l
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) l
        · have := hs (Fin.castAdd m (Fin.natAdd p i))
          simpa only [Fin.append_left, Fin.append_right] using this
        · have := hs (Fin.natAdd (p + n) i)
          simpa only [Fin.append_right] using this
    · rintro ⟨hm, -⟩
      rwa [append_assocIdx] at hm
  rw [key z hzs, key z' hzs']
  exact h z z' hz hz' (Fin.append u y)

end KeyRel

/-- All listed sets have constant rows on the `K`-class of `x`. -/
def AllRowConst (K : KeyRel B sq sp) (L : List (Comp B sp)) (x : Fin q → M) : Prop :=
  ∀ c ∈ L, K.RowConst c.D x

theorem AllRowConst.append {K : KeyRel B sq sp} {L L' : List (Comp B sp)} {x : Fin q → M} :
    AllRowConst K (L ++ L') x ↔ AllRowConst K L x ∧ AllRowConst K L' x := by
  simp only [AllRowConst, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

/-! ### Lists of sets -/

namespace ChartSchema
variable {d : ℕ} (W : ChartSchema B sp d)

def comps : List (Comp B sp) :=
  [⟨W.arity, W.domain, W.domain_definable⟩, Comp.of2 W.coord W.coord_definable, Comp.of2 W.volume W.volume_definable]

theorem rowConst_of {K : KeyRel B sq sp} {x : Fin q → M} (h : AllRowConst K W.comps x) : W.RowConst K x :=
  ⟨h ⟨W.arity, W.domain, W.domain_definable⟩ (by simp [comps]),
    K.rowConst2_of W.coord_definable (h (Comp.of2 W.coord W.coord_definable) (by simp [comps])),
    K.rowConst2_of W.volume_definable (h (Comp.of2 W.volume W.volume_definable) (by simp [comps]))⟩

end ChartSchema

namespace DatumSchema
variable {k : ℕ} (D : DatumSchema B sp k)

def comps : List (Comp B sp) := D.chart.comps ++ [Comp.of2 D.aperture D.aperture_definable]

theorem rowConst_of {K : KeyRel B sq sp} {x : Fin q → M} (h : AllRowConst K D.comps x) : D.RowConst K x := by
  rw [comps, AllRowConst.append] at h
  exact ⟨D.chart.rowConst_of h.1, K.rowConst2_of D.aperture_definable
    (h.2 (Comp.of2 D.aperture D.aperture_definable) (by simp))⟩

end DatumSchema

namespace MoveSchema
variable {k : ℕ} {X : ChartSchema B sp (1 + k)} (μ : MoveSchema X)

def comps : List (Comp B sp) :=
  μ.rest.comps ++ μ.datum.comps ++ μ.result.comps ++
    [⟨_, μ.piece, μ.piece_definable⟩, ⟨_, μ.q₁, μ.q₁_definable⟩, ⟨_, μ.q₂, μ.q₂_definable⟩,
      Comp.of2 μ.isoRest.graph μ.isoRest.graph_definable, Comp.of2 μ.isoSrc.graph μ.isoSrc.graph_definable,
      Comp.of2 μ.isoRest'.graph μ.isoRest'.graph_definable, Comp.of2 μ.isoShell.graph μ.isoShell.graph_definable,
      Comp.of2 μ.isoEnd.graph μ.isoEnd.graph_definable]

theorem rowConst_of {K : KeyRel B sq sp} {x : Fin q → M} (h : AllRowConst K μ.comps x) : μ.RowConst K x := by
  rw [comps, AllRowConst.append, AllRowConst.append, AllRowConst.append] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨μ.rest.rowConst_of h1, μ.datum.rowConst_of h2, μ.result.rowConst_of h3,
    h4 ⟨_, μ.piece, μ.piece_definable⟩ (by simp), h4 ⟨_, μ.q₁, μ.q₁_definable⟩ (by simp),
    h4 ⟨_, μ.q₂, μ.q₂_definable⟩ (by simp),
    K.rowConst2_of μ.isoRest.graph_definable (h4 (Comp.of2 _ μ.isoRest.graph_definable) (by simp)),
    K.rowConst2_of μ.isoSrc.graph_definable (h4 (Comp.of2 _ μ.isoSrc.graph_definable) (by simp)),
    K.rowConst2_of μ.isoRest'.graph_definable (h4 (Comp.of2 _ μ.isoRest'.graph_definable) (by simp)),
    K.rowConst2_of μ.isoShell.graph_definable (h4 (Comp.of2 _ μ.isoShell.graph_definable) (by simp)),
    K.rowConst2_of μ.isoEnd.graph_definable (h4 (Comp.of2 _ μ.isoEnd.graph_definable) (by simp))⟩

end MoveSchema

namespace ChainSchema
variable {k : ℕ}

def comps : {X : ChartSchema B sp (1 + k)} → {m : ℕ} → ChainSchema X m → List (Comp B sp)
  | _, _, .nil _ => []
  | _, _, .cons μ tail => μ.comps ++ comps tail

theorem rowConst_of {K : KeyRel B sq sp} {x : Fin q → M} :
    {X : ChartSchema B sp (1 + k)} → {m : ℕ} → (c : ChainSchema X m) → AllRowConst K c.comps x → c.RowConst K x
  | _, _, .nil _, _ => trivial
  | _, _, .cons μ tail, h => by
    rw [comps, AllRowConst.append] at h
    exact ⟨μ.rowConst_of h.1, rowConst_of tail h.2⟩

end ChainSchema

namespace WitnessSchema
variable {k : ℕ} {X₀ Y₀ : ChartSchema B sp (1 + k)} (W : WitnessSchema X₀ Y₀)

def comps : List (Comp B sp) :=
  X₀.comps ++ Y₀.comps ++ W.left.comps ++ W.right.comps ++ [Comp.of2 W.final.graph W.final.graph_definable] ++
    W.left.last.comps ++ W.right.last.comps

theorem rowConst_of {K : KeyRel B sq sp} {x : Fin q → M} (h : AllRowConst K W.comps x) : W.RowConst K x := by
  rw [comps, AllRowConst.append, AllRowConst.append, AllRowConst.append, AllRowConst.append,
    AllRowConst.append, AllRowConst.append] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨X₀.rowConst_of h1, Y₀.rowConst_of h2, W.left.rowConst_of h3, W.right.rowConst_of h4,
    K.rowConst2_of W.final.graph_definable (h5 (Comp.of2 _ W.final.graph_definable) (by simp)),
    W.left.last.rowConst_of h6, W.right.last.rowConst_of h7⟩

end WitnessSchema

namespace WitnessSchema0
variable {X₀ Y₀ : ChartSchema B sp 0} (W : WitnessSchema0 X₀ Y₀)

def comps : List (Comp B sp) := X₀.comps ++ Y₀.comps ++ [Comp.of2 W.iso.graph W.iso.graph_definable]

theorem rowConst_of {K : KeyRel B sq sp} {x : Fin q → M} (h : AllRowConst K W.comps x) : W.RowConst K x := by
  rw [comps, AllRowConst.append, AllRowConst.append] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨X₀.rowConst_of h1, Y₀.rowConst_of h2,
    K.rowConst2_of W.iso.graph_definable (h3 (Comp.of2 _ W.iso.graph_definable) (by simp))⟩

end WitnessSchema0

end DiamondIntegral.Section7.Lemma714Schema
