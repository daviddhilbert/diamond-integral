import «section 7».Lemma720Stage1
import «section 7».TwoCellInput

/-! Lemma 7.20, step 2: a binary standard contraction assembled from a
normalization and two stages with label-determined displacement, and its fibres.

`Build A` bundles the normalization `N`, a first stage `S₁` on the normalized set
(in the identity order, contracting coordinate `1`) and a second stage `S₂` on the
contracted set. `Build.contraction` is the resulting `StandardContraction A 1`. Its
fibre over `s`, read in normalized coordinates (`TwoCellInput.cellAt`), is described
by the two offsets (`mem_cellAt_iff`):

`(x, y) ∈ cellAt F s ↔ ∃ b, S₂ b = s ∧ b_x = x ∧ rv(y − ε₁ b) = t₁(b)`,

and `S₂ b = s` holds exactly when the labels of `b` are those recovered from `s` and
`rv(x − ε₂ s) = t₂(s)`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCellInput

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- The normalized source in the identity order. -/
abbrev normalizedSet {A : DefSet (rawMixedSpace (M := M) 2 r) S} (N : ZeroCenteredData A) :=
  reindexedVFSet N.map.image (Equiv.refl (Fin 2))

/-- The data of the contraction: a normalization and two stages with label-determined
displacement. -/
structure Build (A : DefSet (rawMixedSpace (M := M) 2 r) S) where
  N : ZeroCenteredData A
  S₁ : ShearContractionStage (G := G) (normalizedSet N)
  S₂ : ShearContractionStage (G := G) S₁.stage.contracted

namespace Build
variable {A : DefSet (rawMixedSpace (M := M) 2 r) S} (X : Build (G := G) A)

/-- The ordered program: the two stages, then the RV target. -/
def program : OrderedStandardContractionProgram (G := G) S (normalizedSet X.N) X.S₂.stage.contracted :=
  .step X.S₁.stage (.step X.S₂.stage (.zero X.S₂.stage.contracted))

theorem program_toMap (a : normalizedSet X.N) :
    X.program.toMap a = X.S₂.stage.contraction (X.S₁.stage.contraction a) := rfl

/-- The standard contraction, with any lift of the program. -/
def contraction (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) :
    StandardContraction (G := G) A (Equiv.refl (Fin 2)) where
  normalization := X.N
  arity := X.S₂.stage.arity
  rvTarget := X.S₂.stage.contracted
  program := X.program
  lift := Classical.choice (exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ
    X.program (reindexedVFSet_properInvariant _ _ (X.N.image_properInvariant h00 hc hκ hs hv)))

section Fibres
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))

/-- The first offset `ε₁`, on the contracted set of the first stage. -/
def eps₁ (b : X.S₁.stage.contracted) : VF M := Stage.eps X.S₁.stage X.S₁.displacement b

/-- The second offset `ε₂`, on the RV target. -/
def eps₂ (s : X.S₂.stage.contracted) : VF M := Stage.eps X.S₂.stage X.S₂.displacement s

theorem contraction_apply (p : A) :
    (X.contraction h00 hc linear hκ hs hv hsmall hΓ).contraction p =
      X.S₂.stage.contraction (X.S₁.stage.contraction
        (vfRelabeling X.N.map.image (Equiv.refl (Fin 2)) (X.N.bijection p))) := rfl

/-- The normalized point of `p`, as a point of the normalized set. -/
theorem relabel_value (p : A) :
    (vfRelabeling X.N.map.image (Equiv.refl (Fin 2)) (X.N.bijection p)).val = X.N.point p.val := rfl

/-- **The fibre of the assembled contraction**, in normalized coordinates. -/
theorem mem_cellAt_iff (s : X.S₂.stage.contracted) (x y : VF M) :
    (x, y) ∈ cellAt (X.contraction h00 hc linear hκ hs hv hsmall hΓ) s ↔
      ∃ b : X.S₁.stage.contracted, X.S₂.stage.contraction b = s ∧ b.val.1 0 = x ∧
        rv M (y - X.eps₁ b) = b.val.2 X.S₁.stage.leading := by
  constructor
  · rintro ⟨p, hp, hq⟩
    let a := vfRelabeling X.N.map.image (Equiv.refl (Fin 2)) (X.N.bijection p)
    have ha : a.val = X.N.point p.val := rfl
    refine ⟨X.S₁.stage.contraction a, hp, ?_, ?_⟩
    · have h1 := congrFun (X.S₁.stage.contraction_fixes_complement a) 0
      have hx : x = (X.N.point p.val).1 0 := (Prod.mk.inj hq).1
      rw [h1, hx]
      rfl
    · have h := ((Stage.contraction_eq_iff X.S₁.stage X.S₁.displacement a
        (X.S₁.stage.contraction a)).mp rfl).2.2
      have hy : y = (X.N.point p.val).1 1 := (Prod.mk.inj hq).2
      rw [hy]
      exact h
  · rintro ⟨b, hb, hx, hy⟩
    obtain ⟨a, ha, hay⟩ := Stage.exists_mem_fibre X.S₁.stage X.S₁.displacement b y hy
    obtain ⟨c, hc'⟩ := (vfRelabeling_bijective X.N.map.image (Equiv.refl (Fin 2))).surjective a
    obtain ⟨p, hp⟩ := (X.N.bijective h00).surjective c
    refine ⟨p, ?_, ?_⟩
    · rw [contraction_apply, hp, hc', ha, hb]
    · have hav : a.val = X.N.point p.val := by
        rw [← hc', ← hp]
        rfl
      have hax : a.val.1 0 = x := by
        rw [← hx]
        exact (congrFun (X.S₁.stage.contraction_fixes_complement a) 0).symm.trans (by rw [ha])
      refine Prod.ext ?_ ?_
      · change x = (X.N.point p.val).1 0
        rw [← hav, hax]
      · change y = (X.N.point p.val).1 1
        rw [← hav]
        exact hay.symm

/-- The labels of the first contracted set recovered from a point of the RV target. -/
def labelsOf (s : X.S₂.stage.contracted) : Fin X.S₁.stage.arity → RVInfinity M :=
  fun i => s.val.2 (X.S₂.stage.oldLabels i)

/-- Membership in a fibre of the second stage. -/
theorem second_contraction_eq_iff (b : X.S₁.stage.contracted) (s : X.S₂.stage.contracted) :
    X.S₂.stage.contraction b = s ↔
      b.val.2 = X.labelsOf s ∧ rv M (b.val.1 0 - X.eps₂ s) = s.val.2 X.S₂.stage.leading := by
  rw [Stage.contraction_eq_iff X.S₂.stage X.S₂.displacement b s]
  constructor
  · rintro ⟨-, hLab, hRV⟩
    exact ⟨funext hLab, hRV⟩
  · rintro ⟨hLab, hRV⟩
    refine ⟨funext (fun i => i.elim0), fun i => congrFun hLab i, hRV⟩

end Fibres

end Build

end DiamondIntegral.Section7.Lemma720
