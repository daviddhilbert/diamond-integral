import «section 7».Lemma722Objects

/-! The cells of Lemma 7.22.

Let `A'` be an object of `μVF^◇[2]` whose form depends only on its labels, and
`F` a standard contraction of `A'` in the order `e` (from the Lemma 7.20
input), with normalization `D`. On the normalized image `Y = D(A')`
(`Lemma722Objects.normObject`) the contraction is read by the original
contraction map of the lift of `F`. Grafting its RV point gives the object
`A* = cellObject` (`GraftObjects.graftObject`), with a graft morphism
`Y → A*` that fixes every VF coordinate.

**Label fibres are cells** (`cellOf_eq`): the label fibre of `A*` over
`(w, s)`, read in the order `(x_{e 0}, x_{e 1})`, is the fibre `cellAt F s` of
the contraction over `s` (in normalized coordinates, as in the Lemma 7.20
input). The labels `w` of `Y` are determined by `s`, since the contraction
retains them. So the uniform cell data of the Lemma 7.20 input are functions of
the labels of `A*`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma722Cells
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section7.GraftObjects DiamondIntegral.Section7.LabelPieces
open DiamondIntegral.Section7.Lemma722Objects DiamondIntegral.Section7.TwoCellInput

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

/-- The form of a graft depends only on the labels when the form of the source
does. -/
theorem graftObject_form_labels {n q : ℕ} (A : VFObject (M := M) (T : Set M) n)
    {D : DefSet (rawMixedSpace (M := M) 0 q) (T : Set M)} (τ : Map A.carrier D) (hτ : ProperCovariant τ)
    (hω : ∀ p z : A.carrier, p.val.2 = z.val.2 → A.form p = A.form z) :
    ∀ p z : (graftObject h00 hc hκ hs hv A τ hτ).carrier, p.val.2 = z.val.2 →
      (graftObject h00 hc hκ hs hv A τ hτ).form p = (graftObject h00 hc hκ hs hv A τ hτ).form z := by
  intro p z he
  obtain ⟨p₀, rfl, hp⟩ := graft_image_point hc A τ p
  obtain ⟨z₀, hz, hz'⟩ := graft_image_point hc A τ z
  subst hz
  change graftForm hc A τ (graft hc τ p₀) = graftForm hc A τ (graft hc τ z₀)
  rw [graftForm_graft, graftForm_graft]
  apply hω
  have h1 := congrArg Prod.snd hp
  have h2 := congrArg Prod.snd hz'
  rw [h1, h2]
  funext i
  exact congrFun he (Fin.castAdd q i)

/-- The label fibre of a set, read in the order `(x_{e 0}, x_{e 1})`. -/
def cellOf {r : ℕ} (X : DefSet (rawMixedSpace (M := M) 2 r) (T : Set M)) (e : Equiv.Perm (Fin 2))
    (w : Fin r → RVInfinity M) : Set (VF M × VF M) :=
  {q | ∃ x : Fin 2 → VF M, (x, w) ∈ X.carrier ∧ q = (x (e 0), x (e 1))}

section Cells
variable (A' : VFObject (M := M) (T : Set M) 2) (hω : ∀ p z : A'.carrier, p.val.2 = z.val.2 → A'.form p = A'.form z)
variable {e : Equiv.Perm (Fin 2)} (F : StandardContraction (G := G) A'.carrier e)

/-- The RV point of the contraction, read on the normalized image. -/
def cellTau : Map (normObject h00 hc hκ hs hv A' hω F.normalization).carrier
    (DefSet.univ (rawMixedSpace (M := M) 0 F.arity) (T : Set M)) :=
  rvProjection F.lift.originalMap

include linear hsmall hΓ in
theorem cellTau_covariant : ProperCovariant (cellTau h00 hc hκ hs hv A' hω F) :=
  ProperCovariant.rvProjection _ (F.lift.originalMap_homeomorphism h00 hc linear hκ hs hv hsmall hΓ
    (F.normalization.image_properInvariant h00 hc hκ hs hv)).covariant

theorem cellTau_labels (y : (normObject h00 hc hκ hs hv A' hω F.normalization).carrier) :
    (cellTau h00 hc hκ hs hv A' hω F y).val.2 = (F.lift.originalContraction y).val.2 :=
  F.lift.originalMap_labels y

/-- **The object `A*`**: the normalized image with the RV point of the
contraction grafted as labels. -/
def cellObject : VFObject (M := M) (T : Set M) 2 :=
  graftObject h00 hc hκ hs hv (normObject h00 hc hκ hs hv A' hω F.normalization) (cellTau h00 hc hκ hs hv A' hω F)
    (cellTau_covariant h00 hc linear hκ hs hv hsmall hΓ A' hω F)

theorem cellObject_form_labels :
    ∀ p z : (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F).carrier, p.val.2 = z.val.2 →
      (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F).form p =
        (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F).form z :=
  graftObject_form_labels h00 hc hκ hs hv _ _ _ (normObject_form_labels h00 hc hκ hs hv A' hω F.normalization)

theorem cellObject_doublyBounded :
    VFDoublyBounded (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F).carrier.carrier := by
  obtain ⟨δ, hδ⟩ := normObject_doublyBounded h00 hc hκ hs hv A' hω F.normalization
  refine ⟨δ, ?_⟩
  rintro _ ⟨p, rfl⟩ i
  exact hδ p.val p.property i

/-- The graft of the RV point is a morphism, fixing every VF coordinate. -/
theorem cellMorphism :
    ∃ K : Morphism G (normObject h00 hc hκ hs hv A' hω F.normalization)
        (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F),
      K.map = graft hc (cellTau h00 hc hκ hs hv A' hω F) :=
  graftMorphism h00 hc linear hκ hs hv hsmall hΓ _ _ _

/-- The contraction retains the labels of the normalized image. -/
theorem originalContraction_retained (y : F.normalization.map.image) (i : Fin (2 + A'.labels)) :
    (F.lift.originalContraction y).val.2 (F.program.oldLabels i) = y.val.2 i :=
  F.program.retained (vfRelabeling F.normalization.map.image e y) i

/-- The RV point over a label of `A*`. -/
def pointOf (w : Fin ((2 + A'.labels) + F.arity) → RVInfinity M)
    (hw : ∃ x : Fin 2 → VF M, (x, w) ∈ (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F).carrier.carrier) :
    F.rvTarget :=
  ⟨(Fin.elim0, fun j => w (Fin.natAdd _ j)), by
    obtain ⟨x, hx⟩ := hw
    obtain ⟨y, hy, -⟩ := graft_image_point hc _ (cellTau h00 hc hκ hs hv A' hω F) ⟨(x, w), hx⟩
    have hval := congrArg Subtype.val hy
    rw [graft_apply] at hval
    have h2 : Fin.append y.val.2 (cellTau h00 hc hκ hs hv A' hω F y).val.2 = w := congrArg Prod.snd hval
    have hl : (fun j => w (Fin.natAdd _ j)) = (F.lift.originalContraction y).val.2 := by
      funext j
      have e1 := congrFun h2 (Fin.natAdd _ j)
      have e2 : Fin.append y.val.2 (cellTau h00 hc hκ hs hv A' hω F y).val.2 (Fin.natAdd _ j) =
          (cellTau h00 hc hκ hs hv A' hω F y).val.2 j := Fin.append_right _ _ j
      exact (e1.symm.trans e2).trans (congrFun (cellTau_labels h00 hc hκ hs hv A' hω F y) j)
    have he : ((Fin.elim0, fun j => w (Fin.natAdd _ j)) : Mixed M 0 F.arity) = (F.lift.originalContraction y).val :=
      Prod.ext (Subsingleton.elim _ _) hl
    rw [he]
    exact (F.lift.originalContraction y).property⟩

/-- **Label fibres of `A*` are the fibres of the contraction.** -/
theorem cellOf_eq (w : Fin ((2 + A'.labels) + F.arity) → RVInfinity M)
    (hw : ∃ x : Fin 2 → VF M, (x, w) ∈ (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F).carrier.carrier) :
    cellOf (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F).carrier e w =
      cellAt F (pointOf h00 hc linear hκ hs hv hsmall hΓ A' hω F w hw) := by
  let τ := cellTau h00 hc hκ hs hv A' hω F
  have hlab : ∀ y : F.normalization.map.image, ∀ x,
      ∀ hx : (x, w) ∈ (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F).carrier.carrier,
      graft hc τ y = ⟨(x, w), hx⟩ → y.val.1 = x ∧ y.val.2 = (fun i => w (Fin.castAdd F.arity i)) ∧
        (F.lift.originalContraction y).val.2 = fun j => w (Fin.natAdd _ j) := by
    intro y x hx hy
    have hval := congrArg Subtype.val hy
    rw [graft_apply] at hval
    have h1 : y.val.1 = x := congrArg Prod.fst hval
    have h2 : Fin.append y.val.2 (τ y).val.2 = w := congrArg Prod.snd hval
    refine ⟨h1, funext fun i => ?_, funext fun j => ?_⟩
    · have e1 := congrFun h2 (Fin.castAdd F.arity i)
      have e2 : Fin.append y.val.2 (τ y).val.2 (Fin.castAdd F.arity i) = y.val.2 i := Fin.append_left _ _ i
      rw [← e1, e2]
    · have e1 := congrFun h2 (Fin.natAdd _ j)
      have e2 : Fin.append y.val.2 (τ y).val.2 (Fin.natAdd _ j) = (τ y).val.2 j := Fin.append_right _ _ j
      rw [← e1, e2, cellTau_labels]
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, -⟩ := graft_image_point hc _ τ ⟨(x, w), hx⟩
    obtain ⟨h1, -, h3⟩ := hlab y x hx hy
    obtain ⟨p₀, hp₀⟩ := (F.normalization.bijective h00).surjective y
    refine ⟨p₀, ?_, ?_⟩
    · apply Subtype.ext
      change (F.lift.originalContraction (F.normalization.bijection p₀)).val = _
      rw [hp₀]
      exact Prod.ext (Subsingleton.elim (α := Fin 0 → VF M) _ _) h3
    · have hpt : F.normalization.point p₀.val = y.val := congrArg Subtype.val hp₀
      rw [hpt, h1]
  · rintro ⟨p₀, hp₀, rfl⟩
    obtain ⟨x₀, hx₀⟩ := hw
    obtain ⟨y', hy', -⟩ := graft_image_point hc _ τ ⟨(x₀, w), hx₀⟩
    obtain ⟨-, h2', h3'⟩ := hlab y' x₀ hx₀ hy'
    let y := F.normalization.bijection p₀
    have hcy : (F.lift.originalContraction y).val.2 = fun j => w (Fin.natAdd _ j) :=
      congrArg (fun z : F.rvTarget => z.val.2) hp₀
    have hyl : y.val.2 = y'.val.2 := by
      funext i
      rw [← originalContraction_retained A' F y i, ← originalContraction_retained A' F y' i, hcy, h3']
    have hmem : ((y.val.1, w) : Mixed M 2 _) ∈ (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F).carrier.carrier := by
      refine ⟨y, ?_⟩
      change (graft hc τ y).val = _
      rw [graft_apply]
      refine Prod.ext rfl ?_
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · have e2 : Fin.append y.val.2 (τ y).val.2 (Fin.castAdd F.arity i) = y.val.2 i := Fin.append_left _ _ i
        change Fin.append y.val.2 (τ y).val.2 (Fin.castAdd F.arity i) = w (Fin.castAdd F.arity i)
        rw [e2, hyl, h2']
      · have e2 : Fin.append y.val.2 (τ y).val.2 (Fin.natAdd _ j) = (τ y).val.2 j := Fin.append_right _ _ j
        change Fin.append y.val.2 (τ y).val.2 (Fin.natAdd _ j) = w (Fin.natAdd _ j)
        rw [e2, cellTau_labels, hcy]
    exact ⟨y.val.1, hmem, rfl⟩

end Cells

end DiamondIntegral.Section7.Lemma722Cells
