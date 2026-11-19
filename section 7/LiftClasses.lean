import «section 7».StrictCharts
import «section 7».MeasuredRVBounds
import «section 6».DiamondLiftHomomorphism
import «section 5».GammaQEFiniteLaws

/-! The lift `μ𝕃 : K₊ μRV^db[k] → K₊ μVF^◇[k]` on Section 7's isomorphism
classes (Corollary 6.37 in the chart presentation).

A class of bounded charts over the VF-generated base is sent to the class of the
Section 6 measured RV object of its `∞`-free strict form (`StrictCharts`). This
is well defined because chart isomorphisms give measured RV isomorphisms
(`MeasuredRVBridge.measuredIso`), and additive because the measured object of a
definable piece of a chart is literally Section 6's restriction, so Section 6's
RV scissors apply. Composing with Section 6's `liftHom` gives the lift into
`K₊ μVF^◇[k]`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section4.RVChartRestrictions
open DiamondIntegral.Section2
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondLiftHomomorphism DiamondIntegral.Section6.DiamondLift
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.StrictCharts
open DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.MeasuredRVBounds

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {k : ℕ}

/-! ### Measured objects of pieces -/

/-- The measured object of a definable piece is Section 6's restriction. -/
theorem toMeasured_res (c : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k)
    (I : Set (Fin c.arity → M))
    (hI : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin c.arity => .rv) I) :
    toMeasured hc (resChart c I hI) =
      (toMeasured hc c).restrict (rawDefSet hc (c.domain ∩ I) (c.domain_definable.inter hI))
        (fun _ h => h.1) := rfl

theorem restrict_congr (U : MeasuredRVObject (M := M) S k)
    {A A' : DefSet (rawRVSpace (M := M) U.object.arity) S} (h : A = A')
    (hA : A.carrier ⊆ U.object.domain.carrier) (hA' : A'.carrier ⊆ U.object.domain.carrier) :
    U.restrict A hA = U.restrict A' hA' := by
  subst h
  rfl

/-- The measured object of the complementary piece is Section 6's complementary
restriction. -/
theorem toMeasured_cres (c : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k)
    (I : Set (Fin c.arity → M))
    (hI : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin c.arity => .rv) I) :
    toMeasured hc (cresChart c I hI) =
      restrictCompl (toMeasured hc c) (rawDefSet hc (c.domain ∩ I) (c.domain_definable.inter hI)) := by
  change (toMeasured hc c).restrict (rawDefSet hc (c.domain \ I) _) (fun _ h => h.1) =
    (toMeasured hc c).restrict _ _
  apply restrict_congr
  apply DefSet.eq_of_carrier_eq
  apply Set.ext
  intro a
  change rvValues a ∈ c.domain \ I ↔ rvValues a ∈ c.domain ∧ ¬ rvValues a ∈ c.domain ∩ I
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 h.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 ⟨h1, h⟩⟩

/-! ### The class map into `K₊ μRV^db[k]` -/

section Lift
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (T : LRV.Substructure M) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : DiamondIntegral.Section2.NontrivialDefinableGamma
    (⟨(T : Set M), ∅⟩ : DiamondIntegral.Section2.ParameterBase M))

/-- The base with no Gamma names. -/
abbrev BT (T : LRV.Substructure M) : GammaParameters.Base (M := M) := ⟨(T : Set M), ∅⟩

/-- The discharged Gamma rational-affine input. -/
abbrev lin : DiamondIntegral.Section2.GammaPiecewiseRationalAffineInput (M := M) :=
  DiamondIntegral.Section5.GammaQE.gamma_piecewise_rational_affine

/-- The Section 6 doubly bounded measured object of a strict bounded chart. -/
def dbOf (c : Chart (BT T) k) (hb : RVMeasuredBounds.DomainBounded c) (hn : NoInfinity c) :
    DBObject (T : Set M) k :=
  ⟨toMeasured hc c, toMeasured_doublyBounded hc h00 lin hκ.le hs hsmall hΓ c hb hn⟩

/-- The Section 6 object of a class representative: its strict form. -/
def dbObj (a : Obj (BT T) k) : DBObject (T : Set M) k :=
  dbOf hc h00 hκ hs T hsmall hΓ (strictChart h00 a.toChart)
    (strictChart_bounded h00 a.toChart a.domain_bounded)
    (fun x hx i => strictChart_infinityFree h00 a.toChart x hx i)

theorem dbOf_iso {c d : Chart (BT T) k} (hcb : RVMeasuredBounds.DomainBounded c) (hcn : NoInfinity c)
    (hdb : RVMeasuredBounds.DomainBounded d) (hdn : NoInfinity d) (F : Iso c d) :
    (rvPresentation (T : Set M) k).iso (dbOf hc h00 hκ hs T hsmall hΓ c hcb hcn)
      (dbOf hc h00 hκ hs T hsmall hΓ d hdb hdn) :=
  ⟨measuredIso hc F⟩

theorem dbObj_iso {a b : Obj (BT T) k} (F : Iso a.toChart b.toChart) :
    (rvPresentation (T : Set M) k).iso (dbObj hc h00 hκ hs T hsmall hΓ a) (dbObj hc h00 hκ hs T hsmall hΓ b) :=
  dbOf_iso hc h00 hκ hs T hsmall hΓ _ _ _ _ (RVMeasuredIsomorphisms.trans
    (RVMeasuredIsomorphisms.symm (strictIso h00 a.toChart))
    (RVMeasuredIsomorphisms.trans F (strictIso h00 b.toChart)))

/-- The class in `K₊ μRV^db[k]` (Section 6's scissor presentation). -/
def rvCls (x : Cls (BT T) k) : DiamondIntegral.Section3.KPlus (rvPresentation (T : Set M) k) :=
  Quotient.lift (fun a => DiamondIntegral.Section3.positiveClass _ (dbObj hc h00 hκ hs T hsmall hΓ a))
    (fun _ _ h => by
      obtain ⟨F⟩ := h
      exact DiamondIntegral.Section3.positiveClass_iso _ (dbObj_iso hc h00 hκ hs T hsmall hΓ F)) x

theorem rvCls_cls (a : Obj (BT T) k) :
    rvCls hc h00 hκ hs T hsmall hΓ (cls a) =
      DiamondIntegral.Section3.positiveClass _ (dbObj hc h00 hκ hs T hsmall hΓ a) := rfl

theorem positiveClass_dbOf_eq {c d : Chart (BT T) k} (hcb : RVMeasuredBounds.DomainBounded c)
    (hcn : NoInfinity c) (hdb : RVMeasuredBounds.DomainBounded d) (hdn : NoInfinity d)
    (h : Nonempty (Iso c d)) :
    DiamondIntegral.Section3.positiveClass (rvPresentation (T : Set M) k) (dbOf hc h00 hκ hs T hsmall hΓ c hcb hcn) =
      DiamondIntegral.Section3.positiveClass _ (dbOf hc h00 hκ hs T hsmall hΓ d hdb hdn) := by
  obtain ⟨F⟩ := h
  exact DiamondIntegral.Section3.positiveClass_iso _ (dbOf_iso hc h00 hκ hs T hsmall hΓ hcb hcn hdb hdn F)

/-- Additivity: the class of a strict chart splits along a definable piece. -/
theorem positiveClass_split (c : Chart (BT T) k) (hb : RVMeasuredBounds.DomainBounded c)
    (hn : NoInfinity c) (I : Set (Fin c.arity → M))
    (hI : DefinableOverBase (BT T) (fun _ : Fin c.arity => .rv) I) :
    DiamondIntegral.Section3.positiveClass (rvPresentation (T : Set M) k) (dbOf hc h00 hκ hs T hsmall hΓ c hb hn) =
      DiamondIntegral.Section3.positiveClass _ (dbOf hc h00 hκ hs T hsmall hΓ (resChart c I hI)
        (restrict_domain_bounded _ _ _ _ hb) (fun x hx => hn x hx.1)) +
      DiamondIntegral.Section3.positiveClass _ (dbOf hc h00 hκ hs T hsmall hΓ (cresChart c I hI)
        (restrict_domain_bounded _ _ _ _ hb) (fun x hx => hn x hx.1)) := by
  let D := rawDefSet hc (c.domain ∩ I) (c.domain_definable.inter hI)
  have hD : D.carrier ⊆ (toMeasured hc c).object.domain.carrier := fun _ h => h.1
  have hU := (dbOf hc h00 hκ hs T hsmall hΓ c hb hn).2
  have h := DiamondIntegral.Section3.positiveClass_scissor (rvPresentation (T : Set M) k)
    (a := ⟨(toMeasured hc c).restrict D hD, (toMeasured hc c).restrict_doublyBounded D hD hU⟩)
    (b := ⟨restrictCompl (toMeasured hc c) D, (toMeasured hc c).restrict_doublyBounded _ _ hU⟩)
    (c := dbOf hc h00 hκ hs T hsmall hΓ c hb hn) (d := ⟨emptyRV (T : Set M) k, emptyRV_doublyBounded⟩)
    ⟨toMeasured hc c, hU, D, hD, rfl, rfl, rfl, rfl⟩
  have he : DiamondIntegral.Section3.positiveClass (rvPresentation (T : Set M) k)
      ⟨emptyRV (T : Set M) k, emptyRV_doublyBounded⟩ = 0 :=
    DiamondIntegral.Section3.positiveClass_empty (rvPresentation (T : Set M) k)
  rw [he, add_zero] at h
  have e1 : (⟨(toMeasured hc c).restrict D hD, (toMeasured hc c).restrict_doublyBounded D hD hU⟩ :
      DBObject (T : Set M) k) = dbOf hc h00 hκ hs T hsmall hΓ (resChart c I hI)
        (restrict_domain_bounded _ _ _ _ hb) (fun x hx => hn x hx.1) :=
    Subtype.ext (toMeasured_res hc c I hI).symm
  have e2 : (⟨restrictCompl (toMeasured hc c) D, (toMeasured hc c).restrict_doublyBounded _ _ hU⟩ :
      DBObject (T : Set M) k) = dbOf hc h00 hκ hs T hsmall hΓ (cresChart c I hI)
        (restrict_domain_bounded _ _ _ _ hb) (fun x hx => hn x hx.1) :=
    Subtype.ext (toMeasured_cres hc c I hI).symm
  rw [e1, e2] at h
  exact h.symm

theorem rvCls_add (x y : Cls (BT T) k) :
    rvCls hc h00 hκ hs T hsmall hΓ (x + y) = rvCls hc h00 hκ hs T hsmall hΓ x + rvCls hc h00 hκ hs T hsmall hΓ y := by
  obtain ⟨a, rfl⟩ := cls_surjective x
  obtain ⟨b, rfl⟩ := cls_surjective y
  rw [← cls_coprod, rvCls_cls, rvCls_cls, rvCls_cls]
  let cp := coprod a b
  let F := strictIso h00 cp.toChart
  let I := image F (L a.toChart b.toChart).domain
  have hI : DefinableOverBase (BT T) (fun _ => .rv) I :=
    image_definable F _ (L a.toChart b.toChart).domain_definable
  change DiamondIntegral.Section3.positiveClass _ (dbOf hc h00 hκ hs T hsmall hΓ (strictChart h00 cp.toChart) _ _) = _
  rw [positiveClass_split hc h00 hκ hs T hsmall hΓ _ _ _ I hI]
  have hpi := cls_piece_image (a := cp) (b := strictObj h00 cp) F (L a.toChart b.toChart).domain
    (L a.toChart b.toChart).domain_definable
  have hcpi := cls_cpiece_image (a := cp) (b := strictObj h00 cp) F (L a.toChart b.toChart).domain
    (L a.toChart b.toChart).domain_definable
  have h1 : cls (piece (strictObj h00 cp) I hI) = cls (strictObj h00 a) := by
    rw [cls_strictObj]
    exact hpi.symm.trans (cls_eq_of_iso (a := piece cp _ (L a.toChart b.toChart).domain_definable) (b := a)
      (coprodInsideLeft a.toChart b.toChart))
  have h2 : cls (cpiece (strictObj h00 cp) I hI) = cls (strictObj h00 b) := by
    rw [cls_strictObj]
    exact hcpi.symm.trans (cls_eq_of_iso (a := cpiece cp _ (L a.toChart b.toChart).domain_definable) (b := b)
      (coprodOutsideLeft a.toChart b.toChart))
  congr 1
  · exact positiveClass_dbOf_eq hc h00 hκ hs T hsmall hΓ _ _ _ _ (cls_eq_iff.mp h1)
  · exact positiveClass_dbOf_eq hc h00 hκ hs T hsmall hΓ _ _ _ _ (cls_eq_iff.mp h2)

section VF
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (B₀ : VFGeneratedFieldBase T) (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

variable (G k) in
/-- Corollary 6.37 on Section 7's classes: the lift `μ𝕃 : K₊ μRV^db[k] → K₊ μVF^◇[k]`. -/
def liftCls : Cls (BT T) k →+ DiamondIntegral.Section6.DiamondGrothendieck.KPlus (T : Set M) G hc k where
  toFun x := liftHom k G h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt (rvCls hc h00 hκ hs T hsmall hΓ x)
  map_zero' := by
    rw [← cls_zero, rvCls_cls, liftHom_class]
    apply DiamondIntegral.Section6.DiamondEmpty.vfClass_of_empty hc
    apply Set.eq_empty_of_forall_notMem
    rintro _ ⟨u, _⟩
    obtain ⟨v, hv', _⟩ := u.property
    exact hv'
  map_add' x y := by
    change liftHom k G h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt (rvCls hc h00 hκ hs T hsmall hΓ (x + y)) = _
    rw [rvCls_add, map_add]

theorem liftCls_cls (a : Obj (BT T) k) :
    liftCls (G := G) (k := k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt (cls a) =
      DiamondIntegral.Section6.DiamondGrothendieck.vfClass G hc
        (liftObject (dbObj hc h00 hκ hs T hsmall hΓ a).1
          (measuredRVLift_properInvariant h00 hc hκ hs hv _ (dbObj hc h00 hκ hs T hsmall hΓ a).2)) :=
  liftHom_class (G := G) (k := k) h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt _

end VF

end Lift

end DiamondIntegral.Section7.LiftClasses
