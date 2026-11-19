import «section 7».SpecialChains
import «section 7».RelativeRestrict

/-! Lemma 7.11 (`special:to:blowup:coa`): a relative step on a set of a chain.

A tagged set `X` of a chain is, as a set, the lift of the chart of its
contraction (`carrier_eq_chartLift`). Transporting relative aperture data
along this equality (`castData`) puts us in the situation of
`SpecialStep.step_of_data`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.SpecialChainStep
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.SpecialChains
open DiamondIntegral.Section7.SpecialStep DiamondIntegral.Section7.MeasuredRVBridge

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-! ### Transport of relative aperture data along an equality of sets -/

section Cast
variable {X Y : DefSet (rawMixedSpace (M := M) n r) S}

/-- Relative aperture data transported along an equality of sets. -/
def castData (h : X = Y) (R : DiamondIntegral.Section6.RelativeApertureData (G := G) X) :
    DiamondIntegral.Section6.RelativeApertureData (G := G) Y :=
  cast (congrArg (fun Z => DiamondIntegral.Section6.RelativeApertureData (G := G) Z) h) R

theorem castData_coordinate (h : X = Y) (R : DiamondIntegral.Section6.RelativeApertureData (G := G) X) :
    (castData h R).coordinate = R.coordinate := by
  subst h
  rfl

theorem castData_activeTags (h : X = Y) (R : DiamondIntegral.Section6.RelativeApertureData (G := G) X) :
    (castData h R).activeTags = R.activeTags := by
  subst h
  rfl

theorem castData_extendedEndpoint (h : X = Y) (R : DiamondIntegral.Section6.RelativeApertureData (G := G) X) :
    (castData h R).extendedEndpoint = R.extendedEndpoint := by
  subst h
  rfl

theorem castData_point (h : X = Y) (R : DiamondIntegral.Section6.RelativeApertureData (G := G) X) :
    (castData h R).point = R.point := by
  subst h
  rfl

theorem castData_image (h : X = Y) (R : DiamondIntegral.Section6.RelativeApertureData (G := G) X) :
    (castData h R).map.image = R.map.image := by
  subst h
  rfl

end Cast

/-! ### A tagged set of a chain is a chart lift -/

theorem mem_lift_iff (hc : CanonicalStructure.IsCanonical (M := M)) {k : ℕ}
    (c : DiamondIntegral.Section4.RVMeasuredCharts.Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k) (p : Mixed M k c.arity) :
    p ∈ (rvLift (toMeasured hc c).object).carrier ↔
      rvValues p.2 ∈ c.domain ∧ rvValues (tupleRV M p.1) = c.coordinate (rvValues p.2) := by
  constructor
  · rintro ⟨u, hu, hv⟩
    have hd : rvValues u.val ∈ c.domain := u.property
    rw [hu] at hd
    refine ⟨hd, ?_⟩
    have h1 : rvValues (tupleRV M p.1) = rvValues ((toMeasured hc c).object.value u) := by
      rw [hv]
      rfl
    rw [h1, ← hu]
    rfl
  · rintro ⟨hd, hv⟩
    refine ⟨⟨p.2, hd⟩, rfl, ?_⟩
    apply rvValues_injective
    change c.coordinate (rvValues p.2) = rvValues (tupleRV M p.1)
    exact hv.symm

section ChartLift
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M}
variable {X : DefSet (rawMixedSpace (M := M) n r) (T : Set M)} (g : Good T X)
variable (hT : ∀ p ∈ X.carrier, ∀ q ∈ X.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)

/-- The contraction of a tagged set of a chain. -/
abbrev contr : MeasuredRVObject (M := M) (T : Set M) n :=
  contractedMeasuredRVObject X hT g.pullback g.finite g.vfBounded g.form g.form_labels

theorem contr_db : (contr g hT).doublyBounded :=
  contractedMeasuredRVObject_doublyBounded _ _ _ _ _ g.rvBounded _ _

/-- A tagged set of a chain is the lift of the chart of its contraction. -/
theorem carrier_eq_chartLift : X = rvLift (toMeasured hc (chartOf hc (contr g hT))).object := by
  apply DefSet.eq_of_carrier_eq
  rw [← preparedRVObject_lift_carrier X g.pullback hT]
  ext p
  refine Iff.trans ?_ (mem_lift_iff hc (chartOf hc (contr g hT)) p).symm
  constructor
  · rintro ⟨u, hu, hv⟩
    have h1 : rvValues p.2 ∈ rawDom (contr g hT) := hu ▸ mem_rawDom (contr g hT) u
    refine ⟨h1, ?_⟩
    have h2 := rawCoord_of (contr g hT) u
    have h3 : rvValues ((contr g hT).object.value u) = rvValues (tupleRV M p.1) := congrArg rvValues hv
    have h4 : rawCoord (contr g hT) (rvValues u.val) = rawCoord (contr g hT) (rvValues p.2) :=
      congrArg (rawCoord (contr g hT)) (congrArg rvValues hu)
    exact (h3.symm.trans h2.symm).trans h4
  · rintro ⟨hd, hv⟩
    obtain ⟨t, ht, he⟩ := hd
    have hpt : p.2 = t := (rvValues_injective he).symm
    refine ⟨⟨t, ht⟩, hpt.symm, ?_⟩
    apply rvValues_injective
    have h2 := rawCoord_of (contr g hT) ⟨t, ht⟩
    have h4 : rawCoord (contr g hT) (rvValues t) = rawCoord (contr g hT) (rvValues p.2) :=
      congrArg (rawCoord (contr g hT)) he
    exact (h2.symm.trans h4).trans hv.symm

end ChartLift

/-! ### Sets from their regularization -/

section FromReg
variable {T : LRV.Substructure M} (V : DefSet (rawMixedSpace (M := M) n r) (T : Set M))

theorem pullback_of_reg (h : IsRVPullback (regularizeMap V).image.carrier) : IsRVPullback V.carrier := by
  show rvHull _ = _
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨p, hp, h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
    have hpr : regularize p ∈ (regularizeMap V).image.carrier := (mem_regularize V).mpr ⟨p, hp, rfl⟩
    have hqr : regularize q ∈ (regularizeMap V).image.carrier :=
      rvPullback_mem_of_sameRV h hpr h1 (regularize_snd_eq.mpr ⟨h1, h2⟩)
    obtain ⟨q', hq', he⟩ := (mem_regularize V).mp hqr
    rw [← regularize_injective he]
    exact hq'
  · intro q hq
    exact (mem_rvHull_iff _ q).mpr ⟨q, hq, rfl, rfl⟩

theorem finite_of_reg (h : ∀ a : Fin n → VF M,
      {L : Fin (n + r) → RVInfinity M | (a, L) ∈ (regularizeMap V).image.carrier}.Finite) :
    ∀ a : Fin n → VF M, {u : Fin r → RVInfinity M | (a, u) ∈ V.carrier}.Finite := by
  intro a
  refine Set.Finite.of_finite_image (f := fun u => Fin.append (tupleRV M a) u) ((h a).subset ?_) ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact (mem_regularize V).mpr ⟨(a, u), hu, rfl⟩
  · intro u _ v _ he
    funext i
    simpa only [Fin.append_right] using congrFun he (Fin.natAdd n i)

end FromReg

/-! ### The relative step with all labels active -/

section RelStep
open DiamondIntegral.Section7.BlowupLiftData DiamondIntegral.Section7.BlowupLiftImage
open DiamondIntegral.Section7.BlowupLiftContraction DiamondIntegral.Section7.BlowupLiftClasses
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.ElementaryBlowups
open SpecialTransformations.Section9 (liftLabelMap)
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {k : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) (1 + k) r) (T : Set M)} (g : Good T X)
variable (R : DiamondIntegral.Section6.RelativeApertureData (G := G) X)
variable (hall : ∀ p ∈ X.carrier, p.2 ∈ R.activeTags.carrier)
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk (T : Set M) < κ)
variable (h00 : M ⊨ Axioms.ACVF00)

/-- The chart of the source of the step. -/
abbrev srcChart : DiamondIntegral.Section4.RVMeasuredCharts.Chart (BT T) (1 + k) := chartOf hc (contr g R.tagged)

theorem srcChart_bounded : DiamondIntegral.Section4.RVMeasuredBounds.DomainBounded (srcChart hc g R) :=
  chartOf_bounded hc _ (contr_db g R.tagged)

theorem src_carrier : X.carrier = (rvLift (toMeasured hc (srcChart hc g R)).object).carrier :=
  congrArg DefSet.carrier (carrier_eq_chartLift hc g R.tagged)

/-- The data transported to the chart lift. -/
def R2 : DiamondIntegral.Section6.RelativeApertureData (G := G) (rvLift (toMeasured hc (srcChart hc g R)).object) :=
  castData (carrier_eq_chartLift hc g R.tagged) R

include hall in
theorem R2_all : ∀ p ∈ (rvLift (toMeasured hc (srcChart hc g R)).object).carrier,
    p.2 ∈ (R2 hc g R).activeTags.carrier := by
  intro p hp
  rw [R2, castData_activeTags]
  exact hall p ((src_carrier hc g R).symm ▸ hp)

/-- The datum of the step. -/
abbrev Dg : DiamondIntegral.Section4.RelativeAnnularGenerators.AnnularDatum (BT T) k :=
  datumOf hc T (srcChart hc g R) (srcChart_bounded hc g R) (R2 hc g R) (R2_all hc g R hall) hκ hs hsmall

theorem hendg : ∀ p ∈ (liftSet hc (Dg hc g R hall hκ hs hsmall)).carrier,
    (rv M ((R2 hc g R).extendedEndpoint p)).val = centrePair (Dg hc g R hall hκ hs hsmall) (rvValues p.2) 1 :=
  fun _ hp => apertureOf_endpoint hc (srcChart hc g R) (R2 hc g R) (R2_all hc g R hall) hp

theorem vreg_eq : Vreg hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R) = (regularizeMap R.map.image).image := by
  show (regularizeMap (R2 hc g R).map.image).image = _
  rw [R2, castData_image]

/-- The image of the step, with the transported form. -/
def relGood : Good T R.map.image where
  pullback := pullback_of_reg _ (by
    rw [← vreg_eq hc g R hall hκ hs hsmall]
    exact vreg_pullback hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R) rfl (R2_all hc g R hall)
      (hendg hc g R hall hκ hs hsmall))
  finite := finite_of_reg _ (by
    rw [← vreg_eq hc g R hall hκ hs hsmall]
    exact vreg_finite hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R) rfl (R2_all hc g R hall)
      (hendg hc g R hall hκ hs hsmall))
  vfBounded := R.image_vfDoublyBounded
  rvBounded := R.image_rvDoublyBounded
  form := g.form.comp (R.bijection.inverse (R.bijective h00))
  form_labels := by
    intro p q he
    obtain ⟨a, rfl⟩ := (R.bijective h00).2 p
    obtain ⟨b, rfl⟩ := (R.bijective h00).2 q
    change g.form (R.bijection.inverse _ (R.bijection a)) = g.form (R.bijection.inverse _ (R.bijection b))
    rw [Map.inverse_apply, Map.inverse_apply]
    apply g.form_labels
    have he' : Fin.append (fun _ : Fin 1 => branchTag (M := M) (R.core a.val)) a.val.2 =
        Fin.append (fun _ : Fin 1 => branchTag (M := M) (R.core b.val)) b.val.2 := he
    funext i
    simpa only [Fin.append_right] using congrFun he' (Fin.natAdd 1 i)

theorem relGood_form (x : X) : (relGood hc g R hall hκ hs hsmall h00).form (R.bijection x) = g.form x := by
  change g.form (R.bijection.inverse _ (R.bijection x)) = _
  rw [Map.inverse_apply]

theorem clsG_src : clsG hc g = cls (⟨srcChart hc g R, srcChart_bounded hc g R⟩ : Obj (BT T) (1 + k)) :=
  (cls_objOf_eq hc (contr_db g R.tagged) (regC_db g)
    (contractionIso R.tagged g.pullback g.finite g.vfBounded g.form g.form_labels
      (regularize_tagged X) (regularize_pullback X g.pullback) (regularize_finite X g.finite)
      (regularize_vfDoublyBounded X g.vfBounded) (regForm g) (regForm_labels g)
      (regularization X) (regularization_bijective X) (regularization_matching X R.tagged) (fun _ => rfl)
      (fun p => regForm_apply g p))).symm

theorem vreg_sub : ((regularizeMap R.map.image).image).carrier ⊆
    (Vreg hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R)).carrier := by
  rw [vreg_eq hc g R hall hκ hs hsmall]

theorem form_eq (q : (regularizeMap R.map.image).image) :
    form hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R) rfl (R2_all hc g R hall) (hendg hc g R hall hκ hs hsmall) h00
        (Map.inclusion (vreg_sub hc g R hall hκ hs hsmall) q) =
      regForm (relGood hc g R hall hκ hs hsmall h00) q := by
  obtain ⟨y, rfl⟩ := (regularization_bijective _).2 q
  obtain ⟨x, rfl⟩ := (R.bijective h00).2 y
  rw [regForm_apply, relGood_form]
  let x' : liftSet hc (Dg hc g R hall hκ hs hsmall) := ⟨x.val, (src_carrier hc g R) ▸ x.property⟩
  have hF : Fmap hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R) x' =
      Map.inclusion (vreg_sub hc g R hall hκ hs hsmall) (regularization _ (R.bijection x)) := by
    apply Subtype.ext
    rw [Fmap_val hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R) rfl (R2_all hc g R hall)
      (hendg hc g R hall hκ hs hsmall)]
    change regularize ((R2 hc g R).point x.val) = regularize (R.point x.val)
    rw [R2, castData_point]
  change (DiamondIntegral.Section6.DiamondLift.liftForm (toMeasured hc (srcChart hc g R)))
    ((Fmap hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R)).inverse _
      (Map.inclusion (vreg_sub hc g R hall hκ hs hsmall) (regularization _ (R.bijection x)))) = g.form x
  rw [← hF, Map.inverse_apply]
  apply Subtype.ext
  change rawVol (contr g R.tagged) (rvValues x.val.2) = gammaMapValue g.form x
  have h := rawVol_of (contr g R.tagged) (pureRVTagQuotient X x)
  exact h.trans (contractedMeasuredRVObject_form _ _ _ _ _ _ _ x)

/-- Lemma 7.11 for a relative step, all labels active: the class of the image
is a blowup of length one of the class of the source. -/
theorem step_rel_active : Step (clsG hc g) (clsG hc (relGood hc g R hall hκ hs hsmall h00)) := by
  rw [clsG_src hc g R]
  have hsub := vreg_sub hc g R hall hκ hs hsmall
  have hbij : Function.Bijective (Map.inclusion hsub) := by
    refine ⟨fun a b he => Subtype.ext (congrArg (fun z : (Vreg hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R)) => z.val) he),
      fun b => ⟨⟨b.val, (congrArg DefSet.carrier (vreg_eq hc g R hall hκ hs hsmall)) ▸ b.property⟩, rfl⟩⟩
  have hmatch : MapsWholeTagFibres (Map.inclusion hsub) := by
    intro p b
    constructor
    · intro he
      obtain ⟨a, rfl⟩ := hbij.2 b
      exact ⟨a, he, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  have h2 : clsG hc (relGood hc g R hall hκ hs hsmall h00) =
      cls (contractionObj hc T (Dg hc g R hall hκ hs hsmall) (R2 hc g R) rfl (R2_all hc g R hall)
        (hendg hc g R hall hκ hs hsmall) h00) :=
    cls_objOf_eq hc (regC_db _) (W_doublyBounded hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R) rfl
        (R2_all hc g R hall) (hendg hc g R hall hκ hs hsmall) h00)
      (contractionIso (regularize_tagged _)
        (regularize_pullback _ (relGood hc g R hall hκ hs hsmall h00).pullback)
        (regularize_finite _ (relGood hc g R hall hκ hs hsmall h00).finite)
        (regularize_vfDoublyBounded _ (relGood hc g R hall hκ hs hsmall h00).vfBounded)
        (regForm (relGood hc g R hall hκ hs hsmall h00)) (regForm_labels _)
        (vreg_tagged hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R) rfl (R2_all hc g R hall) (hendg hc g R hall hκ hs hsmall))
        (vreg_pullback hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R) rfl (R2_all hc g R hall) (hendg hc g R hall hκ hs hsmall))
        (vreg_finite hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R) rfl (R2_all hc g R hall) (hendg hc g R hall hκ hs hsmall))
        (vreg_vfDoublyBounded hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R) rfl (R2_all hc g R hall)
          (hendg hc g R hall hκ hs hsmall))
        (form hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R) rfl (R2_all hc g R hall) (hendg hc g R hall hκ hs hsmall) h00)
        (form_labels hc (Dg hc g R hall hκ hs hsmall) (R2 hc g R) rfl (R2_all hc g R hall)
          (hendg hc g R hall hκ hs hsmall) h00)
        (Map.inclusion hsub) hbij hmatch (fun _ => rfl) (fun q => form_eq hc g R hall hκ hs hsmall h00 q))
  rw [h2]
  exact step_of_data hc T (srcChart hc g R) (srcChart_bounded hc g R) (R2 hc g R) (R2_all hc g R hall) hκ hs hsmall h00

end RelStep

end DiamondIntegral.Section7.SpecialChainStep
