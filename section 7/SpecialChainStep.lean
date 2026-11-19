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

end DiamondIntegral.Section7.SpecialChainStep
