import «section 6».OrderedContractionHeadStarts
import «section 6».MeasuredRVIsomorphisms

/-! Volume forms descend through head-start RV quotients, with exact
pointwise transport through the actual lifted map in degree n+k. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r q : ℕ}

theorem preparedRVObject_nonzero
    (B : DefSet (rawMixedSpace (M := M) n r) S)
    (hTag : ∀ p ∈ B.carrier,∀ z ∈ B.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (hD : VFDoublyBounded B.carrier) (u : (preparedRVObject B hTag).domain) (i : Fin n) :
    ((preparedRVObject B hTag).value u i).val ≠ iRVZero := by
  obtain ⟨p,rfl⟩ := pureRVTagQuotient_surjective B u
  change ((preparedRVVolume B hTag (pureRVTagQuotient B p)).val i).val ≠ iRVZero
  rw [preparedRVVolume_at]
  intro h
  have hz : rv M (p.val.1 i)=rvZero M := Subtype.ext h
  exact hD.nonzero p.property i ((rv_eq_zero_iff _).mp hz)

theorem headStartForm_eq_of_quotient_eq
    (B : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (θ : Fin k → Fin r)
    (η : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hη : ∀ p z : B,p.val.2=z.val.2 → η p=η z)
    (p z : rvHeadStartBundle B k θ)
    (he : pureRVTagQuotient (rvHeadStartBundle B k θ) p=pureRVTagQuotient (rvHeadStartBundle B k θ) z) :
    (η.comp (headStartBaseProjection B k θ)) p=(η.comp (headStartBaseProjection B k θ)) z := by
  apply hη
  simp only [headStartBaseProjection_value]
  exact (pureRVTagQuotient_eq_iff _ p z).mp he

def headStartRVForm
    (B : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (θ : Fin k → Fin r)
    (η : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hη : ∀ p z : B,p.val.2=z.val.2 → η p=η z) :
    Map (pureRVTagDomain (rvHeadStartBundle B k θ)) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  definableSurjectiveDescent (pureRVTagQuotient (rvHeadStartBundle B k θ))
    (pureRVTagQuotient_surjective (rvHeadStartBundle B k θ)) (η.comp (headStartBaseProjection B k θ))
    (headStartForm_eq_of_quotient_eq B k θ η hη)

theorem headStartRVForm_at
    (B : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (θ : Fin k → Fin r)
    (η : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hη : ∀ p z : B,p.val.2=z.val.2 → η p=η z) (p : rvHeadStartBundle B k θ) :
    headStartRVForm B k θ η hη (pureRVTagQuotient (rvHeadStartBundle B k θ) p)=
      η (headStartBaseProjection B k θ p) :=
  definableSurjectiveDescent_apply _ _ _ (headStartForm_eq_of_quotient_eq B k θ η hη) p

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
variable {T : OrderedStandardContractionProgram (G := G) S A U}
namespace OrderedStandardContractionLift

def headStartMeasuredObject
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin n → VF M,∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier ∧ u ∘ π=t}.Finite)
    (η : Map V.target (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hη : ∀ p z : V.target,p.val.2=z.val.2 → η p=η z) : MeasuredRVObject (M := M) S (n+k) where
  object := V.headStartObject k π
  finiteVolume := V.headStartObject_finite_volume hc h00 hκ hs hsmall k π hFin
  nonzero := preparedRVObject_nonzero _ _
    (rvHeadStartBundle_doublyBounded V.target k _ V.doublyBounded V.proper.rvBounded)
  form := headStartRVForm V.target k _ η hη

def headStartLabelMap (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r) :
    Map (rvHeadStartBundle A k π) (V.headStartObject k π).domain :=
  (pureRVTagQuotient (rvHeadStartBundle V.target k (T.oldLabels ∘ π))).comp (V.headStartBijection k π).map

theorem headStartLabelMap_value (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r)
    (p : rvHeadStartBundle A k π) :
    (V.headStartLabelMap k π p).val=(V.headStartLift k π p).val.2 := by
  rw [headStartLift_value]
  rfl

theorem headStart_form_transport
    (V : OrderedStandardContractionLift T) (k : ℕ) (π : Fin k → Fin r)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (η : Map V.target (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hη : ∀ p z : V.target,p.val.2=z.val.2 → η p=η z)
    (hTransport : ∀ p : A,η (V.map p)=ω p) (p : rvHeadStartBundle A k π) :
    headStartRVForm V.target k (T.oldLabels ∘ π) η hη (V.headStartLabelMap k π p)=
      ω (headStartBaseProjection A k π p) := by
  change headStartRVForm V.target k (T.oldLabels ∘ π) η hη
    (pureRVTagQuotient _ ((V.headStartBijection k π).map p))=_
  rw [headStartRVForm_at,(V.headStartBijection k π).base]
  exact hTransport _

end OrderedStandardContractionLift
end DiamondIntegral.Section6
