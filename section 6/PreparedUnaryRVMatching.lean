import «section 6».WholeDiscMeasuredMatching
import «section 2».PartitionEscape

/-! Complete original-base RV-map and volume-form adapters once an
actual unary whole-disc matching has been prepared. The final equality
holds on every RV label, including labels containing exceptional points.
The existence of the preparatory special bijections is not assumed here
as a theorem and remains a separate construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r s : ℕ} {S : Set M}

theorem unary_leading_label_tagged (A : DefSet (rawMixedSpace (M := M) 1 r) S) (j : Fin r)
    (hLead : ∀ p ∈ A.carrier, rv M (p.1 0) = p.2 j) :
    ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  intro p hp q hq he
  funext i
  fin_cases i
  exact (hLead p hp).trans ((congrFun he j).trans (hLead q hq).symm)

theorem leading_label_radius_eq (A : DefSet (rawMixedSpace (M := M) 1 r) S) (j : Fin r)
    (hLead : ∀ p ∈ A.carrier, rv M (p.1 0) = p.2 j) (hD : VFDoublyBounded A.carrier) (p : A) :
    GammaParameters.codeValue (p.val.2 j).val = finiteValue (p.val.1 0) (hD.nonzero p.property 0) := by
  have hc := congrArg Subtype.val (hLead p.val p.property)
  change iRv (p.val.1 0).val = (p.val.2 j).val at hc
  rw [← hc]
  exact codeValue_rv_finite _ _

structure PreparedUnaryRVMatching
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (B : DefSet (rawMixedSpace (M := M) 1 s) S)
    (f : Map A B) (ω : Mixed M 1 r → Gamma M) (σ : Mixed M 1 s → Gamma M) (j : Fin r) (k : Fin s) where
  map : Map (rvTagQuotient A) (rvTagQuotient B)
  bijective : Function.Bijective map
  commutes : ∀ p : A, map (rvTagQuotientMap A p) = rvTagQuotientMap B (f p)
  source_bounded : RVSupportDoublyBounded (rvTagQuotient A).carrier
  target_bounded : RVSupportDoublyBounded (rvTagQuotient B).carrier
  source_form_graph : S.Definable LRV (rawGammaFamilyGraph (rvInputValues '' (Prod.snd '' A.carrier))
    (fun t => {rvContractedGamma A.carrier ω t}))
  target_form_graph : S.Definable LRV (rawGammaFamilyGraph (rvInputValues '' (Prod.snd '' B.carrier))
    (fun t => {rvContractedGamma B.carrier σ t}))
  volume : ∀ u : rvTagQuotient A,
    rvContractedGamma A.carrier ω (rvInputValues u.val.2) * GammaParameters.codeValue (u.val.2 j).val =
      rvContractedGamma B.carrier σ (rvInputValues (map u).val.2) *
        GammaParameters.codeValue ((map u).val.2 k).val

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem prepared_unary_rv_matching_exists [CharZero (VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (B : DefSet (rawMixedSpace (M := M) 1 s) S)
    (f : Map A B) (hf : Function.Bijective f) (hWhole : MapsWholeTagFibres f)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hB : ProperInvariant S B.carrier) (hBD : VFDoublyBounded B.carrier) (hBRV : IsRVPullback B.carrier)
    (j : Fin r) (k : Fin s)
    (hALead : ∀ p ∈ A.carrier, rv M (p.1 0) = p.2 j)
    (hBLead : ∀ p ∈ B.carrier, rv M (p.1 0) = p.2 k)
    (ω : Mixed M 1 r → Gamma M) (σ : Mixed M 1 s → Gamma M)
    (hωGraph : S.Definable LRV (mixedGammaGraph A.carrier ω))
    (hσGraph : S.Definable LRV (mixedGammaGraph B.carrier σ))
    (hω : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → ω p = ω q)
    (hσ : ∀ p ∈ B.carrier, ∀ q ∈ B.carrier, p.2 = q.2 → σ p = σ q)
    (Z : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hZ : vfDim (rawRVSpace (M := M) 1) Z < 1)
    (hconst : ∀ p : A, p.val ∉ Z.carrier →
      ∃ J, HasMixedVFJacobianAt f p J ∧ vfValue J = (ω p.val/σ (f p).val).val) :
    Nonempty (PreparedUnaryRVMatching A B f ω σ j k) := by
  refine ⟨{
    map := rvTagMatchingMap f hWhole
    bijective := rvTagMatchingMap_bijective f hf hWhole
    commutes := rvTagMatchingMap_commutes f hWhole
    source_bounded := rvTagQuotient_rvBounded A hA.rvBounded
    target_bounded := rvTagQuotient_rvBounded B hB.rvBounded
    source_form_graph := rvContractedGamma_graph_definable A.carrier ω hωGraph hω
    target_form_graph := rvContractedGamma_graph_definable B.carrier σ hσGraph hσ
    volume := ?_
  }⟩
  intro u
  obtain ⟨p,rfl⟩ := rvTagQuotientMap_surjective A u
  rw [rvTagMatchingMap_commutes]
  change rvContractedGamma A.carrier ω (rvInputValues p.val.2) * GammaParameters.codeValue (p.val.2 j).val =
    rvContractedGamma B.carrier σ (rvInputValues (f p).val.2) * GammaParameters.codeValue ((f p).val.2 k).val
  rw [rvContractedGamma_at A.carrier ω hω p.val p.property,
    rvContractedGamma_at B.carrier σ hσ (f p).val (f p).property,
    leading_label_radius_eq A j hALead hAD p,leading_label_radius_eq B k hBLead hBD (f p)]
  exact prepared_unary_matching_volume_identity hc hκ hs h00 hsmall hv f hf.injective hWhole
    hA hAD hARV (unary_leading_label_tagged A j hALead) hBD hBRV (unary_leading_label_tagged B k hBLead)
    ω σ hω hσ Z hZ hconst p

end DiamondIntegral.Section6
