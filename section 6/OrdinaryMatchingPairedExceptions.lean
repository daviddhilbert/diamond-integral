import «section 6».OrdinaryFocusExceptions
import «section 6».OrdinaryMatchingZeroFibres
import «section 6».OrdinaryChainZeroEndpoints
import «section 6».PairedUnaryExceptionCenters

/-! The actual ordinary exceptional sets are already paired by the
original bijection: all zero events are terminal zero fibres, and the
ordinary RV matching preserves those fibres. Their paired enlargement
therefore adds no new centers. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem OriginalBaseOrdinarySpecial.exceptions_iff_prepared_zero {f : Map A B}
    (F : OriginalBaseOrdinarySpecial A B f) (hc : CanonicalStructure.IsCanonical (M := M)) (p : A) :
    p.val ∈ (F.exceptions hc).carrier ↔ ordinaryUnaryField (f p).val=(0 : VF M) := by
  let a : F.source := ⟨p.val,(Set.ext_iff.mp F.source_eq p.val).mpr p.property⟩
  have hZero := ordinaryChainZeroSources_iff_endpoint_zero F.special.chain a
  have hAgree : (F.special.toMap a).val=(f p).val := F.agrees p
  change p.val ∈ ordinaryChainZeroSources F.special.chain ↔ ordinaryUnaryField (f p).val=(0 : VF M)
  change p.val ∈ ordinaryChainZeroSources F.special.chain ↔ ordinaryUnaryField (F.special.toMap a).val=(0 : VF M) at hZero
  rwa [hAgree] at hZero

theorem OriginalBaseOrdinaryUnaryMatching.exceptions_paired {f : Map A B}
    (F : OriginalBaseOrdinaryUnaryMatching A B f) (hc : CanonicalStructure.IsCanonical (M := M)) (p : A) :
    p.val ∈ (F.sourceSpecial.exceptions hc).carrier ↔ (f p).val ∈ (F.targetSpecial.exceptions hc).carrier := by
  rw [F.sourceSpecial.exceptions_iff_prepared_zero hc p,F.targetSpecial.exceptions_iff_prepared_zero hc (f p)]
  have hh := F.zero_iff (F.sourceMap p)
  rwa [F.commutes p] at hh

theorem OriginalBaseOrdinaryUnaryMatching.paired_exception_domain_eq {f : Map A B}
    (F : OriginalBaseOrdinaryUnaryMatching A B f) (hc : CanonicalStructure.IsCanonical (M := M)) :
    pairedUnaryExceptionDomain f (F.sourceSpecial.exceptions hc) (F.targetSpecial.exceptions hc)=F.sourceSpecial.exceptions hc := by
  apply defSet_eq_of_carrier_eq
  ext p
  constructor
  · rintro (hp | ⟨a,ha,hfa⟩)
    · exact hp
    · have haE := (F.exceptions_paired hc a).mpr hfa
      exact ha ▸ haE
  · exact Or.inl

end DiamondIntegral.Section6
