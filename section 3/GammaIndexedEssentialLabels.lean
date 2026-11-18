import «section 3».GammaIndexedOriginalLabels
import Integration7.GammaEssentialIndexDomains

/-! For finite rows with empty row volume, the full structural weight
condition is precisely the existing essential condition on the index. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gammaNativeHighLabel_mem (U : GammaObjectAt B Set.univ (n+1))
    (u : Section5.nativeRVGroundDomain (hc := hc) U) :
    u.val ∈ (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)).carrier ↔
      ∀ j, ((Section5.nativeRVGroundVolume U u).val j).val ≠ iRVZero := by
  rw [Section5.nativeRVGroundDomain_carrier]
  have hu := (Section5.nativeRVGroundDomain_carrier U).le u.property
  let v := Section5.nativeRVGroundDomainEquiv U u
  have hv := gammaNativeRVGroundVolume_value U u
  change (_ ∧ _) ↔ _
  constructor
  · intro h j hz
    apply h.2
    apply (@mem_rvLowDomain M N Set.univ n U.object.obj v).mpr
    apply (@rvWeight_le_pred_iff_zero M N n (rvObjectVolume U.object.obj v).val).mpr
    refine ⟨j,?_⟩
    exact (congrArg (fun t : Fin (n+1) → CanonicalRV.RVSort M => (t j).val) hv).symm.trans
      (hz.trans (CanonicalStructure.sortZero_normalize .rv).symm)
  · intro h
    refine ⟨hu,?_⟩
    intro hl
    obtain ⟨j,hj⟩ := (@rvWeight_le_pred_iff_zero M N n (rvObjectVolume U.object.obj v).val).mp
      ((@mem_rvLowDomain M N Set.univ n U.object.obj v).mp hl)
    apply h j
    exact (congrArg (fun t : Fin (n+1) → CanonicalRV.RVSort M => (t j).val) hv).trans
      (hj.trans (CanonicalStructure.sortZero_normalize .rv))

variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin (n+1) → RV (M := M)) → Prop}

theorem gammaIndexed_groundVolume
    (BP : GammaFiniteGraphPresentation B p (n+1) T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv)) (P : F.IndexedPresentation BP)
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :
    (Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma) u).val =
      BP.totalVolume (u.val ∘ Fin.castAdd a) := by
  let v := Section5.nativeRVGroundDomainEquiv (gammaUniversalObject P.toGamma) u
  have hPV : (P.volume v).val = indexedVolume BP.totalVolume (fun t => F.rowValue (rvValues t)) v.val :=
    ((P.graph_iff v.val (P.volume v).val).mp ⟨v,rfl,rfl⟩).2.2.symm
  rw [gammaNativeRVGroundVolume_value]
  change (P.volume v).val = _
  rw [hPV]
  funext i
  change (Fin.append _ _) (Fin.castAdd 0 i) = _
  rw [Fin.append_left]
  rfl

theorem gammaIndexed_high_mem
    (BP : GammaFiniteGraphPresentation B p (n+1) T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv)) (P : F.IndexedPresentation BP)
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :
    u.val ∈ (Section5.nativeRVGroundDomain (hc := hc)
      (gammaHighRestrictionAt (gammaUniversalObject P.toGamma))).carrier ↔
      u.val ∘ Fin.castAdd a ∈ essentialIndexDomain BP := by
  rw [gammaNativeHighLabel_mem,gammaIndexed_groundVolume]
  have hu := P.domain_eq.le (Section5.nativeRVGroundDomainEquiv (gammaUniversalObject P.toGamma) u).property
  exact ⟨fun h => ⟨hu.1,h⟩,fun h => h.2⟩

end DiamondIntegral.Section3
