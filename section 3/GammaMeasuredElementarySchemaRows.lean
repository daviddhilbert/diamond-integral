import «section 3».GammaMeasuredObjectRows
import «section 3».GammaMeasuredEssentialSchemata
import «section 3».GammaMeasuredElementaryForm
import IntegrationSection6.ElementaryValuePrograms

/-! The existing elementary formula and the actual weighted elementary
object have the same old labels and structural blowup tuple. These exact
row identities are used before removing zero structural rows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.vfSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaMeasured_elementary_schema_row_volume
    {z : Fin p → M} (hz : ∀ i, sortEval (sp i) (z i))
    {U : GammaGroundMeasuredRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ (k+1)}
    {F : GammaMeasuredRVSchema hc B p U.underlying.arity (k+1) sp}
    (hF : GammaMeasuredObjectRow z U F)
    (w : Fin (U.underlying.arity+1) → CanonicalRV.RVSort M) (v : Fin (k+1) → CanonicalRV.RVSort M) :
    F.elementaryFormula.object.rowVolume z w v ↔
      ∃ u : U.underlying.domain, u.val = w ∘ Fin.castAdd 1 ∧
        (w ∘ Fin.natAdd U.underlying.arity) ∈ @DefSet.carrier LRV M N _ Set.univ (@positiveRV M N Set.univ) ∧
        blowupValue (Fin.last k) (U.underlying.volume u).val (w (Fin.natAdd U.underlying.arity 0)) = v := by
  have hMap (t : Fin (k+1) → CanonicalRV.RVSort M) :
      (@oldVolumeParameterBlowupMap M N hN (k+1) B.real (Fin.last k)
        ⟨Fin.append t (w ∘ Fin.natAdd U.underlying.arity),Set.mem_univ _⟩).val =
        blowupValue (Fin.last k) t (w (Fin.natAdd U.underlying.arity 0)) :=
    (@oldVolumeParameterBlowupMap_append M N hN (k+1) B.real (Fin.last k) t (w ∘ Fin.natAdd U.underlying.arity)).trans
      (@gammaBlowupValue_normalized M sM hM (k+1) t (Fin.last k) _)
  change (F.object.elementaryFormula (Fin.last k)).rowVolume z w v ↔ _
  rw [F.object.elementary_row_volume_formula (Fin.last k) z hz w v]
  constructor
  · rintro ⟨hD,t,ht,hv⟩
    obtain ⟨u,hu,huv⟩ := (hF.volume _ t).mp ht
    have hDom := (F.object.elementary_row_domain_formula (Fin.last k) z hz w Set.univ).mp hD
    exact ⟨u,hu,hDom.2,(congrArg (fun t => blowupValue (Fin.last k) t (w (Fin.natAdd U.underlying.arity 0))) huv).trans
      ((hMap t).symm.trans hv)⟩
  · rintro ⟨u,hu,hPos,hv⟩
    refine ⟨(F.object.elementary_row_domain_formula (Fin.last k) z hz w Set.univ).mpr
      ⟨hF.domain.symm ▸ (hu ▸ u.property),hPos⟩,(U.underlying.volume u).val,?_,?_⟩
    · exact (hF.volume _ _).mpr ⟨u,hu,rfl⟩
    · exact (hMap _).trans hv

def gammaMeasuredElementaryOldPoint
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaGroundMeasuredRVObject hc B (k+1)) (i : Fin (k+1))
    (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject i)
    (w : (gammaMeasuredElementaryObject hκ hs h00 hr U i hAd).underlying.domain) : U.underlying.domain :=
  ⟨((gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w).val.1,
    ((gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w).property.1⟩

theorem gammaMeasuredElementaryOldPoint_val
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaGroundMeasuredRVObject hc B (k+1)) (i : Fin (k+1))
    (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject i)
    (w : (gammaMeasuredElementaryObject hκ hs h00 hr U i hAd).underlying.domain) :
    (gammaMeasuredElementaryOldPoint hκ hs h00 hr U i hAd w).val = w.val ∘ Fin.castAdd 1 :=
  congrArg Prod.fst (gammaMeasuredElementaryChart_val hκ hs h00 hr U.underlying i hAd w)

theorem gammaMeasuredElementary_literal_volume
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaGroundMeasuredRVObject hc B (k+1)) (i : Fin (k+1))
    (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject i)
    (w : (gammaMeasuredElementaryObject hκ hs h00 hr U i hAd).underlying.domain) :
    ((gammaMeasuredElementaryObject hκ hs h00 hr U i hAd).underlying.volume w).val =
      blowupValue i (U.underlying.volume (gammaMeasuredElementaryOldPoint hκ hs h00 hr U i hAd w)).val
        (w.val (Fin.natAdd U.underlying.arity 0)) := by
  rw [gammaMeasuredElementaryObject_volume]
  congr 1
  have hTail : (show Fin 1 → CanonicalRV.RVSort M from
      ((gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w).val.2) = w.val ∘ Fin.natAdd U.underlying.arity :=
    congrArg Prod.snd (gammaMeasuredElementaryChart_val hκ hs h00 hr U.underlying i hAd w)
  exact congrFun hTail 0

end DiamondIntegral.Section3
