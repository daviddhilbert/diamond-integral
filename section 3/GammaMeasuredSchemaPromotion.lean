import «section 3».GammaMeasuredSchemaValidityFromForms
import «section 3».GammaNativeStructuralValues
import IntegrationSection6.GammaFiniteObjectPromotion
import IntegrationSection6.GammaSchemaNativeRows
import Integration7.NonzeroDensityFormulas

/-! Promote actual measured rows by reusing finite-object promotion and
the tuple-parameter promotion theorem. The entire Gamma code relation is
promoted, with its original representative invariance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p k : ℕ}

theorem gammaMeasured_schema_promotion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (U : GammaObjectAt ⟨B.real ∪ Set.range z,B.gamma⟩ Set.univ k)
    (ω : GammaGroundVolumeForm hc ⟨B.real ∪ Set.range z,B.gamma⟩ (Section5.nativeRVGroundDomain (hc := hc) U)) :
    ∃ F : GammaMeasuredRVSchema hc B p (rvObjectArity U.object.obj) k sp,
      F.valid z ∧
      gammaSchemaRepresents U.toGamma F.object z ∧
      F.object.rowDomain z = (Section5.nativeRVGroundDomain (hc := hc) U).carrier ∧
      (∀ x y, Fin.append (Fin.append z x) y ∈ F.density ↔
        Fin.append x y ∈ gammaRVFormCodeRows ω) := by
  let a := rvObjectArity U.object.obj
  let sx : Fin a → SortTag := fun _ => .rv
  let sy : Fin 1 → SortTag := fun _ => .rv
  let st := Fin.append (Fin.append sp sx) sy
  obtain ⟨F,hF,hFD,hFV⟩ := gamma_sorted_finite_object_promotion hκ hs hr hg sp z hz U.toGamma
  obtain ⟨P,hP,hPz⟩ := gamma_tuple_parameter_promotion B sp (fun _ : Fin (a+1) => .rv) z hz
    (gammaRVFormCodeRows ω) (gammaRVFormCodeRows_definable ω)
  let Q : Set (Fin (p+(a+1)) → M) :=
    {w | ((fun i => w (Fin.castAdd (a+1) i)),fun j => w (Fin.natAdd p j)) ∈ P}
  let D : Set (Fin ((p+a)+1) → M) :=
    {w | w ∘ Fin.cast (Nat.add_assoc p a 1).symm ∈ Q ∧ w ∈ sortedUniverse st}
  have hD : DefinableOverBase B st D := hP.preimage_real st (Fin.cast (Nat.add_assoc p a 1).symm)
  let H : GammaMeasuredRVSchema hc B p a k sp := {
    object := F
    density := nonzeroDensityFormula D
    density_definable := nonzeroDensityFormula_definable hD
    density_code := by
      intro w hw
      refine ⟨?_,hw.2⟩
      simpa only [st,Function.comp_apply,Fin.append_right,sortEval,iRV] using
        hD.proper w hw.1 (Fin.natAdd (p+a) (0 : Fin 1)) }
  have hDensity (x : Fin a → M) (y : Fin 1 → M) :
      Fin.append (Fin.append z x) y ∈ H.density ↔ Fin.append x y ∈ gammaRVFormCodeRows ω := by
    change _ ∈ nonzeroDensityFormula D ↔ _
    rw [nonzeroDensityFormula_append]
    change ((_ ∈ Q ∧ _ ∈ sortedUniverse st) ∧ _) ↔ _
    rw [append_assoc_cast_symm]
    simp only [Q,Set.mem_ofPred_eq,Fin.append_left,Fin.append_right]
    have hRow := Set.ext_iff.mp hPz (Fin.append x y)
    constructor
    · exact fun h => hRow.mp h.1.1
    · intro hxy
      refine ⟨⟨hRow.mpr hxy,?_⟩,?_⟩
      · have hp := gammaRVFormCodeRows_proper ω _ hxy
        intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · refine Fin.addCases (fun l => ?_) (fun l => ?_) j
          · simpa only [st,Fin.append_left] using hz l
          · simpa only [st,sx,Fin.append_left,Fin.append_right] using hp (Fin.castAdd 1 l)
        · simpa only [st,sy,Fin.append_right] using hp (Fin.natAdd a j)
      · have hCode := gammaRVFormCodeRows_code ω _ hxy
        have hn : Fin.append x y (Fin.natAdd a (0 : Fin 1)) ≠ iRVZero := hCode.2
        simpa only [Fin.append_right] using hn
  have hDomain : F.rowDomain z = (Section5.nativeRVGroundDomain (hc := hc) U).carrier := by
    ext r
    exact (hFD (rvValues r)).trans ((gammaRawObjectDomain_tuple_iff U.toGamma.toGammaRVObject r).trans
      (Set.ext_iff.mp (Section5.nativeRVGroundDomain_carrier (hc := hc) U) r).symm)
  exact ⟨H,gammaMeasuredSchema_valid_of_form H z hF _ ω hDomain hDensity,⟨hFD,hFV⟩,hDomain,hDensity⟩

end DiamondIntegral.Section3
