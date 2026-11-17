import «section 3».GammaMeasuredRVSchemata
import «section 3».GammaRawParameterSpecialization
import «section 3».GammaGroundSyntaxBridge
import IntegrationSection6.GammaSortedSchemaRows

/-! A valid density schema realizes an actual Gamma-ground volume form
on its RV row. Its complete representative graph is the supplied formula,
so realization introduces no RV section and no additional Gamma names. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

def GammaMeasuredRVSchema.rowDomain (F : GammaMeasuredRVSchema hc B p a k sp) (z : Fin p → M) :
    GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawRVSpace (M := M) a) where
  carrier := F.object.rowDomain z
  definable := by
    apply gammaGroundDefinable_iff_rvBase.mpr
    have h := gamma_tuple_parameter_specialize sp (fun _ : Fin a => .rv) z F.object.domain_definable
    have he : rvValues '' F.object.rowDomain z = {x | Fin.append z x ∈ F.object.domain} :=
      Set.ext (fun x => (F.object.raw_row_domain_iff z x).symm)
    rw [he]
    exact h

def GammaMeasuredRVSchema.rowForm (F : GammaMeasuredRVSchema hc B p a k sp)
    (z : Fin p → M) (hz : F.valid z) :
    GammaGroundVolumeForm hc ⟨B.real ∪ Set.range z,B.gamma⟩ (F.rowDomain z) := by
  let f : F.rowDomain z → GammaGroundDefSet.univ hc ⟨B.real ∪ Set.range z,B.gamma⟩ (volumeGammaSpace hc) :=
    fun x => ⟨F.rowGammaValue z hz x,Set.mem_univ _⟩
  refine ⟨f,?_⟩
  apply GammaGroundDefinable.of_real_codes
  have hRaw : GammaGroundRawDefinable hc B F.density :=
    (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) F.density_definable.proper).mpr F.density_definable
  have h := gammaGroundRaw_relation_specialize hRaw z
  apply h.congr
  intro w
  constructor
  · intro hw
    have hCode : w ∘ Sum.inr ∈ (volumeGammaSpace hc).domain := by
      simpa only [Function.comp_def,Fin.append_right] using F.density_code _ hw
    let c : (volumeGammaSpace hc).domain := ⟨w ∘ Sum.inr,hCode⟩
    have hRV (j : Fin a) : iRV (w (Sum.inl j)) := by
      simpa only [Fin.append_left,Fin.append_right,Function.comp_def,sortEval,iRV] using
        F.density_definable.proper _ hw (Fin.castAdd 1 (Fin.natAdd p j))
    let r : Fin a → CanonicalRV.RVSort M := fun j => ⟨w (Sum.inl j),hRV j⟩
    have hd : F.rowDensity z r c := hw
    let x : F.rowDomain z := ⟨r,F.rowDensity_support z hz r c hd⟩
    refine ⟨⟨⟨r,rfl⟩,hCode⟩,x,?_,?_⟩
    · exact (rvValues_injective (rvValues_decode ⟨w ∘ Sum.inl,⟨r,rfl⟩⟩)).symm
    · exact ((F.rowGammaValue_graph z hz x c).mp hd).symm
  · rintro ⟨⟨hRV,hCode⟩,x,hx,hv⟩
    let c : (volumeGammaSpace hc).domain := ⟨w ∘ Sum.inr,hCode⟩
    have hxr : rvValues x.val = w ∘ Sum.inl :=
      (congrArg rvValues hx).trans (rvValues_decode ⟨w ∘ Sum.inl,hRV⟩)
    have hd : F.rowDensity z x.val c := (F.rowGammaValue_graph z hz x c).mpr hv.symm
    change Fin.append (Fin.append z (rvValues x.val)) (w ∘ Sum.inr) ∈ F.density at hd
    rw [hxr] at hd
    exact hd

@[simp] theorem GammaMeasuredRVSchema.rowForm_value (F : GammaMeasuredRVSchema hc B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (x : F.rowDomain z) :
    (F.rowForm z hz x).val = F.rowGammaValue z hz x := rfl

end DiamondIntegral.Section3
