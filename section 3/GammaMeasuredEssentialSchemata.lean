import «section 3».GammaMeasuredTypedRowValidity
import «section 3».GammaMeasuredRVSyntax

/-! Reuse the native essential finite-volume schema and restrict the
complete density relation to its exact domain. This removes precisely
the zero structural rows before realizing an actual measured RV object. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

def GammaMeasuredRVSchema.essential (F : GammaMeasuredRVSchema hc B p a k sp) :
    GammaMeasuredRVSchema hc B p a k sp where
  object := essentialFiniteVolumeSchema F.object
  density := {w | w ∈ F.density ∧ w ∘ Fin.castAdd 1 ∈ (essentialFiniteVolumeSchema F.object).domain}
  density_definable := by
    let st := Fin.append (Fin.append sp (fun _ : Fin a => SortTag.rv)) (fun _ : Fin 1 => SortTag.rv)
    have h := F.density_definable.inter
      ((essentialFiniteVolumeSchema F.object).domain_definable.preimage_real st (Fin.castAdd 1))
    convert h using 1
    ext w
    change (_ ∧ _) ↔ (_ ∧ _ ∧ _)
    exact ⟨fun h => ⟨h.1,h.2,F.density_definable.proper w h.1⟩,fun h => ⟨h.1,h.2.1⟩⟩
  density_code w hw := F.density_code w hw.1

theorem GammaMeasuredRVSchema.essential_rowDensity
    (F : GammaMeasuredRVSchema hc B p a k sp) (z : Fin p → M)
    (x : Fin a → CanonicalRV.RVSort M) (c : (volumeGammaSpace hc).domain) :
    F.essential.rowDensity z x c ↔ F.rowDensity z x c ∧ x ∈ F.essential.object.rowDomain z := by
  change (_ ∧ _ ∘ Fin.castAdd 1 ∈ _) ↔ _
  have he : Fin.append (Fin.append z (rvValues x)) c.val ∘ Fin.castAdd 1 = Fin.append z (rvValues x) :=
    funext (Fin.append_left _ _)
  rw [he]
  rfl

theorem GammaMeasuredRVSchema.essential_valid
    (F : GammaMeasuredRVSchema hc B p a k sp) (z : Fin p → M) (hF : F.valid z) : F.essential.valid z := by
  apply GammaMeasuredRVSchema.valid_of_typed _ z (essentialFiniteVolumeSchema_valid F.object z hF.1)
  · intro x hx
    obtain ⟨v,hv,_⟩ := (essentialFiniteVolumeSchema_rowDomain F.object z x).mp hx
    obtain ⟨c,hcValue⟩ := F.rowDensity_exists z hF ⟨x,F.object.valid_row_support hF.1 x v hv⟩
    exact ⟨c,(F.essential_rowDensity z x c).mpr ⟨hcValue,hx⟩⟩
  · intro x c hx
    exact ((F.essential_rowDensity z x c).mp hx).2
  · intro x c hx d
    obtain ⟨hcValue,hD⟩ := (F.essential_rowDensity z x c).mp hx
    exact (F.essential_rowDensity z x d).trans ((and_iff_left hD).trans
      (F.rowDensity_same_value z hF ⟨x,F.rowDensity_support z hF x c hcValue⟩ c hcValue d))

end DiamondIntegral.Section3
