import «section 3».GammaMeasuredRVSchemata
import Integration7.GammaVolumeParameterRecoding
import Integration7.GammaVolumeElementaryFormulas
import Integration7.GammaVolumeCoproductFormulas

/-! Reuse the existing RV-density formula operations as syntax for
complete Gamma code relations. Their RV-function validity is not assumed
or used; the Gamma quotient validity is checked separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
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
variable {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def GammaMeasuredRVSchema.toRVTemplate (F : GammaMeasuredRVSchema hc B p a (k+1) sp) :
    GammaRVVolumeSchema B p a k sp where
  object := F.object
  density := F.density
  density_definable := F.density_definable
  density_nonzero w hw := (F.density_code w hw).2

def GammaMeasuredRVSchema.ofRVTemplate (F : GammaRVVolumeSchema B p a k sp) :
    GammaMeasuredRVSchema hc B p a (k+1) sp where
  object := F.object
  density := F.density
  density_definable := F.density_definable
  density_code w hw := by
    refine ⟨?_,F.density_nonzero w hw⟩
    simpa only [Function.comp_apply,Fin.append_right,sortEval,iRV] using
      F.density_definable.proper w hw (Fin.natAdd (p+a) (0 : Fin 1))

def GammaMeasuredRVSchema.elementaryFormula (F : GammaMeasuredRVSchema hc B p a (k+1) sp) :
    GammaMeasuredRVSchema hc B p (a+1) (k+1) sp :=
  .ofRVTemplate F.toRVTemplate.elementaryFormula

def GammaMeasuredRVSchema.coprodFormula (F : GammaMeasuredRVSchema hc B p a (k+1) sp)
    (G : GammaMeasuredRVSchema hc B p b (k+1) sp) :
    GammaMeasuredRVSchema hc B p (1+(a+b)) (k+1) sp :=
  .ofRVTemplate (F.toRVTemplate.coprodFormula G.toRVTemplate)

def GammaMeasuredRVSchema.recode (F : GammaMeasuredRVSchema hc B p a (k+1) sp)
    (C : GammaParameterRecode B p q sp sq) : GammaMeasuredRVSchema hc B q a (k+1) sq :=
  .ofRVTemplate ((GammaVolumeParameterRecode.mk C).volumeObject F.toRVTemplate)

def gammaVolumeCodeRV (c : (volumeGammaSpace hc).domain) : Fin 1 → CanonicalRV.RVSort M := fun j =>
  ⟨c.val j,by have hj : j = 0 := Subsingleton.elim _ _; subst j; exact c.property.1⟩

theorem GammaMeasuredRVSchema.elementary_rowDensity
    (F : GammaMeasuredRVSchema hc B p a (k+1) sp)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (w : Fin (a+1) → CanonicalRV.RVSort M) (c : (volumeGammaSpace hc).domain) :
    F.elementaryFormula.rowDensity z w c ↔
      F.rowDensity z (w ∘ Fin.castAdd 1) c ∧ w ∈ F.elementaryFormula.object.rowDomain z :=
  F.toRVTemplate.elementary_rowDensity z hz w (gammaVolumeCodeRV c)

end DiamondIntegral.Section3
