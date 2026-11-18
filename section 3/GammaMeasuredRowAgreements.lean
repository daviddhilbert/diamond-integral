import «section 3».GammaMeasuredRVSyntax
import «section 3».GammaMeasuredSchemaRowForms

/-! Literal row agreements from the existing formula machinery transport
Gamma quotient validity and actual Gamma form values. No RV-function
validity is used for a complete representative relation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
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
variable {p q a k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem gammaMeasured_rowAgreement_valid
    {F : GammaMeasuredRVSchema hc B p a (k+1) sp} {G : GammaMeasuredRVSchema hc B q a (k+1) sq}
    {z : Fin p → M} {t : Fin q → M}
    (h : GammaVolumeRowAgreement F.toRVTemplate z G.toRVTemplate t)
    (ht : ∀ i, sortEval (sq i) (t i)) (hBound : F.object.bound = G.object.bound) (hF : F.valid z) : G.valid t := by
  refine ⟨F.object.valid_of_rowAgreement G.object z t ht hBound h.1 hF.1,ht,?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy⟩ := hF.2.2.1 x ((h.1.1 x).mpr hx)
    exact ⟨y,(h.2.2 x y).mp hy⟩
  · intro x y hy
    exact (h.1.1 x).mp (hF.2.2.2.1 x y ((h.2.2 x y).mpr hy))
  · intro x hx
    have hQ := hF.2.2.2.2 x hx
    refine ⟨?_,?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using ht j
      · simpa only [Fin.append_right] using hx j
    · intro y hy y' hy'
      exact (h.2.2 x y').symm.trans (hQ.2 y ((h.2.2 x y).mpr hy) y' hy')

theorem gammaMeasured_rowAgreement_value
    {F : GammaMeasuredRVSchema hc B p a (k+1) sp} {G : GammaMeasuredRVSchema hc B q a (k+1) sq}
    {z : Fin p → M} {t : Fin q → M}
    (h : GammaVolumeRowAgreement F.toRVTemplate z G.toRVTemplate t)
    (hF : F.valid z) (hG : G.valid t)
    (x : F.object.rowDomain z) (y : G.object.rowDomain t) (hxy : x.val = y.val) :
    F.rowGammaValue z hF x = G.rowGammaValue t hG y := by
  obtain ⟨c,hcValue⟩ := (volumeGammaSpace hc).onto (F.rowGammaValue z hF x)
  have hFC : F.rowDensity z x.val c := (F.rowGammaValue_graph z hF x c).mpr hcValue
  have hGC : G.rowDensity t x.val c := (h.density x.val (gammaVolumeCodeRV c)).mp hFC
  have hGY : G.rowDensity t y.val c := Eq.mp (congrArg (fun r => G.rowDensity t r c) hxy) hGC
  exact hcValue.symm.trans ((G.rowGammaValue_graph t hG y c).mp hGY)

theorem GammaMeasuredRVSchema.recode_valid
    (F : GammaMeasuredRVSchema hc B p a (k+1) sp)
    (C : GammaParameterRecode B p q sp sq) (z : Fin p → M) (t : Fin q → M)
    (ht : ∀ i, sortEval (sq i) (t i))
    (h : (GammaVolumeParameterRecode.mk C).VolumeObjectAgreement F.toRVTemplate z t)
    (hF : F.valid z) : (F.recode C).valid t :=
  gammaMeasured_rowAgreement_valid ((GammaVolumeParameterRecode.mk C).volumeObject_rows F.toRVTemplate z t h) ht rfl hF

end DiamondIntegral.Section3
