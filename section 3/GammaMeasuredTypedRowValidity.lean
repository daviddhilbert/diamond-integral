import «section 3».GammaMeasuredRVSchemata

/-! Recognize Gamma quotient-function validity from typed totality,
support, and completeness of each representative class. This is the
quotient counterpart of the existing typed RV-function recognizer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
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

theorem GammaMeasuredRVSchema.valid_of_typed
    (F : GammaMeasuredRVSchema hc B p a k sp) (z : Fin p → M) (hF : F.object.valid z)
    (hTotal : ∀ x ∈ F.object.rowDomain z, ∃ c : (volumeGammaSpace hc).domain, F.rowDensity z x c)
    (hSupport : ∀ x c, F.rowDensity z x c → x ∈ F.object.rowDomain z)
    (hClass : ∀ x c, F.rowDensity z x c → ∀ d : (volumeGammaSpace hc).domain,
      F.rowDensity z x d ↔ (volumeGammaSpace hc).decode c = (volumeGammaSpace hc).decode d) : F.valid z := by
  refine ⟨hF,hF.1,?_,?_,?_⟩
  · intro x hx
    have hRV (j : Fin a) : iRV (x j) := by
      simpa only [Fin.append_right,sortEval,iRV] using F.object.domain_definable.proper _ hx (Fin.natAdd p j)
    let r : Fin a → CanonicalRV.RVSort M := fun j => ⟨x j,hRV j⟩
    obtain ⟨c,hcValue⟩ := hTotal r hx
    exact ⟨c.val,hcValue⟩
  · intro x y hy
    have hRV (j : Fin a) : iRV (x j) := by
      simpa only [Fin.append_left,Fin.append_right,sortEval,iRV] using
        F.density_definable.proper _ hy (Fin.castAdd 1 (Fin.natAdd p j))
    have hCode : y ∈ (volumeGammaSpace hc).domain := by
      simpa only [Function.comp_def,Fin.append_right] using F.density_code _ hy
    exact hSupport (fun j => ⟨x j,hRV j⟩) ⟨y,hCode⟩ hy
  · intro x hx
    let r : Fin a → CanonicalRV.RVSort M := fun j => ⟨x j,hx j⟩
    refine ⟨?_,?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using hF.1 j
      · simpa only [Fin.append_right] using hx j
    · intro y hy y' hy'
      have hCode : y ∈ (volumeGammaSpace hc).domain := by
        simpa only [Function.comp_def,Fin.append_right] using F.density_code _ hy
      let c : (volumeGammaSpace hc).domain := ⟨y,hCode⟩
      constructor
      · intro hDensity
        have hCode' : y' ∈ (volumeGammaSpace hc).domain := by
          simpa only [Function.comp_def,Fin.append_right] using F.density_code _ hDensity
        let d : (volumeGammaSpace hc).domain := ⟨y',hCode'⟩
        exact (gammaVolumeCodeEq_append c d).mpr ((hClass r c hy d).mp hDensity)
      · intro hEq
        have hCode' : y' ∈ (volumeGammaSpace hc).domain := hEq.choose_spec.choose
        let d : (volumeGammaSpace hc).domain := ⟨y',hCode'⟩
        exact (hClass r c hy d).mpr ((gammaVolumeCodeEq_append c d).mp hEq)

end DiamondIntegral.Section3
