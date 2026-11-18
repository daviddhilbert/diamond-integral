import «section 3».GammaMeasuredRVSchemata
import «section 3».GammaRVFormCodeRows

/-! A complete code graph of an actual Gamma form supplies precisely the
quotient-function validity required by the existing finite-row machinery. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

theorem gammaMeasuredSchema_valid_of_form
    (F : GammaMeasuredRVSchema hc B p a k sp) (z : Fin p → M)
    (hF : F.object.valid z) (A : GammaGroundDefSet hc C (rawRVSpace (M := M) a))
    (ω : GammaGroundVolumeForm hc C A)
    (hDomain : F.object.rowDomain z = A.carrier)
    (hDensity : ∀ x y, Fin.append (Fin.append z x) y ∈ F.density ↔
      Fin.append x y ∈ gammaRVFormCodeRows ω) : F.valid z := by
  have hRows (x : Fin a → CanonicalRV.RVSort M) (c : (volumeGammaSpace hc).domain) :
      F.rowDensity z x c ↔ ∃ u : A, u.val = x ∧ (ω u).val = (volumeGammaSpace hc).decode c :=
    (hDensity (rvValues x) c.val).trans (gammaRVFormCodeRows_mem ω x c)
  refine ⟨hF,hF.1,?_,?_,?_⟩
  · intro x hx
    have hRV (j : Fin a) : iRV (x j) := by
      simpa only [Fin.append_right,sortEval,iRV] using F.object.domain_definable.proper _ hx (Fin.natAdd p j)
    let r : Fin a → CanonicalRV.RVSort M := fun j => ⟨x j,hRV j⟩
    have hr : r ∈ A.carrier := hDomain ▸ hx
    let u : A := ⟨r,hr⟩
    obtain ⟨c,hcValue⟩ := (volumeGammaSpace hc).onto (ω u).val
    exact ⟨c.val,(hRows r c).mpr ⟨u,rfl,hcValue.symm⟩⟩
  · intro x y hy
    have hRV (j : Fin a) : iRV (x j) := by
      simpa only [Fin.append_left,Fin.append_right,sortEval,iRV] using
        F.density_definable.proper _ hy (Fin.castAdd 1 (Fin.natAdd p j))
    let r : Fin a → CanonicalRV.RVSort M := fun j => ⟨x j,hRV j⟩
    have hCode : y ∈ (volumeGammaSpace hc).domain := by
      simpa only [Function.comp_def,Fin.append_right] using F.density_code _ hy
    obtain ⟨u,hu,_⟩ := (hRows r ⟨y,hCode⟩).mp hy
    have hr : r ∈ F.object.rowDomain z := hDomain.symm ▸ (hu ▸ u.property)
    exact hr
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
      obtain ⟨u,hu,hω⟩ := (hRows r c).mp hy
      constructor
      · intro hyDensity
        have hCode' : y' ∈ (volumeGammaSpace hc).domain := by
          simpa only [Function.comp_def,Fin.append_right] using F.density_code _ hyDensity
        let d : (volumeGammaSpace hc).domain := ⟨y',hCode'⟩
        obtain ⟨v,hv,hω'⟩ := (hRows r d).mp hyDensity
        have huv : u = v := Subtype.ext (hu.trans hv.symm)
        exact (gammaVolumeCodeEq_append c d).mpr (hω.symm.trans (huv ▸ hω'))
      · intro hEq
        have hCode' : y' ∈ (volumeGammaSpace hc).domain := hEq.choose_spec.choose
        let d : (volumeGammaSpace hc).domain := ⟨y',hCode'⟩
        exact (hRows r d).mpr ⟨u,hu,hω.trans ((gammaVolumeCodeEq_append c d).mp hEq)⟩

end DiamondIntegral.Section3
