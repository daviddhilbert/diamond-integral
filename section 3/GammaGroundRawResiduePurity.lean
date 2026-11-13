import «section 3».GammaGroundResiduePurity
import «section 3».GammaGroundRVCharacterSymmetry
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-- Pure residue-field normalization for any finite original-ground raw
RV relation, in particular for a source/target map graph. -/
theorem gammaGroundRaw_residue_pullback_pure {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hsmall : Cardinal.mk B.real < κ)
    {ι : Type} [Finite ι] (A : Set (ι → M)) (hA : GammaGroundRawDefinable hc B A)
    (hproper : ∀ z ∈ A, ∀ i, iRV (z i)) (s : ι → CanonicalRV.RVSort M) :
    ResiduePurity.PureDef {x : ι → ModelResidue M |
      (fun i => (s i * residueRV (x i)).val) ∈ A} := by
  letI := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let T : Set (Fin (Fintype.card ι) → M) := {z | z ∘ e ∈ A}
  have hT : GammaGroundRawDefinable hc B T := hA.preimage_comp e
  have hp : ∀ z ∈ T, ∀ i, sortEval .rv (z i) := by
    intro z hz i
    have h := hproper (z ∘ e) hz (e.symm i)
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,iRV,sortEval] using h
  have hn := (gammaGroundRawDefinable_iff_sortedBase hp).mp hT
  let D : Set (Fin (Fintype.card ι) → CanonicalRV.RVSort M) := {t | rvValues t ∈ T}
  have him : rvValues '' D = T := by
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ht
    · intro hz
      let t : Fin (Fintype.card ι) → CanonicalRV.RVSort M := fun i => ⟨z i,hp z hz i⟩
      exact ⟨t,hz,rfl⟩
  have hD : GammaGroundDefinable hc B (rawRVSpace (Fintype.card ι)) D := by
    apply gammaGroundDefinable_iff_rvBase.mpr
    rw [him]
    exact hn
  let U : GammaGroundDefSet hc B (rawRVSpace (Fintype.card ι)) := ⟨D,hD⟩
  have h := (gammaGround_residue_pullback_pure hκ hsmall U (s ∘ e.symm)).preimage_comp e.symm
  convert h using 1
  ext x
  change ((fun i => (s i * residueRV (x i)).val) ∈ A) ↔
    ((fun i => (s (e.symm (e i)) * residueRV (x (e.symm (e i)))).val) ∈ A)
  simp only [Equiv.symm_apply_apply]

end DiamondIntegral.Section3
