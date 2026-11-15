import «section 5».NativeRVZeroPatternBases
import «section 5».OriginalRVTotalFamilies
import «section 3».GammaGroundBijectionRestrictions
import «section 3».GammaGroundCarrierBijections

/-! Actual RV bijections preserving selected coordinates restrict to the
corresponding zero strata. Stratifying retained base coordinates commutes
with forming the literal RV-family total. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m d p a : ℕ}

section Iso
variable {X : GammaGroundDefSet hc B (rawRVSpace (M := M) n)}
variable {Y : GammaGroundDefSet hc B (rawRVSpace (M := M) m)}
variable (f : GammaGroundBijection X Y) (j : Fin d → Fin n) (k : Fin d → Fin m)
variable (hcoord : ∀ x : X,(f.map x).val ∘ k = x.val ∘ j)

include hcoord in
theorem nativeRVZeroPattern_bijection_iff (I : Finset (Fin d)) (x : X) :
    nativeRVZeroPattern j I (rvValues x.val) ↔ nativeRVZeroPattern k I (rvValues (f.map x).val) := by
  have he (i : Fin d) : rvValues (f.map x).val (k i) = rvValues x.val (j i) :=
    congrArg Subtype.val (congrFun (hcoord x) i)
  exact forall_congr' (fun i => by rw [he i])

include hcoord in
theorem nativeRVZeroPattern_inverseImage (I : Finset (Fin d)) :
    (f.inverseImage (nativeRVZeroPatternBase Y k I)).carrier = (nativeRVZeroPatternBase X j I).carrier := by
  ext z
  constructor
  · rintro ⟨x,hx,hy⟩
    have h := (nativeRVZeroPatternBase_mem Y k I (f.map x).val).mp hy
    have hp := (nativeRVZeroPattern_bijection_iff f j k hcoord I x).mpr h.2
    exact (nativeRVZeroPatternBase_mem X j I z).mpr ⟨hx ▸ x.property,hx ▸ hp⟩
  · intro hz
    have h := (nativeRVZeroPatternBase_mem X j I z).mp hz
    let x : X := ⟨z,h.1⟩
    exact ⟨x,rfl,(nativeRVZeroPatternBase_mem Y k I (f.map x).val).mpr
      ⟨(f.map x).property,(nativeRVZeroPattern_bijection_iff f j k hcoord I x).mp h.2⟩⟩

def nativeRVZeroPatternBijection (I : Finset (Fin d)) :
    GammaGroundBijection (nativeRVZeroPatternBase X j I) (nativeRVZeroPatternBase Y k I) :=
  (f.restrictTarget _ (fun z hz => ((nativeRVZeroPatternBase_mem Y k I z).mp hz).1)).comp
    (GammaGroundBijection.ofCarrierEq (nativeRVZeroPattern_inverseImage f j k hcoord I).symm)
end Iso

theorem nativeRVTotal_zeroPattern_carrier
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv)) (j : Fin d → Fin p) (I : Finset (Fin d)) :
    (nativeRVZeroPatternBase (originalRVTotalFamily X D) (Fin.castAdd a ∘ j) I).carrier =
      (originalRVTotalFamily (nativeRVZeroPatternBase X j I) D).carrier := by
  ext z
  rw [nativeRVZeroPatternBase_mem,originalRVTotalFamily_mem,originalRVTotalFamily_mem,
    nativeRVZeroPatternBase_mem]
  change ((z ∘ Fin.castAdd a ∈ X.carrier ∧ rvValues z ∈ D.val) ∧
      nativeRVZeroPattern j I (rvValues (z ∘ Fin.castAdd a))) ↔
    ((z ∘ Fin.castAdd a ∈ X.carrier ∧ nativeRVZeroPattern j I (rvValues (z ∘ Fin.castAdd a))) ∧ rvValues z ∈ D.val)
  tauto

end DiamondIntegral.Section5
