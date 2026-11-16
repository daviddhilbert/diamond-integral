import «section 6».CarriedActiveRootTags
import «section 6».BinaryActiveRootFreezing

/-! Equal source metadata preserve a constructed special map to its
entire target. An RV-pullback with a retained head tag is exactly the
full coordinate bundle over its actual projection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem SpecialCovariantChain.changeSource
    {A C : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {g : Map C B}
    (hAC : A = C) (hpoint : ∀ p : A, (f p).val = (g ⟨p.val,hAC ▸ p.property⟩).val)
    (hf : SpecialCovariantChain (G := G) A B f) : SpecialCovariantChain (G := G) C B g := by
  subst C
  have he : f = g := Map.ext (fun p => Subtype.ext (hpoint p))
  simpa only [he] using hf

theorem rvPullback_coordinate_bundle
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hA : IsRVPullback A.carrier)
    (j : Fin r) (htag : ∀ p ∈ A.carrier, rv M (p.1 (Fin.last n)) = p.2 j) :
    A.carrier = (rvCoordinateBundle (vfDropLast A).image j).carrier := by
  apply coordinate_bundle_of_replacement A j htag
  intro p hp d hd
  refine rvPullback_mem_of_sameRV hA hp ?_ rfl
  funext i
  change rv M (p.1 i) = rv M (Function.update p.1 (Fin.last n) d i)
  by_cases hi : i = Fin.last n
  · subst i
    simpa only [Function.update_self] using hd.symm
  · rw [Function.update_of_ne hi]

end DiamondIntegral.Section6
