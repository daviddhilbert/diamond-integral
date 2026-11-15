import «section 5».PuiseuxDefinableMaps

/-! Framing actual original-base maps and bijections, with proved finite
equivariance. The action is derived from the complete original graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry DiamondIntegral.Section3
local instance framedMapsStructure : LRV.Structure Carrier := canonicalInterpret
variable [Carrier ⊨ Axioms.ACVF]
variable {n m : ℕ} (N : ℕ+) (a : Fin n → ℤ) (b : Fin m → ℤ)
    (A : DefSet (rawRVSpace (M := Carrier) n) {c | baseCarrier c})
    (B : DefSet (rawRVSpace (M := Carrier) m) {c | baseCarrier c})
    (hA : HasFrameSupport N a A) (hB : HasFrameSupport N b B)

def framedMap (f : Map A B) : framedRVSet N a A → framedRVSet N b B :=
  fun x => frameSetEquiv N b B hB (f ((frameSetEquiv N a A hA).symm x))

def framedBijection (f : DefinableBijection A B) : framedRVSet N a A ≃ framedRVSet N b B :=
  ((frameSetEquiv N a A hA).symm.trans (_root_.Equiv.ofBijective f.map f.bijective)).trans
    (frameSetEquiv N b B hB)

theorem framedMap_equivariant (f : Map A B) (ζ : rootsOfUnity (N : ℕ) ℂ)
    (x : framedRVSet N a A) :
    (framedMap N a b A B hA hB f
      ⟨weightedAction a ζ.val x.val, (framedRVSet_finiteInvariant N a A ζ x.val).mpr x.property⟩).val =
      weightedAction b ζ.val (framedMap N a b A B hA hB f x).val := by
  obtain ⟨η, hη⟩ := finiteRootProjection_surjective N ζ
  have hη' : η.val N = ζ.val := congrArg Subtype.val hη
  let eA := frameSetEquiv N a A hA
  let u : A := eA.symm x
  let x' : framedRVSet N a A :=
    ⟨weightedAction a ζ.val x.val, (framedRVSet_finiteInvariant N a A ζ x.val).mpr x.property⟩
  obtain ⟨v, hv, hfv⟩ := original_RV_map_equivariant A B f η u
  have hs := frameSetEquiv_action N a A hA η u v hv
  have hu : (frameSetEquiv N a A hA u).val = x.val := congrArg Subtype.val (eA.apply_symm_apply x)
  rw [hu, hη'] at hs
  have hsrc : v = eA.symm x' := by
    apply eA.injective
    rw [eA.apply_symm_apply]
    exact Subtype.ext hs
  have ht := frameSetEquiv_action N b B hB η (f u) (f v) hfv
  rw [hη'] at ht
  change (frameSetEquiv N b B hB (f (eA.symm x'))).val = _
  rw [← hsrc]
  exact ht

theorem framedBijection_equivariant (f : DefinableBijection A B)
    (ζ : rootsOfUnity (N : ℕ) ℂ) (x : framedRVSet N a A) :
    (framedBijection N a b A B hA hB f
      ⟨weightedAction a ζ.val x.val, (framedRVSet_finiteInvariant N a A ζ x.val).mpr x.property⟩).val =
      weightedAction b ζ.val (framedBijection N a b A B hA hB f x).val :=
  framedMap_equivariant N a b A B hA hB f.map ζ x

end DiamondIntegral.Section5.PuiseuxOriginal
