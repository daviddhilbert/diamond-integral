import «section 6».CompatibleCentripetalChains

/-! Transport a literal special restriction across an equality of
the actual source carriers. The full point map and original base are
retained; different definability proofs introduce no new operation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem SpecialCovariantChain.rebaseSource
    (h00 : M ⊨ Axioms.ACVF00)
    {A C : DefSet (rawMixedSpace (M := M) n r) S}
    {B D : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {g : Map C D}
    (hAC : A.carrier = C.carrier)
    (hpoint : ∀ p : A, (f p).val = (g ⟨p.val,hAC ▸ p.property⟩).val)
    (hf : SpecialCovariantChain (G := G) A B f) : SpecialCovariantChain (G := G) C g.image g.toImage := by
  have hEq : A = C := defSet_eq_of_carrier_eq hAC
  subst C
  exact hf.restriction_of_liesOver h00 g (Set.Subset.refl _) hpoint

end DiamondIntegral.Section6
