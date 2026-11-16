import «section 6».UnaryFirstZeroCanonicalTransition
import «section 6».UnaryFirstZeroTerminal

/-! Finite-word completion of the prescribed-core construction. Every
instruction is executed by the checked state transitions. The final
live ordinary map is the actual full remaining ordinary word; no
terminal comparison or whole-disc transport is supplied as an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryFirstZeroState
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r₀ : ℕ}
variable {A₀ : DefSet (rawMixedSpace (M := M) 1 r₀) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {K : UnaryCorePlan A₀}
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hsmall : Cardinal.mk S < κ)

include h00 hκ hs hv hsmall in
theorem exists_terminal {r s : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (T : SpecialTransformations.Section5.Chain R 1 A B) :
    ∀ (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T)
      (Z : UnaryFirstZeroState (G := G) hc K T hT),
    ∃ W : UnaryFirstZeroState (G := G) hc K (.nil B)
        (SpecialTransformations.Section5.GammaChainDefinable.target (ordinaryNamedGammaBase S) T hT),
      ∀ a : A₀,(W.ordinaryMap a).val=(T.toMap (Z.ordinaryMap a)).val := by
  induction T with
  | nil A => exact fun hT Z => ⟨Z,fun _ => rfl⟩
  | @cons r s t A B C step tail ih =>
      intro hT Z
      cases step with
      | canonical A =>
          obtain ⟨W,hW⟩ := ih hT.2 (Z.afterCanonical A tail hT h00 hκ hs hv)
          refine ⟨W,fun a => ?_⟩
          rw [hW a]
          rfl
      | @centripetal r i j D =>
          have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
          subst i
          obtain ⟨W,hW⟩ := ih hT.2 (Z.afterCentripetal D tail hT h00 hκ hs hv hsmall)
          refine ⟨W,fun a => ?_⟩
          rw [hW a]
          rfl

end DiamondIntegral.Section6.UnaryFirstZeroState
