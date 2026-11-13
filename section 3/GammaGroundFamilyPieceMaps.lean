import «section 3».GammaGroundFamilyTagMaps
/-! Piecewise bijections assemble into a definable bijection of tagged
families, even when the source and target imaginary presentations differ. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry

noncomputable section
namespace DiamondIntegral.Section3
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M}

def GammaGroundFamilyBijection.pieces (A : GammaGroundFiniteFamily hc ground P) (piece : Fin A.tags → GammaGroundDefSet hc ground Q)
    (f : ∀ i, GammaGroundBijection (A.piece i) (piece i)) :
    GammaGroundFamilyBijection A ⟨A.tags, piece⟩ where
  equiv := Equiv.sigmaCongrRight (fun i => Equiv.ofBijective (f i).map (f i).bijective)
  definable := by
    classical
    intro i j
    by_cases he : i = j
    · subst j
      exact (f i).map.relation_definable.congr (by
        intro x y
        constructor
        · rintro ⟨a, rfl, rfl⟩
          exact ⟨a, (f i).map a, rfl, rfl, rfl⟩
        · rintro ⟨a, b, rfl, rfl, hab⟩
          have hab' : (f i).map a = b := by
            change (⟨i, (f i).map a⟩ : Σ i, piece i) = ⟨i, b⟩ at hab
            simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hab
          exact ⟨a, rfl, congrArg Subtype.val hab'⟩)
    · have hd : GammaGroundRelationDefinable hc ground P Q (fun _ _ => False) := by
        exact (GammaGroundDefSet.empty hc ground (P.prod Q)).definable
      exact hd.congr (by
        intro x y
        constructor
        · exact False.elim
        · rintro ⟨a, b, _, _, hab⟩
          exact he (congrArg Sigma.fst hab))

end DiamondIntegral.Section3
