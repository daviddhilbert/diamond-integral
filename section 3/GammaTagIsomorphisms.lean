import «section 3».GammaScissors
import «section 3».FamilyTagMaps
import Mathlib.Logic.Equiv.Fin.Basic

/-! Actual Gamma isomorphisms induced by finite tag permutations retain
the full RV code witnesses. This supplies coproduct coherence maps. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def gammaTagHom (A B : GammaObject hc S k) (e : Fin A.tags ≃ Fin B.tags)
    (hp : ∀ i, (A.piece i).carrier = (B.piece (e i)).carrier) : GammaHom A B where
  bijection := familyBijectionOfTagEquiv A B e (fun i => DefinableBijection.ofCarrierEq (hp i))
  contraction := by
    let F := familyBijectionOfTagEquiv A.codeLift B.codeLift e (fun i =>
      DefinableBijection.ofCarrierEq (by
        ext c
        change (((volumeGammaSpace hc).power (Fin k)).decode c ∈ (A.piece i).carrier) ↔ _
        rw [hp i]
        rfl))
    exact ⟨F, fun _ => rfl⟩

def gammaCoprodCommIso (A B : GammaObject hc S k) : A.coprod B ≅ B.coprod A :=
  asIso (show A.coprod B ⟶ B.coprod A from gammaTagHom _ _ finAddFlip (by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [FiniteFamily.coprod, Fin.addCases_left, finAddFlip_apply_castAdd, Fin.addCases_right]
    · simp only [FiniteFamily.coprod, Fin.addCases_right, finAddFlip_apply_natAdd, Fin.addCases_left]))

def gammaCoprodAssocIso (A B D : GammaObject hc S k) : (A.coprod B).coprod D ≅ A.coprod (B.coprod D) :=
  asIso (show (A.coprod B).coprod D ⟶ A.coprod (B.coprod D) from
    gammaTagHom _ _ (finCongr (Nat.add_assoc A.tags B.tags D.tags)) (by
      intro i
      have he := congrFun (Fin.append_assoc A.piece B.piece D.piece) i
      exact congrArg DefSet.carrier he))

def gammaCoprodEmptyIso (A : GammaObject hc S k) : (GammaObject.empty hc S k).coprod A ≅ A :=
  asIso (show (GammaObject.empty hc S k).coprod A ⟶ A from
    gammaTagHom _ _ (finCongr (Nat.zero_add A.tags)) (by
      intro i
      refine Fin.addCases (fun i : Fin 0 => i.elim0) (fun j => ?_) i
      simp only [FiniteFamily.coprod, Fin.addCases_right]
      apply congrArg (fun j : Fin A.tags => (A.piece j).carrier)
      apply Fin.ext
      change j.val = 0 + j.val
      exact (Nat.zero_add _).symm))

end DiamondIntegral.Section3
