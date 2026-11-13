import «section 3».GammaGroundGammaScissors
import «section 3».GammaGroundFamilyTagMaps
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def gammaGroundGammaTagHom (A B : GammaGroundGammaObject hc ground k) (e : Fin A.tags ≃ Fin B.tags)
    (hp : ∀ i, (A.piece i).carrier = (B.piece (e i)).carrier) : GammaGroundGammaHom A B where
  bijection := gammaGroundFamilyBijectionOfTagEquiv A B e (fun i => GammaGroundBijection.ofCarrierEq (hp i))
  contraction := by
    let F := gammaGroundFamilyBijectionOfTagEquiv A.codeLift B.codeLift e (fun i =>
      GammaGroundBijection.ofCarrierEq (by
        ext c
        change (((volumeGammaSpace hc).power (Fin k)).decode c ∈ (A.piece i).carrier) ↔ _
        rw [hp i]
        rfl))
    exact ⟨F, fun _ => rfl⟩

def gammaGroundGammaCoprodCommIso (A B : GammaGroundGammaObject hc ground k) : A.coprod B ≅ B.coprod A :=
  asIso (show A.coprod B ⟶ B.coprod A from gammaGroundGammaTagHom _ _ finAddFlip (by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [GammaGroundFiniteFamily.coprod, Fin.addCases_left, finAddFlip_apply_castAdd, Fin.addCases_right]
    · simp only [GammaGroundFiniteFamily.coprod, Fin.addCases_right, finAddFlip_apply_natAdd, Fin.addCases_left]))

def gammaGroundGammaCoprodAssocIso (A B D : GammaGroundGammaObject hc ground k) : (A.coprod B).coprod D ≅ A.coprod (B.coprod D) :=
  asIso (show (A.coprod B).coprod D ⟶ A.coprod (B.coprod D) from
    gammaGroundGammaTagHom _ _ (finCongr (Nat.add_assoc A.tags B.tags D.tags)) (by
      intro i
      have he := congrFun (Fin.append_assoc A.piece B.piece D.piece) i
      exact congrArg GammaGroundDefSet.carrier he))

def gammaGroundGammaCoprodEmptyIso (A : GammaGroundGammaObject hc ground k) : (GammaGroundGammaObject.empty hc ground k).coprod A ≅ A :=
  asIso (show (GammaGroundGammaObject.empty hc ground k).coprod A ⟶ A from
    gammaGroundGammaTagHom _ _ (finCongr (Nat.zero_add A.tags)) (by
      intro i
      refine Fin.addCases (fun i : Fin 0 => i.elim0) (fun j => ?_) i
      simp only [GammaGroundFiniteFamily.coprod, Fin.addCases_right]
      apply congrArg (fun j : Fin A.tags => (A.piece j).carrier)
      apply Fin.ext
      change j.val = 0 + j.val
      exact (Nat.zero_add _).symm))

end DiamondIntegral.Section3
