import «section 3».GammaGroundGammaRepresentatives
import «section 3».GammaGroundGammaSemiring
import «section 3».GammaGroundGammaSinglePiece
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}

theorem gammaGroundGammaSemiringClass_coprod (A D : GammaGroundGammaObject hc B k) :
    gammaGroundGammaSemiringClass (A.coprod D) = gammaGroundGammaSemiringClass A + gammaGroundGammaSemiringClass D := by
  have h := congrArg (gammaGroundGammaKPlusToSemiring (hc := hc) (ground := B)) (gammaGroundGammaClass_coprod A D)
  simpa only [map_add,gammaGroundGammaKPlusToSemiring_class] using h

/-- Finite family tags contribute a genuine positive sum of native
Gamma pieces; tag changes retain their original full-code lifts. -/
theorem gammaGroundGammaSemiringClass_finite_pieces (N : ℕ)
    (p : Fin N → GammaGroundGammaPiece hc B k) :
    gammaGroundGammaSemiringClass (⟨N,p⟩ : GammaGroundGammaObject hc B k) =
      ∑ i, gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (p i)) := by
  induction N with
  | zero =>
    have he : (⟨0,p⟩ : GammaGroundGammaObject hc B k) = GammaGroundGammaObject.empty hc B k := by
      congr 1
      funext i
      exact i.elim0
    rw [he,gammaGroundGammaSemiringClass_empty,Finset.univ_eq_empty,Finset.sum_empty]
  | succ N ih =>
    let A := GammaGroundGammaObject.single (p 0)
    let D : GammaGroundGammaObject hc B k := ⟨N,fun j => p j.succ⟩
    let e : Fin (N+1) ≃ Fin (1+N) := finCongr (Nat.add_comm N 1)
    have hp : ∀ i, (p i).carrier = ((A.coprod D).piece (e i)).carrier := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · have he0 : e 0 = Fin.castAdd N (0 : Fin 1) := Fin.ext rfl
        simp only [he0,GammaGroundFiniteFamily.coprod,A,D,GammaGroundGammaObject.single,Fin.addCases_left]
      · have hej : e j.succ = Fin.natAdd 1 j := by
          apply Fin.ext
          change j.val+1 = 1+j.val
          omega
        simp only [hej,GammaGroundFiniteFamily.coprod,A,D,GammaGroundGammaObject.single,Fin.addCases_right]
    let E : (⟨N+1,p⟩ : GammaGroundGammaObject hc B k) ≅ A.coprod D :=
      asIso (show _ ⟶ _ from gammaGroundGammaTagHom _ _ e hp)
    rw [gammaGroundGammaSemiringClass_iso E,gammaGroundGammaSemiringClass_coprod]
    rw [ih]
    exact (Fin.sum_univ_succ (fun i => gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (p i)))).symm

theorem gammaGroundGammaSemiringClass_tag_sum (A : GammaGroundGammaObject hc B k) :
    gammaGroundGammaSemiringClass A = ∑ i, gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (A.piece i)) := by
  cases A with
  | mk N p => exact gammaGroundGammaSemiringClass_finite_pieces N p
end DiamondIntegral.Section3
