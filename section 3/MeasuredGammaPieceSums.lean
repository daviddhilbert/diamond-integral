import «section 3».GammaGroundMeasuredGammaSemiring
import «section 3».GammaGroundMeasuredGammaRepresentatives
import «section 3».GammaPieceSums
import «section 3».GammaGroundGammaProductLaws
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundMeasuredGammaSemiringClass_coprod (A D : GammaGroundMeasuredGammaObject hc B k) :
    gammaGroundMeasuredGammaSemiringClass (A.coprod D) =
      gammaGroundMeasuredGammaSemiringClass A + gammaGroundMeasuredGammaSemiringClass D := by
  have h := congrArg (gammaGroundMeasuredGammaKPlusToSemiring (hc := hc) (ground := B))
    (gammaGroundMeasuredGammaClass_coprod A D)
  simpa only [map_add,gammaGroundMeasuredGammaKPlusToSemiring_class] using h

theorem gammaGroundMeasuredGammaSemiringClass_finite_pieces (N : ℕ)
    (p : Fin N → GammaGroundGammaPiece hc B k) (w : ∀ i, GammaGroundVolumeForm hc B (p i)) :
    gammaGroundMeasuredGammaSemiringClass (⟨⟨N,p⟩,w⟩ : GammaGroundMeasuredGammaObject hc B k) =
      ∑ i, gammaGroundMeasuredGammaSemiringClass
        (⟨GammaGroundGammaObject.single (p i),fun _ => w i⟩ : GammaGroundMeasuredGammaObject hc B k) := by
  induction N with
  | zero =>
    let A : GammaGroundMeasuredGammaObject hc B k := ⟨⟨0,p⟩,w⟩
    let h : GammaGroundMeasuredGammaHom A (GammaGroundMeasuredGammaObject.empty hc B k) :=
      ⟨(gammaGroundGammaEmptyTagsIso A.underlying rfl).hom,fun a => a.1.elim0⟩
    rw [gammaGroundMeasuredGammaSemiringClass_iso (asIso (show A ⟶ _ from h)),
      gammaGroundMeasuredGammaSemiringClass_empty,Finset.univ_eq_empty,Finset.sum_empty]
  | succ N ih =>
    let A : GammaGroundMeasuredGammaObject hc B k := ⟨GammaGroundGammaObject.single (p 0),fun _ => w 0⟩
    let D : GammaGroundMeasuredGammaObject hc B k := ⟨⟨N,fun j => p j.succ⟩,fun j => w j.succ⟩
    let e : Fin (N+1) ≃ Fin (1+N) := finCongr (Nat.add_comm N 1)
    have hp : ∀ i, (p i).carrier = ((A.coprod D).underlying.piece (e i)).carrier := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · have he0 : e 0 = Fin.castAdd N (0 : Fin 1) := Fin.ext rfl
        simp only [he0,GammaGroundMeasuredGammaObject.coprod,GammaGroundFiniteFamily.coprod,A,D,
          GammaGroundGammaObject.single,Fin.addCases_left]
      · have hej : e j.succ = Fin.natAdd 1 j := by
          apply Fin.ext
          change j.val+1 = 1+j.val
          omega
        simp only [hej,GammaGroundMeasuredGammaObject.coprod,GammaGroundFiniteFamily.coprod,A,D,
          GammaGroundGammaObject.single,Fin.addCases_right]
    let S : GammaGroundMeasuredGammaObject hc B k := ⟨⟨N+1,p⟩,w⟩
    let f := gammaGroundGammaTagHom S.underlying (A.coprod D).underlying e hp
    have hpres : ∀ a : S.underlying.Carrier, S.combinedWeight a = (A.coprod D).combinedWeight (f.bijection.equiv a) := by
      rintro ⟨i,a⟩
      revert a
      refine Fin.cases ?_ (fun j => ?_) i
      · intro a
        let b : A.underlying.Carrier := ⟨(0 : Fin 1),a⟩
        have he0 : e 0 = Fin.castAdd N (0 : Fin 1) := Fin.ext rfl
        have hm : f.bijection.equiv ⟨0,a⟩ = gammaGroundFamilyCoprodInl A.underlying D.underlying b :=
          gammaGroundFamilyCarrier_ext _ he0 rfl
        rw [hm,gammaGroundMeasuredGammaCoprod_combined_left]
        rfl
      · intro a
        let b : D.underlying.Carrier := ⟨j,a⟩
        have hej : e j.succ = Fin.natAdd 1 j := by
          apply Fin.ext
          change j.val+1 = 1+j.val
          omega
        have hm : f.bijection.equiv ⟨j.succ,a⟩ = gammaGroundFamilyCoprodInr A.underlying D.underlying b :=
          gammaGroundFamilyCarrier_ext _ hej rfl
        rw [hm,gammaGroundMeasuredGammaCoprod_combined_right]
        rfl
    let h : GammaGroundMeasuredGammaHom S (A.coprod D) := ⟨f,hpres⟩
    rw [gammaGroundMeasuredGammaSemiringClass_iso (asIso (show _ ⟶ _ from h)),gammaGroundMeasuredGammaSemiringClass_coprod]
    rw [ih]
    exact (Fin.sum_univ_succ (fun i => gammaGroundMeasuredGammaSemiringClass
      (⟨GammaGroundGammaObject.single (p i),fun _ => w i⟩ : GammaGroundMeasuredGammaObject hc B k))).symm
end DiamondIntegral.Section3
