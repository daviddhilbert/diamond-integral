import «section 3».GammaGroundGammaProductCodeMaps
import «section 3».FamilySigmaProducts
/-! Both Gamma products and their full RV code families separate into
their two original factors, compatibly with the quotient decoder. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def gammaGroundGammaProductCarrierPieceEquiv (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l) :
    (gammaGroundGammaAppendMap A B).image ≃ A × B :=
  (Equiv.ofBijective (gammaGroundGammaAppendBijection A B).map (gammaGroundGammaAppendBijection A B).bijective).symm.trans
    (Equiv.Set.prod A.carrier B.carrier)

@[simp] theorem gammaGroundGammaProductCarrierPieceEquiv_append (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l)
    (a : A) (b : B) : gammaGroundGammaProductCarrierPieceEquiv A B
      ((gammaGroundGammaAppendBijection A B).map ⟨(a.val, b.val), a.property, b.property⟩) = (a, b) := by
  change (Equiv.Set.prod A.carrier B.carrier)
    ((Equiv.ofBijective (gammaGroundGammaAppendBijection A B).map (gammaGroundGammaAppendBijection A B).bijective).symm
      ((Equiv.ofBijective (gammaGroundGammaAppendBijection A B).map (gammaGroundGammaAppendBijection A B).bijective)
        ⟨(a.val, b.val), a.property, b.property⟩)) = _
  rw [Equiv.symm_apply_apply]
  rfl

def gammaGroundGammaProductCodePieceEquiv (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l) :
    gammaGroundCodePreimage (gammaGroundGammaAppendMap A B).image ≃ (gammaGroundCodePreimage A) × (gammaGroundCodePreimage B) :=
  (Equiv.ofBijective (fun p : (gammaGroundCodePreimage A) × (gammaGroundCodePreimage B) => gammaGroundGammaProductCode A B p.1 p.2) (by
    constructor
    · intro a b he
      have ht := congrArg (fun c : gammaGroundCodePreimage (gammaGroundGammaAppendMap A B).image => gammaCodeTuple c.val) he
      change gammaCodeTuple (gammaCodeAppend a.1.val a.2.val) = gammaCodeTuple (gammaCodeAppend b.1.val b.2.val) at ht
      rw [gammaCodeAppend_tuple, gammaCodeAppend_tuple] at ht
      have hp : (gammaCodeTuple a.1.val, gammaCodeTuple a.2.val) =
          (gammaCodeTuple b.1.val, gammaCodeTuple b.2.val) := rvAppend_injective ht
      apply Prod.ext
      · exact Subtype.ext (gammaGroundGammaCodeTuple_injective (congrArg Prod.fst hp))
      · exact Subtype.ext (gammaGroundGammaCodeTuple_injective (congrArg Prod.snd hp))
    · intro c
      obtain ⟨a, b, he⟩ := gammaGroundGammaProductCode_surjective A B c
      exact ⟨(a, b), he⟩)).symm

@[simp] theorem gammaGroundGammaProductCodePieceEquiv_code (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l)
    (a : gammaGroundCodePreimage A) (b : gammaGroundCodePreimage B) :
    gammaGroundGammaProductCodePieceEquiv A B (gammaGroundGammaProductCode A B a b) = (a, b) := by
  exact (gammaGroundGammaProductCodePieceEquiv A B).apply_symm_apply (a, b)

def GammaGroundGammaObject.productCarrierEquiv (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l) :
    (A.product B).Carrier ≃ A.Carrier × B.Carrier :=
  (Equiv.sigmaCongrRight (fun i => gammaGroundGammaProductCarrierPieceEquiv
    (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2))).trans
      ((Equiv.sigmaCongrLeft (β := fun p : Fin A.tags × Fin B.tags => (A.piece p.1) × (B.piece p.2))
        finProdFinEquiv.symm).trans (familySigmaProductEquiv (fun i => A.piece i) (fun j => B.piece j)))

def GammaGroundGammaObject.productCodeEquiv (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l) :
    (A.product B).codeLift.Carrier ≃ A.codeLift.Carrier × B.codeLift.Carrier :=
  (Equiv.sigmaCongrRight (fun i => gammaGroundGammaProductCodePieceEquiv
    (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2))).trans
      ((Equiv.sigmaCongrLeft (β := fun p : Fin A.tags × Fin B.tags =>
        (gammaGroundCodePreimage (A.piece p.1)) × (gammaGroundCodePreimage (B.piece p.2))) finProdFinEquiv.symm).trans
          (familySigmaProductEquiv (fun i => gammaGroundCodePreimage (A.piece i)) (fun j => gammaGroundCodePreimage (B.piece j))))

@[simp] theorem GammaGroundGammaObject.productCarrierEquiv_append (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l)
    (i : Fin (A.tags * B.tags)) (a : A.piece (finProdFinEquiv.symm i).1) (b : B.piece (finProdFinEquiv.symm i).2) :
    A.productCarrierEquiv B ⟨i, (gammaGroundGammaAppendBijection _ _).map ⟨(a.val, b.val), a.property, b.property⟩⟩ =
      (⟨(finProdFinEquiv.symm i).1, a⟩, ⟨(finProdFinEquiv.symm i).2, b⟩) := by
  let e := gammaGroundGammaProductCarrierPieceEquiv (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2)
  let p := (gammaGroundGammaAppendBijection (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2)).map
    ⟨(a.val, b.val), a.property, b.property⟩
  change ((⟨(finProdFinEquiv.symm i).1, (e p).1⟩ : A.Carrier),
    (⟨(finProdFinEquiv.symm i).2, (e p).2⟩ : B.Carrier)) = _
  have he : e p = (a, b) := gammaGroundGammaProductCarrierPieceEquiv_append _ _ a b
  rw [he]

@[simp] theorem GammaGroundGammaObject.productCodeEquiv_code (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l)
    (i : Fin (A.tags * B.tags)) (a : gammaGroundCodePreimage (A.piece (finProdFinEquiv.symm i).1))
    (b : gammaGroundCodePreimage (B.piece (finProdFinEquiv.symm i).2)) :
    A.productCodeEquiv B ⟨i, gammaGroundGammaProductCode _ _ a b⟩ =
      (⟨(finProdFinEquiv.symm i).1, a⟩, ⟨(finProdFinEquiv.symm i).2, b⟩) := by
  let e := gammaGroundGammaProductCodePieceEquiv (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2)
  let p := gammaGroundGammaProductCode (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2) a b
  change ((⟨(finProdFinEquiv.symm i).1, (e p).1⟩ : A.codeLift.Carrier),
    (⟨(finProdFinEquiv.symm i).2, (e p).2⟩ : B.codeLift.Carrier)) = _
  have he : e p = (a, b) := gammaGroundGammaProductCodePieceEquiv_code _ _ a b
  rw [he]

theorem gammaGroundGammaProductCode_decode (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l)
    (a : gammaGroundCodePreimage A) (b : gammaGroundCodePreimage B) :
    gammaGroundCodeDecode (gammaGroundGammaAppendMap A B).image (gammaGroundGammaProductCode A B a b) =
      (gammaGroundGammaAppendBijection A B).map
        ⟨((gammaGroundCodeDecode A a).val, (gammaGroundCodeDecode B b).val), (gammaGroundCodeDecode A a).property, (gammaGroundCodeDecode B b).property⟩ :=
  Subtype.ext (gammaCodeAppend_decode a.val b.val)

theorem GammaGroundGammaObject.productCodeEquiv_decode (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l)
    (c : (A.product B).codeLift.Carrier) :
    A.productCarrierEquiv B ((A.product B).decode c) =
      (A.decode (A.productCodeEquiv B c).1, B.decode (A.productCodeEquiv B c).2) := by
  obtain ⟨i, c⟩ := c
  obtain ⟨a, b, rfl⟩ := gammaGroundGammaProductCode_surjective
    (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2) c
  have he : (A.product B).decode ⟨i, gammaGroundGammaProductCode _ _ a b⟩ =
      ⟨i, (gammaGroundGammaAppendBijection _ _).map
        ⟨((gammaGroundCodeDecode _ a).val, (gammaGroundCodeDecode _ b).val), (gammaGroundCodeDecode _ a).property, (gammaGroundCodeDecode _ b).property⟩⟩ :=
    congrArg (fun x : (A.product B).piece i => (⟨i, x⟩ : (A.product B).Carrier)) (gammaGroundGammaProductCode_decode _ _ a b)
  rw [he, GammaGroundGammaObject.productCarrierEquiv_append, GammaGroundGammaObject.productCodeEquiv_code]
  rfl

end DiamondIntegral.Section3
