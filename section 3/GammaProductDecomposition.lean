import «section 3».GammaRVProductCodeMaps
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

def gammaProductCarrierPieceEquiv (A : GammaPiece hc S k) (B : GammaPiece hc S l) :
    (gammaAppendMap A B).image ≃ A × B :=
  (Equiv.ofBijective (gammaAppendBijection A B).map (gammaAppendBijection A B).bijective).symm.trans
    (Equiv.Set.prod A.carrier B.carrier)

@[simp] theorem gammaProductCarrierPieceEquiv_append (A : GammaPiece hc S k) (B : GammaPiece hc S l)
    (a : A) (b : B) : gammaProductCarrierPieceEquiv A B
      ((gammaAppendBijection A B).map ⟨(a.val, b.val), a.property, b.property⟩) = (a, b) := by
  change (Equiv.Set.prod A.carrier B.carrier)
    ((Equiv.ofBijective (gammaAppendBijection A B).map (gammaAppendBijection A B).bijective).symm
      ((Equiv.ofBijective (gammaAppendBijection A B).map (gammaAppendBijection A B).bijective)
        ⟨(a.val, b.val), a.property, b.property⟩)) = _
  rw [Equiv.symm_apply_apply]
  rfl

def gammaProductCodePieceEquiv (A : GammaPiece hc S k) (B : GammaPiece hc S l) :
    codePreimage (gammaAppendMap A B).image ≃ (codePreimage A) × (codePreimage B) :=
  (Equiv.ofBijective (fun p : (codePreimage A) × (codePreimage B) => gammaProductCode A B p.1 p.2) (by
    constructor
    · intro a b he
      have ht := congrArg (fun c : codePreimage (gammaAppendMap A B).image => gammaCodeTuple c.val) he
      change gammaCodeTuple (gammaCodeAppend a.1.val a.2.val) = gammaCodeTuple (gammaCodeAppend b.1.val b.2.val) at ht
      rw [gammaCodeAppend_tuple, gammaCodeAppend_tuple] at ht
      have hp : (gammaCodeTuple a.1.val, gammaCodeTuple a.2.val) =
          (gammaCodeTuple b.1.val, gammaCodeTuple b.2.val) := rvAppend_injective ht
      apply Prod.ext
      · exact Subtype.ext (gammaCodeTuple_injective (congrArg Prod.fst hp))
      · exact Subtype.ext (gammaCodeTuple_injective (congrArg Prod.snd hp))
    · intro c
      obtain ⟨a, b, he⟩ := gammaProductCode_surjective A B c
      exact ⟨(a, b), he⟩)).symm

@[simp] theorem gammaProductCodePieceEquiv_code (A : GammaPiece hc S k) (B : GammaPiece hc S l)
    (a : codePreimage A) (b : codePreimage B) :
    gammaProductCodePieceEquiv A B (gammaProductCode A B a b) = (a, b) := by
  exact (gammaProductCodePieceEquiv A B).apply_symm_apply (a, b)

def GammaObject.productCarrierEquiv (A : GammaObject hc S k) (B : GammaObject hc S l) :
    (A.product B).Carrier ≃ A.Carrier × B.Carrier :=
  (Equiv.sigmaCongrRight (fun i => gammaProductCarrierPieceEquiv
    (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2))).trans
      ((Equiv.sigmaCongrLeft (β := fun p : Fin A.tags × Fin B.tags => (A.piece p.1) × (B.piece p.2))
        finProdFinEquiv.symm).trans (familySigmaProductEquiv (fun i => A.piece i) (fun j => B.piece j)))

def GammaObject.productCodeEquiv (A : GammaObject hc S k) (B : GammaObject hc S l) :
    (A.product B).codeLift.Carrier ≃ A.codeLift.Carrier × B.codeLift.Carrier :=
  (Equiv.sigmaCongrRight (fun i => gammaProductCodePieceEquiv
    (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2))).trans
      ((Equiv.sigmaCongrLeft (β := fun p : Fin A.tags × Fin B.tags =>
        (codePreimage (A.piece p.1)) × (codePreimage (B.piece p.2))) finProdFinEquiv.symm).trans
          (familySigmaProductEquiv (fun i => codePreimage (A.piece i)) (fun j => codePreimage (B.piece j))))

@[simp] theorem GammaObject.productCarrierEquiv_append (A : GammaObject hc S k) (B : GammaObject hc S l)
    (i : Fin (A.tags * B.tags)) (a : A.piece (finProdFinEquiv.symm i).1) (b : B.piece (finProdFinEquiv.symm i).2) :
    A.productCarrierEquiv B ⟨i, (gammaAppendBijection _ _).map ⟨(a.val, b.val), a.property, b.property⟩⟩ =
      (⟨(finProdFinEquiv.symm i).1, a⟩, ⟨(finProdFinEquiv.symm i).2, b⟩) := by
  let e := gammaProductCarrierPieceEquiv (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2)
  let p := (gammaAppendBijection (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2)).map
    ⟨(a.val, b.val), a.property, b.property⟩
  change ((⟨(finProdFinEquiv.symm i).1, (e p).1⟩ : A.Carrier),
    (⟨(finProdFinEquiv.symm i).2, (e p).2⟩ : B.Carrier)) = _
  have he : e p = (a, b) := gammaProductCarrierPieceEquiv_append _ _ a b
  rw [he]

@[simp] theorem GammaObject.productCodeEquiv_code (A : GammaObject hc S k) (B : GammaObject hc S l)
    (i : Fin (A.tags * B.tags)) (a : codePreimage (A.piece (finProdFinEquiv.symm i).1))
    (b : codePreimage (B.piece (finProdFinEquiv.symm i).2)) :
    A.productCodeEquiv B ⟨i, gammaProductCode _ _ a b⟩ =
      (⟨(finProdFinEquiv.symm i).1, a⟩, ⟨(finProdFinEquiv.symm i).2, b⟩) := by
  let e := gammaProductCodePieceEquiv (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2)
  let p := gammaProductCode (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2) a b
  change ((⟨(finProdFinEquiv.symm i).1, (e p).1⟩ : A.codeLift.Carrier),
    (⟨(finProdFinEquiv.symm i).2, (e p).2⟩ : B.codeLift.Carrier)) = _
  have he : e p = (a, b) := gammaProductCodePieceEquiv_code _ _ a b
  rw [he]

theorem gammaProductCode_decode (A : GammaPiece hc S k) (B : GammaPiece hc S l)
    (a : codePreimage A) (b : codePreimage B) :
    codeDecode (gammaAppendMap A B).image (gammaProductCode A B a b) =
      (gammaAppendBijection A B).map
        ⟨((codeDecode A a).val, (codeDecode B b).val), (codeDecode A a).property, (codeDecode B b).property⟩ :=
  Subtype.ext (gammaCodeAppend_decode a.val b.val)

theorem GammaObject.productCodeEquiv_decode (A : GammaObject hc S k) (B : GammaObject hc S l)
    (c : (A.product B).codeLift.Carrier) :
    A.productCarrierEquiv B ((A.product B).decode c) =
      (A.decode (A.productCodeEquiv B c).1, B.decode (A.productCodeEquiv B c).2) := by
  obtain ⟨i, c⟩ := c
  obtain ⟨a, b, rfl⟩ := gammaProductCode_surjective
    (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2) c
  have he : (A.product B).decode ⟨i, gammaProductCode _ _ a b⟩ =
      ⟨i, (gammaAppendBijection _ _).map
        ⟨((codeDecode _ a).val, (codeDecode _ b).val), (codeDecode _ a).property, (codeDecode _ b).property⟩⟩ :=
    congrArg (fun x : (A.product B).piece i => (⟨i, x⟩ : (A.product B).Carrier)) (gammaProductCode_decode _ _ a b)
  rw [he, GammaObject.productCarrierEquiv_append, GammaObject.productCodeEquiv_code]
  rfl

end DiamondIntegral.Section3
