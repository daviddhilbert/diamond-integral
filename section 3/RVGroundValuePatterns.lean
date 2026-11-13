import «section 3».RVCoefficientGammaPatterns
import «section 3».RVGlobalValuePatterns
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GuardedRVNormalForm
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def equalityGammaPattern (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (b : EqualityValuePattern E)
    (γ : Fin n → Values.Gamma (M := M)) : Prop :=
  (monomialGammaEqualValue E.left E.right a r γ ↔ b.1 = true) ∧
    (∀ i, monomialGammaResidue (E.leftK.terms i) a r γ ↔ b.2.1 i = true) ∧
    (∀ i, monomialGammaResidue (E.rightK.terms i) a r γ ↔ b.2.2 i = true)

def literalGammaPattern (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) :
    LiteralValuePattern L → (Fin n → Values.Gamma (M := M)) → Prop :=
  match L with
  | .equality E _ => equalityGammaPattern E a r
  | .order _ _ => fun _ _ => True

def globalGammaPattern (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (b : RVDNFGlobalPattern D)
    (γ : Fin n → Values.Gamma (M := M)) : Prop :=
  ∀ L : rvDNFLiterals D, literalGammaPattern L.val a r (b L) γ

theorem equalityGammaPattern_semantics (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (b : EqualityValuePattern E)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    equalityGammaPattern E a r b (fun i => rvUnitValueHom (x i)) ↔ equalityPatternCell E a r b x := by
  simp only [equalityGammaPattern,equalityPatternCell,polynomialResiduePattern,
    monomialGammaEqualValue_semantics,monomialGammaResidue_semantics]

theorem literalGammaPattern_semantics (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (b : LiteralValuePattern L)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    literalGammaPattern L a r b (fun i => rvUnitValueHom (x i)) ↔ literalPatternCell L a r b x := by
  cases L with
  | equality E pos => exact equalityGammaPattern_semantics E a r b x
  | order E pos => rfl

theorem globalGammaPattern_semantics (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (b : RVDNFGlobalPattern D)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    globalGammaPattern D a r b (fun i => rvUnitValueHom (x i)) ↔
      ∀ L : rvDNFLiterals D, literalPatternCell L.val a r (b L) x :=
  forall_congr' (fun L => literalGammaPattern_semantics L.val a r (b L) x)

theorem fullGamma_bool_pattern {B : FullBaseAtomicity.Base (M := M)} {ι : Type} [Finite ι]
    {P : (ι → Values.Gamma (M := M)) → Prop} (hP : FullGammaSyntax.Definable B P) (b : Bool) :
    FullGammaSyntax.Definable B (fun γ => P γ ↔ b = true) := by
  cases b
  · exact hP.not.congr (fun γ => by simp)
  · exact hP.congr (fun γ => by simp)

theorem equalityGammaPattern_definable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (p : Parameters (commonRealNames B))
    (E : EqualityPayload (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n))
    (b : EqualityValuePattern E) : FullGammaSyntax.Definable (integrationGammaBase B)
      (equalityGammaPattern E (sourceVFFixedValues p n) (sourceRVFixedParameters p) b) := by
  have he := fullGamma_bool_pattern (monomialGammaEqualValue_definable hκ hs h00 hc B hsmall p E.left E.right) b.1
  have hl := FullGammaSyntax.Definable.forall_finite (fun i => fullGamma_bool_pattern
    (monomialGammaResidue_definable hκ hs h00 hc B hsmall p (E.leftK.terms i)) (b.2.1 i))
  have hr := FullGammaSyntax.Definable.forall_finite (fun i => fullGamma_bool_pattern
    (monomialGammaResidue_definable hκ hs h00 hc B hsmall p (E.rightK.terms i)) (b.2.2 i))
  exact he.and (hl.and hr)

theorem literalGammaPattern_definable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (p : Parameters (commonRealNames B))
    (L : RVLiteral (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n))
    (b : LiteralValuePattern L) : FullGammaSyntax.Definable (integrationGammaBase B)
      (literalGammaPattern L (sourceVFFixedValues p n) (sourceRVFixedParameters p) b) := by
  cases L with
  | equality E pos => exact equalityGammaPattern_definable hκ hs h00 hc B hsmall p E b
  | order E pos => exact FullGammaSyntax.Definable.true_ _

/-- Every global value pattern from a common-name normal form descends
to a full Gamma predicate over the original real/Gamma base. -/
theorem globalGammaPattern_definable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (p : Parameters (commonRealNames B))
    (D : LiteralDNF (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n))
    (b : RVDNFGlobalPattern D) : FullGammaSyntax.Definable (integrationGammaBase B)
      (globalGammaPattern D (sourceVFFixedValues p n) (sourceRVFixedParameters p) b) :=
  FullGammaSyntax.Definable.forall_finite (fun L => literalGammaPattern_definable hκ hs h00 hc B hsmall p L.val (b L))
end DiamondIntegral.Section3
