import «section 3».NativeGammaBoundaries
import «section 3».FiniteControlledColumns
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]



/-- Every Gamma column of a residue-tuple relation has a common finite
order controller, over exactly the original ground. -/
theorem residue_tuple_gamma_finite_columns {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    {n : ℕ} (R : (Fin n → M) → Values.Gamma (M := M) → Prop)
    (hR : DefinableOverBase B (Fin.lastCases .rv (fun _ => .rv))
      {z | NonzeroRV (z (Fin.last n)) ∧ R (Fin.init z) (codeValue (z (Fin.last n)))})
    (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A)
    (D : Fin n → Set M) (hD : ∀ i, DefinableAtBase B .rv (D i))
    (hvalues : ∀ i, (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D i}).Finite)
    (hsub : ∀ a ∈ A, ∀ i, a i ∈ D i) :
    (relationColumn (fun γ a => R a γ) '' A).Finite := by
  let G := nativeGammaBoundaryRelation h00 B R hR
  have hE := goodGammaImage_finite_residue_tuple hκ hs h00 B hsmall hγsmall G A hA D hD hvalues hsub
  refine finite_columns_of_finite_boundary_union (fun γ a => R a γ) A ?_ (goodGammaImage G A) hE ?_
  · intro a ha
    have hc := integrationGammaDefinable (nativeGammaColumn_definable B R hR a)
    obtain ⟨F,hF,_,_⟩ := FullGammaPoint.exists_definable_minimal_controller h00 _ hc
    exact ⟨F,hF⟩
  · intro a ha γ hγ
    refine ⟨a,ha,?_⟩
    change γ ∈ gammaRow (nativeGammaBoundaryCarrier R) a
    have has : ∀ i, iRV (a i) := by
      intro i
      simpa only [sortEval,iRV] using hA.proper a ha i
    rw [nativeGammaBoundaryRow_eq,if_pos has]
    exact hγ
end DiamondIntegral.Section3
