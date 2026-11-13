import «section 3».RVMonomialFibreRigidity
import «section 3».IntegerRectangularKernel
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3

/-- Integral monomial maps in arbitrary input and output arities respect multiplication. -/
theorem rectangularMonomial_mul {ι κ G : Type} [Fintype ι] [Fintype κ] [CommGroup G]
    (A : Matrix κ ι ℤ) (x y : ι → G) :
    integerMonomialMap A (x*y) = integerMonomialMap A x * integerMonomialMap A y := by
  funext i
  simp only [integerMonomialMap,Pi.mul_apply,mul_zpow,Finset.prod_mul_distrib]

/-- Injectivity on a full value coset detects the whole residue-torus map,
including when its input and output arities differ. -/
theorem rectangularMonomial_residue_injective
    {ι κ G H Γ : Type} [Fintype ι] [Fintype κ] [CommGroup G] [CommGroup H] [CommGroup Γ]
    (v : G →* Γ) (ρ : H →* G) (hρ : Function.Injective ρ)
    (hvalue : ∀ h, v (ρ h) = 1) (A : Matrix κ ι ℤ) (x : ι → G)
    (hinj : Set.InjOn (integerMonomialMap A) {y | (fun i => v (y i)) = fun i => v (x i)}) :
    Function.Injective (integerMonomialMap (G := H) A) := by
  intro a b hab
  let u : ι → G := x * (ρ ∘ a)
  let w : ι → G := x * (ρ ∘ b)
  have hu : (fun i => v (u i)) = fun i => v (x i) := by
    funext i
    exact (map_mul v _ _).trans (by simp only [Function.comp_apply,hvalue,mul_one])
  have hw : (fun i => v (w i)) = fun i => v (x i) := by
    funext i
    exact (map_mul v _ _).trans (by simp only [Function.comp_apply,hvalue,mul_one])
  have he : integerMonomialMap A u = integerMonomialMap A w := by
    rw [rectangularMonomial_mul,rectangularMonomial_mul]
    congr 1
    funext i
    have hv := congrArg (fun z : κ → H => ρ (z i)) hab
    simpa only [integerMonomialMap,Function.comp_apply,map_prod,map_zpow] using hv
  have huw := hinj hu hw he
  funext i
  apply hρ
  apply mul_left_cancel (a := x i)
  exact congrFun huw i

/-- Injective character maps into fewer coordinates are impossible. -/
theorem rectangularMonomial_arity_le_of_injective
    {H : Type} [CommGroup H] [Nontrivial H]
    (hpower : ∀ d : ℤ, Function.Injective (fun h : H => h ^ d) → IsUnit d)
    {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℤ)
    (hinj : Function.Injective (integerMonomialMap (G := H) A)) : m ≤ k := by
  have hs := integerMonomialMap_row_span_eq_top_of_injective hpower A hinj
  have h := finrank_range_le_card (R := ℤ) A
  change Module.finrank ℤ (Submodule.span ℤ (Set.range A)) ≤ Fintype.card (Fin k) at h
  have hs' : Submodule.span ℤ (Set.range A) = ⊤ := hs
  rw [hs'] at h
  simpa only [finrank_top,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using h

/-- An injective rectangular RV affine monomial map on a full value
fibre needs at least as many output coordinates as input coordinates. -/
theorem rvAffineRectangularMonomial_full_fibre_arity_le
    {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] (h00 : M ⊨ Axioms.ACVF00)
    {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℤ) (c : Fin k → (CanonicalRV.RVSort M)ˣ)
    (δ : Fin m → Values.Gamma (M := M))
    (hinj : Set.InjOn (fun x => c * integerMonomialMap A x) {x | rvUnitTupleValues x = δ}) : m ≤ k := by
  let : CharZero (RVResidueField M) := rvResidueField_charZero h00
  let : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  let : IsAlgClosed (RVResidueField M) := ProvedResidueClosure.provedResidueClosure _ _ Values.presentationValuation
  let : Nontrivial (RVResidueField M)ˣ := ⟨⟨Units.mk0 (2 : RVResidueField M) (by norm_num),1,by
    intro he
    have hv := congrArg Units.val he
    norm_num at hv⟩⟩
  obtain ⟨x,hx⟩ := rvUnitTupleValues_surjective m δ
  apply rectangularMonomial_arity_le_of_injective (fieldUnit_zpow_injective_isUnit (K := RVResidueField M)) A
  apply rectangularMonomial_residue_injective (rvUnitValueHom (M := M)) residueUnitToRV
    residueUnitToRV_injective residueUnitToRV_value_one A x
  intro a ha b hb hab
  exact hinj (ha.trans hx) (hb.trans hx) (congrArg (fun z => c*z) hab)
end DiamondIntegral.Section3
