import «section 3».GammaGroundRVUnitAngularCells
import «section 3».RVUnitGraphProjections
import «section 3».RVGenericGraphBlocks
import «section 3».GammaGroundAngularCoefficientPoints
import «section 3».RVAngularInputFibres
import «section 3».IntegerMonomialReindexing
import «section 3».RVMonomialFibreRigidity
import «section 3».GammaGenericValueFibres
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

/-- On the whole value fibre of a Gamma-generic input, an actual
definable RV map is an integral monomial with original-ground RV coefficients. -/
theorem gammaGroundRVUnitMap_generic_fibre_monomial {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m)) (f : GammaGroundMap A D)
    (x : A) (hxg : GammaTupleIndependentOver B (rvUnitTupleValues x.val)) :
    ∃ C : Matrix (Fin m) (Fin n) ℤ, ∃ c : Fin m → (CanonicalRV.RVSort M)ˣ,
      (∀ j, DefinableClosureAtBase B .rv (rvUnitValues c j)) ∧
      ∀ y : A, rvUnitTupleValues y.val = rvUnitTupleValues x.val → (f y).val = c * integerMonomialMap C y.val := by
  let T := f.unitGraphMap.image
  let p := (f.unitGraphMap x).val
  have hp : p ∈ T.carrier := ⟨x,rfl⟩
  obtain ⟨N,X,hE,_,hcov⟩ := gammaGroundRVUnit_angular_cells hκ hs h00 hsmall T
  obtain ⟨i,hpi⟩ := (hcov p).mp hp
  let E : RVAngularCell (X i).carrier := Classical.choice (hE i)
  let K := Section2.zeroFaceChart (Set.range E.active)
  let I : Fin n → Fin (n+m) := Fin.castAdd m
  let O : Fin m → Fin (n+m) := Fin.natAdd n
  have hsub : (X i).carrier ⊆ T.carrier := fun z hz => (hcov z).mpr ⟨i,hz⟩
  let label := f.unitGraphLabel.restrict hsub
  have hlabel : label.FiniteFibres := f.unitGraphLabel_finite.comp
    (GammaGroundMap.finiteFibres_of_injective (show Function.Injective (GammaGroundMap.inclusion hsub) from
      fun _ _ he => Subtype.ext (congrArg (fun z : T => z.val) he)))
  have hg : GammaTupleIndependentOver B (fun j => rvUnitValueHom (p (I j))) := by
    have he : (fun j => rvUnitValueHom (p (I j))) = rvUnitTupleValues x.val :=
      congrArg rvUnitTupleValues (f.unitGraphMap_input x)
    exact he.symm ▸ hxg
  have hproj : Set.InjOn (fun z => z ∘ I) T.carrier := f.unitGraph_input_injective
  obtain ⟨e,he⟩ := gammaGroundRVAngular_generic_graph_block hκ hs h00 hsmall hγsmall hΓ (X i) E K I
    ⟨p,hpi⟩ hg _ label hlabel (hproj.mono hsub)
  let J := I ∘ e
  have hJ : Set.InjOn (fun z => z ∘ J) T.carrier := by
    intro a ha b hb hab
    apply hproj ha hb
    funext j
    have hj := congrFun hab (e.symm j)
    simpa only [J,Function.comp_apply,Equiv.apply_symm_apply] using hj
  let r := (E.coordinateEquiv K p).1
  let u := (E.coordinateEquiv K p).2
  obtain ⟨L,R,G,hR,_,hcover⟩ := gammaGroundRVAngularCell_finite_products hκ hs h00 hsmall hγsmall hΓ (X i) E K
  obtain ⟨j,hr,hu⟩ := (hcover p).mp hpi
  have hG : (G j).carrier.Nonempty := ⟨rvUnitTupleValues u,hu⟩
  have hrect : ∀ s ∈ (R j).carrier, ∀ v, rvUnitTupleValues v ∈ (G j).carrier →
      (E.coordinateEquiv K).symm (s,v) ∈ (X i).carrier := by
    intro s hs v hv
    apply (hcover _).mpr
    refine ⟨j,?_,?_⟩
    · rw [(E.coordinateEquiv K).apply_symm_apply]
      exact hs
    · rw [(E.coordinateEquiv K).apply_symm_apply]
      exact hv
  let W := E.outputCoefficientMatrix K J O
  let c := integerMonomialMap W r
  have hc : ∀ a, DefinableClosureAtBase B .rv (rvUnitValues c a) :=
    gammaGroundRVAngularProduct_residue_image_point_definable (X i) E K J he (R j) (hR j) (G j) hG hrect
      (hJ.mono hsub) _ (gammaGroundRVUnitRectangularMonomialMap (R j) W) ⟨r,hr⟩
  let C : Matrix (Fin m) (Fin n) ℤ := fun a b => E.outputMonomialMatrix K J O a (e.symm b)
  refine ⟨C,c,hc,?_⟩
  intro y hy
  let q := (f.unitGraphMap y).val
  have hq : q ∈ T.carrier := ⟨y,rfl⟩
  have hyq : rvUnitTupleValues (q ∘ J) = rvUnitTupleValues (p ∘ J) := by
    funext a
    have hpy := congrFun (f.unitGraphMap_input y) (e a)
    have hpx := congrFun (f.unitGraphMap_input x) (e a)
    change rvUnitValueHom (q (I (e a))) = rvUnitValueHom (p (I (e a)))
    exact (congrArg rvUnitValueHom hpy).trans
      ((congrFun hy (e a)).trans (congrArg rvUnitValueHom hpx).symm)
  have hh := E.output_on_value_fibre K J O he T.carrier hsub hJ p hpi q hq hyq
  have hqin : q ∘ J = y.val ∘ e := by
    funext a
    exact congrFun (f.unitGraphMap_input y) (e a)
  have hqout : q ∘ O = (f y).val := f.unitGraphMap_output y
  rw [hqout,hqin,integerMonomialMap_reindex_input] at hh
  exact hh
/-- Injectivity makes the generic-fibre exponent matrix unimodular. -/
theorem gammaGroundRVUnitMap_generic_fibre_unimodular {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (A D : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (f : GammaGroundMap A D)
    (hf : Function.Injective f) (x : A) (hxg : GammaTupleIndependentOver B (rvUnitTupleValues x.val)) :
    ∃ C : Matrix (Fin n) (Fin n) ℤ, IsUnit C.det ∧
    ∃ c : Fin n → (CanonicalRV.RVSort M)ˣ,
      (∀ j, DefinableClosureAtBase B .rv (rvUnitValues c j)) ∧
      ∀ y : A, rvUnitTupleValues y.val = rvUnitTupleValues x.val →
        (f y).val = c * integerMonomialMap C y.val := by
  obtain ⟨C,c,hc,hformula⟩ := gammaGroundRVUnitMap_generic_fibre_monomial hκ hs h00 hsmall hγsmall hΓ A D f x hxg
  refine ⟨C,?_,c,hc,hformula⟩
  apply rvAffineMonomial_full_fibre_unimodular h00 C c (rvUnitTupleValues x.val)
  intro a ha b hb hab
  have haA := gammaGroundRVUnit_generic_value_fibre_invariant hκ hs h00 hsmall A x hxg a ha.symm
  have hbA := gammaGroundRVUnit_generic_value_fibre_invariant hκ hs h00 hsmall A x hxg b hb.symm
  have he : f ⟨a,haA⟩ = f ⟨b,hbA⟩ := by
    apply Subtype.ext
    rw [hformula ⟨a,haA⟩ ha,hformula ⟨b,hbA⟩ hb]
    exact hab
  exact congrArg Subtype.val (hf he)
end DiamondIntegral.Section3
