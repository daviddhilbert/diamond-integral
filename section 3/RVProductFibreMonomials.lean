import «section 3».RVGenericFibreJointInjection
import «section 3».RVGenericResiduePoints
import «section 3».GammaGroundRealExtensions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-- Fixing the retained parameter preserves joint injectivity of the
residue and free-coordinate maps. -/
theorem gammaGround_fibreSource_joint_injective
    {P Q R T : Space LRV M} {A : GammaGroundDefSet hc B (P.prod R)}
    {D : GammaGroundDefSet hc B Q} {E : GammaGroundDefSet hc B T}
    (f : GammaGroundMap A D) (g : GammaGroundMap A E)
    (hjoint : ∀ a b : A, g a = g b → f a = f b → a = b) (c : R.domain) :
    ∀ a b : gammaGroundRealPointFibre A c,
      g.fibreSource c a = g.fibreSource c b →
      f.fibreSource c a = f.fibreSource c b → a = b := by
  intro a b hg hf
  let a0 : A := ⟨(a.val,R.decode c),a.property⟩
  let b0 : A := ⟨(b.val,R.decode c),b.property⟩
  have hg0 : g a0 = g b0 := Subtype.ext (congrArg Subtype.val hg)
  have hf0 : f a0 = f b0 := Subtype.ext (congrArg Subtype.val hf)
  apply Subtype.ext
  exact congrArg (fun z : A => z.val.1) (hjoint a0 b0 hg0 hf0)

/-- The full generic fibre of a jointly injective product map has one
residue output and an affine unimodular free-coordinate formula. Every
coefficient is definable over exactly the original ground plus the
retained residue tuple. -/
theorem gammaGroundRVProduct_generic_fibre_monomial {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {n m p : ℕ}
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n)))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace m))
    (S : GammaGroundDefSet hc B (rawRVUnitSpace p))
    (hS : (rvUnitTupleValues '' S.carrier).Finite)
    (f : GammaGroundMap T D) (g : GammaGroundMap T S)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b) (r : R)
    (x : gammaGroundRealPointFibre T ⟨rvUnitValues r.val,Set.mem_range_self _⟩)
    (hxg : GammaTupleIndependentOver B (rvUnitTupleValues x.val)) :
    ∃ C : Matrix (Fin m) (Fin m) ℤ, IsUnit C.det ∧
    ∃ c : Fin m → (CanonicalRV.RVSort M)ˣ, ∃ s : Fin p → (CanonicalRV.RVSort M)ˣ,
      (∀ j, DefinableClosureAtBase (adjoinRVUnitTuple B r.val) .rv (rvUnitValues c j)) ∧
      (∀ j, DefinableClosureAtBase (adjoinRVUnitTuple B r.val) .rv (rvUnitValues s j)) ∧
      ∀ y : gammaGroundRealPointFibre T ⟨rvUnitValues r.val,Set.mem_range_self _⟩,
        rvUnitTupleValues y.val = rvUnitTupleValues x.val →
        (f.fibreSource ⟨rvUnitValues r.val,Set.mem_range_self _⟩ y).val = c * integerMonomialMap C y.val ∧
        (g.fibreSource ⟨rvUnitValues r.val,Set.mem_range_self _⟩ y).val = s := by
  let cr : (rawRVUnitSpace (M := M) n).domain := ⟨rvUnitValues r.val,Set.mem_range_self _⟩
  let A := gammaGroundRealPointFibre T cr
  let F := f.fibreSource cr
  let G := g.fibreSource cr
  have hsmallC : Cardinal.mk (adjoinRVUnitTuple B r.val).real < κ :=
    small_union_range hκ B.real hsmall (rvUnitValues r.val)
  have hΓC : Section2.NontrivialDefinableGamma (adjoinRVUnitTuple B r.val) :=
    hΓ.mono Set.subset_union_left Set.Subset.rfl
  have hxC : GammaTupleIndependentOver (adjoinRVUnitTuple B r.val) (rvUnitTupleValues x.val) :=
    (gammaGroundRVUnit_residue_gamma_independent_iff hκ hs h00 hsmall R hR r _).mpr hxg
  have hj := gammaGround_fibreSource_joint_injective f g hjoint cr
  obtain ⟨C,hC,c,hcdef,hformula⟩ := gammaGroundRVUnitMap_generic_fibre_joint_unimodular
    hκ hs h00 hsmallC hγsmall hΓC A (D.monoReal Set.subset_union_left)
      (S.monoReal Set.subset_union_left) hS F G hj x hxC
  obtain ⟨s,hsdef,hsformula⟩ := gammaGroundRVUnitResidueMap_generic_fibre_definable
    hκ hs h00 hsmallC hγsmall hΓC A (S.monoReal Set.subset_union_left) hS G x hxC
  exact ⟨C,hC,c,s,hcdef,hsdef,fun y hy => ⟨hformula y hy,hsformula y hy⟩⟩
end DiamondIntegral.Section3
