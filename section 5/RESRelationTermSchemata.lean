import «section 5».RESPrimitiveSchemata

/-! Native ideal witnesses retain their actual coefficient-object list
and orientation bit as finite schema data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

structure RESRelationTermSchema (B : Base (M := M)) (p : ℕ) (sp : Fin p → SortTag) where
  primitive : RESPrimitiveSchema B p sp
  coefficients : List ((a : ℕ) × RESSetSchema B p a sp)
  reversed : Bool

def RESRelationTermSchema.Valid (hc : CanonicalStructure.IsCanonical (M := M))
    (T : RESRelationTermSchema B p sp) (z : Fin p → M) : Prop :=
  T.primitive.Valid hc z ∧ ∀ A ∈ T.coefficients, A.2.Valid hc z

theorem RESRelationTermSchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (T : RESRelationTermSchema B p sp) : DefinableOverBase B sp {z | T.Valid hc z} := by
  have hcfs := DefinableOverBase.finite_iInter (Finset.univ : Finset (Fin T.coefficients.length))
    (fun i => {z | (T.coefficients.get i).2.Valid hc z})
    (fun i _ => (T.coefficients.get i).2.valid_definable hc)
  have h := (T.primitive.valid_definable hc).inter hcfs
  convert h using 1
  ext z
  change (_ ∧ ∀ A ∈ T.coefficients, A.2.Valid hc z) ↔
    (_ ∧ z ∈ sortedUniverse sp ∧ ∀ i ∈ Finset.univ, (T.coefficients.get i).2.Valid hc z)
  simp only [Finset.mem_univ, forall_const]
  have hp : T.primitive.Valid hc z → z ∈ sortedUniverse sp := by
    intro hz
    exact T.primitive.valid_definable hc |>.proper z hz
  constructor
  · rintro ⟨hprim, hall⟩
    exact ⟨hprim, hp hprim, fun i => hall _ (List.get_mem _ _)⟩
  · rintro ⟨hprim, _, hall⟩
    refine ⟨hprim, ?_⟩
    intro A hA
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hA
    exact hall i

def RESRelationTermSchema.realize (hc : CanonicalStructure.IsCanonical (M := M))
    (T : RESRelationTermSchema B p sp) (z : Fin p → M) (h : T.Valid hc z) :
    RESFiniteWitness.RelationTerm hc ⟨B.real ∪ Set.range z, B.gamma⟩ where
  primitive := T.primitive.realize hc z h.1
  coefficient := List.ofFn (fun i : Fin T.coefficients.length =>
    ⟨(T.coefficients.get i).1, (T.coefficients.get i).2.object hc z (h.2 _ (List.get_mem _ _))⟩)
  reversed := T.reversed

def RESRelationTermSchema.recode (R : GammaParameterRecode B p q sp sq)
    (T : RESRelationTermSchema B p sp) : RESRelationTermSchema B q sq where
  primitive := T.primitive.recode R
  coefficients := T.coefficients.map (fun A => ⟨A.1, A.2.recode R⟩)
  reversed := T.reversed

def RESRelationTermSchema.RowAgreement (R : GammaParameterRecode B p q sp sq)
    (T : RESRelationTermSchema B p sp) (z : Fin p → M) (t : Fin q → M) : Prop :=
  T.primitive.RowAgreement R z t ∧ ∀ A ∈ T.coefficients, R.DomainAgreement A.2.domain z t

theorem RESRelationTermSchema.recode_valid_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) (T : RESRelationTermSchema B p sp)
    (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hrow : T.RowAgreement R z t) : T.Valid hc z ↔ (T.recode R).Valid hc t := by
  simp only [Valid, recode, List.forall_mem_map]
  apply and_congr (T.primitive.recode_valid_iff hc R z t hz ht hrow.1)
  exact forall_congr' (fun (A : (a : ℕ) × RESSetSchema B p a sp) => imp_congr_right (fun hA => A.2.recode_valid_iff hc R z t hz ht (hrow.2 A hA)))

theorem RESRelationTermSchema.recode_orientation (R : GammaParameterRecode B p q sp sq)
    (T : RESRelationTermSchema B p sp) : (T.recode R).reversed = T.reversed := rfl

theorem RESRelationTermSchema.recode_coefficient_count (R : GammaParameterRecode B p q sp sq)
    (T : RESRelationTermSchema B p sp) : (T.recode R).coefficients.length = T.coefficients.length :=
  List.length_map _

end DiamondIntegral.Section5
