import «section 5».NativeRVValuePatterns
import «section 5».OriginalPredicateSyntax

/-! A finite native RES schema consists of an original-base domain family
and a fixed bound on its full value support. Valid rows realize actual
native RES objects, on the literal domain, including its zero coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure RESSetSchema (B : Base (M := M)) (p a : ℕ) (sp : Fin p → SortTag) where
  domain : GammaDomainFormula B p a sp
  valueBound : ℕ

def RESSetSchema.rowDomain {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag}
    (F : RESSetSchema B p a sp) (z : Fin p → M) : Set (Fin a → M) :=
  {x | Fin.append z x ∈ F.domain.val}

theorem RESSetSchema.row_domain_definable {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag}
    (F : RESSetSchema B p a sp) (z : Fin p → M) :
    DefinableOverBase ⟨B.real ∪ Set.range z, B.gamma⟩ (fun _ => .rv) (F.rowDomain z) :=
  gamma_tuple_parameter_specialize sp (fun _ => .rv) z F.domain.property

def RESSetSchema.validity (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag}
    (F : RESSetSchema B p a sp) : LRV.Formula (commonRealNames B ⊕ Fin p) :=
  rvFiniteValueValidityFormula F.valueBound (nativeRVValueSyntax (M := M)) (gammaDomainSyntax hc B F.domain)

def RESSetSchema.Valid (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag}
    (F : RESSetSchema B p a sp) (z : Fin p → M) : Prop :=
  (∀ i, sortEval (sp i) (z i)) ∧ (F.validity hc).Realize (predicateParameterValues B z)

theorem RESSetSchema.valid_iff_finite_values (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag}
    (F : RESSetSchema B p a sp) (z : Fin p → M) :
    F.Valid hc z ↔ (∀ i, sortEval (sp i) (z i)) ∧
      (rawRVValuePattern '' F.rowDomain z).Finite ∧
        (rawRVValuePattern '' F.rowDomain z).ncard ≤ F.valueBound := by
  have hs (x : Fin a → M) (hx : (gammaDomainSyntax hc B F.domain).Realize
      (Sum.elim (predicateParameterValues B z) x)) (i : Fin a) : iRV (x i) := by
    have h := (gammaDomainSyntax_realize hc B F.domain z x).mp hx
    simpa only [Fin.append_right, sortEval, iRV] using F.domain.property.proper _ h (Fin.natAdd p i)
  have he : {x : Fin a → M | (gammaDomainSyntax hc B F.domain).Realize
      (Sum.elim (predicateParameterValues B z) x)} = F.rowDomain z := by
    ext x
    exact gammaDomainSyntax_realize hc B F.domain z x
  unfold Valid validity
  rw [rvFiniteValueValidityFormula_card F.valueBound (nativeRVValueSyntax (M := M)) _ _ hs, he]

def RESSetSchema.object (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag}
    (F : RESSetSchema B p a sp) (z : Fin p → M) (h : F.Valid hc z) :
    GammaGroundRESObject hc ⟨B.real ∪ Set.range z, B.gamma⟩ a :=
  nativeRESObjectOfRawSet hc _ (F.rowDomain z) (F.row_domain_definable z)
    ((F.valid_iff_finite_values hc z).mp h).2.1

theorem raw_RV_value_image_eq_chart_range {B : Base (M := M)} {k : ℕ} (A : RVMeasuredCharts.Chart B k) :
    rawRVValuePattern '' A.domain = Set.range A.valuePattern := by
  ext γ
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    funext i
    have hp : iRV (x i) := by
      simpa only [sortEval, iRV] using A.domain_definable.proper x hx i
    simp only [rawRVValuePattern, RVMeasuredCharts.Chart.valuePattern, dif_pos hp]
  · rintro ⟨x, rfl⟩
    refine ⟨x.val, x.property, ?_⟩
    funext i
    have hp : iRV (x.val i) := by
      simpa only [sortEval, iRV] using A.domain_definable.proper x.val x.property i
    simp only [rawRVValuePattern, RVMeasuredCharts.Chart.valuePattern, dif_pos hp]

theorem res_set_schema_at_parameter (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {p k : ℕ} (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i))
    (A : RVMeasuredCharts.RESChart ⟨B.real ∪ Set.range z, B.gamma⟩ k) :
    ∃ F : RESSetSchema B p A.arity sp, F.Valid hc z ∧ F.rowDomain z = A.domain := by
  obtain ⟨D, hD⟩ := promote_original_gamma_predicate hc B sp z hz A.domain A.domain_definable
  let F : RESSetSchema B p A.arity sp := ⟨D, (rawRVValuePattern '' A.domain).ncard⟩
  have he : F.rowDomain z = A.domain := by
    ext x
    exact ((gammaDomainSyntax_realize hc B D z x).symm).trans (hD x)
  refine ⟨F, (F.valid_iff_finite_values hc z).mpr ?_, he⟩
  rw [he]
  exact ⟨hz, (raw_RV_value_image_eq_chart_range A.toChart).symm ▸ A.finite_values, le_rfl⟩

end DiamondIntegral.Section5
