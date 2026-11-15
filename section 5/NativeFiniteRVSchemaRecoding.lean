import «section 5».NativeFiniteRVSchemaValidity

/-! The complete finite label validity assertion, including its fixed
cardinality bound and nonzero outputs, transports by exact domain and
full label-graph agreement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def nativeFiniteRVSchemaRecode (R : GammaParameterRecode B p q sp sq)
    (F : GammaFiniteRVSchema B p a k sp) : GammaFiniteRVSchema B q a k sq where
  domain := (R.domain (finiteRVSchemaDomain F)).val
  volume := (R.relation (finiteRVSchemaLabels F)).val
  domain_definable := (R.domain (finiteRVSchemaDomain F)).property
  volume_definable := (R.relation (finiteRVSchemaLabels F)).property
  bound := F.bound

theorem finiteRVSchema_valid_recode_iff (R : GammaParameterRecode B p q sp sq)
    (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hD : R.DomainAgreement (finiteRVSchemaDomain F) z t)
    (hV : R.RelationAgreement (finiteRVSchemaLabels F) z t) :
    F.valid z ↔ (nativeFiniteRVSchemaRecode R F).valid t := by
  constructor
  · rintro ⟨_,hfun,hsrc,hbound⟩
    refine ⟨ht,?_,?_,?_⟩
    · intro x hx
      obtain ⟨y,hy,hu⟩ := hfun x ((hD x).mpr hx)
      exact ⟨y,(hV x y).mp hy,fun y' hy' => hu y' ((hV x y').mpr hy')⟩
    · intro x y hxy
      exact (hD x).mp (hsrc x y ((hV x y).mpr hxy))
    · intro y hy
      have he : {x | Fin.append (Fin.append t x) y ∈ (nativeFiniteRVSchemaRecode R F).volume} =
          {x | Fin.append (Fin.append z x) y ∈ F.volume} := Set.ext (fun x => (hV x y).symm)
      change _ ∧ _
      rw [he]
      exact hbound y hy
  · rintro ⟨_,hfun,hsrc,hbound⟩
    refine ⟨hz,?_,?_,?_⟩
    · intro x hx
      obtain ⟨y,hy,hu⟩ := hfun x ((hD x).mp hx)
      exact ⟨y,(hV x y).mpr hy,fun y' hy' => hu y' ((hV x y').mp hy')⟩
    · intro x y hxy
      exact (hD x).mpr (hsrc x y ((hV x y).mp hxy))
    · intro y hy
      have he : {x | Fin.append (Fin.append z x) y ∈ F.volume} =
          {x | Fin.append (Fin.append t x) y ∈ (nativeFiniteRVSchemaRecode R F).volume} :=
        Set.ext (fun x => hV x y)
      change _ ∧ _
      rw [he]
      exact hbound y hy

theorem finiteRVSchemaLabelsNonzero_recode_iff (R : GammaParameterRecode B p q sp sq)
    (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) (t : Fin q → M)
    (hV : R.RelationAgreement (finiteRVSchemaLabels F) z t) :
    finiteRVSchemaLabelsNonzero F z ↔ finiteRVSchemaLabelsNonzero (nativeFiniteRVSchemaRecode R F) t := by
  constructor
  · exact fun h x y hxy => h x y ((hV x y).mpr hxy)
  · exact fun h x y hxy => h x y ((hV x y).mp hxy)

theorem nativeFiniteRVSchemaValid_recode_iff (R : GammaParameterRecode B p q sp sq)
    (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hD : R.DomainAgreement (finiteRVSchemaDomain F) z t)
    (hV : R.RelationAgreement (finiteRVSchemaLabels F) z t) :
    nativeFiniteRVSchemaValid F z ↔ nativeFiniteRVSchemaValid (nativeFiniteRVSchemaRecode R F) t :=
  and_congr (finiteRVSchema_valid_recode_iff R F z t hz ht hD hV)
    (finiteRVSchemaLabelsNonzero_recode_iff R F z t hV)

end DiamondIntegral.Section5
