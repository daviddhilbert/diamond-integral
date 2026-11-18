import «section 3».GammaMeasuredObjectRows
import «section 3».GammaMeasuredSchemaOperationValidity

/-! The reused coproduct formula describes the literal measured tagged
union, including its complete Gamma density graph. Native tag transport
is supplied by the existing Section 5 normalization lemmas. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaMeasuredObjectRow.coprod
    {z : Fin p → M} (hz : ∀ i, sortEval (sp i) (z i))
    {U V : GammaGroundMeasuredRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ (k+1)}
    {F : GammaMeasuredRVSchema hc B p U.underlying.arity (k+1) sp}
    {G : GammaMeasuredRVSchema hc B p V.underlying.arity (k+1) sp}
    (hF : GammaMeasuredObjectRow z U F) (hG : GammaMeasuredObjectRow z V G) (L : ℕ) :
    GammaMeasuredObjectRow z (U.coprod V) ((F.coprodFormula G).withBound L) := by
  have hCover (w : (U.coprod V).underlying.domain) :
      (∃ u, gammaGroundRVCoprodLeft U.underlying V.underlying u = w) ∨
      ∃ v, gammaGroundRVCoprodRight U.underlying V.underlying v = w := by
    rcases w.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · exact Or.inl ⟨u,Subtype.ext hu⟩
    · exact Or.inr ⟨v,Subtype.ext hv⟩
  have hLeft (u : U.underlying.domain) :
      ((U.coprod V).form (gammaGroundRVCoprodLeft U.underlying V.underlying u)).val = (U.form u).val :=
    (cast_inj (gammaCarrier hc)).mp (gammaGroundMeasuredRVCoprod_form_left U V u)
  have hRight (v : V.underlying.domain) :
      ((U.coprod V).form (gammaGroundRVCoprodRight U.underlying V.underlying v)).val = (V.form v).val :=
    (cast_inj (gammaCarrier hc)).mp (gammaGroundMeasuredRVCoprod_form_right U V v)
  refine ⟨?_,?_,?_⟩
  · ext w
    change w ∈ (F.object.coprodFormula G.object).rowDomain z ↔ _
    rw [F.object.coprod_row_domain_formula G.object z hz w]
    constructor
    · rintro (⟨x,hx,ht⟩ | ⟨y,hy,ht⟩)
      · exact Or.inl ⟨⟨x,hF.domain ▸ hx⟩,(@Section5.rvLeftTag_normalized M sM hM U.underlying.arity V.underlying.arity x).symm.trans ht⟩
      · exact Or.inr ⟨⟨y,hG.domain ▸ hy⟩,(@Section5.rvRightTag_normalized M sM hM U.underlying.arity V.underlying.arity y).symm.trans ht⟩
    · rintro (⟨u,hu⟩ | ⟨v,hv⟩)
      · exact Or.inl ⟨u.val,hF.domain.symm ▸ u.property,(@Section5.rvLeftTag_normalized M sM hM _ _ u.val).trans hu⟩
      · exact Or.inr ⟨v.val,hG.domain.symm ▸ v.property,(@Section5.rvRightTag_normalized M sM hM _ _ v.val).trans hv⟩
  · intro w y
    change (F.object.coprodFormula G.object).rowVolume z w y ↔ _
    rw [F.object.coprod_row_volume_formula G.object z hz w y]
    constructor
    · rintro (⟨x,hx,ht⟩ | ⟨x,hx,ht⟩)
      · obtain ⟨u,hu,hv⟩ := (hF.volume x y).mp hx
        subst x
        refine ⟨gammaGroundRVCoprodLeft U.underlying V.underlying u,
          (@Section5.rvLeftTag_normalized M sM hM _ _ u.val).symm.trans ht,?_⟩
        exact (congrArg Subtype.val (gammaGroundRVCoprod_volume_left U.underlying V.underlying u)).trans hv
      · obtain ⟨v,hv,hy⟩ := (hG.volume x y).mp hx
        subst x
        refine ⟨gammaGroundRVCoprodRight U.underlying V.underlying v,
          (@Section5.rvRightTag_normalized M sM hM _ _ v.val).symm.trans ht,?_⟩
        exact (congrArg Subtype.val (gammaGroundRVCoprod_volume_right U.underlying V.underlying v)).trans hy
    · rintro ⟨q,hq,hy⟩
      rcases hCover q with ⟨u,rfl⟩ | ⟨v,rfl⟩
      · refine Or.inl ⟨u.val,(hF.volume u.val y).mpr ⟨u,rfl,?_⟩,
          (@Section5.rvLeftTag_normalized M sM hM _ _ u.val).trans hq⟩
        exact (congrArg Subtype.val (gammaGroundRVCoprod_volume_left U.underlying V.underlying u)).symm.trans hy
      · refine Or.inr ⟨v.val,(hG.volume v.val y).mpr ⟨v,rfl,?_⟩,
          (@Section5.rvRightTag_normalized M sM hM _ _ v.val).trans hq⟩
        exact (congrArg Subtype.val (gammaGroundRVCoprod_volume_right U.underlying V.underlying v)).symm.trans hy
  · intro w c
    have hRows := F.toRVTemplate.coprod_rowDensity G.toRVTemplate z hz w (gammaVolumeCodeRV c)
    change ((F.coprodFormula G).withBound L).rowDensity z w c ↔ _
    change (F.toRVTemplate.coprodFormula G.toRVTemplate).rowDensity z w (gammaVolumeCodeRV c) ↔ _
    rw [hRows]
    constructor
    · rintro (⟨x,hx,ht⟩ | ⟨x,hx,ht⟩)
      · obtain ⟨u,hu,hv⟩ := (hF.density x c).mp hx
        subst x
        exact ⟨gammaGroundRVCoprodLeft U.underlying V.underlying u,
          (@Section5.rvLeftTag_normalized M sM hM _ _ u.val).symm.trans ht,(hLeft u).trans hv⟩
      · obtain ⟨v,hv,hy⟩ := (hG.density x c).mp hx
        subst x
        exact ⟨gammaGroundRVCoprodRight U.underlying V.underlying v,
          (@Section5.rvRightTag_normalized M sM hM _ _ v.val).symm.trans ht,(hRight v).trans hy⟩
    · rintro ⟨q,hq,hy⟩
      rcases hCover q with ⟨u,rfl⟩ | ⟨v,rfl⟩
      · exact Or.inl ⟨u.val,(hF.density u.val c).mpr ⟨u,rfl,(hLeft u).symm.trans hy⟩,
          (@Section5.rvLeftTag_normalized M sM hM _ _ u.val).trans hq⟩
      · exact Or.inr ⟨v.val,(hG.density v.val c).mpr ⟨v,rfl,(hRight v).symm.trans hy⟩,
          (@Section5.rvRightTag_normalized M sM hM _ _ v.val).trans hq⟩

end DiamondIntegral.Section3
