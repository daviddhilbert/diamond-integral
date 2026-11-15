import «section 5».RESValueBoundDefinability
import «section 5».OriginalQuotientValidity
import «section 5».RESSetSchemaRecoding
import «section 5».CylindricalFormulaCongruence
import IntegrationSection6.GammaFamilyQuantifiers

/-! A varying Gamma value is represented by its full nonzero-RV preimage,
with a nonempty support of size at most one. No representative is named. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

structure GammaValueSchema (B : Base (M := M)) (p : ℕ) (sp : Fin p → SortTag) where
  domain : GammaDomainFormula B p 1 sp

def GammaValueSchema.resSchema (F : GammaValueSchema B p sp) : RESSetSchema B p 1 sp := ⟨F.domain, 1⟩

def GammaValueSchema.Valid (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaValueSchema B p sp) (z : Fin p → M) : Prop :=
  F.resSchema.Valid hc z ∧
    (quotientDomainValidityFormula (nativeGammaRelationSyntax hc).proper
      (nativeGammaRelationSyntax hc).equal (gammaDomainSyntax hc B F.domain)).Realize
        (predicateParameterValues B z) ∧
    ∃ x : Fin 1 → M, Fin.append z x ∈ F.domain.val

theorem GammaValueSchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaValueSchema B p sp) : DefinableOverBase B sp {z | F.Valid hc z} := by
  have hq := original_quotient_domain_validity_definable hc F.domain
  have he := gamma_family_row_exists_definable sp (fun _ : Fin 1 => .rv) F.domain.property
  have h := (F.resSchema.valid_definable hc).inter (hq.inter he)
  convert h using 1
  ext z
  change (_ ∧ _ ∧ _) ↔ (_ ∧ (_ ∧ _) ∧ _)
  constructor
  · rintro ⟨hr, hq, he⟩
    exact ⟨hr, ⟨hr.1, hq⟩, he⟩
  · rintro ⟨hr, ⟨_, hq⟩, he⟩
    exact ⟨hr, hq, he⟩

theorem GammaValueSchema.full_singleton_row (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaValueSchema B p sp) (z : Fin p → M) (h : F.Valid hc z) :
    ∃ α : Values.Gamma (M := M), ∀ x : Fin 1 → M,
      Fin.append z x ∈ F.domain.val ↔ Proper x ∧ codeValue (x 0) = α := by
  let G := nativeGammaRelationSyntax hc
  have hrep := quotientFormulaDomain_full_preimage G.proper G.equal
    (gammaDomainSyntax hc B F.domain) (predicateParameterValues B z) NonzeroRV codeValue
    G.proper_realize G.equal_realize h.2.1
  have hq := (quotientDomainValidityFormula_realize G.proper G.equal
    (gammaDomainSyntax hc B F.domain) (predicateParameterValues B z)).mp h.2.1
  have hp (x : Fin 1 → M) (hx : Fin.append z x ∈ F.domain.val) : Proper x :=
    fun i => (G.proper_realize _).mp
      (hq.1 x ((gammaDomainSyntax_realize hc B F.domain z x).mpr hx) i)
  obtain ⟨x0, hx0⟩ := h.2.2
  refine ⟨codeValue (x0 0), ?_⟩
  have hb := (F.resSchema.valid_iff_finite_values hc z).mp h.1
  have hs : (rawRVValuePattern '' F.resSchema.rowDomain z).Subsingleton :=
    (Set.ncard_le_one hb.2.1).mp hb.2.2
  intro x
  constructor
  · intro hx
    have hpattern := hs (Set.mem_image_of_mem rawRVValuePattern hx)
      (Set.mem_image_of_mem rawRVValuePattern hx0)
    have hE := (rvValuePatternEqualityFormula_realize (nativeRVValueSyntax (M := M)) 1
      (Fin.elim0 : Fin 0 → M) x x0 (fun i => (hp x hx i).1) (fun i => (hp x0 hx0 i).1)).mpr hpattern
    rw [rvValuePatternEqualityFormula, tupleQuotientEqualityFormula_realize] at hE
    have he := ((nativeRVValueSyntax (M := M)).realize (x 0) (x0 0)).mp (hE 0)
    exact ⟨hp x hx, le_antisymm
      ((original_le_codeValue_iff _ _ (hp x hx 0) (hp x0 hx0 0)).mp he.1)
      ((original_le_codeValue_iff _ _ (hp x0 hx0 0) (hp x hx 0)).mp he.2)⟩
  · rintro ⟨hx, he⟩
    apply (gammaDomainSyntax_realize hc B F.domain z x).mp
    apply (hq.2 x0 x
      (fun i => (G.proper_realize _).mpr (hp x0 hx0 i))
      (fun i => (G.proper_realize _).mpr (hx i)) ?_).mp
      ((gammaDomainSyntax_realize hc B F.domain z x0).mpr hx0)
    intro i
    fin_cases i
    exact (G.equal_realize _ _ (hp x0 hx0 0) (hx 0)).mpr he.symm

def GammaValueSchema.value (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaValueSchema B p sp) (z : Fin p → M) (h : F.Valid hc z) : Values.Gamma (M := M) :=
  Classical.choose (F.full_singleton_row hc z h)

theorem GammaValueSchema.value_row (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaValueSchema B p sp) (z : Fin p → M) (h : F.Valid hc z) (x : Fin 1 → M) :
    Fin.append z x ∈ F.domain.val ↔ Proper x ∧ codeValue (x 0) = F.value hc z h :=
  Classical.choose_spec (F.full_singleton_row hc z h) x

theorem GammaValueSchema.value_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaValueSchema B p sp) (z : Fin p → M) (h : F.Valid hc z) :
    GammaDefinableClosureAtBase ⟨B.real ∪ Set.range z, B.gamma⟩ (F.value hc z h) := by
  change DefinableOverBase _ (fun _ : Fin 1 => .rv)
    {x | x 0 ∈ Values.gammaPullback {F.value hc z h}}
  convert F.resSchema.row_domain_definable z using 1
  ext x
  rw [show x ∈ F.resSchema.rowDomain z ↔ Fin.append z x ∈ F.domain.val from Iff.rfl,
    F.value_row hc z h x]
  constructor
  · intro hx
    have hnz : NonzeroRV (x 0) := by
      obtain ⟨hr, h0, _⟩ := hx
      exact ⟨hr, h0⟩
    refine ⟨(fun i => ?_), (gammaPullback_mem_codeValue_iff _ _ hnz).mp hx⟩
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]
    exact ⟨hnz.1, hnz.2⟩
  · rintro ⟨hx, he⟩
    exact (gammaPullback_mem_codeValue_iff _ _ (hx 0)).mpr he

def GammaValueSchema.recode (R : GammaParameterRecode B p q sp sq)
    (F : GammaValueSchema B p sp) : GammaValueSchema B q sq := ⟨R.domain F.domain⟩

theorem GammaValueSchema.recode_valid_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) (F : GammaValueSchema B p sp)
    (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hrow : R.DomainAgreement F.domain z t) : F.Valid hc z ↔ (F.recode R).Valid hc t := by
  have hr := F.resSchema.recode_valid_iff hc R z t hz ht hrow
  have hraw (x : Fin 1 → M) :
      (gammaDomainSyntax hc B F.domain).Realize (Sum.elim (predicateParameterValues B z) x) ↔
      (gammaDomainSyntax hc B (R.domain F.domain)).Realize (Sum.elim (predicateParameterValues B t) x) :=
    (gammaDomainSyntax_realize hc B F.domain z x).trans
      ((hrow x).trans (gammaDomainSyntax_realize hc B (R.domain F.domain) t x).symm)
  have hq := quotientDomainValidity_congr (nativeGammaRelationSyntax hc).proper
    (nativeGammaRelationSyntax hc).equal _ _ _ _ hraw
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  exact and_congr hr (and_congr hq (exists_congr hrow))

theorem GammaValueSchema.recode_value_eq (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) (F : GammaValueSchema B p sp)
    (z : Fin p → M) (t : Fin q → M)
    (hrow : R.DomainAgreement F.domain z t)
    (hz : F.Valid hc z) (ht : (F.recode R).Valid hc t) :
    F.value hc z hz = (F.recode R).value hc t ht := by
  obtain ⟨x, hx⟩ := hz.2.2
  exact ((F.value_row hc z hz x).mp hx).2.symm.trans
    (((F.recode R).value_row hc t ht x).mp ((hrow x).mp hx)).2

theorem GammaValueSchema.valid_of_full_singleton_row (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaValueSchema B p sp) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (α : Values.Gamma (M := M))
    (hrow : ∀ x : Fin 1 → M, Fin.append z x ∈ F.domain.val ↔
      Proper x ∧ codeValue (x 0) = α) : F.Valid hc z := by
  let G := nativeGammaRelationSyntax hc
  have hpattern (x : Fin 1 → M) (hx : Fin.append z x ∈ F.domain.val) :
      rawRVValuePattern x = fun _ : Fin 1 => α.val := by
    obtain ⟨hp, he⟩ := (hrow x).mp hx
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hnz : NonzeroRV (x 0) := ⟨(hp 0).1, (hp 0).2⟩
    rw [codeValue, dif_pos hnz] at he
    have hval := congrArg Subtype.val he
    simpa only [rawRVValuePattern, dif_pos hnz.1, GammaParameters.value, Values.gammaOf] using hval
  have hsub : rawRVValuePattern '' F.resSchema.rowDomain z ⊆ {fun _ : Fin 1 => α.val} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hpattern x hx
  have hres : F.resSchema.Valid hc z := (F.resSchema.valid_iff_finite_values hc z).mpr
    ⟨hz, (Set.finite_singleton _).subset hsub,
      (Set.ncard_le_ncard hsub (Set.finite_singleton _)).trans (by simp [resSchema])⟩
  have hrep : gammaFormulaRepresents (gammaDomainSyntax hc B F.domain)
      (predicateParameterValues B z) {γ : Fin 1 → Values.Gamma (M := M) | γ 0 = α} := by
    intro x
    exact (gammaDomainSyntax_realize hc B F.domain z x).trans (hrow x)
  obtain ⟨t, ht, he⟩ := EndpointLogic.codeValue_surjective α
  refine ⟨hres, quotientDomainValidity_of_gamma_presentation G.proper G.equal
    G.proper_realize G.equal_realize _ _ _ hrep,
    (fun _ : Fin 1 => t), (hrow _).mpr ⟨fun _ => ht, he⟩⟩

theorem gamma_value_schema_at_parameter (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (α : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase ⟨B.real ∪ Set.range z, B.gamma⟩ α) :
    ∃ F : GammaValueSchema B p sp, ∃ h : F.Valid hc z, F.value hc z h = α := by
  obtain ⟨D, hD⟩ := promote_original_gamma_predicate hc B sp z hz
    {x : Fin 1 → M | x 0 ∈ Values.gammaPullback {α}} hα
  let F : GammaValueSchema B p sp := ⟨D⟩
  have hrow (x : Fin 1 → M) : Fin.append z x ∈ F.domain.val ↔
      Proper x ∧ codeValue (x 0) = α := by
    rw [show Fin.append z x ∈ F.domain.val ↔ x 0 ∈ Values.gammaPullback {α} from
      (gammaDomainSyntax_realize hc B D z x).symm.trans (hD x)]
    constructor
    · intro hx
      have hp : NonzeroRV (x 0) := by
        obtain ⟨hr, h0, _⟩ := hx
        exact ⟨hr, h0⟩
      refine ⟨fun i => ?_, (gammaPullback_mem_codeValue_iff _ _ hp).mp hx⟩
      have hi : i = 0 := Subsingleton.elim _ _
      rw [hi]
      exact ⟨hp.1, hp.2⟩
    · rintro ⟨hp, he⟩
      exact (gammaPullback_mem_codeValue_iff _ _ (hp 0)).mpr he
  have hv := F.valid_of_full_singleton_row hc z hz α hrow
  refine ⟨F, hv, ?_⟩
  obtain ⟨x, hx⟩ := hv.2.2
  exact ((F.value_row hc z hv x).mp hx).2.symm.trans ((hrow x).mp hx).2

end DiamondIntegral.Section5
