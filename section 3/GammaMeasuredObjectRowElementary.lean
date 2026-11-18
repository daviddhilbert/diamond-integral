import «section 3».GammaMeasuredElementarySchemaRows
import «section 3».GammaMeasuredGeometricSchemata

/-! The essential part of the reused elementary formula is precisely
the actual original-ground measured elementary object. Zero structural
rows are removed by the existing native normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.vfSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
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

theorem GammaMeasuredObjectRow.elementary
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ)
    {z : Fin p → M} (hz : ∀ i, sortEval (sp i) (z i))
    {U : GammaGroundMeasuredRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ (k+1)}
    {F : GammaMeasuredRVSchema hc B p U.underlying.arity (k+1) sp}
    (hF : GammaMeasuredObjectRow z U F)
    (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject (Fin.last k)) (L : ℕ) :
    GammaMeasuredObjectRow z
      (gammaMeasuredElementaryObject hκ hs h00 (small_union_range hκ B.real hr z) U (Fin.last k) hAd)
      (F.elementaryFormula.essential.withBound L) := by
  let hrz := small_union_range hκ B.real hr z
  let E := gammaMeasuredElementaryObject hκ hs h00 hrz U (Fin.last k) hAd
  let H := F.elementaryFormula
  have hDomain (w : Fin (U.underlying.arity+1) → CanonicalRV.RVSort M) :
      w ∈ H.essential.object.rowDomain z ↔ w ∈ E.underlying.domain.carrier := by
    constructor
    · intro hw
      obtain ⟨v,hv,hnz⟩ := (essentialFiniteVolumeSchema_rowDomain H.object z w).mp hw
      obtain ⟨u,hu,hPos,hVol⟩ := (gammaMeasured_elementary_schema_row_volume hz hF w v).mp hv
      have hn : (w (Fin.natAdd U.underlying.arity 0)).val ≠ iRVZero := by
        intro hzero
        have hs0 : w (Fin.natAdd U.underlying.arity 0) = 0 :=
          Subtype.ext (hzero.trans RVOperations.zero_val.symm)
        have he := congrArg (fun t => (t (Fin.last k)).val) hVol
        rw [blowupValue_same,hs0,zero_mul,RVOperations.zero_val] at he
        exact hnz (Fin.last k) he.symm
      have hsP := (gammaBasicPositive_nonzero_labels (hc := hc)
        (B := ⟨B.real ∪ Set.range z,B.gamma⟩) (w ∘ Fin.natAdd U.underlying.arity)).mp ⟨hPos,hn⟩
      apply (gammaMeasuredElementary_positive_domain hκ hs h00 hrz U.underlying (Fin.last k) hAd).ge
      rw [mem_gammaGroundRVProductDomain]
      exact ⟨u.val,u.property,w ∘ Fin.natAdd U.underlying.arity,hsP,
        (congrArg (fun t => Fin.append t (w ∘ Fin.natAdd U.underlying.arity)) hu).trans Fin.append_castAdd_natAdd⟩
    · intro hw
      let q : E.underlying.domain := ⟨w,hw⟩
      let u := gammaMeasuredElementaryOldPoint hκ hs h00 hrz U (Fin.last k) hAd q
      have hOld := gammaMeasuredElementaryOldPoint_val hκ hs h00 hrz U (Fin.last k) hAd q
      have hTail := congrArg Prod.snd (gammaMeasuredElementaryChart_val hκ hs h00 hrz U.underlying (Fin.last k) hAd q)
      have hPos : (w ∘ Fin.natAdd U.underlying.arity) ∈
          @DefSet.carrier LRV M N _ Set.univ (@positiveRV M N Set.univ) := by
        have hp := ((gammaMeasuredElementaryChart hκ hs h00 hrz U.underlying (Fin.last k) hAd).map q).property.2
        rw [hTail] at hp
        exact ((gammaBasicPositive_nonzero_labels (hc := hc)
          (B := ⟨B.real ∪ Set.range z,B.gamma⟩) _).mpr hp).1
      apply (essentialFiniteVolumeSchema_rowDomain H.object z w).mpr
      refine ⟨(E.underlying.volume q).val,?_,E.underlying.nonzero q⟩
      exact (gammaMeasured_elementary_schema_row_volume hz hF w _).mpr
        ⟨u,hOld,hPos,(gammaMeasuredElementary_literal_volume hκ hs h00 hrz U (Fin.last k) hAd q).symm⟩
  have hVolume (w : Fin (U.underlying.arity+1) → CanonicalRV.RVSort M) (v : Fin (k+1) → CanonicalRV.RVSort M)
      (hv : H.essential.object.rowVolume z w v) :
      ∃ q : E.underlying.domain, q.val = w ∧ (E.underlying.volume q).val = v := by
    have hParts := (essentialFiniteVolumeSchema_rowVolume H.object z w v).mp hv
    have hD := (essentialFiniteVolumeSchema_rowDomain H.object z w).mpr ⟨v,hParts⟩
    let q : E.underlying.domain := ⟨w,(hDomain w).mp hD⟩
    obtain ⟨u,hu,_,hVol⟩ := (gammaMeasured_elementary_schema_row_volume hz hF w v).mp hParts.1
    have hOld : gammaMeasuredElementaryOldPoint hκ hs h00 hrz U (Fin.last k) hAd q = u :=
      Subtype.ext ((gammaMeasuredElementaryOldPoint_val hκ hs h00 hrz U (Fin.last k) hAd q).trans hu.symm)
    refine ⟨q,rfl,?_⟩
    rw [gammaMeasuredElementary_literal_volume,hOld]
    exact hVol
  have hSub (w) (hw : w ∈ H.essential.object.rowDomain z) : w ∈ H.object.rowDomain z := by
    obtain ⟨v,hv,_⟩ := (essentialFiniteVolumeSchema_rowDomain H.object z w).mp hw
    exact F.object.elementary_row_support (Fin.last k) z hz w v hv
  have hForm (q : E.underlying.domain) :
      (E.form q).val = (U.form (gammaMeasuredElementaryOldPoint hκ hs h00 hrz U (Fin.last k) hAd q)).val :=
    (cast_inj (gammaCarrier hc)).mp (gammaMeasuredElementaryObject_form hκ hs h00 hrz U (Fin.last k) hAd q)
  refine ⟨Set.ext hDomain,?_,?_⟩
  · intro w v
    constructor
    · exact hVolume w v
    · rintro ⟨q,rfl,hv⟩
      obtain ⟨v₀,hv₀,hnz⟩ := (essentialFiniteVolumeSchema_rowDomain H.object z q.val).mp ((hDomain q.val).mpr q.property)
      have hRow := (essentialFiniteVolumeSchema_rowVolume H.object z q.val v₀).mpr ⟨hv₀,hnz⟩
      obtain ⟨q',hq',hv'⟩ := hVolume q.val v₀ hRow
      have he : q' = q := Subtype.ext hq'
      have hvv : v₀ = v := hv'.symm.trans ((congrArg (fun a => (E.underlying.volume a).val) he).trans hv)
      exact Eq.mp (congrArg (fun v => H.essential.object.rowVolume z q.val v) hvv) hRow
  · intro w c
    change H.essential.rowDensity z w c ↔ _
    rw [H.essential_rowDensity,F.elementary_rowDensity z hz]
    constructor
    · rintro ⟨⟨hcValue,_⟩,hD⟩
      let q : E.underlying.domain := ⟨w,(hDomain w).mp hD⟩
      obtain ⟨u,hu,hω⟩ := (hF.density _ c).mp hcValue
      have he : gammaMeasuredElementaryOldPoint hκ hs h00 hrz U (Fin.last k) hAd q = u :=
        Subtype.ext ((gammaMeasuredElementaryOldPoint_val hκ hs h00 hrz U (Fin.last k) hAd q).trans hu.symm)
      exact ⟨q,rfl,(hForm q).trans ((congrArg (fun a => (U.form a).val) he).trans hω)⟩
    · rintro ⟨q,rfl,hω⟩
      have hD := (hDomain q.val).mpr q.property
      refine ⟨⟨(hF.density _ c).mpr ⟨gammaMeasuredElementaryOldPoint hκ hs h00 hrz U (Fin.last k) hAd q,
        gammaMeasuredElementaryOldPoint_val hκ hs h00 hrz U (Fin.last k) hAd q,(hForm q).symm.trans hω⟩,
        hSub q.val hD⟩,hD⟩

end DiamondIntegral.Section3
