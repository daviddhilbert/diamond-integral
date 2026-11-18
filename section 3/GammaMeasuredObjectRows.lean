import «section 3».GammaMeasuredActualIsomorphismWitnesses

/-! Literal measured object rows expose the existing native dictionary
through domain points, volume tuples, and complete Gamma code graphs.
This avoids repeating internal-presentation conversions in finite proofs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

structure GammaMeasuredObjectRow
    (z : Fin p → M) (U : GammaGroundMeasuredRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k)
    (F : GammaMeasuredRVSchema hc B p U.underlying.arity k sp) : Prop where
  domain : F.object.rowDomain z = U.underlying.domain.carrier
  volume : ∀ x y, F.object.rowVolume z x y ↔
    ∃ u : U.underlying.domain, u.val = x ∧ (U.underlying.volume u).val = y
  density : ∀ x c, F.rowDensity z x c ↔
    ∃ u : U.underlying.domain, u.val = x ∧ (U.form u).val = (volumeGammaSpace hc).decode c

theorem GammaMeasuredObjectRow.of_native
    {z : Fin p → M} {U : GammaGroundMeasuredRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k}
    {F : GammaMeasuredRVSchema hc B p U.underlying.arity k sp}
    (hRF : gammaSchemaRepresents (Section5.groundRVAt U.underlying).toGamma F.object z)
    (hDF : ∀ x y, Fin.append (Fin.append z x) y ∈ F.density ↔ Fin.append x y ∈ gammaRVFormCodeRows U.form) :
    GammaMeasuredObjectRow z U F := by
  refine ⟨?_,?_,?_⟩
  · ext x
    exact (gammaSchemaRepresents_domain (Section5.groundRVAt U.underlying).toGamma F.object z hRF x).trans (Set.ext_iff.mp (Section5.groundRVAt_domain U.underlying) x)
  · intro x y
    rw [gammaSchemaRepresents_volume (Section5.groundRVAt U.underlying).toGamma F.object z hRF]
    constructor
    · rintro ⟨a,ha,hv⟩
      refine ⟨(Section5.groundRVAtDomainEquiv U.underlying).symm a,ha,?_⟩
      exact (Section5.groundRVAt_volume_eq U.underlying a).symm.trans hv
    · rintro ⟨u,hu,hv⟩
      refine ⟨Section5.groundRVAtDomainEquiv U.underlying u,hu,?_⟩
      exact (Section5.groundRVAt_volume_eq U.underlying _).trans
        ((congrArg (fun v => (U.underlying.volume v).val) ((Section5.groundRVAtDomainEquiv U.underlying).symm_apply_apply u)).trans hv)
  · intro x c
    exact (hDF (rvValues x) c.val).trans (gammaRVFormCodeRows_mem U.form x c)

theorem GammaMeasuredObjectRow.native
    {z : Fin p → M} {U : GammaGroundMeasuredRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k}
    {F : GammaMeasuredRVSchema hc B p U.underlying.arity k sp} (h : GammaMeasuredObjectRow z U F) :
    gammaSchemaRepresents (Section5.groundRVAt U.underlying).toGamma F.object z := by
  apply gammaSchemaRepresents_of_typed
  · intro x
    exact (Set.ext_iff.mp h.domain x).trans (Set.ext_iff.mp (Section5.groundRVAt_domain U.underlying) x).symm
  · intro x y
    rw [h.volume x y]
    constructor
    · rintro ⟨u,hu,hv⟩
      refine ⟨Section5.groundRVAtDomainEquiv U.underlying u,hu,?_⟩
      exact (Section5.groundRVAt_volume_eq U.underlying _).trans
        ((congrArg (fun v => (U.underlying.volume v).val) ((Section5.groundRVAtDomainEquiv U.underlying).symm_apply_apply u)).trans hv)
    · rintro ⟨a,ha,hv⟩
      exact ⟨(Section5.groundRVAtDomainEquiv U.underlying).symm a,ha,
        (Section5.groundRVAt_volume_eq U.underlying a).symm.trans hv⟩

theorem GammaMeasuredObjectRow.raw_density
    {z : Fin p → M} {U : GammaGroundMeasuredRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k}
    {F : GammaMeasuredRVSchema hc B p U.underlying.arity k sp} (h : GammaMeasuredObjectRow z U F)
    (x : Fin U.underlying.arity → M) (y : Fin 1 → M) :
    Fin.append (Fin.append z x) y ∈ F.density ↔ Fin.append x y ∈ gammaRVFormCodeRows U.form := by
  constructor
  · intro hd
    have hx (j) : iRV (x j) := by
      simpa only [Fin.append_left,Fin.append_right,sortEval,iRV] using
        F.density_definable.proper _ hd (Fin.castAdd 1 (Fin.natAdd p j))
    have hcValue : y ∈ (volumeGammaSpace hc).domain := by
      simpa only [Function.comp_def,Fin.append_right] using F.density_code _ hd
    let r : Fin U.underlying.arity → CanonicalRV.RVSort M := fun j => ⟨x j,hx j⟩
    let c : (volumeGammaSpace hc).domain := ⟨y,hcValue⟩
    exact (gammaRVFormCodeRows_mem U.form r c).mpr ((h.density r c).mp hd)
  · intro hd
    have hp := gammaRVFormCodeRows_proper U.form _ hd
    have hx (j) : iRV (x j) := by simpa only [Fin.append_left,sortEval,iRV] using hp (Fin.castAdd 1 j)
    have hcValue : y ∈ (volumeGammaSpace hc).domain := by
      simpa only [Function.comp_def,Fin.append_right] using gammaRVFormCodeRows_code U.form _ hd
    let r : Fin U.underlying.arity → CanonicalRV.RVSort M := fun j => ⟨x j,hx j⟩
    let c : (volumeGammaSpace hc).domain := ⟨y,hcValue⟩
    exact (h.density r c).mpr ((gammaRVFormCodeRows_mem U.form r c).mp hd)

theorem gammaMeasured_object_row_promotion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (U : GammaGroundMeasuredRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k) :
    ∃ F : GammaMeasuredRVSchema hc B p U.underlying.arity k sp, F.valid z ∧ GammaMeasuredObjectRow z U F := by
  obtain ⟨F,hF,hRF,_,hDF⟩ := gammaGroundMeasured_object_schema_promotion hκ hs hr hg sp z hz U
  exact ⟨F,hF,GammaMeasuredObjectRow.of_native hRF hDF⟩

end DiamondIntegral.Section3
