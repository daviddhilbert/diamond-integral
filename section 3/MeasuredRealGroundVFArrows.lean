import «section 3».MeasuredRealGroundObjects
import «section 3».GammaGroundMeasuredVFScissors

/-! The ordinary and redundant-Gamma VF presentations have the same
actual measured arrows. The positive-degree dimension convention is
translated by the checked intrinsic/companion comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3.MeasuredRealGround
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (B : Section2.VFGeneratedFieldBase C.base)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

theorem vfIsoFromReal {k : ℕ} (U V : MeasuredVFData C hc k) (h : Nonempty (U.toObject ≅ V.toObject)) :
    Nonempty (GammaGroundMeasuredVFHom C.uncountable.le C.saturated C.small hv
      (vfFromReal C hc B U) (vfFromReal C hc B V)) := by
  obtain ⟨e⟩ := h
  cases k with
  | zero =>
    let f : ZeroMeasuredVFHom U.toObject V.toObject := e.hom
    exact ⟨⟨⟨GammaGroundMap.ofReal f.bijection.map,f.bijection.bijective⟩,f.preserves⟩⟩
  | succ n =>
    obtain ⟨r,_⟩ := e.hom.property
    let g : GammaGroundEssentialVFMap (vfFromReal C hc B U).domain (vfFromReal C hc B V).domain := {
      source := GammaGroundDefSet.ofReal r.val.source
      target := GammaGroundDefSet.ofReal r.val.target
      source_subset := r.val.source_subset
      target_subset := r.val.target_subset
      source_small := (vf_small_iff_companion hc C.saturated C.small hv (Nat.succ_pos n)
        (U.domain.sdiff r.val.source)).mpr r.val.source_small
      target_small := (vf_small_iff_companion hc C.saturated C.small hv (Nat.succ_pos n)
        (V.domain.sdiff r.val.target)).mpr r.val.target_small
      map := GammaGroundMap.ofReal r.val.map
      bijective := r.val.bijective }
    have hg : g.Preserves Values.vfValueHom (gammaGroundMeasuredVFWeight (vfFromReal C hc B U))
        (gammaGroundMeasuredVFWeight (vfFromReal C hc B V)) := r.property
    exact ⟨gammaGroundMeasuredOfRepresentative C.uncountable.le C.saturated C.small hv (Nat.succ_pos n) ⟨g,hg⟩⟩

theorem vfIsoToReal {k : ℕ}
    (U V : GammaGroundMeasuredVFData hc (measuredRealGroundContext C B).base k)
    (h : Nonempty (GammaGroundMeasuredVFHom C.uncountable.le C.saturated C.small hv U V)) :
    Nonempty ((vfToReal C hc B U).toObject ≅ (vfToReal C hc B V).toObject) := by
  obtain ⟨f⟩ := h
  cases k with
  | zero =>
    let e : ZeroMeasuredVFHom (vfToReal C hc B U).toObject (vfToReal C hc B V).toObject :=
      ⟨⟨f.bijection.map.toRealNames (measuredRealGroundContext_gamma_names C B),f.bijection.bijective⟩,f.preserves⟩
    exact ⟨asIso e⟩
  | succ n =>
    obtain ⟨r,_⟩ := f.property
    let hNames := measuredRealGroundContext_gamma_names C B
    let g : EssentialVFMap (vfToReal C hc B U).domain (vfToReal C hc B V).domain := {
      source := r.val.source.toRealNames hNames
      target := r.val.target.toRealNames hNames
      source_subset := r.val.source_subset
      target_subset := r.val.target_subset
      source_small := (vf_small_iff_companion hc C.saturated C.small hv (Nat.succ_pos n)
        ((vfToReal C hc B U).domain.sdiff (r.val.source.toRealNames hNames))).mp r.val.source_small
      target_small := (vf_small_iff_companion hc C.saturated C.small hv (Nat.succ_pos n)
        ((vfToReal C hc B V).domain.sdiff (r.val.target.toRealNames hNames))).mp r.val.target_small
      map := r.val.map.toRealNames hNames
      bijective := r.val.bijective }
    have hg : g.Preserves Values.vfValueHom (vfToReal C hc B U).toObject.weight
        (vfToReal C hc B V).toObject.weight := r.property
    exact ⟨asIso (PositiveMeasuredVF.ofRepresentative ⟨g,hg⟩)⟩

end DiamondIntegral.Section3.MeasuredRealGround
