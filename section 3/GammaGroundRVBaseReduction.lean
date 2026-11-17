import «section 3».GammaGroundMeasuredRVCategories
import «section 3».GammaGroundSyntaxBridge
import «section 3».GammaGroundRawDescent
import «section 3».GammaGroundSortedSyntax
import IntegrationSection6.GammaDefinableBaseReduction

/-! Definably adjoined names can be eliminated from actual RV objects
and complete Gamma form graphs. Their functions and carriers stay literal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)}
variable {Q R : Space LRV M}

theorem gammaGround_reduce_RV_codes (H : GammaDefinableBaseReduction C B)
    (hRV : ∀ w ∈ Q.domain, ∀ i, iRV (w i)) {A : Set Q.Carrier}
    (hA : GammaGroundDefinable hc C Q A) : GammaGroundDefinable hc B Q A := by
  letI : Fintype Q.Index := Fintype.ofFinite Q.Index
  let e := Fintype.equivFin Q.Index
  let D : Set (Fin (Fintype.card Q.Index) → M) := {w | w ∘ e ∈ Q.preimage A}
  have hRaw : GammaGroundRawDefinable hc C D := hA.on_real_codes.preimage_comp e
  have hProper : ∀ w ∈ D, ∀ j, sortEval SortTag.rv (w j) := by
    intro w hw j
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,sortEval,iRV] using hRV (w ∘ e) hw.1 (e.symm j)
  have hD := H.definable ((gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := C) hProper).mp hRaw)
  have hDown := (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) hProper).mpr hD
  apply GammaGroundDefinable.of_real_codes
  apply (hDown.preimage_comp e.symm).congr
  intro w
  have he : (w ∘ e.symm) ∘ e = w := by
    funext i
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
  change ((w ∘ e.symm) ∘ e ∈ Q.preimage A) ↔ _
  rw [he]

theorem gammaRawRVSpace_codes (a : ℕ) :
    ∀ w ∈ (rawRVSpace (M := M) a).domain, ∀ i, iRV (w i) := by
  rintro w ⟨x,rfl⟩ i
  exact (x i).property

theorem gammaVolumeSpace_codes : ∀ w ∈ (volumeGammaSpace hc).domain, ∀ i, iRV (w i) := by
  intro w hw i
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hw.1

def gammaGroundRVCodeReduceSet (H : GammaDefinableBaseReduction C B)
    (hRV : ∀ w ∈ Q.domain, ∀ i, iRV (w i)) (A : GammaGroundDefSet hc C Q) :
    GammaGroundDefSet hc B Q := ⟨A.carrier,gammaGround_reduce_RV_codes H hRV A.definable⟩

def gammaGroundRVCodeReduceMap (H : GammaDefinableBaseReduction C B)
    (hQ : ∀ w ∈ Q.domain, ∀ i, iRV (w i)) (hR : ∀ w ∈ R.domain, ∀ i, iRV (w i))
    {A : GammaGroundDefSet hc C Q} {D : GammaGroundDefSet hc C R} (f : GammaGroundMap A D) :
    GammaGroundMap (gammaGroundRVCodeReduceSet H hQ A) (gammaGroundRVCodeReduceSet H hR D) where
  toFun := f.toFun
  graph_definable := gammaGround_reduce_RV_codes H (fun w hw i => by
    cases i with
    | inl i => exact hQ (w ∘ Sum.inl) hw.1 i
    | inr i => exact hR (w ∘ Sum.inr) hw.2 i) f.graph_definable

def gammaGroundRVReduceObject (H : GammaDefinableBaseReduction C B) {k : ℕ}
    (U : GammaGroundRVObject hc C k) : GammaGroundRVObject hc B k where
  arity := U.arity
  domain := gammaGroundRVCodeReduceSet H (gammaRawRVSpace_codes _) U.domain
  volume := gammaGroundRVCodeReduceMap H (gammaRawRVSpace_codes _) (gammaRawRVSpace_codes _) U.volume
  finite := U.finite
  nonzero := U.nonzero

def gammaGroundRVReduceForm (H : GammaDefinableBaseReduction C B) {a : ℕ}
    {A : GammaGroundDefSet hc C (rawRVSpace (M := M) a)} (ω : GammaGroundVolumeForm hc C A) :
    GammaGroundVolumeForm hc B (gammaGroundRVCodeReduceSet H (gammaRawRVSpace_codes _) A) :=
  gammaGroundRVCodeReduceMap H (gammaRawRVSpace_codes _) gammaVolumeSpace_codes ω

def gammaGroundMeasuredRVReduceObject (H : GammaDefinableBaseReduction C B) {k : ℕ}
    (U : GammaGroundMeasuredRVObject hc C k) : GammaGroundMeasuredRVObject hc B k :=
  ⟨gammaGroundRVReduceObject H U.underlying,gammaGroundRVReduceForm H U.form⟩

def gammaGroundMeasuredRVReduceHom (H : GammaDefinableBaseReduction C B) {k : ℕ}
    {U V : GammaGroundMeasuredRVObject hc C k} (f : GammaGroundMeasuredRVHom U V) :
    GammaGroundMeasuredRVHom (gammaGroundMeasuredRVReduceObject H U) (gammaGroundMeasuredRVReduceObject H V) where
  bijection := ⟨gammaGroundRVCodeReduceMap H (gammaRawRVSpace_codes _) (gammaRawRVSpace_codes _) f.bijection.map,
    f.bijection.bijective⟩
  preserves := f.preserves

end DiamondIntegral.Section3
