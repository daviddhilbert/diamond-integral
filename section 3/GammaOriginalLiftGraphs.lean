import «section 3».GammaGroundDifferentiation
import «section 5».NativeGammaPointBridge
import Section7.GammaLiftEquivalence

/-! Original-Gamma lift graphs retain their actual pointwise graph witness.
Differentiation uses only the original VF coefficient field. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 SpecialTransformations.Section7 SpecialTransformations.Section9

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : GammaParameters.Base (M := M)} {n r s : ℕ}

theorem gammaOriginalLiftIso_with_graph {U V : GammaRVObject B n}
    (F : rvObjectDomain U.object ≃ rvObjectDomain V.object)
    (A : Set (Fin (n+n) → M))
    (hA : gammaRawVolumeCorrespondence U V F ⊆ rawLiftDomain A)
    (hGraph : GammaGraphDefinable B (gammaLiftGraph F A)) :
    ∃ e : GammaIso B U.lift V.lift,
      ∀ p : U.lift, gammaLiftGraph F A p.val (e.equiv p).val := by
  let R := gammaLiftGraph F A
  have hRight (p : U.lift) := gammaLiftGraph_existsUnique_right F A hA p
  have hLeft (q : V.lift) := gammaLiftGraph_existsUnique_left F A hA q
  let f (p : U.lift) : V.lift :=
    ⟨(hRight p).exists.choose,(hRight p).exists.choose_spec.2.1⟩
  have hf (p : U.lift) : R p.val (f p).val := (hRight p).exists.choose_spec
  have hBij : Function.Bijective f := by
    constructor
    · intro p q h
      apply Subtype.ext
      exact (hLeft (f q)).unique (by simpa only [h] using hf p) (hf q)
    · intro q
      obtain ⟨p,hp,_⟩ := hLeft q
      let a : U.lift := ⟨p,hp.1⟩
      exact ⟨a,Subtype.ext ((hRight a).unique (hf a) hp)⟩
  have hg : GammaGraphDefinable B
      (fun p q => ∃ x : U.lift, x.val = p ∧ (f x).val = q) := by
    apply GammaGraphDefinable.congr hGraph
    intro p q
    constructor
    · intro h
      let a : U.lift := ⟨p,h.1⟩
      exact ⟨a,rfl,(hRight a).unique (hf a) h⟩
    · rintro ⟨a,rfl,h⟩
      exact h ▸ hf a
  exact ⟨⟨Equiv.ofBijective f hBij,hg⟩,hf⟩

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaOriginalIso_differentiable
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hS : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : Set (Point (M := M) n r)} {D : Set (Point (M := M) n s)}
    (hA : GammaSetDefinable B A) (hD : GammaSetDefinable B D)
    (e : GammaIso B A D) (a : A)
    (ha : AlgebraicIndependent (vfParameterField B.real) a.val.1) :
    ∃ L : (Fin n → Section2.VF M) →ₗ[Section2.VF M] (Fin n → Section2.VF M),
      HasMixedVFDerivativeAt e.equiv a L := by
  let f := Section5.nativeGammaPointBijection (hc := hc) hA hD e
  have he : (f.map : A → D) = e.equiv := by
    funext p
    apply Subtype.ext
    exact Section5.nativeGammaPointBijection_apply hA hD e p
  obtain ⟨L,hL⟩ := gammaGround_differentiable_of_independent hκ hs hS hv f.map a ha
  rw [he] at hL
  exact ⟨L,hL⟩

end DiamondIntegral.Section3
