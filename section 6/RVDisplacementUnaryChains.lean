import «section 6».VFInterpolationTransitions
import «section 6».BoundedOrderedUnaryChains

/-! A retained-label translation in any positive VF dimension factors
into actual relatively unary proper homeomorphisms. The interpolation
construction preserves every intermediate double bound when both ends
are doubly bounded. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

def vfCoordinatePrefix (k : ℕ) (i : Fin n) : Prop := i.val<k

theorem vfInterpolation_full_value (f : Map A B) (p : A) :
    (vfInterpolation f (vfCoordinatePrefix n) p).val=(f p).val := by
  apply Prod.ext
  · funext i
    rw [vfInterpolation_coordinate]
    exact if_pos i.isLt
  · exact vfInterpolation_tags f _ p

theorem vfInterpolation_full_image (f : Map A B) (hf : Function.Surjective f) :
    (vfInterpolationMap f (vfCoordinatePrefix n)).image=B := by
  apply defSet_eq_of_carrier_eq
  ext q
  constructor
  · rintro ⟨p,hp⟩
    have he : (f p).val=q := (vfInterpolation_full_value f p).symm.trans hp
    exact he ▸ (f p).property
  · intro hq
    obtain ⟨p,hp⟩ := hf ⟨q,hq⟩
    exact ⟨p,(vfInterpolation_full_value f p).trans (congrArg Subtype.val hp)⟩

theorem vfInterpolation_full_map (f : Map A B) (hf : Function.Surjective f) :
    changeMapTarget (vfInterpolation f (vfCoordinatePrefix n)) (vfInterpolation_full_image f hf)=f := by
  apply Map.ext
  intro p
  apply Subtype.ext
  rw [changeMapTarget_value]
  exact vfInterpolation_full_value f p

theorem vfInterpolation_unary_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hn : 0<n) (f : Map A B) (hF : ProperCovariantHomeomorphism f) (π : Fin r → Fin s)
    (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i) (hD : ∀ i,RVCoordinateDisplacement f i) :
    ∀ k,k≤n → ∃ F : RetainedUnaryHomeChain (G := G) S (vfInterpolation f (vfCoordinatePrefix k)) π,
      VFDoublyBounded A.carrier → VFDoublyBounded B.carrier → F.DoublyBounded := by
  intro k
  induction k with
  | zero =>
    intro hk
    have hHome := vfInterpolation_homeomorphism h00 hc linear hκ hs hv hsmall hΓ f hF (vfCoordinatePrefix 0) π hRetain hD
    let F : RetainedUnaryHomeChain (G := G) S (vfInterpolation f (vfCoordinatePrefix 0)) π :=
      .unary ⟨0,hn⟩ hHome
        (by
          intro p i hi
          rw [vfInterpolation_coordinate]
          exact if_neg (Nat.not_lt_zero i.val))
        (fun p _ => unit_derivative_of_rv_displacements hv _ hHome.covariant
          (vfInterpolation_rv_displacements f _ hD) p)
        (vfInterpolation_retained f _ π hRetain)
    exact ⟨F,fun hAD hBD => ⟨hAD,vfInterpolation_doublyBounded f _ hAD hBD⟩⟩
  | succ k ih =>
    intro hk
    have hkn : k<n := Nat.lt_of_succ_le hk
    obtain ⟨F,hFBound⟩ := ih (Nat.le_of_succ_le hk)
    let P : Fin n → Prop := vfCoordinatePrefix k
    let Q : Fin n → Prop := vfCoordinatePrefix (k+1)
    let hP := vfInterpolation_bijective f P π hRetain hD
    let Hmap := vfInterpolationTransition f P Q hP
    have hHome := vfInterpolationTransition_homeomorphism h00 hc linear hκ hs hv hsmall hΓ f hF P Q π hRetain hD
    let H : RetainedUnaryHomeChain (G := G) S Hmap id :=
      .unary ⟨k,hkn⟩ hHome
        (vfInterpolationTransition_relative f P Q hP ⟨k,hkn⟩ (by
          intro i hi
          have hNe : i.val ≠ k := fun he => hi (Fin.ext he)
          change (i.val<k) ↔ (i.val<k+1)
          omega))
        (fun p _ => unit_derivative_of_rv_displacements hv _ hHome.covariant
          (vfInterpolationTransition_rv_displacements f P Q hP hD) p)
        (vfInterpolationTransition_retained f P Q hP)
    have hMap : Hmap.comp (vfInterpolation f P)=vfInterpolation f Q := by
      apply Map.ext
      exact vfInterpolationTransition_at f P Q hP
    let K := RetainedUnaryHomeChain.comp F H
    refine ⟨K.changeMap hMap,fun hAD hBD => ?_⟩
    apply (K.doublyBounded_changeMap hMap).mpr
    exact ⟨hFBound hAD hBD,⟨vfInterpolation_doublyBounded f P hAD hBD,vfInterpolation_doublyBounded f Q hAD hBD⟩⟩

theorem unary_chain_of_rv_displacements
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hn : 0<n) (f : Map A B) (hF : ProperCovariantHomeomorphism f) (π : Fin r → Fin s)
    (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i) (hD : ∀ i,RVCoordinateDisplacement f i) :
    ∃ F : RetainedUnaryHomeChain (G := G) S f π,
      VFDoublyBounded A.carrier → VFDoublyBounded B.carrier → F.DoublyBounded := by
  obtain ⟨F,hFBound⟩ := vfInterpolation_unary_chain h00 hc linear hκ hs hv hsmall hΓ hn f hF π hRetain hD n le_rfl
  let H := F.changeTarget (vfInterpolation_full_image f hF.bijective.surjective)
  refine ⟨H.changeMap (vfInterpolation_full_map f hF.bijective.surjective),fun hAD hBD => ?_⟩
  apply (H.doublyBounded_changeMap _).mpr
  apply (F.doublyBounded_changeTarget _).mpr
  exact hFBound hAD hBD

end DiamondIntegral.Section6
