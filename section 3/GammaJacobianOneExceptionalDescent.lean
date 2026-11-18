import «section 3».GammaGroundJacobianValue
import «section 3».GammaGroundEqualizers
import «section 3».GammaGroundGenericGeometry
import «section 3».GammaGroundDifferentiation

/-! An intrinsic small exceptional set for Jacobian one gives the same
identity at every original-ground generic point. Its presentation may
use further real parameters; the actual Jacobian locus remains over the
original Gamma ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {n r s : ℕ}
variable {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
variable {D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n s)}

def gammaGroundVFOneMap : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawVFSpace (M := M) 1)) :=
  GammaGroundMap.ofGlobal A _ (by
    exact Map.ofCodes (DefSet.univ (rawMixedSpace n r) B.real) (fun _ _ => (1 : VFType (M := M)))
      (fun _ _ => iVFOne)
      (fun _ => (SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
        (L := LRV) Fn.vfOne Fin.elim0 (fun i => i.elim0))).mono (Set.empty_subset _))
      (fun _ => ⟨fun _ => 1,rfl⟩)
      (fun _ => vfValues_injective (vfValues_decode _))) (fun _ => Set.mem_univ _)

theorem gammaIntrinsicVFDimension_mono
    {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
    {X Y : Set (rawMixedSpace (M := M) n r).Carrier} (hXY : X ⊆ Y) :
    Section2.vfDimension X ≤ Section2.vfDimension Y := by
  apply Finset.sup_le
  intro i hi
  by_cases h : Section2.HasVFInteriorDim X i.val
  · rw [ite_eq_left h]
    apply Section2.HasVFInteriorDim.le_dimension
    obtain ⟨e,t,ht⟩ := h
    refine ⟨e,t,?_⟩
    apply ht.mono
    exact interior_mono (Set.image_mono (fun _ hx => hXY hx))
  · simp only [ite_eq_right h,bot_le]

theorem gammaGround_jacobian_one_of_small_exception
    [CharZero (Section2.VF M)]
    {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hn : 0 < n) (f : GammaGroundMap A D)
    (Z : Set (rawMixedSpace (M := M) n r).Carrier)
    (hZ : Section2.vfDimension Z < (n : WithBot ℕ))
    (hJ : ∀ p : A, p.val ∉ Z → HasMixedVFJacobianAt f p 1)
    (p : A) (hp : AlgebraicIndependent (vfParameterField B.real) p.val.1) :
    HasMixedVFJacobianAt f p 1 := by
  let E := (gammaGroundJacobianValueMap hn f).equalizer gammaGroundVFOneMap
  let Bad := (A.sdiff E).inter (gammaGroundDifferentiabilityLocus hn f)
  have hbad : Bad.carrier ⊆ Z := by
    intro x hx
    by_contra hxZ
    obtain ⟨q,hqx,L,hL⟩ := (mem_gammaGroundDifferentiabilityLocus hn f x).mp hx.2
    have hval := gammaGroundJacobianValue_of_derivative f q L hL
    obtain ⟨F,hF,hDF⟩ := hL
    have hdet : (LinearMap.toMatrix' L).det = 1 :=
      HasMixedVFJacobianAt.unique ⟨F,hF,hDF.hasJacobianAt⟩ (hJ q (hqx.symm ▸ hxZ))
    apply hx.1.2
    refine ⟨q,hqx,?_⟩
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact hval.trans hdet
  have hsmall : Section2.vfDimension Bad.carrier < (n : WithBot ℕ) :=
    (gammaIntrinsicVFDimension_mono hbad).trans_lt hZ
  obtain ⟨L,F,hF,hL⟩ := gammaGround_differentiable_of_independent hκ hs hr hv f p hp
  have hE : p.val ∈ E.carrier := by
    by_contra hpE
    apply gammaGround_independent_not_mem Bad hκ hs hr hv hn hsmall p.val hp
    exact ⟨⟨p.property,hpE⟩,(mem_gammaGroundDifferentiabilityLocus hn f p.val).mpr ⟨p,rfl,L,F,hF,hL⟩⟩
  obtain ⟨q,hqp,hq⟩ := hE
  have hqp' : q = p := Subtype.ext hqp
  subst q
  have hvp : gammaGroundJacobianValue f p = 1 := congrFun hq 0
  have hdet : (LinearMap.toMatrix' L).det = 1 :=
    (gammaGroundJacobianValue_of_derivative f p L ⟨F,hF,hL⟩).symm.trans hvp
  exact ⟨F,hF,by simpa only [hdet] using hL.hasJacobianAt⟩

end DiamondIntegral.Section3
