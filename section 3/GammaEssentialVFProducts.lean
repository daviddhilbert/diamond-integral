import «section 3».GammaMixedProductJacobians
import «section 3».GammaGroundEssentialVFMap

/-! Cartesian products of actual essential Gamma-ground maps retain
cofull source and target, including zero-degree factors. Cofullness is
tested on generic points and uses no dimensional cancellation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

include hκ hs hr hv in
theorem gammaGround_mem_cofull_all {n a : ℕ}
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n a)}
    (E : GammaGroundDefSet hc B (rawMixedSpace (M := M) n a))
    (hE : Section2.vfDimension (A.sdiff E).carrier < (n : WithBot ℕ)) (p : GammaGroundGeneric A) :
    p.val.val ∈ E.carrier := by
  cases n with
  | zero =>
    have he := (vf_small_zero_iff_empty (A.sdiff E).carrier).mp hE
    by_contra hp
    exact Set.notMem_empty p.val.val (he ▸ (show p.val.val ∈ (A.sdiff E).carrier from ⟨p.val.property,hp⟩))
  | succ n => exact gammaGround_mem_of_small_complement E hκ hs hr hv (Nat.succ_pos n) hE p

include hκ hs hr hv in
theorem gammaGround_cofull_of_generics_all {n a : ℕ}
    (A E : GammaGroundDefSet hc B (rawMixedSpace (M := M) n a))
    (hE : ∀ p : GammaGroundGeneric A, p.val.val ∈ E.carrier) :
    Section2.vfDimension (A.sdiff E).carrier < (n : WithBot ℕ) := by
  cases n with
  | zero =>
    apply (vf_small_zero_iff_empty _).mpr
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact hp.2 (hE ⟨⟨p,hp.1⟩,algebraicIndependent_empty_type⟩)
  | succ n => exact gammaGround_small_complement_of_generic A E hκ hs hr hv (Nat.succ_pos n) hE

include hκ hs hr hv in
theorem gammaGround_cofull_product {n m a b : ℕ}
    (A E : GammaGroundDefSet hc B (rawMixedSpace (M := M) n a))
    (D H : GammaGroundDefSet hc B (rawMixedSpace (M := M) m b))
    (hE : Section2.vfDimension (A.sdiff E).carrier < (n : WithBot ℕ))
    (hH : Section2.vfDimension (D.sdiff H).carrier < (m : WithBot ℕ)) :
    Section2.vfDimension ((gammaGroundMixedProductDomain A D).sdiff (gammaGroundMixedProductDomain E H)).carrier <
      ((n+m : ℕ) : WithBot ℕ) := by
  apply gammaGround_cofull_of_generics_all hκ hs hr hv
  intro p
  have hp := (mem_gammaGroundMixedProductDomain A D p.val.val).mp p.val.property
  let u : A := ⟨(p.val.val.1 ∘ Fin.castAdd m,p.val.val.2 ∘ Fin.castAdd b),hp.1⟩
  let v : D := ⟨(p.val.val.1 ∘ Fin.natAdd n,p.val.val.2 ∘ Fin.natAdd a),hp.2⟩
  have hu : AlgebraicIndependent (vfParameterField B.real) u.val.1 :=
    p.property.comp (Fin.castAdd m) (Fin.castAdd_injective n m)
  have hv' : AlgebraicIndependent (vfParameterField B.real) v.val.1 :=
    p.property.comp (Fin.natAdd n) (Fin.natAdd_injective m n)
  exact (mem_gammaGroundMixedProductDomain E H p.val.val).mpr
    ⟨gammaGround_mem_cofull_all hκ hs hr hv E hE ⟨u,hu⟩,
      gammaGround_mem_cofull_all hκ hs hr hv H hH ⟨v,hv'⟩⟩

def GammaGroundEssentialVFMap.product {n m a a' b b' : ℕ}
    {U : GammaGroundDefSet hc B (rawMixedSpace (M := M) n a)}
    {U' : GammaGroundDefSet hc B (rawMixedSpace (M := M) n a')}
    {V : GammaGroundDefSet hc B (rawMixedSpace (M := M) m b)}
    {V' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m b')}
    (f : GammaGroundEssentialVFMap U U') (g : GammaGroundEssentialVFMap V V') :
    GammaGroundEssentialVFMap (gammaGroundMixedProductDomain U V) (gammaGroundMixedProductDomain U' V') where
  source := gammaGroundMixedProductDomain f.source g.source
  target := gammaGroundMixedProductDomain f.target g.target
  source_subset := by
    intro p hp
    have h := (mem_gammaGroundMixedProductDomain f.source g.source p).mp hp
    exact (mem_gammaGroundMixedProductDomain U V p).mpr ⟨f.source_subset h.1,g.source_subset h.2⟩
  target_subset := by
    intro p hp
    have h := (mem_gammaGroundMixedProductDomain f.target g.target p).mp hp
    exact (mem_gammaGroundMixedProductDomain U' V' p).mpr ⟨f.target_subset h.1,g.target_subset h.2⟩
  source_small := gammaGround_cofull_product hκ hs hr hv U f.source V g.source f.source_small g.source_small
  target_small := gammaGround_cofull_product hκ hs hr hv U' f.target V' g.target f.target_small g.target_small
  map := gammaMixedProductMap f.map g.map
  bijective := (gammaMixedProductBijection ⟨f.map,f.bijective⟩ ⟨g.map,g.bijective⟩).bijective

end DiamondIntegral.Section3
