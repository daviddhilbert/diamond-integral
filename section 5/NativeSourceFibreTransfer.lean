import «section 5».OriginalFibreIntegralVanishing
import «section 3».GammaGroundRealExtensions

/-! Changing source charts restricts to an actual bijection of every
fibre over its unchanged exact parameter base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {n r m s p q : ℕ}
variable {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
variable {A' : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
variable {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)}
variable (f : GammaGroundMap A C) (g : GammaGroundMap A' C)
variable (T : GammaGroundBijection A A') (h : ∀ a,g (T.map a) = f a)
variable (z : Fin (p+q) → M)

def nativeSourceFibreMap : GammaGroundMap (nativeMixedMapFibreAt f z) (nativeMixedMapFibreAt g z) := by
  have hs : (nativeMixedMapFibreAt f z).carrier ⊆ (A.monoReal
      (show B.real ⊆ B.real ∪ Set.range z from Set.subset_union_left)).carrier := by
    intro x hx
    obtain ⟨a,rfl,_⟩ := (nativeMixedMapFibreAt_mem f z x).mp hx
    exact a.property
  let F := (T.map.monoReal (T := B.real ∪ Set.range z) Set.subset_union_left).restrict hs
  refine F.corestrict ?_
  intro x
  obtain ⟨a,ha,hz⟩ := (nativeMixedMapFibreAt_mem f z x.val).mp x.property
  have he : (F x).val = (T.map a).val := by
    change (T.map ⟨x.val,hs x.property⟩).val = _
    exact congrArg (fun a : A => (T.map a).val) (Subtype.ext ha.symm)
  exact (nativeMixedMapFibreAt_mem g z (F x).val).mpr ⟨T.map a,he.symm,by rw [h]; exact hz⟩

theorem nativeSourceFibreMap_value (x : nativeMixedMapFibreAt f z) (a : A) (ha : a.val = x.val) :
    (nativeSourceFibreMap f g T h z x).val = (T.map a).val := by
  change (T.map ⟨x.val,_⟩).val = _
  exact congrArg (fun a : A => (T.map a).val) (Subtype.ext ha.symm)

theorem nativeSourceFibreMap_bijective : Function.Bijective (nativeSourceFibreMap f g T h z) := by
  constructor
  · intro x y hxy
    obtain ⟨a,ha,_⟩ := (nativeMixedMapFibreAt_mem f z x.val).mp x.property
    obtain ⟨b,hb,_⟩ := (nativeMixedMapFibreAt_mem f z y.val).mp y.property
    have he := congrArg Subtype.val hxy
    rw [nativeSourceFibreMap_value f g T h z x a ha,nativeSourceFibreMap_value f g T h z y b hb] at he
    have hab := T.bijective.injective (Subtype.ext he)
    exact Subtype.ext (ha.symm.trans ((congrArg Subtype.val hab).trans hb))
  · intro y
    obtain ⟨b,hb,hz⟩ := (nativeMixedMapFibreAt_mem g z y.val).mp y.property
    obtain ⟨a,ha⟩ := T.bijective.surjective b
    have hfa : nativeMixedCode (f a).val = z := by rw [← h,ha]; exact hz
    let x : nativeMixedMapFibreAt f z := ⟨a.val,(nativeMixedMapFibreAt_mem f z a.val).mpr ⟨a,rfl,hfa⟩⟩
    refine ⟨x,Subtype.ext ?_⟩
    rw [nativeSourceFibreMap_value f g T h z x a rfl,ha]
    exact hb

def nativeSourceFibreBijection : GammaGroundBijection (nativeMixedMapFibreAt f z) (nativeMixedMapFibreAt g z) :=
  ⟨nativeSourceFibreMap f g T h z,nativeSourceFibreMap_bijective f g T h z⟩

end DiamondIntegral.Section5
