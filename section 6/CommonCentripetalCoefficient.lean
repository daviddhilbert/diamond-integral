import «section 6».CentripetalCoefficientRefinement

/-! A finite family of original-base named nonnegative coefficients
has a common named refinement. The unordered product of their distinct
values introduces no names and also handles the empty family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {I : Type} [Finite I]

theorem exists_common_named_coefficient (a : I → VF M)
    (hNZ : ∀ i, a i ≠ 0) (hpos : ∀ i, (1 : GammaInfinity M) ≤ vfValue (a i))
    (hdef : ∀ i, S.Definable₁ LRV {(a i).val}) :
    ∃ c : VF M, c ≠ 0 ∧ S.Definable₁ LRV {c.val} ∧
      (1 : GammaInfinity M) ≤ vfValue c ∧ ∀ i, vfValue (a i) ≤ vfValue c := by
  letI : Fintype I := Fintype.ofFinite I
  let E : Finset (VF M) := Finset.univ.image a
  have hMem (i : I) : a i ∈ E := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hIndex (x : VF M) (hx : x ∈ E) : ∃ i, a i = x := by
    obtain ⟨i,_,he⟩ := Finset.mem_image.mp hx
    exact ⟨i,he⟩
  have hEpos (x : VF M) (hx : x ∈ E) : (1 : GammaInfinity M) ≤ vfValue x := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hpos i
  have hENZ (x : VF M) (hx : x ∈ E) : x ≠ 0 := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hNZ i
  have hEdef : S.Definable₁ LRV (Subtype.val '' (E : Set (VF M))) := by
    have hd (i : I) : S.Definable LRV {z : Fin 1 → M | z 0 = (a i).val} := hdef i
    have h := Set.definable_iUnion_of_finite hd
    change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' (E : Set (VF M))}
    convert h using 1
    ext z
    constructor
    · rintro ⟨x,hx,hxz⟩
      obtain ⟨i,hix⟩ := hIndex x hx
      exact Set.mem_iUnion.mpr ⟨i,hxz.symm.trans (congrArg Subtype.val hix.symm)⟩
    · intro hz
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      exact ⟨a i,hMem i,hi.symm⟩
  let c : VF M := ∏ x ∈ E, x
  have hval : vfValue c = ∏ x ∈ E, vfValue x := map_prod Values.vfValueHom (fun x => x) E
  refine ⟨c,Finset.prod_ne_zero_iff.mpr hENZ,finiteProduct_definable S E hEdef,?_,?_⟩
  · rw [hval]
    exact Finset.one_le_prod hEpos
  · intro i
    rw [hval]
    exact Finset.single_le_prod hEpos (hMem i)

end DiamondIntegral.Section6
