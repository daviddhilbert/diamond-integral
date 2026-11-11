import «section 2».ScalarExtensions

/-! Source projections and restricted images of the full graph of a
unary VF function, without additional choices or parameters. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem scalarPartialGraph_domain_definable (S : Set M) (A : Set (VF M)) (f : VF M → VF M)
    (hf : S.Definable LRV (scalarPartialGraph A f)) : S.Definable₁ LRV (Subtype.val '' A) := by
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' A}
  convert hf.image_comp (fun _ : Fin 1 => (0 : Fin 2)) using 1
  ext z
  constructor
  · rintro ⟨x,hx,hxz⟩
    exact ⟨![x.val,(f x).val],⟨x,hx,rfl,rfl⟩,by funext j; fin_cases j; exact hxz⟩
  · rintro ⟨w,⟨x,hx,hxw,hfw⟩,hw⟩
    exact ⟨x,hx,hxw.trans (congrFun hw 0)⟩

theorem scalarPartialGraph_restricted_image_definable (S : Set M)
    (A C : Set (VF M)) (hCA : C ⊆ A) (hC : S.Definable₁ LRV (Subtype.val '' C))
    (f : VF M → VF M) (hf : S.Definable LRV (scalarPartialGraph A f)) :
    S.Definable₁ LRV (Subtype.val '' (f '' C)) := by
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' (f '' C)}
  have h := (hf.inter (hC.preimage_comp (fun _ : Fin 1 => (0 : Fin 2)))).image_comp
    (fun _ : Fin 1 => (1 : Fin 2))
  convert h using 1
  ext z
  constructor
  · rintro ⟨y,⟨x,hx,rfl⟩,hyz⟩
    refine ⟨![x.val,(f x).val],⟨⟨x,hCA hx,rfl,rfl⟩,x,hx,rfl⟩,?_⟩
    funext j
    fin_cases j
    exact hyz
  · rintro ⟨w,⟨⟨x,hx,hxw,hfw⟩,y,hy,hyw⟩,hw⟩
    have he : x = y := Subtype.ext (hxw.trans hyw.symm)
    exact ⟨f x,⟨x,he.symm ▸ hy,rfl⟩,hfw.trans (congrFun hw 0)⟩

end DiamondIntegral.Section2
