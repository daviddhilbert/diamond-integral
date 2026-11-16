import «section 6».ProtectedRootIteration

/-! On every noncore output-label fiber the actual unary root step has
a single inverse translation, including the inactive-focus case. This
identifies membership in the literal image of every source subset. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}

theorem restriction_image_mem_iff
    {A C : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (hf : Function.Injective f) (hCA : C.carrier ⊆ A.carrier) (a : A) :
    (f a).val ∈ (f.restrict hCA).image.carrier ↔ a.val ∈ C.carrier := by
  constructor
  · rintro ⟨p,hp⟩
    have he : f ⟨p.val,hCA p.property⟩ = f a := Subtype.ext hp
    exact (congrArg Subtype.val (hf he)) ▸ p.property
  · intro ha
    exact ⟨⟨a.val,ha⟩,rfl⟩

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def CentripetalData.unaryTagFocus (D : CentripetalData (G := G) A) (u : Fin r → RVInfinity M) : VF M :=
  if u ∈ D.activeTags.carrier then D.focus 0 u else 0

theorem CentripetalData.extendedFocus_unary (D : CentripetalData (G := G) A)
    {a : Mixed M 1 r} (ha : a ∈ A.carrier) : D.extendedFocus a = D.unaryTagFocus a.2 := by
  by_cases hu : a.2 ∈ D.activeTags.carrier
  · rw [D.extendedFocus_active ha hu,unaryTagFocus,if_pos hu]
    have hzero : Function.update a.1 D.coordinate 0 = 0 := by
      funext i
      have hi : i = D.coordinate := Subsingleton.elim _ _
      subst i
      simp only [Function.update_self,Pi.zero_apply]
    rw [hzero]
  · rw [D.extendedFocus_inactive hu,unaryTagFocus,if_neg hu]

namespace UnaryRootFamily

theorem stepMap_bijective (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00) :
    Function.Bijective (stepMap D) := (regularization_bijective _).comp (D.bijective h00)

theorem noncore_input (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (q : Mixed M 1 (1+(1+r))) (hq : q ∈ (regularizeMap D.map.image).image.carrier)
    (hflag : q.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) = branchTag false) :
    ∃ a : A, stepPoint D a.val = q ∧ a.val.2 = oldTags q.2 ∧ D.core a.val = false ∧
      a.val.1 0 = q.1 0 + D.unaryTagFocus (oldTags q.2) := by
  obtain ⟨a,he⟩ := (stepMap_bijective D h00).surjective ⟨q,hq⟩
  have he' : stepPoint D a.val = q := congrArg Subtype.val he
  have hu : a.val.2 = oldTags q.2 := by
    funext i
    have hh := congrArg (fun p : Mixed M 1 (1+(1+r)) => p.2 (Fin.natAdd 1 (Fin.natAdd 1 i))) he'
    simpa only [stepPoint,regularize,CentripetalData.point,Fin.append_right,oldTags] using hh
  have hcore : D.core a.val = false := by
    apply branchTag_injective h00
    have hh := congrArg (fun p : Mixed M 1 (1+(1+r)) => p.2 (Fin.natAdd 1 (Fin.castAdd r 0))) he'
    simpa only [stepPoint,regularize,CentripetalData.point,Fin.append_right,Fin.append_left] using hh.trans hflag
  have hcoord : D.coordinate = 0 := Subsingleton.elim _ _
  have hscalar : a.val.1 0-D.extendedFocus a.val = q.1 0 := by
    have hh := congrArg (fun p : Mixed M 1 (1+(1+r)) => p.1 0) he'
    simpa only [stepPoint,regularize,CentripetalData.point,hcoord,Function.update_self,
      hcore,Bool.false_eq_true,ite_false,add_zero] using hh
  rw [D.extendedFocus_unary a.property,hu] at hscalar
  exact ⟨a,he',hu,hcore,(sub_eq_iff_eq_add).mp hscalar⟩

theorem noncore_subset_image_mem_iff
    (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (C : DefSet (rawMixedSpace (M := M) 1 r) S) (hCA : C.carrier ⊆ A.carrier)
    (q : Mixed M 1 (1+(1+r))) (hq : q ∈ (regularizeMap D.map.image).image.carrier)
    (hflag : q.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) = branchTag false) :
    q ∈ ((stepMap D).restrict hCA).image.carrier ↔
      ((fun _ : Fin 1 => q.1 0+D.unaryTagFocus (oldTags q.2)),oldTags q.2) ∈ C.carrier := by
  obtain ⟨a,he,hu,hcore,hscalar⟩ := noncore_input D h00 q hq hflag
  have hmem := restriction_image_mem_iff (stepMap D) (stepMap_bijective D h00).injective hCA a
  rw [stepMap_apply,he] at hmem
  have hpoint : a.val = ((fun _ : Fin 1 => q.1 0+D.unaryTagFocus (oldTags q.2)),oldTags q.2) := by
    apply Prod.ext _ hu
    funext i
    fin_cases i
    exact hscalar
  rw [hpoint] at hmem
  exact hmem

end UnaryRootFamily
end DiamondIntegral.Section6
