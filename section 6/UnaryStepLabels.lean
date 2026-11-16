import «section 6».UnaryCoreFibres

/-! Recover the current leading term, the retained branch, and the
actual inverse source point from the labels of a unary root step. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.UnaryRootFamily

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem step_image_leading_term (D : CentripetalData (G := G) A)
    {q : Mixed M 1 (1+(1+r))} (hq : q ∈ (regularizeMap D.map.image).image.carrier) :
    rv M (q.1 0) = q.2 0 := by
  obtain ⟨p,hp⟩ := hq
  change regularize p.val = q at hp
  have hfield : p.val.1 = q.1 := congrArg Prod.fst hp
  have htag := congrArg (fun z : Mixed M 1 (1+(1+r)) => z.2 (Fin.castAdd (1+r) 0)) hp
  change rv M (p.val.1 0) = q.2 0 at htag
  rwa [hfield] at htag

theorem step_image_branch (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    {q : Mixed M 1 (1+(1+r))} (hq : q ∈ (regularizeMap D.map.image).image.carrier) :
    q.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) = branchTag false ∨
      q.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) = branchTag true := by
  obtain ⟨a,he⟩ := (stepMap_bijective D h00).surjective ⟨q,hq⟩
  have he' : stepPoint D a.val = q := congrArg Subtype.val he
  have htag := congrArg (fun z : Mixed M 1 (1+(1+r)) => z.2 (Fin.natAdd 1 (Fin.castAdd r 0))) he'
  have htag' : branchTag (M := M) (D.core a.val) = q.2 (Fin.natAdd 1 (Fin.castAdd r 0)) := by
    simpa only [stepPoint,regularize,CentripetalData.point,Fin.append_right,Fin.append_left] using htag
  cases hc : D.core a.val
  · exact Or.inl (by simpa only [hc] using htag'.symm)
  · exact Or.inr (by simpa only [hc] using htag'.symm)

theorem noncore_inverse_mem (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    {q : Mixed M 1 (1+(1+r))} (hq : q ∈ (regularizeMap D.map.image).image.carrier)
    (hflag : q.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) = branchTag false) :
    ((fun _ : Fin 1 => q.1 0+D.unaryTagFocus (oldTags q.2)),oldTags q.2) ∈ A.carrier := by
  obtain ⟨a,he,hu,hcore,hscalar⟩ := noncore_input D h00 q hq hflag
  have hpoint : a.val = ((fun _ : Fin 1 => q.1 0+D.unaryTagFocus (oldTags q.2)),oldTags q.2) := by
    apply Prod.ext
    · funext i
      fin_cases i
      exact hscalar
    · exact hu
  exact hpoint ▸ a.property

end DiamondIntegral.Section6.UnaryRootFamily
