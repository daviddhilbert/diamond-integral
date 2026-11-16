import «section 6».RegularizedCarriedComponents

/-! The image of a refined component is again a refinement: after
fixing all new output labels its VF fiber is the old output fiber or
empty. This is the inductive invariant needed for a whole finite chain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CentripetalData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {C : DefSet (rawMixedSpace (M := M) n s) S}
variable (D : CentripetalData (G := G) A) (π : Fin r → Fin s)
variable (hC : ProperInvariant S C.carrier) (hDouble : VFDoublyBounded C.carrier)
variable (hTagged : ∀ p ∈ C.carrier, ∀ q ∈ C.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
variable (hFibres : ∀ u : Fin s → RVInfinity M,
  vfFibre C.carrier u = ∅ ∨ vfFibre C.carrier u = vfFibre A.carrier (u ∘ π))

theorem refineLabels_image_fibre_subset (v : Fin (1+s) → RVInfinity M) :
    vfFibre (D.refineLabels π hC hDouble hTagged hFibres).map.image.carrier v ⊆
      vfFibre D.map.image.carrier (v ∘ prefixLabelSelection π) := by
  intro b hb
  obtain ⟨p,hp,he⟩ := (show (b,v) ∈ (D.refineLabels π hC hDouble hTagged hFibres).point '' C.carrier by
    rw [← image_carrier]; exact hb)
  rw [D.image_carrier]
  refine ⟨(p.1,p.2 ∘ π),labelRefinement_source_subset π hFibres p hp,?_⟩
  have h := D.refineLabels_point_commutes π hC hDouble hTagged hFibres p hp
  dsimp only at h
  rw [he] at h
  exact h.symm

theorem refineLabels_image_fibre_empty (v : Fin (1+s) → RVInfinity M)
    (hEmpty : vfFibre C.carrier (v ∘ Fin.natAdd 1) = ∅) :
    vfFibre (D.refineLabels π hC hDouble hTagged hFibres).map.image.carrier v = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro b hb
  obtain ⟨p,hp,he⟩ := (show (b,v) ∈ (D.refineLabels π hC hDouble hTagged hFibres).point '' C.carrier by
    rw [← image_carrier]; exact hb)
  have htags : p.2 = v ∘ Fin.natAdd 1 := by
    funext i
    simpa only [point,Fin.append_right,Function.comp_apply] using
      congrArg (fun q : Mixed M n (1+s) => q.2 (Fin.natAdd 1 i)) he
  have hp' : p.1 ∈ vfFibre C.carrier (v ∘ Fin.natAdd 1) := htags ▸ hp
  rw [hEmpty] at hp'
  exact hp'

theorem refineLabels_image_fibre_eq (v : Fin (1+s) → RVInfinity M)
    (hSame : vfFibre C.carrier (v ∘ Fin.natAdd 1) =
      vfFibre A.carrier ((v ∘ Fin.natAdd 1) ∘ π)) :
    vfFibre (D.refineLabels π hC hDouble hTagged hFibres).map.image.carrier v =
      vfFibre D.map.image.carrier (v ∘ prefixLabelSelection π) := by
  apply Set.Subset.antisymm
  · exact D.refineLabels_image_fibre_subset π hC hDouble hTagged hFibres v
  · intro b hb
    obtain ⟨a,ha,hDa⟩ := (show (b,v ∘ prefixLabelSelection π) ∈ D.point '' A.carrier by
      rw [← D.image_carrier]; exact hb)
    let u := v ∘ Fin.natAdd 1
    have hOld : a.2 = u ∘ π := by
      funext i
      have h := congrArg (fun q : Mixed M n (1+r) => q.2 (Fin.natAdd 1 i)) hDa
      simpa only [point,Fin.append_right,Function.comp_apply,prefixLabelSelection,Fin.addCases_right,u] using h
    let p : Mixed M n s := (a.1,u)
    have hp : p ∈ C.carrier := by
      apply (Set.ext_iff.mp hSame a.1).mpr
      exact hOld ▸ ha
    have hbase : ((p.1,p.2 ∘ π) : Mixed M n r) = a := Prod.ext rfl hOld.symm
    let E := D.refineLabels π hC hDouble hTagged hFibres
    have hComm : ((E.point p).1,(E.point p).2 ∘ prefixLabelSelection π) =
        (b,v ∘ prefixLabelSelection π) := by
      exact (D.refineLabels_point_commutes π hC hDouble hTagged hFibres p hp).trans
        ((congrArg D.point hbase).trans hDa)
    have hVF : (E.point p).1 = b := congrArg Prod.fst hComm
    have hRV : (E.point p).2 = v := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have h := congrArg (fun q : Mixed M n (1+r) => q.2 (Fin.castAdd r j)) hComm
        simpa only [Function.comp_apply,prefixLabelSelection,Fin.addCases_left] using h
      · change Fin.append (fun _ : Fin 1 => branchTag (M := M) (E.core p)) p.2 (Fin.natAdd 1 j) = v (Fin.natAdd 1 j)
        simp only [Fin.append_right,p,u,Function.comp_apply]
    rw [E.image_carrier]
    exact ⟨p,hp,Prod.ext hVF hRV⟩

theorem refineLabels_image_fibre_old_or_empty (v : Fin (1+s) → RVInfinity M) :
    vfFibre (D.refineLabels π hC hDouble hTagged hFibres).map.image.carrier v = ∅ ∨
      vfFibre (D.refineLabels π hC hDouble hTagged hFibres).map.image.carrier v =
        vfFibre D.map.image.carrier (v ∘ prefixLabelSelection π) := by
  cases hFibres (v ∘ Fin.natAdd 1) with
  | inl he => exact Or.inl (D.refineLabels_image_fibre_empty π hC hDouble hTagged hFibres v he)
  | inr he => exact Or.inr (D.refineLabels_image_fibre_eq π hC hDouble hTagged hFibres v he)

end DiamondIntegral.Section6.CentripetalData
