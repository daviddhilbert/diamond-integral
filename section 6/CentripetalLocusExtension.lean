import «section 6».UnaryLiftingFieldBase

/-! Extend a permitted centripetal component from a whole old-label
locus by the identity in VF on the other labels. The actual full focus
graph and all covariance data stay over the original parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CentripetalData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A C : DefSet (rawMixedSpace (M := M) n r) S}

def extendOnTags (D : CentripetalData (G := G) C)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (hC : C.carrier = (focusActive A U).carrier)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    CentripetalData (G := G) A := by
  let W : DefSet (rawRVSpace (M := M) r) S :=
    ⟨D.activeTags.carrier ∩ U.carrier,D.activeTags.definable.inter _ U.definable⟩
  have hsub : (focusActive A W).carrier ⊆ (focusActive C D.activeTags).carrier := by
    intro p hp
    refine ⟨?_,hp.2.1⟩
    rw [hC]
    exact ⟨hp.1,hp.2.2⟩
  have hFib (u : Fin r → RVInfinity M) (hu : u ∈ U.carrier) :
      vfFibre C.carrier u = vfFibre A.carrier u := by
    ext x
    change (x,u) ∈ C.carrier ↔ (x,u) ∈ A.carrier
    rw [hC]
    exact and_iff_left hu
  exact {
    coordinate := D.coordinate
    activeTags := W
    focus := D.focus
    focusMap := D.focusMap.comp (Map.inclusion hsub)
    focusMap_eq := fun p => D.focusMap_eq ⟨p.val,hsub p.property⟩
    sourceProper := hA
    sourceDoublyBounded := hAD
    tagged := htag
    continuous := fun u hu => by rw [← hFib u hu.2]; exact D.continuous u hu.1
    focusRV := fun p hp hu => D.focusRV p (by rw [hC]; exact ⟨hp,hu.2⟩) hu.1
    coefficient := D.coefficient
    coefficient_nonzero := D.coefficient_nonzero
    coefficient_nonnegative := D.coefficient_nonnegative
    coefficient_definable := D.coefficient_definable
    covariance := fun u hu => by rw [← hFib u hu.2]; exact D.covariance u hu.1 }

theorem extendOnTags_extendedFocus (D : CentripetalData (G := G) C)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (hC : C.carrier = (focusActive A U).carrier)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (p : Mixed M n r) (hp : p ∈ C.carrier) :
    (D.extendOnTags U hC hA hAD htag).extendedFocus p = D.extendedFocus p := by
  let E := D.extendOnTags U hC hA hAD htag
  have hpA : p ∈ A.carrier := by rw [hC] at hp; exact hp.1
  have hpU : p.2 ∈ U.carrier := by rw [hC] at hp; exact hp.2
  by_cases hact : p.2 ∈ D.activeTags.carrier
  · have hEact : p.2 ∈ E.activeTags.carrier := ⟨hact,hpU⟩
    rw [E.extendedFocus_active hpA hEact,D.extendedFocus_active hp hact]
    rfl
  · have hEact : p.2 ∉ E.activeTags.carrier := fun h => hact h.1
    rw [E.extendedFocus_inactive hEact,D.extendedFocus_inactive hact]

theorem extendOnTags_point (D : CentripetalData (G := G) C)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (hC : C.carrier = (focusActive A U).carrier)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (p : Mixed M n r) (hp : p ∈ C.carrier) :
    (D.extendOnTags U hC hA hAD htag).point p = D.point p := by
  let E := D.extendOnTags U hC hA hAD htag
  have hExt : E.extendedFocus p = D.extendedFocus p := D.extendOnTags_extendedFocus U hC hA hAD htag p hp
  have hCore : E.core p = D.core p := by
    change decide _ = decide _
    simp only [hExt]
    rfl
  change E.point p = D.point p
  simp only [point,hExt,hCore]
  rfl

theorem extendOnTags_outside (D : CentripetalData (G := G) C)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (hC : C.carrier = (focusActive A U).carrier)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (p : Mixed M n r) (hp : p ∈ A.carrier) (hpC : p ∉ C.carrier) :
    (D.extendOnTags U hC hA hAD htag).point p =
      (p.1,Fin.append (fun _ : Fin 1 => branchTag false) p.2) := by
  let E := D.extendOnTags U hC hA hAD htag
  have hinactive : p.2 ∉ E.activeTags.carrier := by
    intro hact
    apply hpC
    rw [hC]
    exact ⟨hp,hact.2⟩
  apply Prod.ext (E.point_inactive hinactive)
  change Fin.append (fun _ : Fin 1 => branchTag (E.core p)) p.2 = _
  rw [E.core_inactive hinactive]

end DiamondIntegral.Section6.CentripetalData
