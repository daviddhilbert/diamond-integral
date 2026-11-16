import «section 6».ReindexedCentripetalData
import «section 6».ApertureRestrictionData

/-! Exact conjugation of permitted point maps and their protected
restrictions under VF coordinate permutations. Coefficients and branch
flags are retained, and the entire target image is identified. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
namespace CentripetalData

theorem reindexVF_extendedFocus (D : CentripetalData (G := G) A) (e : Fin n ≃ Fin n)
    (p : Mixed M n r) (hp : p ∈ A.carrier) :
    (D.reindexVF e).extendedFocus (reindexVFPoint e p)=D.extendedFocus p := by
  have hpNew : reindexVFPoint e p ∈ (reindexedVFSet A e).carrier := ⟨⟨p,hp⟩,rfl⟩
  by_cases hu : p.2 ∈ D.activeTags.carrier
  · rw [(D.reindexVF e).extendedFocus_active hpNew hu,D.extendedFocus_active hp hu]
    change D.focus (Function.update (p.1 ∘ e) (e.symm D.coordinate) 0 ∘ e.symm) p.2=
      D.focus (Function.update p.1 D.coordinate 0) p.2
    rw [erased_comp_fin_equiv]
    have he : (p.1 ∘ e) ∘ e.symm=p.1 := by
      funext i
      simp only [Function.comp_apply,Equiv.apply_symm_apply]
    rw [he]
  · exact ((D.reindexVF e).extendedFocus_inactive (p := reindexVFPoint e p) hu).trans
      (D.extendedFocus_inactive (p := p) hu).symm

theorem reindexVF_extendedFocus_at (D : CentripetalData (G := G) A) (e : Fin n ≃ Fin n)
    (p : Mixed M n r) (hp : p ∈ (reindexedVFSet A e).carrier) :
    (D.reindexVF e).extendedFocus p=D.extendedFocus (reindexVFPoint e.symm p) := by
  have h := D.reindexVF_extendedFocus e (reindexVFPoint e.symm p) ((mem_reindexedVFSet A e p).mp hp)
  have he : reindexVFPoint e (reindexVFPoint e.symm p)=p := by
    simpa only [Equiv.symm_symm] using reindexVFPoint_inverse e.symm p
  rw [he] at h
  exact h

theorem reindexVF_core (D : CentripetalData (G := G) A) (e : Fin n ≃ Fin n)
    (p : Mixed M n r) (hp : p ∈ A.carrier) :
    (D.reindexVF e).core (reindexVFPoint e p)=D.core p := by
  change decide (vfValue (D.coefficient*(D.reindexVF e).extendedFocus (reindexVFPoint e p)) <
    vfValue ((p.1 ∘ e) (e.symm D.coordinate)-(D.reindexVF e).extendedFocus (reindexVFPoint e p)))=D.core p
  rw [D.reindexVF_extendedFocus e p hp]
  simp only [Function.comp_apply,Equiv.apply_symm_apply]
  rfl

theorem reindexVF_point (D : CentripetalData (G := G) A) (e : Fin n ≃ Fin n)
    (p : Mixed M n r) (hp : p ∈ A.carrier) :
    (D.reindexVF e).point (reindexVFPoint e p)=reindexVFPoint e (D.point p) := by
  change (Function.update (p.1 ∘ e) (e.symm D.coordinate)
    ((p.1 ∘ e) (e.symm D.coordinate)-(D.reindexVF e).extendedFocus (reindexVFPoint e p)+
      if (D.reindexVF e).core (reindexVFPoint e p) then
        D.coefficient*(D.reindexVF e).extendedFocus (reindexVFPoint e p) else 0),
    Fin.append (fun _ : Fin 1 => branchTag (M := M) ((D.reindexVF e).core (reindexVFPoint e p))) p.2)=_
  rw [D.reindexVF_extendedFocus e p hp,D.reindexVF_core e p hp]
  simp only [Function.comp_apply,Equiv.apply_symm_apply]
  apply Prod.ext
  · exact (update_comp_fin_equiv p.1 e D.coordinate _).symm
  · rfl

theorem reindexVF_image (D : CentripetalData (G := G) A) (e : Fin n ≃ Fin n) :
    (D.reindexVF e).map.image=reindexedVFSet D.map.image e := by
  apply defSet_eq_of_carrier_eq
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    obtain ⟨a,ha⟩ := p.property
    change reindexVFPoint e a.val=p.val at ha
    refine ⟨D.bijection a,?_⟩
    change reindexVFPoint e (D.point a.val)=(D.reindexVF e).point p.val
    have he := D.reindexVF_point e a.val a.property
    rw [ha] at he
    exact he.symm
  · rintro ⟨q,rfl⟩
    obtain ⟨a,ha⟩ := q.property
    refine ⟨⟨reindexVFPoint e a.val,⟨a,rfl⟩⟩,?_⟩
    exact (D.reindexVF_point e a.val a.property).trans (congrArg (reindexVFPoint e) ha)

end CentripetalData

theorem ApertureRestrictionData.reindexVF
    {P : DefSet (rawMixedSpace (M := M) n r) S}
    {D : CentripetalData (G := G) A} {E : CentripetalData (G := G) P}
    (h : ApertureRestrictionData D E) (e : Fin n ≃ Fin n) :
    ApertureRestrictionData (D.reindexVF e) (E.reindexVF e) := by
  have hSub : (reindexedVFSet P e).carrier ⊆ (reindexedVFSet A e).carrier := by
    intro p hp
    exact (mem_reindexedVFSet A e p).mpr (h.subset ((mem_reindexedVFSet P e p).mp hp))
  refine ⟨hSub,congrArg e.symm h.coordinate,h.coefficient,?_⟩
  intro p hp
  rw [E.reindexVF_extendedFocus_at e p hp,D.reindexVF_extendedFocus_at e p (hSub hp)]
  exact h.focus (reindexVFPoint e.symm p) ((mem_reindexedVFSet P e p).mp hp)

end DiamondIntegral.Section6
