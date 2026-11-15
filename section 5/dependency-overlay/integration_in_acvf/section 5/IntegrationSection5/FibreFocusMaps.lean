import IntegrationSection5.FibreFocusPresentation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.FibreFocusData
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}

def inactive (D : FibreFocusData A i k) : DefSet (M := M) S n m :=
  PresentedSet.mk (carrier A \ D.locus) (SetDefinable.sdiff _ (setDefinable A) D.locus_definable)

def activeEtaMap (D : FibreFocusData A i k) : Map D.active (PresentedSet.univ (pointSpace n m) S) :=
  Map.comp (subtractMap i (PresentedSet.prod D.active (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)))
    (Map.pair (Map.id D.active) D.centerMap)

def inactiveEtaMap (D : FibreFocusData A i k) : Map D.inactive (PresentedSet.univ (pointSpace n m) S) :=
  Map.inclusion (Set.subset_univ _)

def etaMap (D : FibreFocusData A i k) : Map A (PresentedSet.univ (pointSpace n m) S) :=
  Map.mk (fun p => ⟨D.eta p.val,Set.mem_univ _⟩)
    (RelationDefinable.congr _ _ (RelationDefinable.union _ _
      (Map.graph_definable D.activeEtaMap) (Map.graph_definable D.inactiveEtaMap)) (by
        intro p q
        constructor
        · rintro (⟨a,rfl,he⟩ | ⟨a,rfl,he⟩)
          · refine ⟨⟨a.val,a.property.1⟩,rfl,?_⟩
            change replace i a.val (vfAt a.val i-D.center a.val) = q at he
            simpa only [eta,if_pos a.property.2] using he
          · refine ⟨⟨a.val,a.property.1⟩,rfl,?_⟩
            change a.val = q at he
            simpa only [eta,if_neg a.property.2] using he
        · rintro ⟨a,rfl,he⟩
          by_cases hl : a.val ∈ D.locus
          · exact Or.inl ⟨⟨a.val,a.property,hl⟩,rfl,by change replace i a.val (vfAt a.val i-D.center a.val) = q; simpa only [eta,if_pos hl] using he⟩
          · exact Or.inr ⟨⟨a.val,a.property,hl⟩,rfl,by change a.val = q; simpa only [eta,if_neg hl] using he⟩))

theorem eta_labels (D : FibreFocusData A i k) (p : Point (M := M) n m) : (D.eta p).2 = p.2 := by
  by_cases hp : p ∈ D.locus <;> simp [eta,replace,hp]

theorem eta_other (D : FibreFocusData A i k) (p : Point (M := M) n m) (j : Fin n) (hj : j ≠ i) :
    vfAt (D.eta p) j = vfAt p j := by
  by_cases hp : p ∈ D.locus <;> simp [eta,replace,vfAt,hp,hj]

theorem erase_eta (D : FibreFocusData A i k) (p : Point (M := M) n m) : erase i (D.eta p) = erase i p := by
  refine Prod.ext ?_ (D.eta_labels p)
  funext j
  by_cases hj : j = i
  · subst j
    simp [erase,replace]
  · simpa only [erase,replace,Function.update_of_ne hj,vfAt] using D.eta_other p j hj

theorem eta_injOn (D : FibreFocusData A i k) : Set.InjOn D.eta (carrier A) := by
  intro p hp q hq he
  have hr : p.2 = q.2 := (D.eta_labels p).symm.trans ((congrArg Prod.snd he).trans (D.eta_labels q))
  have ho (j : Fin n) (hj : j ≠ i) : vfAt p j = vfAt q j :=
    (D.eta_other p j hj).symm.trans ((congrArg (fun z => vfAt z j) he).trans (D.eta_other q j hj))
  have hrv : SameRV p q := by
    apply (sameRV_iff _ _).mpr
    refine ⟨fun j => ?_,hr⟩
    by_cases hj : j = i
    · subst j
      exact (D.tagged p hp).symm.trans ((congrFun hr k).trans (D.tagged q hq))
    · exact congrArg rv (ho j hj)
  have hm := D.locus_saturated p hp q hq hrv ho
  by_cases hpc : p ∈ D.locus
  · have hqc := hm.mp hpc
    have herase := (D.erase_eta p).symm.trans ((congrArg (erase i) he).trans (D.erase_eta q))
    have hc := D.independent p ⟨hp,hpc⟩ q ⟨hq,hqc⟩ herase
    have hi : vfAt p i-D.center p = vfAt q i-D.center q := by
      simpa only [eta,if_pos hpc,if_pos hqc,replace,vfAt,Function.update_self] using congrArg (fun z => vfAt z i) he
    apply Prod.ext ?_ hr
    funext j
    by_cases hj : j = i
    · subst j
      rw [hc] at hi
      exact sub_left_inj.mp hi
    · exact ho j hj
  · have hqc : q ∉ D.locus := fun h => hpc (hm.mpr h)
    simpa only [eta,if_neg hpc,if_neg hqc] using he

def image (D : FibreFocusData A i k) : DefSet (M := M) S n m := Map.image D.etaMap

def toImage (D : FibreFocusData A i k) : Map A D.image := Map.toImage D.etaMap

theorem toImage_bijective (D : FibreFocusData A i k) : Function.Bijective D.toImage := by
  constructor
  · intro p q he
    exact Subtype.ext (D.eta_injOn p.property q.property (congrArg (fun z : D.image => z.val) he))
  · rintro ⟨q,p,hp⟩
    exact ⟨p,Subtype.ext hp⟩

end IntegrationInACVF.Section5.FibreFocusData
