import «section 6».RefinementPortGraphFibres

/-! Porting a label-retaining bijection through full RV refinements
again has whole old target fibres or empty fibres. The actual target
frame has proper invariant geometry and all required double bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

theorem RVRefinementFrame.port_retained (hc : CanonicalStructure.IsCanonical (M := M))
    (X : RVRefinementFrame A) (f : Map A B) (p : X.base) (i : Fin X.arity) :
    (X.portMap hc f p).val.2 (Fin.natAdd s i)=p.val.2 i := retainedRVOutput_retained hc _ p i

theorem RVRefinementFrame.port_bijective (hc : CanonicalStructure.IsCanonical (M := M))
    (X : RVRefinementFrame A) (f : Map A B) (hf : Function.Injective f) : Function.Bijective (X.portMap hc f) := by
  refine ⟨?_,map_toImage_surjective _⟩
  intro p z he
  have hOld : f (X.oldPoint p)=f (X.oldPoint z) := by
    apply Subtype.ext
    exact (retainedRVOutput_selected hc (f.comp X.oldMap) p).symm.trans
      ((congrArg (fun q : (retainedRVOutputMap hc (f.comp X.oldMap)).image =>
        (q.val.1,q.val.2 ∘ Fin.castAdd X.arity)) he).trans (retainedRVOutput_selected hc (f.comp X.oldMap) z))
  have hPoint := hf hOld
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun q : A => q.val.1) hPoint
  · funext i
    exact (X.port_retained hc f p i).symm.trans
      ((congrArg (fun q => q.val.2 (Fin.natAdd s i)) he).trans (X.port_retained hc f z i))

theorem RVRefinementFrame.port_target_fibres (hc : CanonicalStructure.IsCanonical (M := M))
    (X : RVRefinementFrame A) (f : Map A B) (hf : Function.Bijective f) (π : Fin r → Fin s)
    (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i) (v : Fin (s+X.arity) → RVInfinity M) :
    vfFibre (retainedRVOutputMap hc (f.comp X.oldMap)).image.carrier v=∅ ∨
      vfFibre (retainedRVOutputMap hc (f.comp X.oldMap)).image.carrier v=vfFibre B.carrier (v ∘ Fin.castAdd X.arity) := by
  by_cases hNE : (vfFibre (retainedRVOutputMap hc (f.comp X.oldMap)).image.carrier v).Nonempty
  · right
    obtain ⟨b,p,hp⟩ := hNE
    change (X.portMap hc f p).val=(b,v) at hp
    have hOldTags : (f (X.oldPoint p)).val.2=v ∘ Fin.castAdd X.arity := by
      have h := retainedRVOutput_selected hc (f.comp X.oldMap) p
      change ((X.portMap hc f p).val.1,(X.portMap hc f p).val.2 ∘ Fin.castAdd X.arity)=(f (X.oldPoint p)).val at h
      rw [hp] at h
      exact (congrArg Prod.snd h).symm
    apply Set.Subset.antisymm
    · rintro y ⟨z,hz⟩
      change (X.portMap hc f z).val=(y,v) at hz
      have h := retainedRVOutput_selected hc (f.comp X.oldMap) z
      change ((X.portMap hc f z).val.1,(X.portMap hc f z).val.2 ∘ Fin.castAdd X.arity)=(f (X.oldPoint z)).val at h
      rw [hz] at h
      change (y,v ∘ Fin.castAdd X.arity) ∈ B.carrier
      have he : (f (X.oldPoint z)).val=(y,v ∘ Fin.castAdd X.arity) := h.symm
      exact he ▸ (f (X.oldPoint z)).property
    · intro y hy
      obtain ⟨a,ha⟩ := hf.surjective ⟨(y,v ∘ Fin.castAdd X.arity),hy⟩
      have hTagsA : a.val.2=(X.oldPoint p).val.2 := by
        funext i
        exact (hRetain a i).symm.trans
          ((congrArg (fun q : B => q.val.2 (π i)) ha).trans ((congrFun hOldTags (π i)).symm.trans (hRetain (X.oldPoint p) i)))
      have hSource : (a.val.1,p.val.2) ∈ X.base.carrier := by
        change a.val.1 ∈ vfFibre X.base.carrier p.val.2
        rw [X.fibre_eq_of_mem p]
        change (a.val.1,(X.oldPoint p).val.2) ∈ A.carrier
        exact hTagsA ▸ a.property
      let z : X.base := ⟨(a.val.1,p.val.2),hSource⟩
      have hOld : X.oldPoint z=a := Subtype.ext (Prod.ext rfl hTagsA.symm)
      refine ⟨z,?_⟩
      apply Prod.ext
      · change (f (X.oldPoint z)).val.1=y
        rw [hOld]
        exact congrArg (fun q : B => q.val.1) ha
      · have hTargetTags := congrArg Prod.snd hp
        simp only [RVRefinementFrame.portMap_value] at hTargetTags
        change Fin.append (f (X.oldPoint z)).val.2 p.val.2=v
        rw [hOld]
        have hSame : (f a).val.2=(f (X.oldPoint p)).val.2 :=
          (congrArg (fun q : B => q.val.2) ha).trans hOldTags.symm
        rw [hSame]
        exact hTargetTags
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hNE)

theorem RVRefinementFrame.port_target_doublyBounded (hc : CanonicalStructure.IsCanonical (M := M))
    (X : RVRefinementFrame A) (f : Map A B) (hB : VFDoublyBounded B.carrier) :
    VFDoublyBounded (retainedRVOutputMap hc (f.comp X.oldMap)).image.carrier := by
  obtain ⟨α,hα⟩ := hB
  exact ⟨α,by rintro q ⟨p,rfl⟩ i; exact hα (f (X.oldPoint p)).val (f (X.oldPoint p)).property i⟩

theorem RVRefinementFrame.port_target_rvBounded (hc : CanonicalStructure.IsCanonical (M := M))
    (X : RVRefinementFrame A) (f : Map A B) (hB : RVSupportDoublyBounded B.carrier) :
    RVSupportDoublyBounded (retainedRVOutputMap hc (f.comp X.oldMap)).image.carrier := by
  obtain ⟨α,hα⟩ := hB
  obtain ⟨β,hβ⟩ := X.proper.rvBounded
  have hloA : ((max α β)⁻¹).val ≤ (α⁻¹).val := inv_le_inv' (le_max_left α β)
  have hloB : ((max α β)⁻¹).val ≤ (β⁻¹).val := inv_le_inv' (le_max_right α β)
  refine ⟨max α β,?_⟩
  rintro q ⟨p,rfl⟩ i
  change ((max α β)⁻¹).val ≤ Values.vrv ((X.portMap hc f p).val.2 i) ∧
    Values.vrv ((X.portMap hc f p).val.2 i) ≤ (max α β).val
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [RVRefinementFrame.portMap_value,Fin.append_left] using
      And.intro (hloA.trans (hα (f (X.oldPoint p)).val (f (X.oldPoint p)).property j).1)
        ((hα (f (X.oldPoint p)).val (f (X.oldPoint p)).property j).2.trans (show α.val ≤ (max α β).val from le_max_left _ _))
  · simpa only [RVRefinementFrame.portMap_value,Fin.append_right] using
      And.intro (hloB.trans (hβ p.val p.property j).1)
        ((hβ p.val p.property j).2.trans (show β.val ≤ (max α β).val from le_max_right _ _))

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def RVRefinementFrame.portTarget
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : RVRefinementFrame A) (f : Map A B) (hf : Function.Bijective f) (π : Fin r → Fin s)
    (hRetain : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i)
    (hB : ProperInvariant S B.carrier) (hBD : VFDoublyBounded B.carrier) : RVRefinementFrame B := by
  let Y := (retainedRVOutputMap hc (f.comp X.oldMap)).image
  have hD := X.port_target_doublyBounded hc f hBD
  have hR := X.port_target_rvBounded hc f hB.rvBounded
  have hFib := X.port_target_fibres hc f hf π hRetain
  have hProper : ProperInvariant S Y.carrier := by
    obtain ⟨α,hα⟩ := hD
    apply (lemma_6_5 h00 hc hκ hs hv Y.carrier Y.definable ⟨α⁻¹,fun p hp i => (hα p hp i).1⟩ hR).mpr
    intro v
    cases hFib v with
    | inl he => exact he.symm ▸ isClopen_empty
    | inr he => exact he.symm ▸ hB.clopen_fibres hv _
  exact ⟨s+X.arity,Y,Fin.castAdd X.arity,hProper,hD,hFib⟩

end DiamondIntegral.Section6
