import «section 6».RVTagMatching
import «section 6».UnaryBoundaryCoreComponents

/-! Whole-fibre matching is preserved under actual bijective changes
that preserve exactly equality of old RV labels. All conjugations use
the definable inverse maps and keep the original parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s t u : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}
variable {C : DefSet (rawMixedSpace (M := M) n t) S} {D : DefSet (rawMixedSpace (M := M) m u) S}

theorem MapsWholeTagFibres.tags_iff (f : Map A B) (h : MapsWholeTagFibres f)
    (hf : Function.Injective f) (p q : A) : (f p).val.2=(f q).val.2 ↔ p.val.2=q.val.2 := by
  constructor
  · intro he
    obtain ⟨a,ha,hfa⟩ := (h q (f p)).mp he
    have hap : a=p := hf hfa
    exact (congrArg (fun z : A => z.val.2) hap).symm.trans ha
  · exact h.labels f p q

theorem mapsWholeTagFibres_of_tag_equivalence (f : Map A B) (hf : Function.Surjective f)
    (hTags : ∀ p q : A,(f p).val.2=(f q).val.2 ↔ p.val.2=q.val.2) : MapsWholeTagFibres f := by
  intro p b
  obtain ⟨a,rfl⟩ := hf b
  constructor
  · intro h
    exact ⟨a,(hTags a p).mp h,rfl⟩
  · rintro ⟨c,hc,hca⟩
    exact (congrArg (fun z : B => z.val.2) hca).symm.trans ((hTags c p).mpr hc)

theorem MapsWholeTagFibres.conjugate (f : Map A B) (hf : Function.Bijective f) (h : MapsWholeTagFibres f)
    (α : Map A C) (hα : Function.Bijective α) (β : Map B D) (hβ : Function.Bijective β)
    (hαTags : ∀ p q : A,(α p).val.2=(α q).val.2 ↔ p.val.2=q.val.2)
    (hβTags : ∀ p q : B,(β p).val.2=(β q).val.2 ↔ p.val.2=q.val.2) :
    MapsWholeTagFibres (β.comp (f.comp (α.inverse hα))) := by
  have hInv : Function.Surjective (α.inverse hα) := by
    intro a
    exact ⟨α a,Map.inverse_apply α hα a⟩
  have hSurj : Function.Surjective (β.comp (f.comp (α.inverse hα))) :=
    hβ.surjective.comp (hf.surjective.comp hInv)
  apply mapsWholeTagFibres_of_tag_equivalence (β.comp (f.comp (α.inverse hα))) hSurj
  intro p q
  change (β (f (α.inverse hα p))).val.2=(β (f (α.inverse hα q))).val.2 ↔ p.val.2=q.val.2
  rw [hβTags,h.tags_iff f hf.injective]
  have hh := hαTags (α.inverse hα p) (α.inverse hα q)
  simpa only [Map.apply_inverse] using hh.symm

end DiamondIntegral.Section6
