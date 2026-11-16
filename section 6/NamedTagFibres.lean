import «section 6».RVContractedGammaForms

/-! Actual fixed-old-tag source domains with all tag coordinates named
in the stated base. Their images under a whole-fiber bijection are the
full corresponding target fibers, not just a pointwise inclusion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}

def namedTagFiber (A : DefSet (rawMixedSpace (M := M) n r) S)
    (u : Fin r → RVInfinity M) (hu : ∀ i, (u i).val ∈ S) : DefSet (rawMixedSpace (M := M) n r) S := by
  have hEq (i : Fin r) : S.Definable LRV {z : Fin n ⊕ Fin r → M | z (.inr i) = (u i).val} :=
    (Set.DefinableFun.proj (L := LRV) (A := S)).ofPred_eq (LRV.definableFun_const _ (hu i))
  have hAll := Set.definable_iInter_of_finite hEq
  refine ⟨{p | p ∈ A.carrier ∧ p.2 = u},?_⟩
  apply (mixed_definable_iff_values_image S _).mpr
  have hA := (mixed_definable_iff_values_image S _).mp A.definable
  convert hA.inter hAll using 1
  ext z
  constructor
  · rintro ⟨p,⟨hp,hpu⟩,rfl⟩
    refine ⟨⟨p,hp,rfl⟩,?_⟩
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    intro i
    exact congrArg (fun v : Fin r → RVInfinity M => (v i).val) hpu
  · rintro ⟨⟨p,hp,hpz⟩,hEq⟩
    refine ⟨p,⟨hp,?_⟩,hpz⟩
    funext i
    apply Subtype.ext
    have h := Set.mem_iInter.mp hEq i
    change z (.inr i) = (u i).val at h
    exact (congrFun hpz (.inr i)).trans h

theorem namedTagFiber_subset (A : DefSet (rawMixedSpace (M := M) n r) S)
    (u : Fin r → RVInfinity M) (hu : ∀ i, (u i).val ∈ S) : (namedTagFiber A u hu).carrier ⊆ A.carrier :=
  fun _ hp => hp.1

theorem namedTagFiber_projection (A : DefSet (rawMixedSpace (M := M) n r) S)
    (u : Fin r → RVInfinity M) (hu : ∀ i, (u i).val ∈ S) (x : Fin n → VF M) :
    (∃ p : namedTagFiber A u hu, p.val.1 = x) ↔ (x,u) ∈ A.carrier := by
  constructor
  · rintro ⟨p,hp⟩
    have he : p.val = (x,u) := Prod.ext hp p.property.2
    exact he ▸ p.property.1
  · intro hx
    exact ⟨⟨(x,u),hx,rfl⟩,rfl⟩

variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}

theorem namedTagFiber_image (f : Map A B) (h : MapsWholeTagFibres f) (p : A)
    (hu : ∀ i, (p.val.2 i).val ∈ S) :
    (f.restrict (namedTagFiber_subset A p.val.2 hu)).image.carrier =
      {b | b ∈ B.carrier ∧ b.2 = (f p).val.2} := by
  ext b
  constructor
  · rintro ⟨q,rfl⟩
    let a : A := ⟨q.val,q.property.1⟩
    exact ⟨(f a).property,h.labels f a p q.property.2⟩
  · rintro ⟨hb,hTag⟩
    obtain ⟨a,ha,hfa⟩ := (h p ⟨b,hb⟩).mp hTag
    let q : namedTagFiber A p.val.2 hu := ⟨a.val,a.property,ha⟩
    exact ⟨q,congrArg Subtype.val hfa⟩

theorem namedTagFiber_image_projection (f : Map A B) (h : MapsWholeTagFibres f) (p : A)
    (hu : ∀ i, (p.val.2 i).val ∈ S) (x : Fin m → VF M) :
    (∃ b : (f.restrict (namedTagFiber_subset A p.val.2 hu)).image, b.val.1 = x) ↔
      (x,(f p).val.2) ∈ B.carrier := by
  constructor
  · rintro ⟨b,hb⟩
    have hMem := (Set.ext_iff.mp (namedTagFiber_image f h p hu) b.val).mp b.property
    have he : b.val = (x,(f p).val.2) := Prod.ext hb hMem.2
    exact he ▸ hMem.1
  · intro hx
    have hb : (x,(f p).val.2) ∈ (f.restrict (namedTagFiber_subset A p.val.2 hu)).image.carrier :=
      (Set.ext_iff.mp (namedTagFiber_image f h p hu) _).mpr ⟨hx,rfl⟩
    exact ⟨⟨_,hb⟩,rfl⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem namedTagFiber_open (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hOpen : ∀ u, IsOpen (vfFibre A.carrier u)) (u : Fin r → RVInfinity M)
    (hu : ∀ i, (u i).val ∈ S) : ∀ v, IsOpen (vfFibre (namedTagFiber A u hu).carrier v) := by
  intro v
  by_cases hv : v = u
  · subst v
    have he : vfFibre (namedTagFiber A u hu).carrier u = vfFibre A.carrier u := by
      ext x
      change ((x,u) ∈ A.carrier ∧ u = u) ↔ (x,u) ∈ A.carrier
      exact and_iff_left rfl
    rw [he]
    exact hOpen u
  · have he : vfFibre (namedTagFiber A u hu).carrier v = ∅ := by
      ext x
      change ((x,v) ∈ A.carrier ∧ v = u) ↔ False
      tauto
    rw [he]
    exact isOpen_empty

end DiamondIntegral.Section6
