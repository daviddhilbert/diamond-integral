import «section 6».BinaryReleasedPreparation

/-! The actual retained core is the true branch tag in the full
regularized image. Its complete original-base graph, proper invariance,
double bounds and exact source description are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem rvTagSlice_properInvariant
    (A : DefSet (rawMixedSpace (M := M) n r) S) (j : Fin r) (b : Bool)
    (hA : ProperInvariant S A.carrier) : ProperInvariant S (rvTagSlice A j b).carrier := by
  have hsub : (rvTagSlice A j b).carrier ⊆ A.carrier := fun _ h => h.1
  refine ⟨(rvTagSlice A j b).definable,hA.vfBounded.mono hsub,hA.rvBounded.mono hsub,fun u => ?_⟩
  obtain ⟨α,hα,hInv⟩ := hA.radii u
  exact ⟨α,hα,fun a c hac => and_congr (hInv a c hac) Iff.rfl⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace CentripetalData

variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def coreRegularizedImage (D : CentripetalData (G := G) A) :
    DefSet (rawMixedSpace (M := M) n (n+(1+r))) S :=
  rvTagSlice (regularizeMap D.map.image).image (Fin.natAdd n (Fin.castAdd r (0 : Fin 1))) true

theorem regularized_core_flag (D : CentripetalData (G := G) A) (a : Mixed M n r) :
    (regularize (D.point a)).2 (Fin.natAdd n (Fin.castAdd r (0 : Fin 1))) =
      branchTag (M := M) (D.core a) := by
  simp only [regularize,point,Fin.append_right,Fin.append_left]

theorem mem_coreRegularizedImage (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (q : Mixed M n (n+(1+r))) :
    q ∈ D.coreRegularizedImage.carrier ↔
      ∃ a, a ∈ A.carrier ∧ D.core a = true ∧ regularize (D.point a) = q := by
  constructor
  · rintro ⟨⟨z,hz⟩,hflag⟩
    obtain ⟨a,ha⟩ := z.property
    have he : regularize (D.point a.val) = q := (congrArg regularize ha).trans hz
    have hh := congrArg (fun p : Mixed M n (n+(1+r)) =>
      p.2 (Fin.natAdd n (Fin.castAdd r (0 : Fin 1)))) he
    rw [D.regularized_core_flag] at hh
    exact ⟨a.val,a.property,branchTag_injective h00 (hh.trans hflag),he⟩
  · rintro ⟨a,ha,hcore,he⟩
    refine ⟨⟨D.bijection ⟨a,ha⟩,he⟩,?_⟩
    rw [← he,D.regularized_core_flag,hcore]

theorem coreRegularizedImage_subset (D : CentripetalData (G := G) A) :
    D.coreRegularizedImage.carrier ⊆ (regularizeMap D.map.image).image.carrier := fun _ h => h.1

theorem coreRegularizedImage_doublyBounded (D : CentripetalData (G := G) A) :
    VFDoublyBounded D.coreRegularizedImage.carrier := by
  obtain ⟨γ,hγ⟩ := regularized_vfDoublyBounded D.image_vfDoublyBounded
  exact ⟨γ,fun p hp => hγ p (D.coreRegularizedImage_subset hp)⟩

theorem coreRegularizedImage_tagged (D : CentripetalData (G := G) A) :
    ∀ p ∈ D.coreRegularizedImage.carrier, ∀ q ∈ D.coreRegularizedImage.carrier,
      p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  have ht : ∀ p ∈ (regularizeMap D.map.image).image.carrier,
      ∀ q ∈ (regularizeMap D.map.image).image.carrier,
      p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
    rw [regularization_carrier]
    exact regularized_tagged _
  exact fun p hp q hq => ht p (D.coreRegularizedImage_subset hp) q (D.coreRegularizedImage_subset hq)

theorem coreRegularizedImage_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) A) : ProperInvariant S D.coreRegularizedImage.carrier :=
  rvTagSlice_properInvariant _ _ _ (regularization_properInvariant h00 hc hκ hs hv _
    (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded)

end CentripetalData
end DiamondIntegral.Section6
