import «section 6».RelativeApertureCharts

/-! Complete graph fibers of the concrete finite-aperture map. The old
RV tags are recoverable from the output. Source fibers are the clopen
branches, and the fiber maps are the actual triangular shears. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.RelativeApertureData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem graphFibre_iff (D : RelativeApertureData (G := G) A)
    (u : Fin r → RVInfinity M) (v : Fin (1+r) → RVInfinity M)
    (a b : Fin n → VF M) : graphFibre D.bijection u v a b ↔
      (a,u) ∈ A.carrier ∧ D.point (a,u) = (b,v) := by
  constructor
  · rintro ⟨p,hp,hfp⟩
    change D.point p.val = (b,v) at hfp
    exact ⟨hp ▸ p.property,(congrArg D.point hp).symm.trans hfp⟩
  · rintro ⟨ha,he⟩
    exact ⟨⟨(a,u),ha⟩,rfl,he⟩

theorem graphSource_iff (D : RelativeApertureData (G := G) A)
    (u : Fin r → RVInfinity M) (v : Fin (1+r) → RVInfinity M) (a : Fin n → VF M) :
    a ∈ graphFibreSource D.bijection u v ↔
      (a,u) ∈ A.carrier ∧ D.outputTags u (D.core (a,u)) = v := by
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨ha,he⟩ := (D.graphFibre_iff u v a b).mp hb
    exact ⟨ha,congrArg Prod.snd he⟩
  · rintro ⟨ha,he⟩
    exact ⟨(D.point (a,u)).1,(D.graphFibre_iff u v _ _).mpr ⟨ha,Prod.ext rfl he⟩⟩

theorem graphSource_outputTags (D : RelativeApertureData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (u : Fin r → RVInfinity M) (b : Bool) :
    graphFibreSource D.bijection u (D.outputTags u b) = D.branch u b := by
  ext a
  rw [D.graphSource_iff]
  exact and_congr_right (fun _ => ⟨fun he => D.outputTags_injective h00 u he,
    congrArg (D.outputTags u)⟩)

theorem graphSource_empty (D : RelativeApertureData (G := G) A)
    (u : Fin r → RVInfinity M) (v : Fin (1+r) → RVInfinity M)
    (hv : ¬ ∃ b, D.outputTags u b = v) : graphFibreSource D.bijection u v = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact hv ⟨D.core (a,u),((D.graphSource_iff u v a).mp ha).2⟩

theorem graphMap_eq_shear (D : RelativeApertureData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (u : Fin r → RVInfinity M) (b : Bool) :
    Set.EqOn (graphFibreMap D.bijection u (D.outputTags u b))
      (coordinateShear D.coordinate (D.branchFocus u b)) (D.branch u b) := by
  intro a ha
  have hsource : a ∈ graphFibreSource D.bijection u (D.outputTags u b) :=
    (D.graphSource_outputTags h00 u b).symm ▸ ha
  have hg := (D.graphFibre_iff u (D.outputTags u b) a _).mp
    (graphFibreMap_graph D.bijection u (D.outputTags u b) hsource)
  exact (congrArg Prod.fst hg.2).symm.trans (congrArg Prod.fst (D.point_on_branch u b ha))

theorem graphRange_outputTags (D : RelativeApertureData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (u : Fin r → RVInfinity M) (b : Bool) :
    graphFibreRange D.bijection u (D.outputTags u b) =
      coordinateShear D.coordinate (D.branchFocus u b) '' D.branch u b := by
  rw [graphFibreRange_eq_image,D.graphSource_outputTags h00]
  exact (D.graphMap_eq_shear h00 u b).image_eq

theorem graphSource_isClopen (D : RelativeApertureData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (u : Fin r → RVInfinity M) (v : Fin (1+r) → RVInfinity M) :
    IsClopen (graphFibreSource D.bijection u v) := by
  classical
  by_cases he : ∃ b, D.outputTags u b = v
  · obtain ⟨b,rfl⟩ := he
    rw [D.graphSource_outputTags h00]
    exact D.branch_isClopen hv u b
  · rw [D.graphSource_empty u v he]
    exact isClopen_empty

theorem graph_continuous (D : RelativeApertureData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    ContinuousOnGraphFibres D.bijection := by
  classical
  intro u v
  by_cases he : ∃ b, D.outputTags u b = v
  · obtain ⟨b,rfl⟩ := he
    rw [D.graphSource_outputTags h00]
    have hshear : ContinuousOn (coordinateShear D.coordinate (D.branchFocus u b)) (D.branch u b) :=
      fun a ha => (continuousAt_coordinateShear D.coordinate (D.branchFocus u b) a
        (D.branchFocus_continuousAt hv u b ha.1)).continuousWithinAt
    exact hshear.congr (D.graphMap_eq_shear h00 u b)
  · rw [D.graphSource_empty u v he]
    exact continuousOn_empty _

theorem graphRange_isOpen (D : RelativeApertureData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (u : Fin r → RVInfinity M) (v : Fin (1+r) → RVInfinity M) :
    IsOpen (graphFibreRange D.bijection u v) := by
  classical
  by_cases he : ∃ b, D.outputTags u b = v
  · obtain ⟨b,rfl⟩ := he
    rw [D.graphRange_outputTags h00]
    exact coordinateShear_image_isOpen D.coordinate (D.branchFocus u b) _
      (D.branch_isClopen hv u b).isOpen (fun a ha => D.branchFocus_continuousAt hv u b ha.1)
  · rw [graphFibreRange_eq_image,D.graphSource_empty u v he,Set.image_empty]
    exact isOpen_empty

theorem graphRange_isClopen (D : RelativeApertureData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (u : Fin r → RVInfinity M) (v : Fin (1+r) → RVInfinity M) :
    IsClopen (graphFibreRange D.bijection u v) := by
  have hb : ∃ γ : Gamma M, ∀ x ∈ graphFibreSource D.bijection u v, ∀ i, γ.val ≤ vfValue (x i) := by
    obtain ⟨γ,hγ⟩ := D.sourceProper.vfBounded
    exact ⟨γ,fun x hx i => hγ (x,u) (graphFibreSource_subset D.bijection u v hx) i⟩
  have hclosed := (lemma_2_48 h00 hc hκ hs hv _ (graphFibreSource_definable D.bijection u v)
    (D.graphSource_isClopen h00 hv u v).isClosed hb _ (graphFibreMap_definable D.bijection u v)
    (D.graph_continuous h00 hv u v)).1
  exact ⟨(graphFibreRange_eq_image D.bijection u v).symm ▸ hclosed,D.graphRange_isOpen h00 hv u v⟩

theorem image_fibre (D : RelativeApertureData (G := G) A) (v : Fin (1+r) → RVInfinity M) :
    vfFibre D.map.image.carrier v = graphFibreRange D.bijection (v ∘ Fin.natAdd 1) v := by
  ext b
  constructor
  · rintro ⟨p,he⟩
    change D.point p.val = (b,v) at he
    have hu : p.val.2 = v ∘ Fin.natAdd 1 := funext (fun i => by
      simpa only [point,Fin.append_right,Function.comp_apply] using
        congrArg (fun q : Mixed M n (1+r) => q.2 (Fin.natAdd 1 i)) he)
    refine ⟨p.val.1,(D.graphFibre_iff _ _ _ _).mpr ?_⟩
    exact ⟨hu ▸ p.property,by rw [← hu]; exact he⟩
  · rintro ⟨a,ha⟩
    obtain ⟨hp,he⟩ := (D.graphFibre_iff _ _ _ _).mp ha
    exact ⟨⟨(a,v ∘ Fin.natAdd 1),hp⟩,he⟩

end DiamondIntegral.Section6.RelativeApertureData
