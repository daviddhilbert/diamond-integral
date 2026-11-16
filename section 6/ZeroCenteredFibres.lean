import «section 6».ZeroCenteredGeometry

/-! Actual graph fibers of the preliminary zero-centered preparation.
Every fixed branch is a constant translation of a clopen source fiber. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.ZeroCenteredData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem graphFibre_iff (D : ZeroCenteredData A)
    (u : Fin r → RVInfinity M) (v : Fin (n+r) → RVInfinity M)
    (a b : Fin n → VF M) : graphFibre D.bijection u v a b ↔
      (a,u) ∈ A.carrier ∧ D.point (a,u) = (b,v) := by
  constructor
  · rintro ⟨p,hp,hfp⟩
    change D.point p.val = (b,v) at hfp
    exact ⟨hp ▸ p.property,(congrArg D.point hp).symm.trans hfp⟩
  · rintro ⟨ha,he⟩
    exact ⟨⟨(a,u),ha⟩,rfl,he⟩

theorem graphSource_iff (D : ZeroCenteredData A)
    (u : Fin r → RVInfinity M) (v : Fin (n+r) → RVInfinity M) (a : Fin n → VF M) :
    a ∈ graphFibreSource D.bijection u v ↔
      (a,u) ∈ A.carrier ∧ D.tags u (D.core (a,u)) = v := by
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨ha,he⟩ := (D.graphFibre_iff u v a b).mp hb
    exact ⟨ha,congrArg Prod.snd he⟩
  · rintro ⟨ha,he⟩
    exact ⟨(D.point (a,u)).1,(D.graphFibre_iff u v _ _).mpr ⟨ha,Prod.ext rfl he⟩⟩

theorem graphSource_tags (D : ZeroCenteredData A)
    (h00 : M ⊨ Axioms.ACVF00) (u : Fin r → RVInfinity M) (b : Fin n → Bool) :
    graphFibreSource D.bijection u (D.tags u b) = D.branch u b := by
  ext a
  rw [D.graphSource_iff]
  exact and_congr_right (fun _ => ⟨fun he => D.tags_injective h00 u he,
    congrArg (D.tags u)⟩)

theorem graphSource_empty (D : ZeroCenteredData A)
    (u : Fin r → RVInfinity M) (v : Fin (n+r) → RVInfinity M)
    (hv : ¬ ∃ b, D.tags u b = v) : graphFibreSource D.bijection u v = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact hv ⟨D.core (a,u),((D.graphSource_iff u v a).mp ha).2⟩

theorem graphMap_eq_translation (D : ZeroCenteredData A)
    (h00 : M ⊨ Axioms.ACVF00) (u : Fin r → RVInfinity M) (b : Fin n → Bool) :
    Set.EqOn (graphFibreMap D.bijection u (D.tags u b))
      (fun x => x + D.shift b) (D.branch u b) := by
  intro a ha
  have hsource : a ∈ graphFibreSource D.bijection u (D.tags u b) :=
    (D.graphSource_tags h00 u b).symm ▸ ha
  have hg := (D.graphFibre_iff u (D.tags u b) a _).mp
    (graphFibreMap_graph D.bijection u (D.tags u b) hsource)
  exact (congrArg Prod.fst hg.2).symm.trans (congrArg Prod.fst (D.point_on_branch u b ha))

theorem graphRange_tags (D : ZeroCenteredData A)
    (h00 : M ⊨ Axioms.ACVF00) (u : Fin r → RVInfinity M) (b : Fin n → Bool) :
    graphFibreRange D.bijection u (D.tags u b) =
      (fun x => x + D.shift b) '' D.branch u b := by
  rw [graphFibreRange_eq_image,D.graphSource_tags h00]
  exact (D.graphMap_eq_translation h00 u b).image_eq

theorem graphSource_isClopen (D : ZeroCenteredData A)
    (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (u : Fin r → RVInfinity M) (v : Fin (n+r) → RVInfinity M) :
    IsClopen (graphFibreSource D.bijection u v) := by
  classical
  by_cases he : ∃ b, D.tags u b = v
  · obtain ⟨b,rfl⟩ := he
    rw [D.graphSource_tags h00]
    exact D.branch_isClopen hv u b
  · rw [D.graphSource_empty u v he]
    exact isClopen_empty

theorem graph_continuous (D : ZeroCenteredData A)
    (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    ContinuousOnGraphFibres D.bijection := by
  classical
  intro u v
  by_cases he : ∃ b, D.tags u b = v
  · obtain ⟨b,rfl⟩ := he
    rw [D.graphSource_tags h00]
    have hshear : ContinuousOn (fun x => x + D.shift b) (D.branch u b) :=
      (continuous_id.add_const (D.shift b)).continuousOn
    exact hshear.congr (D.graphMap_eq_translation h00 u b)
  · rw [D.graphSource_empty u v he]
    exact continuousOn_empty _

theorem graphRange_isOpen (D : ZeroCenteredData A)
    (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (u : Fin r → RVInfinity M) (v : Fin (n+r) → RVInfinity M) :
    IsOpen (graphFibreRange D.bijection u v) := by
  classical
  by_cases he : ∃ b, D.tags u b = v
  · obtain ⟨b,rfl⟩ := he
    rw [D.graphRange_tags h00]
    exact (Homeomorph.addRight (D.shift b)).isOpenMap _ (D.branch_isClopen hv u b).isOpen
  · rw [graphFibreRange_eq_image,D.graphSource_empty u v he,Set.image_empty]
    exact isOpen_empty

theorem graphRange_isClopen (D : ZeroCenteredData A)
    (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (u : Fin r → RVInfinity M) (v : Fin (n+r) → RVInfinity M) :
    IsClopen (graphFibreRange D.bijection u v) := by
  classical
  by_cases he : ∃ b, D.tags u b = v
  · obtain ⟨b,rfl⟩ := he
    rw [D.graphRange_tags h00]
    exact ⟨(Homeomorph.addRight (D.shift b)).isClosedMap _ (D.branch_isClopen hv u b).isClosed,
      (Homeomorph.addRight (D.shift b)).isOpenMap _ (D.branch_isClopen hv u b).isOpen⟩
  · rw [graphFibreRange_eq_image,D.graphSource_empty u v he,Set.image_empty]
    exact isClopen_empty

theorem image_fibre (D : ZeroCenteredData A) (v : Fin (n+r) → RVInfinity M) :
    vfFibre D.map.image.carrier v = graphFibreRange D.bijection (v ∘ Fin.natAdd n) v := by
  ext b
  constructor
  · rintro ⟨p,he⟩
    change D.point p.val = (b,v) at he
    have hu : p.val.2 = v ∘ Fin.natAdd n := funext (fun i => by
      simpa only [point,tags,Fin.append_right,Function.comp_apply] using
        congrArg (fun q : Mixed M n (n+r) => q.2 (Fin.natAdd n i)) he)
    refine ⟨p.val.1,(D.graphFibre_iff _ _ _ _).mpr ?_⟩
    exact ⟨hu ▸ p.property,by rw [← hu]; exact he⟩
  · rintro ⟨a,ha⟩
    obtain ⟨hp,he⟩ := (D.graphFibre_iff _ _ _ _).mp ha
    exact ⟨⟨(a,v ∘ Fin.natAdd n),hp⟩,he⟩

end DiamondIntegral.Section6.ZeroCenteredData
