import «section 5».VarietyImmersionPartitions

/-! Actual common refinements of equivariant immersed presentations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] Object.reduced reducedPullback_isReduced
  schemeReductionMap_isClosedImmersion
variable {X Y Z : Object}

theorem reducedPullbackFst_immersion (f : Morphism Y X) (g : Morphism Z X)
    [IsImmersion g.hom] : IsImmersion (reducedPullbackFst f.hom g.hom) := by
  unfold reducedPullbackFst
  infer_instance

theorem reducedPullbackSnd_immersion (f : Morphism Y X) (g : Morphism Z X)
    [IsImmersion f.hom] : IsImmersion (reducedPullbackSnd f.hom g.hom) := by
  unfold reducedPullbackSnd
  infer_instance

attribute [local instance] reducedPullbackFst_immersion reducedPullbackSnd_immersion

theorem commonImmersion_invariant (f : Morphism Y X) (g : Morphism Z X) :
    Y.Invariant (Set.range (reducedPullbackFst f.hom g.hom)) := by
  intro h y
  rw [reducedPullbackFst_range]
  change f.hom (schemePointAction Y.action h y) ∈ Set.range g.hom ↔ f.hom y ∈ Set.range g.hom
  have he := congrArg (fun m : Y.scheme ⟶ X.scheme => m y) (f.equivariant h)
  change f.hom (schemePointAction Y.action h y) = schemePointAction X.action h (f.hom y) at he
  rw [he]
  exact g.range_invariant h (f.hom y)

def commonImmersionObject (f : Morphism Y X) (g : Morphism Z X) [IsImmersion g.hom] : Object :=
  invariantImmersedObject Y (reducedPullbackFst f.hom g.hom) (commonImmersion_invariant f g)

def commonImmersionLeft (f : Morphism Y X) (g : Morphism Z X) [IsImmersion g.hom] :
    Morphism (commonImmersionObject f g) Y :=
  invariantImmersedInclusion Y (reducedPullbackFst f.hom g.hom) (commonImmersion_invariant f g)

def commonImmersionRight (f : Morphism Y X) (g : Morphism Z X) [IsImmersion g.hom] :
    Morphism (commonImmersionObject f g) Z where
  hom := reducedPullbackSnd f.hom g.hom
  overC := by
    change reducedPullbackSnd f.hom g.hom ≫ Z.toC = reducedPullbackFst f.hom g.hom ≫ Y.toC
    rw [← g.overC, ← f.overC, ← Category.assoc, ← Category.assoc, reducedPullback_condition]
  equivariant h := by
    apply (cancel_mono g.hom).mp
    let P := commonImmersionObject f g
    let a := (commonImmersionLeft f g).hom
    let b := reducedPullbackSnd f.hom g.hom
    have he : a ≫ f.hom = b ≫ g.hom := reducedPullback_condition _ _
    change ((P.action h).asIso.hom ≫ b) ≫ g.hom = (b ≫ (Z.action h).asIso.hom) ≫ g.hom
    calc
      ((P.action h).asIso.hom ≫ b) ≫ g.hom = (P.action h).asIso.hom ≫ (a ≫ f.hom) := by
        rw [Category.assoc, he]
      _ = (a ≫ (Y.action h).asIso.hom) ≫ f.hom := by
        rw [← Category.assoc, (commonImmersionLeft f g).equivariant]
      _ = (a ≫ f.hom) ≫ (X.action h).asIso.hom := by
        rw [Category.assoc, f.equivariant, Category.assoc]
      _ = (b ≫ g.hom) ≫ (X.action h).asIso.hom := by rw [he]
      _ = (b ≫ (Z.action h).asIso.hom) ≫ g.hom := by
        rw [Category.assoc, Category.assoc, g.equivariant]

structure ImmersedPresentation (X : Object) (D : Set X.scheme) where
  index : Type
  finite : Fintype index
  piece : index → Object
  inclusion : ∀ i, Morphism (piece i) X
  immersion : ∀ i, IsImmersion (inclusion i).hom
  contained : ∀ i, Set.range (inclusion i).hom ⊆ D
  partition : ∀ x, x ∈ D ↔ ∃! i, x ∈ Set.range (inclusion i).hom

def ImmersedPresentation.value {D : Set X.scheme} (c : ImmersedPresentation X D) : Ring :=
  letI := c.finite
  ∑ i, objectClass (c.piece i)

theorem immersed_presentation_independent {D : Set X.scheme}
    (c d : ImmersedPresentation X D) : c.value = d.value := by
  letI := c.finite
  letI := d.finite
  letI (i : c.index) := c.immersion i
  letI (j : d.index) := d.immersion j
  let P := fun i j => commonImmersionObject (c.inclusion i) (d.inclusion j)
  have hc (i : c.index) : objectClass (c.piece i) = ∑ j, objectClass (P i j) := by
    letI (j : d.index) : IsImmersion (commonImmersionLeft (c.inclusion i) (d.inclusion j)).hom :=
      reducedPullbackFst_immersion _ _
    apply objectClass_finite_immersed_partition (c.piece i) (P i)
      (fun j => commonImmersionLeft (c.inclusion i) (d.inclusion j))
    intro x
    have hxD := c.contained i (Set.mem_range_self x)
    have hp := (d.partition ((c.inclusion i).hom x)).mp hxD
    have he (j : d.index) : x ∈ Set.range (commonImmersionLeft (c.inclusion i) (d.inclusion j)).hom ↔
        (c.inclusion i).hom x ∈ Set.range (d.inclusion j).hom := by
      change x ∈ Set.range (reducedPullbackFst (c.inclusion i).hom (d.inclusion j).hom) ↔ _
      rw [reducedPullbackFst_range]
      rfl
    obtain ⟨j, hj, huniq⟩ := hp
    exact ⟨j, (he j).mpr hj, fun k hk => huniq k ((he k).mp hk)⟩
  have hd (j : d.index) : objectClass (d.piece j) = ∑ i, objectClass (P i j) := by
    letI (i : c.index) : IsImmersion (commonImmersionRight (c.inclusion i) (d.inclusion j)).hom :=
      reducedPullbackSnd_immersion _ _
    apply objectClass_finite_immersed_partition (d.piece j) (fun i => P i j)
      (fun i => commonImmersionRight (c.inclusion i) (d.inclusion j))
    intro y
    have hyD := d.contained j (Set.mem_range_self y)
    have hp := (c.partition ((d.inclusion j).hom y)).mp hyD
    have he (i : c.index) : y ∈ Set.range (commonImmersionRight (c.inclusion i) (d.inclusion j)).hom ↔
        (d.inclusion j).hom y ∈ Set.range (c.inclusion i).hom := by
      change y ∈ Set.range (reducedPullbackSnd (c.inclusion i).hom (d.inclusion j).hom) ↔ _
      rw [reducedPullbackSnd_range]
      rfl
    obtain ⟨i, hi, huniq⟩ := hp
    exact ⟨i, (he i).mpr hi, fun k hk => huniq k ((he k).mp hk)⟩
  change (∑ i, objectClass (c.piece i)) = ∑ j, objectClass (d.piece j)
  simp_rw [hc, hd]
  exact Finset.sum_comm

end DiamondIntegral.Section5.EquivariantVariety
