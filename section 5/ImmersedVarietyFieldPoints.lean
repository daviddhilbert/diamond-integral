import «section 5».ComplexVarietyCharts
import «section 5».ReducedImmersionLifts

/-! A finite immersed partition covers all extension-field scheme
points uniquely. This is an actual factorization through each reduced
stratum, not a statement only about complex closed points. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] EquivariantVariety.Object.reduced
variable {K : Type} [Field K] [Algebra ℂ K]

def EquivariantVariety.Object.fieldPoint (X : EquivariantVariety.Object) :=
  {p : Spec (.of K) ⟶ X.scheme | p ≫ X.toC = Spec.map (CommRingCat.ofHom (algebraMap ℂ K))}

def EquivariantVariety.Morphism.fieldPointMap {X Y : EquivariantVariety.Object}
    (f : EquivariantVariety.Morphism X Y) (p : X.fieldPoint (K := K)) : Y.fieldPoint (K := K) :=
  ⟨p.val ≫ f.hom,by
    change (p.val ≫ f.hom) ≫ Y.toC = _
    rw [Category.assoc,f.overC]
    exact p.property⟩

theorem EquivariantVariety.ImmersedPresentation.fieldPoint_factor
    {X : EquivariantVariety.Object} (c : EquivariantVariety.ImmersedPresentation X Set.univ)
    (p : X.fieldPoint (K := K)) :
    ∃! i, ∃ q : (c.piece i).fieldPoint (K := K), (c.inclusion i).fieldPointMap q = p := by
  let η : Spec (.of K) := default
  obtain ⟨i,hi,huniq⟩ := (c.partition (p.val η)).mp (Set.mem_univ _)
  letI := c.immersion i
  have hR : Set.range p.val ⊆ Set.range (c.inclusion i).hom := by
    rintro _ ⟨y,rfl⟩
    exact (Subsingleton.elim y η) ▸ hi
  obtain ⟨L,hL,_⟩ := reduced_immersion_lift (c.inclusion i).hom p.val hR
  have hLC : L ≫ (c.piece i).toC = Spec.map (CommRingCat.ofHom (algebraMap ℂ K)) := by
    rw [← (c.inclusion i).overC,← Category.assoc,hL]
    exact p.property
  refine ⟨i,⟨⟨L,hLC⟩,Subtype.ext hL⟩,?_⟩
  rintro j ⟨q,hq⟩
  apply huniq j
  have he := congrArg (fun r : X.fieldPoint (K := K) => r.val η) hq
  exact ⟨q.val η,he⟩

def EquivariantVariety.ImmersedPresentation.fieldPointPartitionMap
    {X : EquivariantVariety.Object} (c : EquivariantVariety.ImmersedPresentation X Set.univ)
    (q : Σ i,(c.piece i).fieldPoint (K := K)) : X.fieldPoint (K := K) :=
  (c.inclusion q.1).fieldPointMap q.2

theorem EquivariantVariety.ImmersedPresentation.fieldPointPartitionMap_bijective
    {X : EquivariantVariety.Object} (c : EquivariantVariety.ImmersedPresentation X Set.univ) :
    Function.Bijective (c.fieldPointPartitionMap (K := K)) := by
  constructor
  · rintro ⟨i,p⟩ ⟨j,q⟩ he
    obtain ⟨k,hk,huniq⟩ := c.fieldPoint_factor (c.fieldPointPartitionMap ⟨i,p⟩)
    have hi : i = k := huniq i ⟨p,rfl⟩
    have hj : j = k := huniq j ⟨q,he.symm⟩
    have hij : i = j := hi.trans hj.symm
    cases hij
    letI := c.immersion i
    have hpq : p = q := by
      apply Subtype.ext
      apply (cancel_mono (c.inclusion i).hom).mp
      exact congrArg Subtype.val he
    exact congrArg (fun q : (c.piece i).fieldPoint (K := K) => (⟨i,q⟩ : Σ i,(c.piece i).fieldPoint (K := K))) hpq
  · intro p
    obtain ⟨i,⟨q,hq⟩,_⟩ := c.fieldPoint_factor p
    exact ⟨⟨i,q⟩,hq⟩

def EquivariantVariety.ImmersedPresentation.fieldPointEquiv
    {X : EquivariantVariety.Object} (c : EquivariantVariety.ImmersedPresentation X Set.univ) :
    (Σ i,(c.piece i).fieldPoint (K := K)) ≃ X.fieldPoint (K := K) :=
  Equiv.ofBijective c.fieldPointPartitionMap c.fieldPointPartitionMap_bijective

end DiamondIntegral.Section5
