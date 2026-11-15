import «section 5».SchemeBranchPoints

/-! The relation on all scheme points defined by a family of reduced
affine graph schemes. Complex-point uniqueness proves actual scheme-point
uniqueness; every branch certificate realizes this same relation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
variable {S T J : Type} [CommRing S] [CommRing T] [Algebra ℂ S] [Algebra ℂ T]
variable (A : J → Type) [∀ j, CommRing (A j)] [∀ j, Algebra ℂ (A j)]
variable (f : ∀ j, S →ₐ[ℂ] A j) (a : ∀ j, T →ₐ[ℂ] A j)

def affineBranchRelation (x : Spec (.of S)) (y : Spec (.of T)) : Prop :=
  ∃ (j : J) (z : Spec (.of (A j))),
    Spec.map (CommRingCat.ofHom (f j).toRingHom) z = x ∧
      Spec.map (CommRingCat.ofHom (a j).toRingHom) z = y

theorem affineBranchRelation_left_functional
    [∀ j, Algebra.FiniteType ℂ (A j)] [∀ j, _root_.IsReduced (A j)]
    [∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (f j).toRingHom))]
    (hc : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp (f i) = ψ.comp (f j) → φ.comp (a i) = ψ.comp (a j))
    {x : Spec (.of S)} {y z : Spec (.of T)}
    (hy : affineBranchRelation A f a x y) (hz : affineBranchRelation A f a x z) : y = z := by
  obtain ⟨i, u, hux, huy⟩ := hy
  obtain ⟨j, v, hvx, hvz⟩ := hz
  have h := affine_branches_point_functional (f i) (f j) (a i) (a j) (hc i j) u v (hux.trans hvx.symm)
  exact huy.symm.trans (h.trans hvz)

theorem affineBranchRelation_right_functional
    [∀ j, Algebra.FiniteType ℂ (A j)] [∀ j, _root_.IsReduced (A j)]
    [∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (a j).toRingHom))]
    (hc : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp (a i) = ψ.comp (a j) → φ.comp (f i) = ψ.comp (f j))
    {x z : Spec (.of S)} {y : Spec (.of T)}
    (hx : affineBranchRelation A f a x y) (hz : affineBranchRelation A f a z y) : x = z := by
  obtain ⟨i, u, hux, huy⟩ := hx
  obtain ⟨j, v, hvz, hvy⟩ := hz
  have h := affine_branches_point_functional (a i) (a j) (f i) (f j) (hc i j) u v (huy.trans hvy.symm)
  exact hux.symm.trans (h.trans hvz)

variable {A f a}

theorem AffineBranchCertificate.point {X : Scheme}
    {base : X ⟶ Spec (.of S)} {F : X ⟶ Spec (.of T)}
    (c : AffineBranchCertificate A f a base F) (x : X) :
    affineBranchRelation A f a (base x) (F x) := by
  obtain ⟨i, y, rfl⟩ := c.cover.exists_eq x
  refine ⟨c.index i, c.lift i y, ?_, ?_⟩
  · exact congrArg (fun h => h y) (c.input_fac i)
  · exact congrArg (fun h => h y) (c.output_fac i)

variable (A f a)

theorem affineBranchRelation_mem_left {x : Spec (.of S)} {y : Spec (.of T)}
    (h : affineBranchRelation A f a x y) :
    x ∈ ⋃ j, Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom)) := by
  obtain ⟨j, z, hz, _⟩ := h
  exact Set.mem_iUnion.mpr ⟨j, z, hz⟩

theorem affineBranchRelation_mem_right {x : Spec (.of S)} {y : Spec (.of T)}
    (h : affineBranchRelation A f a x y) :
    y ∈ ⋃ j, Set.range (Spec.map (CommRingCat.ofHom (a j).toRingHom)) := by
  obtain ⟨j, z, _, hz⟩ := h
  exact Set.mem_iUnion.mpr ⟨j, z, hz⟩

end DiamondIntegral.Section5
