import «section 5».AffineBranchRelations
import «section 5».CertifiedInversePieces

/-! Certified regular strata for a bijective affine graph have a finite
common decomposition by actual reduced schemes immersed on both sides.
Coverage and unique membership hold on all scheme points. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] reducedPullback_isReduced
variable {S T J : Type} [CommRing S] [CommRing T] [Algebra ℂ S] [Algebra ℂ T]
variable (A : J → Type) [∀ j, CommRing (A j)] [∀ j, Algebra ℂ (A j)]
variable (f : ∀ j, S →ₐ[ℂ] A j) (a : ∀ j, T →ₐ[ℂ] A j)

structure AffineBranchStratification where
  index : Type
  finite : Fintype index
  scheme : index → Scheme
  base : ∀ i, scheme i ⟶ Spec (.of S)
  immersion : ∀ i, IsImmersion (base i)
  reduced : ∀ i, AlgebraicGeometry.IsReduced (scheme i)
  output : ∀ i, scheme i ⟶ Spec (.of T)
  certificate : ∀ i, AffineBranchCertificate A f a (base i) (output i)
  partition : ∀ x, (x ∈ ⋃ j, Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))) ↔
    ∃! i, x ∈ Set.range (base i)

variable {A f a}

def certifiedCommonPiece (c : AffineBranchStratification A f a)
    (d : AffineBranchStratification A a f) (i : c.index) (j : d.index) : Scheme :=
  reducedPullback (c.output i) (d.base j)

def certifiedCommonLeft (c : AffineBranchStratification A f a)
    (d : AffineBranchStratification A a f) (i : c.index) (j : d.index) :
    certifiedCommonPiece c d i j ⟶ c.scheme i := reducedPullbackFst _ _

def certifiedCommonRight (c : AffineBranchStratification A f a)
    (d : AffineBranchStratification A a f) (i : c.index) (j : d.index) :
    certifiedCommonPiece c d i j ⟶ d.scheme j := reducedPullbackSnd _ _

theorem certifiedCommon_immersions
    [∀ j, Algebra.FiniteType ℂ (A j)]
    (hv : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp (a i) = ψ.comp (a j) → φ.comp (f i) = ψ.comp (f j))
    (c : AffineBranchStratification A f a) (d : AffineBranchStratification A a f)
    (i : c.index) (j : d.index) :
    IsImmersion (certifiedCommonLeft c d i j) ∧ IsImmersion (certifiedCommonRight c d i j) ∧
      certifiedCommonLeft c d i j ≫ c.base i = certifiedCommonRight c d i j ≫ d.output j := by
  letI := c.immersion i
  letI := d.immersion j
  exact certified_inverse_pieces A f a hv (c.base i) (d.base j)
    (c.output i) (d.output j) (c.certificate i) (d.certificate j)

theorem certifiedCommon_left_partition
    (c : AffineBranchStratification A f a) (d : AffineBranchStratification A a f)
    (i : c.index) (x : c.scheme i) :
    ∃! j, x ∈ Set.range (certifiedCommonLeft c d i j) := by
  have hp := (c.certificate i).point x
  have hmem := affineBranchRelation_mem_right A f a hp
  obtain ⟨j, hj, huniq⟩ := (d.partition (c.output i x)).mp hmem
  refine ⟨j, ?_, ?_⟩
  · change x ∈ Set.range (reducedPullbackFst (c.output i) (d.base j))
    rw [reducedPullbackFst_range]
    exact hj
  · intro k hk
    apply huniq k
    change x ∈ Set.range (reducedPullbackFst (c.output i) (d.base k)) at hk
    rwa [reducedPullbackFst_range] at hk

theorem certifiedCommon_right_partition
    [∀ j, Algebra.FiniteType ℂ (A j)] [∀ j, _root_.IsReduced (A j)]
    [∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (f j).toRingHom))]
    (hu : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp (f i) = ψ.comp (f j) → φ.comp (a i) = ψ.comp (a j))
    (hv : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp (a i) = ψ.comp (a j) → φ.comp (f i) = ψ.comp (f j))
    (c : AffineBranchStratification A f a) (d : AffineBranchStratification A a f)
    (j : d.index) (y : d.scheme j) :
    ∃! i, y ∈ Set.range (certifiedCommonRight c d i j) := by
  have hy := (d.certificate j).symm.point y
  have hmem := affineBranchRelation_mem_left A f a hy
  obtain ⟨i, hi, huniq⟩ := (c.partition (d.output j y)).mp hmem
  obtain ⟨x, hx⟩ := hi
  have hxrel := (c.certificate i).point x
  rw [hx] at hxrel
  have hxy := affineBranchRelation_left_functional A f a hu hxrel hy
  refine ⟨i, ?_, ?_⟩
  · change y ∈ Set.range (reducedPullbackSnd (c.output i) (d.base j))
    rw [reducedPullbackSnd_range]
    exact ⟨x, hxy⟩
  · intro k hk
    obtain ⟨w, hw⟩ := hk
    apply huniq k
    refine ⟨certifiedCommonLeft c d k j w, ?_⟩
    have he := (certifiedCommon_immersions hv c d k j).2.2
    have hew := congrArg (fun h => h w) he
    change c.base k (certifiedCommonLeft c d k j w) =
      d.output j (certifiedCommonRight c d k j w) at hew
    exact hew.trans (congrArg (d.output j) hw)

end DiamondIntegral.Section5
