import «section 5».ReducedAffineBranchGluing
import «section 5».ImmersionBranchGluing

/-! A branch certificate records actual local lifts of two morphisms
to affine graph schemes. Certificates pull back along every morphism;
complex-point single-valuedness then proves equality on reduced schemes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {S T J : Type} [CommRing S] [CommRing T]
variable [Algebra ℂ S] [Algebra ℂ T]
variable (A : J → Type) [∀ j, CommRing (A j)] [∀ j, Algebra ℂ (A j)]
variable (f : ∀ j, S →ₐ[ℂ] A j) (a : ∀ j, T →ₐ[ℂ] A j)

structure AffineBranchCertificate {X : Scheme} (base : X ⟶ Spec (.of S)) (F : X ⟶ Spec (.of T)) where
  cover : X.OpenCover
  index : cover.I₀ → J
  lift : ∀ i, cover.X i ⟶ Spec (.of (A (index i)))
  input_fac : ∀ i, lift i ≫ Spec.map (CommRingCat.ofHom (f (index i)).toRingHom) = cover.f i ≫ base
  output_fac : ∀ i, lift i ≫ Spec.map (CommRingCat.ofHom (a (index i)).toRingHom) = cover.f i ≫ F

variable {A f a}

def AffineBranchCertificate.pullback {X W : Scheme}
    {base : X ⟶ Spec (.of S)} {F : X ⟶ Spec (.of T)}
    (c : AffineBranchCertificate A f a base F) (r : W ⟶ X) :
    AffineBranchCertificate A f a (r ≫ base) (r ≫ F) where
  cover := c.cover.pullback₁ r
  index := c.index
  lift i := c.cover.pullbackHom r i ≫ c.lift i
  input_fac i := by
    rw [Category.assoc, c.input_fac, ← Category.assoc, c.cover.pullbackHom_map, Category.assoc]
  output_fac i := by
    rw [Category.assoc, c.output_fac, ← Category.assoc, c.cover.pullbackHom_map, Category.assoc]

def AffineBranchCertificate.symm {X : Scheme}
    {base : X ⟶ Spec (.of S)} {F : X ⟶ Spec (.of T)}
    (c : AffineBranchCertificate A f a base F) : AffineBranchCertificate A a f F base where
  cover := c.cover
  index := c.index
  lift := c.lift
  input_fac := c.output_fac
  output_fac := c.input_fac

theorem AffineBranchCertificate.functional {K : Type} (B : K → Type)
    [∀ j, CommRing (B j)] [∀ j, Algebra ℂ (B j)]
    [∀ j, Algebra.FiniteType ℂ (A j)] [∀ j, Algebra.FiniteType ℂ (B j)]
    (g : ∀ j, S →ₐ[ℂ] B j) (b : ∀ j, T →ₐ[ℂ] B j)
    (hc : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : B j →ₐ[ℂ] ℂ),
      φ.comp (f i) = ψ.comp (g j) → φ.comp (a i) = ψ.comp (b j))
    {X : Scheme} [AlgebraicGeometry.IsReduced X]
    {base : X ⟶ Spec (.of S)} {F H : X ⟶ Spec (.of T)}
    (c : AffineBranchCertificate A f a base F)
    (d : AffineBranchCertificate B g b base H) : F = H := by
  apply c.cover.hom_ext
  intro i
  let V : (c.cover.X i).OpenCover := d.cover.pullback₁ (c.cover.f i)
  apply V.hom_ext
  intro j
  let p := V.f j
  let q := d.cover.pullbackHom (c.cover.f i) j
  letI : AlgebraicGeometry.IsReduced (c.cover.X i) := isReduced_of_isOpenImmersion (c.cover.f i)
  letI : AlgebraicGeometry.IsReduced (V.X j) := isReduced_of_isOpenImmersion p
  have hpb : p ≫ c.cover.f i = q ≫ d.cover.f j := (d.cover.pullbackHom_map (c.cover.f i) j).symm
  have hi : (p ≫ c.lift i) ≫ Spec.map (CommRingCat.ofHom (f (c.index i)).toRingHom) =
      (q ≫ d.lift j) ≫ Spec.map (CommRingCat.ofHom (g (d.index j)).toRingHom) := by
    calc
      _ = (p ≫ c.cover.f i) ≫ base := by rw [Category.assoc, c.input_fac, ← Category.assoc]
      _ = (q ≫ d.cover.f j) ≫ base := congrArg (fun z => z ≫ base) hpb
      _ = _ := by rw [Category.assoc, ← d.input_fac, ← Category.assoc]
  have he := scheme_complex_overlap_agreement (f (c.index i)) (g (d.index j))
    (a (c.index i)) (b (d.index j)) (hc (c.index i) (d.index j)) (p ≫ c.lift i) (q ≫ d.lift j) hi
  calc
    p ≫ (c.cover.f i ≫ F) = (p ≫ c.lift i) ≫
        Spec.map (CommRingCat.ofHom (a (c.index i)).toRingHom) := by rw [← c.output_fac, ← Category.assoc]
    _ = (q ≫ d.lift j) ≫ Spec.map (CommRingCat.ofHom (b (d.index j)).toRingHom) := he
    _ = (q ≫ d.cover.f j) ≫ H := by rw [Category.assoc, d.output_fac, ← Category.assoc]
    _ = p ≫ (c.cover.f i ≫ H) := by rw [← hpb, Category.assoc]

theorem glue_immersion_branches_certificate
    [∀ j, Algebra.FiniteType ℂ (A j)] [∀ j, _root_.IsReduced (A j)]
    [∀ j, IsImmersion (Spec.map (CommRingCat.ofHom (f j).toRingHom))]
    (hc : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp (f i) = ψ.comp (f j) → φ.comp (a i) = ψ.comp (a j))
    {X : Scheme} [AlgebraicGeometry.IsReduced X] (base : X ⟶ Spec (.of S))
    (ho : ∀ j, IsOpen {x : X |
      base x ∈ Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))})
    (hcover : ∀ x : X, ∃ j, base x ∈ Set.range (Spec.map (CommRingCat.ofHom (f j).toRingHom))) :
    ∃ F : X ⟶ Spec (.of T), Nonempty (AffineBranchCertificate A f a base F) := by
  obtain ⟨F, hF, _⟩ := glue_immersion_branches A f base a hc ho hcover
  refine ⟨F, ⟨?_⟩⟩
  exact {
    cover := immersionBranchCover A f base ho hcover
    index := id
    lift := immersionBranchLift A f base ho
    input_fac := immersionBranchLift_fac A f base ho
    output_fac := fun j => (hF j).symm }

end DiamondIntegral.Section5
