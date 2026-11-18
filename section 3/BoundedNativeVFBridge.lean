import «section 3».GammaGroundVFDimension
import «section 3».GammaGroundCitedBoundedIntegral
import «section 3».GammaGroundEmptyBijections
import «section 5».Completed18VFObjects
import «section 5».NativeSortedGroundTransfer
import Section5.GammaDimensionCriterion
import Section8.GammaRadiusBase
import IntegrationSection6.FiniteVFIntegralValues
import IntegrationSection6.GammaMixedEmptyIsomorphisms
import IntegrationSection6.FiniteGammaLiftGluing

/-! Theorem 3.22, bounded part: the manuscript dimension-bounded VF
category `VF[k]` over a Gamma-ground base is identified with the native
dimension-bounded category of [18] over a second base with the same
definable sets. The manuscript dimension (interior dimension of
coordinate projections) and the native one (finite-to-one definable maps
to `VF^j × RV^r × Γ^d` with `j ≤ k`) agree through the common
transcendence-degree criterion. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open DiamondIntegral.Section5
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

section Dimension
variable {hc : CanonicalStructure.IsCanonical (M := M)}

/-- Over a canonical structure the normalized transcendence degree is the
original one. -/
theorem boundedNative_trdeg_eq (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) {n : ℕ}
    (x : Fin n → Section2.VF M) :
    @vfTupleTrdeg M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) S n x = @vfTupleTrdeg M sM hM S n x := by
  have key : ∀ (N' : LRV.Structure M) (hN' : @Theory.Model LRV M N' Axioms.ACVF) (_ : N' = sM)
      (y : Fin n → @Section2.VF M N') (z : Fin n → @Section2.VF M sM), HEq y z →
      @vfTupleTrdeg M N' hN' S n y = @vfTupleTrdeg M sM hM S n z := by
    intro N' hN' h y z hyz
    subst h
    cases hyz
    rfl
  exact key (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM)
    (SpecialTransformations.Section8.normalize_eq_of_isCanonical hc) x x HEq.rfl

/-- The manuscript VF dimension bound is the native one. -/
theorem boundedNative_dimension_iff {B : Base (M := M)}
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n r : ℕ} (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (k : ℕ) :
    Section2.vfDimension D.carrier ≤ (k : WithBot ℕ) ↔ GammaHasVFDimLE B D.carrier k := by
  rw [gammaGroundVFDimension_le_iff_point_rank D.definable hκ hs hr hv k,
    gamma_dim_le_iff_rank hκ hs h00 hr (groundMixed_gamma_set D)]
  exact ⟨fun h p hp => (boundedNative_trdeg_eq hc B.real p.1).trans_le (h p hp),
    fun h p hp => (boundedNative_trdeg_eq hc B.real p.1).symm.trans_le (h p hp)⟩

end Dimension

section Bridge
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B₀ B : Base (M := M)} {k : ℕ}
variable (H : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B₀ sn D → DefinableOverBase B sn D)
variable (K : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B sn D → DefinableOverBase B₀ sn D)
variable (hdim : ∀ {n r : ℕ} (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (k : ℕ),
  Section2.vfDimension D.carrier ≤ (k : WithBot ℕ) ↔ GammaHasVFDimLE B D.carrier k)

theorem boundedVFClass_bijection {D E : GammaGroundVFObject hc B₀ k}
    (e : GammaGroundBijection D.domain E.domain) : gammaGroundVFClass D = gammaGroundVFClass E :=
  gammaGroundVFClass_iso (asIso (show D ⟶ E from e))

/-- A manuscript `VF[k]` object as a native bounded object. -/
def boundedGroundNative (A : GammaGroundVFObject hc B₀ k) : GammaVFFiniteObject B k :=
  ⟨⟨(A.vfArity,A.rvArity),A.domain.carrier,groundMixed_gamma_set (sortedTransferMixedDomain H A.domain),
    (hdim (sortedTransferMixedDomain H A.domain) k).mp A.dimension⟩,A.finite⟩

/-- A native bounded object as a manuscript `VF[k]` object. -/
def boundedNativeGround (A : GammaVFFiniteObject B k) : GammaGroundVFObject hc B₀ k :=
  ⟨A.val.arity.1,A.val.arity.2,
    sortedTransferMixedDomain K (nativeGammaPointDomain (hc := hc) A.val.domain A.val.definable),
    (hdim (nativeGammaPointDomain (hc := hc) A.val.domain A.val.definable) k).mpr A.val.dimension,
    A.property⟩

theorem nativeBoundedEmpty_domain :
    ((gammaVFFinitePresentation B k).empty.val.domain) = ∅ := by
  ext p
  constructor
  · rintro ⟨u,_,_⟩
    exact u.property
  · exact False.elim

/-- A native bounded object with empty domain has class zero. -/
theorem nativeBoundedClass_empty (A : GammaVFFiniteObject B k) (hA : A.val.domain = ∅) :
    PositiveAdditiveGrothendieck.of (gammaVFFinitePresentation B k) A = 0 :=
  (PositiveAdditiveGrothendieck.of_iso (gammaVFFinitePresentation B k)
    (b := (gammaVFFinitePresentation B k).empty)
    ⟨gammaEmptyMixedIso hA nativeBoundedEmpty_domain⟩).trans
    (PositiveAdditiveGrothendieck.of_empty _)

/-- A manuscript `VF[k]` object with empty domain has class zero. -/
theorem groundBoundedClass_empty (A : GammaGroundVFObject hc B₀ k) (hA : A.domain.carrier = ∅) :
    gammaGroundVFClass A = 0 :=
  (boundedVFClass_bijection (E := GammaGroundVFObject.empty hc B₀ k)
    (GammaGroundBijection.ofEmpty hA rfl)).trans gammaGroundVFClass_empty

omit hdim in
/-- The four-term union/intersection relation in the manuscript `VF[k]`. -/
theorem boundedVFClass_union_inter {n r : ℕ}
    (D E U I : GammaGroundDefSet hc B₀ (rawMixedSpace (M := M) n r))
    (hU : U.carrier = D.carrier ∪ E.carrier) (hI : I.carrier = D.carrier ∩ E.carrier)
    (dD dE dU dI fD fE fU fI) :
    gammaGroundVFClass (⟨n,r,D,dD,fD⟩ : GammaGroundVFObject hc B₀ k) +
      gammaGroundVFClass (⟨n,r,E,dE,fE⟩ : GammaGroundVFObject hc B₀ k) =
    gammaGroundVFClass (⟨n,r,U,dU,fU⟩ : GammaGroundVFObject hc B₀ k) +
      gammaGroundVFClass (⟨n,r,I,dI,fI⟩ : GammaGroundVFObject hc B₀ k) := by
  let A : GammaGroundVFObject hc B₀ k := ⟨n,r,D,dD,fD⟩
  let C : GammaGroundVFObject hc B₀ k := ⟨n,r,E,dE,fE⟩
  let Uo : GammaGroundVFObject hc B₀ k := ⟨n,r,U,dU,fU⟩
  let Io : GammaGroundVFObject hc B₀ k := ⟨n,r,I,dI,fI⟩
  have hDU : D.carrier ⊆ U.carrier := fun x h => hU ▸ Or.inl h
  have hIE : I.carrier ⊆ E.carrier := fun x h => (hI ▸ h : x ∈ D.carrier ∩ E.carrier).2
  have h₁ := gammaGroundVFClass_scissor Uo D hDU
  have h₂ := gammaGroundVFClass_scissor C I hIE
  have ha : gammaGroundVFClass (Uo.restrict D hDU) = gammaGroundVFClass A :=
    boundedVFClass_bijection (GammaGroundBijection.ofCarrierEq rfl)
  have hi : gammaGroundVFClass (C.restrict I hIE) = gammaGroundVFClass Io :=
    boundedVFClass_bijection (GammaGroundBijection.ofCarrierEq rfl)
  have hq : gammaGroundVFClass (Uo.restrict (Uo.domain.sdiff D) (fun _ h => h.1)) =
      gammaGroundVFClass (C.restrict (C.domain.sdiff I) (fun _ h => h.1)) := by
    apply boundedVFClass_bijection
    apply GammaGroundBijection.ofCarrierEq
    ext x
    change (x ∈ U.carrier ∧ x ∉ D.carrier) ↔ (x ∈ E.carrier ∧ x ∉ I.carrier)
    have hu := Set.ext_iff.mp hU x
    have hi' := Set.ext_iff.mp hI x
    change x ∈ U.carrier ↔ x ∈ D.carrier ∨ x ∈ E.carrier at hu
    change x ∈ I.carrier ↔ x ∈ D.carrier ∧ x ∈ E.carrier at hi'
    rw [hu,hi']
    tauto
  rw [ha,hq] at h₁
  rw [hi] at h₂
  change gammaGroundVFClass A + gammaGroundVFClass C = gammaGroundVFClass Uo + gammaGroundVFClass Io
  rw [← h₁,← h₂]
  ac_rfl

def boundedGroundNativeInvariant :
    PositiveAdditiveGrothendieck.Invariant (gammaGroundVFPresentation hc B₀ k)
      (A := PositiveAdditiveGrothendieck.KPlus (gammaVFFinitePresentation B k)) where
  toFun A := PositiveAdditiveGrothendieck.of (gammaVFFinitePresentation B k) (boundedGroundNative H hdim A)
  iso {a b} h := by
    obtain ⟨e⟩ := h
    exact PositiveAdditiveGrothendieck.of_iso (gammaVFFinitePresentation B k)
      ⟨groundMixed_gamma_iso (sortedTransferMixedBijection H e.hom)⟩
  empty := nativeBoundedClass_empty _ rfl
  scissor {a b d e} h := by
    obtain ⟨U,X,hX,ha,hb,hd,he⟩ := h
    subst a b d e
    let Z : GammaVFFiniteObject B k :=
      ⟨⟨(U.vfArity,U.rvArity),∅,
        groundMixed_gamma_set (GammaGroundDefSet.empty hc B (rawMixedSpace (M := M) U.vfArity U.rvArity)),
        (hdim (GammaGroundDefSet.empty hc B (rawMixedSpace (M := M) U.vfArity U.rvArity)) k).mp
          (by rw [show (GammaGroundDefSet.empty hc B (rawMixedSpace (M := M) U.vfArity U.rvArity)).carrier = ∅ from rfl,
            Section2.vfDimension_empty]; exact bot_le)⟩,fun _ => Set.finite_empty⟩
    have hz : PositiveAdditiveGrothendieck.of (gammaVFFinitePresentation B k) Z = 0 :=
      nativeBoundedClass_empty Z rfl
    have hs : GammaVFAllScissor
        (gammaVFAllFromBounded (boundedGroundNative H hdim (U.restrict X hX)))
        (gammaVFAllFromBounded (boundedGroundNative H hdim (U.restrict (U.domain.sdiff X) (fun _ h => h.1))))
        (gammaVFAllFromBounded (boundedGroundNative H hdim U)) (gammaVFAllFromBounded Z) := by
      apply (gammaVFAllScissor_domains _ _ _ _ _ _ _ _ _ _ _ _).mpr
      constructor
      · ext x
        change x ∈ U.domain.carrier ↔ (x ∈ X.carrier ∨ x ∈ U.domain.carrier ∧ x ∉ X.carrier)
        exact ⟨fun hx => (Classical.em (x ∈ X.carrier)).elim Or.inl (fun hn => Or.inr ⟨hx,hn⟩),
          fun hx => hx.elim (fun h => hX h) And.left⟩
      · ext x
        change False ↔ (x ∈ X.carrier ∧ x ∈ U.domain.carrier ∧ x ∉ X.carrier)
        tauto
    have h := PositiveAdditiveGrothendieck.of_scissor (gammaVFFinitePresentation B k)
      (a := boundedGroundNative H hdim (U.restrict X hX))
      (b := boundedGroundNative H hdim (U.restrict (U.domain.sdiff X) (fun _ h => h.1)))
      (c := boundedGroundNative H hdim U) (d := Z) hs
    change _ = _ + PositiveAdditiveGrothendieck.of (gammaVFFinitePresentation B k)
      (boundedGroundNative H hdim (GammaGroundVFObject.empty hc B₀ k))
    rw [nativeBoundedClass_empty (boundedGroundNative H hdim (GammaGroundVFObject.empty hc B₀ k)) rfl]
    rw [hz] at h
    exact h

def boundedNativeGroundInvariant :
    PositiveAdditiveGrothendieck.Invariant (gammaVFFinitePresentation B k)
      (A := GammaGroundVFKPlus hc B₀ k) where
  toFun A := gammaGroundVFClass (boundedNativeGround K hdim A)
  iso {a b} h := by
    obtain ⟨e⟩ := h
    exact boundedVFClass_bijection
      (sortedTransferMixedBijection K (nativeGammaPointBijection a.val.definable b.val.definable e))
  empty := groundBoundedClass_empty _ nativeBoundedEmpty_domain
  scissor {a c d e} h := by
    rcases a with ⟨⟨⟨n,r⟩,A,hA,dA⟩,fA⟩
    rcases c with ⟨⟨c,C,hC,dC⟩,fC⟩
    rcases d with ⟨⟨d,D,hD,dD⟩,fD⟩
    rcases e with ⟨⟨e,E,hE,dE⟩,fE⟩
    have h' : GammaVFAllScissor ⟨(n,r),A,hA,fA⟩ ⟨c,C,hC,fC⟩ ⟨d,D,hD,fD⟩ ⟨e,E,hE,fE⟩ := h
    rcases h' with ⟨hc',hd,he,hu,hi⟩
    change (n,r) = c at hc'
    change (n,r) = d at hd
    change (n,r) = e at he
    subst c; subst d; subst e
    obtain ⟨rfl,rfl⟩ := (gammaVFAllScissor_domains A C D E hA hC hD hE fA fC fD fE).mp ⟨rfl,rfl,rfl,hu,hi⟩
    exact boundedVFClass_union_inter _ _ _ _ rfl rfl _ _ _ _ _ _ _ _

def boundedGroundNativeHom :
    GammaGroundVFKPlus hc B₀ k →+ PositiveAdditiveGrothendieck.KPlus (gammaVFFinitePresentation B k) :=
  PositiveAdditiveGrothendieck.lift _ (boundedGroundNativeInvariant H hdim)

def boundedNativeGroundHom :
    PositiveAdditiveGrothendieck.KPlus (gammaVFFinitePresentation B k) →+ GammaGroundVFKPlus hc B₀ k :=
  PositiveAdditiveGrothendieck.lift _ (boundedNativeGroundInvariant K hdim)

theorem boundedGroundNativeHom_class (A : GammaGroundVFObject hc B₀ k) :
    boundedGroundNativeHom H hdim (gammaGroundVFClass A) =
      PositiveAdditiveGrothendieck.of (gammaVFFinitePresentation B k) (boundedGroundNative H hdim A) :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

theorem boundedNativeGroundHom_class (A : GammaVFFiniteObject B k) :
    boundedNativeGroundHom K hdim (PositiveAdditiveGrothendieck.of (gammaVFFinitePresentation B k) A) =
      gammaGroundVFClass (boundedNativeGround K hdim A) :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

/-- The manuscript bounded VF semigroup is the native one of [18]. -/
def boundedVFNativeEquiv :
    GammaGroundVFKPlus hc B₀ k ≃+ PositiveAdditiveGrothendieck.KPlus (gammaVFFinitePresentation B k) := by
  have h₁ : (boundedNativeGroundHom K hdim).comp (boundedGroundNativeHom H hdim) =
      AddMonoidHom.id (GammaGroundVFKPlus hc B₀ k) := by
    apply PositiveAdditiveGrothendieck.hom_ext
    intro A
    change boundedNativeGroundHom K hdim (boundedGroundNativeHom H hdim (gammaGroundVFClass A)) =
      gammaGroundVFClass A
    rw [boundedGroundNativeHom_class,boundedNativeGroundHom_class]
    exact boundedVFClass_bijection (GammaGroundBijection.ofCarrierEq rfl)
  have h₂ : (boundedGroundNativeHom H hdim).comp (boundedNativeGroundHom K hdim) =
      AddMonoidHom.id (PositiveAdditiveGrothendieck.KPlus (gammaVFFinitePresentation B k)) := by
    apply PositiveAdditiveGrothendieck.hom_ext
    intro A
    change boundedGroundNativeHom H hdim (boundedNativeGroundHom K hdim
      (PositiveAdditiveGrothendieck.of (gammaVFFinitePresentation B k) A)) = _
    rw [boundedNativeGroundHom_class,boundedGroundNativeHom_class]
    exact PositiveAdditiveGrothendieck.of_iso _ ⟨gammaIso_reflexive A.val.domain A.val.definable⟩
  exact {
    toFun := boundedGroundNativeHom H hdim
    invFun := boundedNativeGroundHom K hdim
    left_inv := fun x => DFunLike.congr_fun h₁ x
    right_inv := fun x => DFunLike.congr_fun h₂ x
    map_add' := (boundedGroundNativeHom H hdim).map_add }

theorem boundedVFNativeEquiv_class (A : GammaGroundVFObject hc B₀ k) :
    boundedVFNativeEquiv H K hdim (gammaGroundVFClass A) =
      PositiveAdditiveGrothendieck.of (gammaVFFinitePresentation B k) (boundedGroundNative H hdim A) :=
  boundedGroundNativeHom_class H hdim A

end Bridge

end DiamondIntegral.Section3
