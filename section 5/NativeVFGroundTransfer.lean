import «section 5».NativeSortedGroundTransfer
import «section 3».PresentationHomExt
import «section 3».GammaGroundVFSemiring

/-! Equivalent actual sorted parameter presentations induce inverse
semiring maps on the positive native VF categories. Literal carriers,
all zero strata and actual bijections are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)}
variable (H : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B sn D → DefinableOverBase C sn D)

def sortedTransferFiniteVFObject (A : GammaGroundFiniteVFObject hc B) : GammaGroundFiniteVFObject hc C :=
  ⟨A.vfArity,A.rvArity,sortedTransferMixedDomain H A.domain,A.finite⟩

theorem nativePositiveVFClass_bijection {D E : GammaGroundFiniteVFObject hc B}
    (e : GammaGroundBijection D.domain E.domain) :
    gammaGroundVFSemiringClass D = gammaGroundVFSemiringClass E :=
  gammaGroundVFSemiringClass_iso (asIso (show D ⟶ E from e))

def sortedTransferVFInvariant : PositiveGrothendieck.Invariant (gammaGroundVFSemiringPresentation hc B)
    (R := GammaGroundVFPositiveSemiring hc C) where
  toFun A := gammaGroundVFSemiringClass (sortedTransferFiniteVFObject H A)
  iso h := by
    obtain ⟨e⟩ := h
    exact nativePositiveVFClass_bijection (sortedTransferMixedBijection H e.hom)
  empty := (nativePositiveVFClass_bijection (D := sortedTransferFiniteVFObject H (GammaGroundFiniteVFObject.empty hc B))
    (E := GammaGroundFiniteVFObject.empty hc C) (GammaGroundBijection.ofCarrierEq rfl)).trans gammaGroundVFSemiringClass_empty
  unit := (nativePositiveVFClass_bijection (D := sortedTransferFiniteVFObject H (GammaGroundFiniteVFObject.unit hc B))
    (E := GammaGroundFiniteVFObject.unit hc C) (GammaGroundBijection.ofCarrierEq rfl)).trans gammaGroundVFSemiringClass_unit
  product A D := (nativePositiveVFClass_bijection
    (D := sortedTransferFiniteVFObject H (A.product D))
    (E := (sortedTransferFiniteVFObject H A).product (sortedTransferFiniteVFObject H D))
    (GammaGroundBijection.ofCarrierEq (by
      ext x
      change x ∈ (A.product D).domain.carrier ↔ _
      exact (mem_gammaGroundMixedProductDomain A.domain D.domain x).trans
        (mem_gammaGroundMixedProductDomain (sortedTransferMixedDomain H A.domain) (sortedTransferMixedDomain H D.domain) x).symm))).trans (gammaGroundVFSemiringClass_product _ _)
  scissor {a b d e} h := by
    obtain ⟨U,X,hX,ha,hb,hd,he⟩ := h
    subst a b d e
    let U' := sortedTransferFiniteVFObject H U
    let X' := sortedTransferMixedDomain H X
    have hx : X'.carrier ⊆ U'.domain.carrier := hX
    have h₁ := nativePositiveVFClass_bijection
      (D := sortedTransferFiniteVFObject H (U.restrict X hX)) (E := U'.restrict X' hx)
      (GammaGroundBijection.ofCarrierEq rfl)
    have h₂ := nativePositiveVFClass_bijection
      (D := sortedTransferFiniteVFObject H (U.restrict (U.domain.sdiff X) (fun _ h => h.1)))
      (E := U'.restrict (U'.domain.sdiff X') (fun _ h => h.1)) (GammaGroundBijection.ofCarrierEq rfl)
    have he := gammaGroundVFSemiringClass_scissor (hc := hc) (ground := C)
      (A := U'.restrict X' hx) (B := U'.restrict (U'.domain.sdiff X') (fun _ h => h.1))
      (D := U') (E := GammaGroundFiniteVFObject.empty hc C) ⟨U',X',hx,rfl,rfl,rfl,rfl⟩
    rw [h₁,h₂]
    have h₃ := nativePositiveVFClass_bijection
      (D := sortedTransferFiniteVFObject H (GammaGroundFiniteVFObject.empty hc B))
      (E := GammaGroundFiniteVFObject.empty hc C) (GammaGroundBijection.ofCarrierEq rfl)
    rw [h₃]
    exact he

def sortedTransferVFPositive : GammaGroundVFPositiveSemiring hc B →+* GammaGroundVFPositiveSemiring hc C :=
  PositiveGrothendieck.lift (gammaGroundVFSemiringPresentation hc B) (sortedTransferVFInvariant H)

theorem sortedTransferVFPositive_class (A : GammaGroundFiniteVFObject hc B) :
    sortedTransferVFPositive H (gammaGroundVFSemiringClass A) =
      gammaGroundVFSemiringClass (sortedTransferFiniteVFObject H A) := PositiveGrothendieck.lift_of _ _ A

variable (K : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase C sn D → DefinableOverBase B sn D)

theorem sortedTransferVFPositive_left_inv (x : GammaGroundVFPositiveSemiring hc B) :
    sortedTransferVFPositive K (sortedTransferVFPositive H x) = x := by
  have h : (sortedTransferVFPositive (hc := hc) K).comp (sortedTransferVFPositive (hc := hc) H) = RingHom.id _ := by
    apply positivePresentationHom_ext (gammaGroundVFSemiringPresentation hc B)
    intro A
    change sortedTransferVFPositive K (sortedTransferVFPositive H (gammaGroundVFSemiringClass A)) = _
    rw [sortedTransferVFPositive_class,sortedTransferVFPositive_class]
    exact nativePositiveVFClass_bijection (GammaGroundBijection.ofCarrierEq rfl)
  exact RingHom.congr_fun h x

def sortedTransferVFPositiveEquiv : GammaGroundVFPositiveSemiring hc B ≃+* GammaGroundVFPositiveSemiring hc C where
  toFun := sortedTransferVFPositive H
  invFun := sortedTransferVFPositive K
  left_inv := sortedTransferVFPositive_left_inv H K
  right_inv := sortedTransferVFPositive_left_inv K H
  map_add' := fun x y => (sortedTransferVFPositive (hc := hc) H).map_add x y
  map_mul' := fun x y => (sortedTransferVFPositive (hc := hc) H).map_mul x y

end DiamondIntegral.Section5
