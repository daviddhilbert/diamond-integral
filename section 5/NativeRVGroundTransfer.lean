import «section 5».NativeRVObjectGroundTransfer
import «section 3».GammaGroundRVProductScissors
import «section 3».PresentationHomExt

/-! Actual parameter substitution on the positive graded RV semiring. -/
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

theorem nativePositiveRVClass_bijection {k : ℕ} {D E : GammaGroundRVObject hc B k}
    (e : GammaGroundBijection D.domain E.domain) :
    gammaGroundRVSemiringClass D = gammaGroundRVSemiringClass E :=
  gammaGroundRVSemiringClass_iso (asIso (show D ⟶ E from e))

theorem sortedTransferRVClass_empty (k : ℕ) :
    gammaGroundRVSemiringClass (sortedTransferRVObject H (GammaGroundRVObject.empty hc B k)) = 0 :=
  (nativePositiveRVClass_bijection (D := sortedTransferRVObject H (GammaGroundRVObject.empty hc B k))
    (E := GammaGroundRVObject.empty hc C k) (GammaGroundBijection.ofCarrierEq rfl)).trans gammaGroundRVSemiringClass_empty

def sortedTransferRVInvariant : PositiveGrothendieck.Invariant (gammaGroundRVSemiringPresentation hc B)
    (R := GammaGroundRVPositiveSemiring hc C) where
  toFun A := gammaGroundRVSemiringClass (sortedTransferRVObject H A.2)
  iso {A D} h := by
    obtain ⟨a,U⟩ := A
    obtain ⟨b,V⟩ := D
    obtain ⟨hab,⟨e⟩⟩ := h
    cases hab
    exact nativePositiveRVClass_bijection (sortedTransferRVBijection H e)
  empty := sortedTransferRVClass_empty H 0
  unit := (nativePositiveRVClass_bijection (D := sortedTransferRVObject H (GammaGroundRVObject.unit hc B))
    (E := GammaGroundRVObject.unit hc C) (GammaGroundBijection.ofCarrierEq rfl)).trans gammaGroundRVSemiringClass_unit
  product A D := (nativePositiveRVClass_bijection
    (D := sortedTransferRVObject H (A.2.product D.2))
    (E := (sortedTransferRVObject H A.2).product (sortedTransferRVObject H D.2))
    (GammaGroundBijection.ofCarrierEq (by
      ext x
      exact (mem_gammaGroundRVProductDomain A.2.domain D.2.domain x).trans
        (mem_gammaGroundRVProductDomain (sortedTransferRVDomain H A.2.domain) (sortedTransferRVDomain H D.2.domain) x).symm))).trans
          (gammaGroundRVSemiringClass_product _ _)
  scissor {a b d e} h := by
    rcases h with ⟨k,A,B,D,E,hs,rfl,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl,rfl⟩
    · obtain ⟨U,X,hX,ha,hb,hd,he⟩ := hs
      subst A B D E
      let U' := sortedTransferRVObject H U
      let X' := sortedTransferRVDomain H X
      have hx : X'.carrier ⊆ U'.domain.carrier := hX
      have h₁ := nativePositiveRVClass_bijection
        (D := sortedTransferRVObject H (U.restrict X hX)) (E := U'.restrict X' hx)
        (GammaGroundBijection.ofCarrierEq rfl)
      have h₂ := nativePositiveRVClass_bijection
        (D := sortedTransferRVObject H (U.restrict (U.domain.sdiff X) (fun _ h => h.1)))
        (E := U'.restrict (U'.domain.sdiff X') (fun _ h => h.1)) (GammaGroundBijection.ofCarrierEq rfl)
      change gammaGroundRVSemiringClass _ + gammaGroundRVSemiringClass _ =
        gammaGroundRVSemiringClass _ + gammaGroundRVSemiringClass _
      rw [h₁,h₂,sortedTransferRVClass_empty]
      exact (gammaGroundRVSemiringClass_scissor (hc := hc) (ground := C) ⟨U',X',hx,rfl,rfl,rfl,rfl⟩).trans (by rw [gammaGroundRVSemiringClass_empty,add_zero])
    · change gammaGroundRVSemiringClass _ + gammaGroundRVSemiringClass _ =
        gammaGroundRVSemiringClass _ + gammaGroundRVSemiringClass _
      simp only [sortedTransferRVClass_empty,add_zero]

def sortedTransferRVPositive : GammaGroundRVPositiveSemiring hc B →+* GammaGroundRVPositiveSemiring hc C :=
  PositiveGrothendieck.lift (gammaGroundRVSemiringPresentation hc B) (sortedTransferRVInvariant H)

theorem sortedTransferRVPositive_class {k : ℕ} (A : GammaGroundRVObject hc B k) :
    sortedTransferRVPositive H (gammaGroundRVSemiringClass A) =
      gammaGroundRVSemiringClass (sortedTransferRVObject H A) := by
  change PositiveGrothendieck.lift (gammaGroundRVSemiringPresentation hc B) (sortedTransferRVInvariant H)
    (PositiveGrothendieck.of (gammaGroundRVSemiringPresentation hc B) ⟨k,A⟩) = _
  exact PositiveGrothendieck.lift_of (gammaGroundRVSemiringPresentation hc B) (sortedTransferRVInvariant H) ⟨k,A⟩

variable (K : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase C sn D → DefinableOverBase B sn D)

theorem sortedTransferRVPositive_left_inv (x : GammaGroundRVPositiveSemiring hc B) :
    sortedTransferRVPositive K (sortedTransferRVPositive H x) = x := by
  have h : (sortedTransferRVPositive (hc := hc) K).comp (sortedTransferRVPositive (hc := hc) H) = RingHom.id _ := by
    apply positivePresentationHom_ext (gammaGroundRVSemiringPresentation hc B)
    intro A
    change sortedTransferRVPositive K (sortedTransferRVPositive H (gammaGroundRVSemiringClass A.2)) = _
    rw [sortedTransferRVPositive_class,sortedTransferRVPositive_class]
    exact nativePositiveRVClass_bijection (GammaGroundBijection.ofCarrierEq rfl)
  exact RingHom.congr_fun h x

def sortedTransferRVPositiveEquiv : GammaGroundRVPositiveSemiring hc B ≃+* GammaGroundRVPositiveSemiring hc C where
  toFun := sortedTransferRVPositive H
  invFun := sortedTransferRVPositive K
  left_inv := sortedTransferRVPositive_left_inv H K
  right_inv := sortedTransferRVPositive_left_inv K H
  map_add' := fun x y => (sortedTransferRVPositive (hc := hc) H).map_add x y
  map_mul' := fun x y => (sortedTransferRVPositive (hc := hc) H).map_mul x y

end DiamondIntegral.Section5
