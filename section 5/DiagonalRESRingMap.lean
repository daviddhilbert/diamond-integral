import «section 5».RationalBijectionDescent
import «section 5».RESSetOperations

/-! The inverse raw comparison is an actual ring homomorphism to the
ungraded native RES ring. Every defining relation is checked on literal
original-base domains; no root parameter or label choice is retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4
local instance diagonalRESRingMapStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem rationalDescent_carrier_image {n : ℕ} (q : Fin n → ℚ) (X : Set (Fin n → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X) (hiX : RationalInvariant q X) :
    (rationalDescendedSet q X hX).carrier = rationalFrame q '' X := by
  ext r
  exact rationalDescent_mem_image q X hX hiX r

theorem rationalDescent_product (X Y : DiagonalConstructible.Object) :
    (rationalDescendedSet (DiagonalConstructible.product X Y).weights
      (DiagonalConstructible.product X Y).domain (DiagonalConstructible.product X Y).definable).carrier =
    (resSetProduct canonicalInterpret_isCanonical
      (rationalDescendedSet X.weights X.domain X.definable)
      (rationalDescendedSet Y.weights Y.domain Y.definable)
      (rationalDescendedSet_finite_values _ _ _) (rationalDescendedSet_finite_values _ _ _)).carrier := by
  ext z
  rw [rationalDescent_mem_image _ _ _ (DiagonalConstructible.product X Y).invariant,
    resSetProduct_mem, rationalDescent_mem_image _ _ _ X.invariant,
    rationalDescent_mem_image _ _ _ Y.invariant]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨(fun i => w (Fin.castAdd Y.arity i)), hw.1, ?_⟩,
      ⟨(fun i => w (Fin.natAdd X.arity i)), hw.2, ?_⟩⟩
    · funext i
      simp only [DiagonalConstructible.product, rationalFrame, Fin.append_left]
    · funext i
      simp only [DiagonalConstructible.product, rationalFrame, Fin.append_right]
  · rintro ⟨⟨x, hx, hxe⟩, ⟨y, hy, hye⟩⟩
    refine ⟨Fin.append x y, ⟨?_, ?_⟩, ?_⟩
    · simpa only [Fin.append_left] using hx
    · simpa only [Fin.append_right] using hy
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [DiagonalConstructible.product, rationalFrame, Fin.append_left] using congrFun hxe j
      · simpa only [DiagonalConstructible.product, rationalFrame, Fin.append_right] using congrFun hye j

theorem diagonalRESClass_product (X Y : DiagonalConstructible.Object) :
    diagonalRESClass (DiagonalConstructible.product X Y) = diagonalRESClass X * diagonalRESClass Y := by
  exact (resSetClass_congr canonicalInterpret_isCanonical _ _ _ _
    (rationalDescent_product X Y)).trans (resSetClass_product canonicalInterpret_isCanonical _ _ _ _)

theorem diagonalRESClass_empty (X : DiagonalConstructible.Object) (he : X.domain = ∅) :
    diagonalRESClass X = 0 := by
  apply resSetClass_empty
  rw [rationalDescent_carrier_image _ _ _ X.invariant, he, Set.image_empty]

theorem diagonalRESClass_unit : diagonalRESClass DiagonalConstructible.unit = 1 := by
  let U := GammaGroundRESObject.unit canonicalInterpret_isCanonical
    (EmptyGammaGround.base {c | baseCarrier c})
  have he : (rationalDescendedSet DiagonalConstructible.unit.weights DiagonalConstructible.unit.domain
      DiagonalConstructible.unit.definable).carrier = (originalDomain canonicalInterpret_isCanonical U).carrier := by
    ext r
    rw [rationalDescent_mem_image _ _ _ DiagonalConstructible.unit.invariant]
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact ⟨Fin.elim0, Set.mem_univ _, funext (fun i => Fin.elim0 i)⟩
  exact (resSetClass_congr canonicalInterpret_isCanonical _ _ _ _ he).trans
    ((resSetClass_originalDomain _ U).trans (nativeUngradedClass_unit _ _))

theorem rationalDescent_scissor (X : DiagonalConstructible.Object)
    (D : Set (Fin X.arity → ℂ)) (hD : (Set.univ : Set ℂ).Definable Language.ring D)
    (hiD : RationalInvariant X.weights D) :
    (rationalDescendedSet (DiagonalConstructible.outside X D hD hiD).weights
      (DiagonalConstructible.outside X D hD hiD).domain (DiagonalConstructible.outside X D hD hiD).definable).carrier =
    (rationalDescendedSet X.weights X.domain X.definable).carrier \
      (rationalDescendedSet (DiagonalConstructible.cut X D hD hiD).weights
        (DiagonalConstructible.cut X D hD hiD).domain (DiagonalConstructible.cut X D hD hiD).definable).carrier := by
  rw [rationalDescent_carrier_image _ _ _ (DiagonalConstructible.outside X D hD hiD).invariant,
    rationalDescent_carrier_image _ _ _ X.invariant,
    rationalDescent_carrier_image _ _ _ (DiagonalConstructible.cut X D hD hiD).invariant]
  change rationalFrame X.weights '' (X.domain \ D) =
    rationalFrame X.weights '' X.domain \ rationalFrame X.weights '' (X.domain ∩ D)
  ext r
  constructor
  · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro ⟨y, ⟨_, hy⟩, he⟩
    exact hn ((rationalFrame_injective X.weights he) ▸ hy)
  · rintro ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, ⟨hx, fun hd => hn ⟨x, ⟨hx, hd⟩, rfl⟩⟩, rfl⟩

theorem diagonalRESClass_scissor (X : DiagonalConstructible.Object)
    (D : Set (Fin X.arity → ℂ)) (hD : (Set.univ : Set ℂ).Definable Language.ring D)
    (hiD : RationalInvariant X.weights D) :
    diagonalRESClass X = diagonalRESClass (DiagonalConstructible.cut X D hD hiD) +
      diagonalRESClass (DiagonalConstructible.outside X D hD hiD) := by
  apply resSetClass_scissor
  · rw [rationalDescent_carrier_image _ _ _ (DiagonalConstructible.cut X D hD hiD).invariant,
      rationalDescent_carrier_image _ _ _ X.invariant]
    exact Set.image_mono Set.inter_subset_left
  · exact rationalDescent_scissor X D hD hiD

def diagonalRESInvariant : DiagonalConstructible.Invariant
    (RESDimensionFreeRing.Ring (EmptyGammaGround.base {c | baseCarrier c})) where
  value := diagonalRESClass
  unit := diagonalRESClass_unit
  product := diagonalRESClass_product
  iso _ _ f := diagonalRESClass_iso f
  empty := diagonalRESClass_empty
  scissor := diagonalRESClass_scissor

def diagonalToRES : DiagonalConstructible.Ring →+*
    RESDimensionFreeRing.Ring (EmptyGammaGround.base {c | baseCarrier c}) :=
  DiagonalConstructible.lift diagonalRESInvariant

theorem diagonalToRES_objectClass (X : DiagonalConstructible.Object) :
    diagonalToRES (DiagonalConstructible.objectClass X) = diagonalRESClass X :=
  DiagonalConstructible.lift_objectClass diagonalRESInvariant X

end DiamondIntegral.Section5.PuiseuxOriginal
