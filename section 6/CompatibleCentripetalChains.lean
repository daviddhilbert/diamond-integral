import «section 6».CarriedComponentRestrictions

/-! A finite preparation chain with compatible component data on one
protected piece. The certificate retains the pointwise permitted old
restrictions required by the manuscript, rather than inferring them
from the final image alone. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

inductive CompatibleCentripetalChain : {r s : ℕ} →
    (A : DefSet (rawMixedSpace (M := M) n r) S) →
    (B : DefSet (rawMixedSpace (M := M) n s) S) → Map A B →
    DefSet (rawMixedSpace (M := M) n r) S → Prop where
  | identity (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
      (P : DefSet (rawMixedSpace (M := M) n r) S) (hPA : P.carrier ⊆ A.carrier)
      (hP : ProperInvariant S P.carrier) : CompatibleCentripetalChain A A (Map.id A) P
  | regularize (A : DefSet (rawMixedSpace (M := M) n r) S)
      (hA : ProperInvariant S A.carrier) (hVF : VFDoublyBounded A.carrier)
      (P : DefSet (rawMixedSpace (M := M) n r) S) (hPA : P.carrier ⊆ A.carrier)
      (hP : ProperInvariant S P.carrier) (hPVF : VFDoublyBounded P.carrier) :
      CompatibleCentripetalChain A (regularizeMap A).image (regularization A) P
  | centripetal (A : DefSet (rawMixedSpace (M := M) n r) S) (D : CentripetalData (G := G) A)
      (P : DefSet (rawMixedSpace (M := M) n r) S) (hPA : P.carrier ⊆ A.carrier)
      (E : CentripetalData (G := G) P) (hPoint : ∀ p ∈ P.carrier, E.point p = D.point p) :
      CompatibleCentripetalChain A D.map.image D.bijection P
  | comp {A : DefSet (rawMixedSpace (M := M) n r) S}
      {B : DefSet (rawMixedSpace (M := M) n s) S}
      {C : DefSet (rawMixedSpace (M := M) n t) S} {f : Map A B} {g : Map B C}
      (P : DefSet (rawMixedSpace (M := M) n r) S) (hPA : P.carrier ⊆ A.carrier)
      (hf : CompatibleCentripetalChain A B f P)
      (hg : CompatibleCentripetalChain B C g (f.restrict hPA).image) :
      CompatibleCentripetalChain A C (g.comp f) P

theorem CompatibleCentripetalChain.toChain {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : DefSet (rawMixedSpace (M := M) n r) S}
    (h : CompatibleCentripetalChain (G := G) A B f P) : CentripetalChain (G := G) A B f := by
  induction h with
  | identity A hA P hPA hP => exact .identity A hA
  | regularize A hA hVF P hPA hP hPVF => exact .regularize A hA hVF
  | centripetal A D P hPA E hPoint => exact .centripetal A D
  | comp P hPA hf hg ihf ihg => exact .comp ihf ihg

theorem CompatibleCentripetalChain.source_subset {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : DefSet (rawMixedSpace (M := M) n r) S}
    (h : CompatibleCentripetalChain (G := G) A B f P) : P.carrier ⊆ A.carrier := by
  cases h with
  | identity A hA P hPA hP => exact hPA
  | regularize A hA hVF P hPA hP hPVF => exact hPA
  | centripetal A D P hPA E hPoint => exact hPA
  | comp P hPA hf hg => exact hPA

theorem CompatibleCentripetalChain.source_proper {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : DefSet (rawMixedSpace (M := M) n r) S}
    (h : CompatibleCentripetalChain (G := G) A B f P) : ProperInvariant S P.carrier := by
  induction h with
  | identity A hA P hPA hP => exact hP
  | regularize A hA hVF P hPA hP hPVF => exact hP
  | centripetal A D P hPA E hPoint => exact E.sourceProper
  | comp P hPA hf hg ihf ihg => exact ihf

theorem CompatibleCentripetalChain.literal_restriction {r s : ℕ}
    (h00 : M ⊨ Axioms.ACVF00)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : DefSet (rawMixedSpace (M := M) n r) S}
    (h : CompatibleCentripetalChain (G := G) A B f P) :
    ∀ hPA : P.carrier ⊆ A.carrier,
      SpecialCovariantChain (G := G) P (f.restrict hPA).image (f.restrict hPA).toImage := by
  induction h with
  | identity A hA P hPA hP =>
    intro hSub
    exact (SpecialCovariantChain.identity P hP).restriction_of_liesOver h00 (Map.id A) hSub (fun _ => rfl)
  | regularize A hA hVF P hPA hP hPVF =>
    intro hSub
    exact regularization_restriction_chain h00 hSub hP hPVF
  | centripetal A D P hPA E hPoint =>
    intro hSub
    exact centripetal_restriction_chain h00 D E hSub hPoint
  | @comp r s t A B C f g P hPA hf hg ihf ihg =>
    intro hSub
    have hMid : (f.restrict hPA).image.carrier ⊆ B.carrier := by
      rintro q ⟨p,hp⟩
      exact hp ▸ (f.restrict hPA p).property
    exact (SpecialCovariantChain.comp (ihf hSub) (ihg hMid)).restriction_of_liesOver
      h00 (g.comp f) hSub (fun _ => rfl)

end DiamondIntegral.Section6
