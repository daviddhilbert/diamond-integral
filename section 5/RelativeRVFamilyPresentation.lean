import «section 5».OriginalRVTotalGraphs
import «section 5».RESSetSumSchemata
import «section 5».RESSetProductSchemata
import Section4.PositiveAdditivePresentation

/-! The relative positive presentation remembers the original RV base.
Products share that base; isomorphisms preserve its coordinates. The
absolute total-family value will therefore be an additive invariant. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ}

abbrev RelativeRVFamily (B : Base (M := M)) (p : ℕ) :=
  (a : ℕ) × GammaDomainFormula B p a (fun _ => .rv)

def RelativeRVFamily.total (F : RelativeRVFamily B p)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) := originalRVTotalFamily X F.2

def RelativeRVFamily.empty (B : Base (M := M)) (p : ℕ) : RelativeRVFamily B p :=
  ⟨0,⟨∅,DefinableOverBase.empty B _⟩⟩

def RelativeRVFamily.one (B : Base (M := M)) (p : ℕ) : RelativeRVFamily B p :=
  ⟨0,⟨sortedUniverse (Fin.append (fun _ : Fin p => .rv) (fun _ : Fin 0 => .rv)),
    real_definableOverBase B _ _ (sortedUniverse_definable B.real _)⟩⟩

def RelativeRVFamily.sum (F G : RelativeRVFamily B p) : RelativeRVFamily B p :=
  ⟨1+(F.1+G.1),((⟨F.2,0⟩ : RESSetSchema B p F.1 (fun _ => .rv)).sum
    (⟨G.2,0⟩ : RESSetSchema B p G.1 (fun _ => .rv))).domain⟩

def RelativeRVFamily.product (F G : RelativeRVFamily B p) : RelativeRVFamily B p :=
  ⟨G.1+F.1,((⟨F.2,0⟩ : RESSetSchema B p F.1 (fun _ => .rv)).product
    (⟨G.2,0⟩ : RESSetSchema B p G.1 (fun _ => .rv))).domain⟩

structure RelativeRVBijection
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F G : RelativeRVFamily B p) where
  bijection : GammaGroundBijection (F.total X) (G.total X)
  preserves_base : ∀ u : F.total X,
    (bijection.map u).val ∘ Fin.castAdd G.1 = u.val ∘ Fin.castAdd F.1

def RelativeRVBijection.id
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F : RelativeRVFamily B p) :
    RelativeRVBijection X F F := ⟨GammaGroundBijection.id _,fun _ => rfl⟩

def RelativeRVBijection.comp
    {X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)} {F G H : RelativeRVFamily B p}
    (g : RelativeRVBijection X G H) (f : RelativeRVBijection X F G) : RelativeRVBijection X F H :=
  ⟨g.bijection.comp f.bijection,fun u => (g.preserves_base (f.bijection.map u)).trans (f.preserves_base u)⟩

def RelativeRVBijection.symm
    {X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)} {F G : RelativeRVFamily B p}
    (f : RelativeRVBijection X F G) : RelativeRVBijection X G F := by
  refine ⟨f.bijection.symm,?_⟩
  intro u
  have h := f.preserves_base (f.bijection.symm.map u)
  have he : f.bijection.map (f.bijection.symm.map u) = u := GammaGroundMap.apply_inverse _ _ u
  rw [he] at h
  exact h.symm

def relativeRVFamilyPresentation
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) : Presentation (RelativeRVFamily B p) where
  iso F G := Nonempty (RelativeRVBijection X F G)
  empty := RelativeRVFamily.empty B p
  scissor F G H I := F = H.sum I ∧ G = RelativeRVFamily.empty B p

theorem relativeRVFamilyClass_sum
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F G : RelativeRVFamily B p) :
    of (relativeRVFamilyPresentation X) (F.sum G) =
      of (relativeRVFamilyPresentation X) F + of (relativeRVFamilyPresentation X) G := by
  have h := of_scissor (relativeRVFamilyPresentation X)
    (a := F.sum G) (b := RelativeRVFamily.empty B p) (c := F) (d := G) ⟨rfl,rfl⟩
  have hempty : of (relativeRVFamilyPresentation X) (RelativeRVFamily.empty B p) = 0 :=
    of_empty (relativeRVFamilyPresentation X)
  simpa only [hempty,add_zero] using h

theorem relativeRVFamilyClass_iso
    {X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)} {F G : RelativeRVFamily B p}
    (f : RelativeRVBijection X F G) :
    of (relativeRVFamilyPresentation X) F = of (relativeRVFamilyPresentation X) G :=
  of_iso (relativeRVFamilyPresentation X) ⟨f⟩

end DiamondIntegral.Section5
