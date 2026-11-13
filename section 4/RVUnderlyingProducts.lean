import «section 4».RVUnderlyingIsomorphisms
import «section 4».RVMeasuredProductProperties

/-! Cartesian products of actual underlying RV bijections retain their
original-base definable graphs, even when their chart degrees differ. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVUnderlyingProducts
open RVMeasuredCharts RVMeasuredProduct RVRealProducts FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def domainEquiv {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l) :
    (product a b).domain ≃ a.domain × b.domain where
  toFun u := (⟨u.val ∘ headIndex b.arity a.arity, u.property.1⟩,
    ⟨u.val ∘ tailIndex b.arity a.arity, u.property.2⟩)
  invFun p := ⟨join b.arity a.arity p.1.val p.2.val, (productSet_join _ _ _ _).mpr ⟨p.1.property, p.2.property⟩⟩
  left_inv u := Subtype.ext (join_reconstruct b.arity a.arity u.val)
  right_inv p := Prod.ext (Subtype.ext (funext (join_head b.arity a.arity p.1.val p.2.val)))
    (Subtype.ext (funext (join_tail b.arity a.arity p.1.val p.2.val)))

def productEquiv {B : Base (M := M)} {k l m n : ℕ} {a : Chart B k} {b : Chart B l}
    {c : Chart B m} {d : Chart B n} (F : RVUnderlyingIsomorphisms.Iso a b) (G : RVUnderlyingIsomorphisms.Iso c d) :
    (product a c).domain ≃ (product b d).domain :=
  (domainEquiv a c).trans ((Equiv.prodCongr F.equiv G.equiv).trans (domainEquiv b d).symm)

theorem productEquiv_coe {B : Base (M := M)} {k l m n : ℕ} {a : Chart B k} {b : Chart B l}
    {c : Chart B m} {d : Chart B n} (F : RVUnderlyingIsomorphisms.Iso a b) (G : RVUnderlyingIsomorphisms.Iso c d)
    (u : (product a c).domain) :
    (productEquiv F G u).val = productMap F.extension G.extension u.val := by
  change join d.arity b.arity (F.equiv ⟨u.val ∘ headIndex c.arity a.arity, u.property.1⟩).val
    (G.equiv ⟨u.val ∘ tailIndex c.arity a.arity, u.property.2⟩).val = _
  unfold productMap
  exact congrArg₂ (join d.arity b.arity)
    (F.extension_on ⟨u.val ∘ headIndex c.arity a.arity, u.property.1⟩).symm
    (G.extension_on ⟨u.val ∘ tailIndex c.arity a.arity, u.property.2⟩).symm

def productIso {B : Base (M := M)} {k l m n : ℕ} {a : Chart B k} {b : Chart B l}
    {c : Chart B m} {d : Chart B n} (F : RVUnderlyingIsomorphisms.Iso a b) (G : RVUnderlyingIsomorphisms.Iso c d) :
    RVUnderlyingIsomorphisms.Iso (product a c) (product b d) where
  equiv := productEquiv F G
  graph_definable := by
    have h := product_graph_definable B a.domain c.domain F.extension G.extension F.extension_graph G.extension_graph
    have he : {w | ∃ u : (product a c).domain,
        w = join (product b d).arity (product a c).arity u.val (productEquiv F G u).val} =
        graphOn (product a c).domain (productMap F.extension G.extension) := by
      ext w
      change (∃ u : (product a c).domain, w = join (d.arity + b.arity) (c.arity + a.arity) u.val (productEquiv F G u).val) ↔
        w ∈ graphOn (productSet a.domain c.domain) (productMap F.extension G.extension)
      constructor
      · rintro ⟨u, rfl⟩
        apply (graphOn_exists (productSet a.domain c.domain) (productMap F.extension G.extension) _).mpr
        exact ⟨u.val, u.property, congrArg (join (product b d).arity (product a c).arity u.val) (productEquiv_coe F G u)⟩
      · intro hw
        obtain ⟨u, hu, rfl⟩ := (graphOn_exists (productSet a.domain c.domain) (productMap F.extension G.extension) _).mp hw
        exact ⟨⟨u, hu⟩, congrArg (join (product b d).arity (product a c).arity u) (productEquiv_coe F G ⟨u, hu⟩).symm⟩
    rw [he]
    exact h

end DiamondIntegral.Section4.RVUnderlyingProducts
