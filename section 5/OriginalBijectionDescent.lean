import «section 5».ActualGraphDescent
import «section 3».DefinableBijections

/-! Equivariant constructible bijections descend to actual original-base
definable bijections. The complete graph, with every representative, is kept. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry DiamondIntegral.Section3
local instance bijectionDescentStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem append_relation_definable {S : Set Carrier} {n m : ℕ}
    (G : DefSet (rawRVSpace (M := Carrier) (n + m)) S) :
    (rawRVSpace n).RelationDefinable (rawRVSpace m) S
      (fun x y => Fin.append x y ∈ G.carrier) := by
  let P := rawRVSpace (M := Carrier) n
  let Q := rawRVSpace (M := Carrier) m
  have hg := G.definable.preimage_comp (finSumFinEquiv.symm : Fin (n + m) → Fin n ⊕ Fin m)
  have hd := ((P.definable_domain S).preimage_comp Sum.inl).inter
    ((Q.definable_domain S).preimage_comp Sum.inr)
  have hrow (x : Fin n → CanonicalRV.RVSort Carrier) (y : Fin m → CanonicalRV.RVSort Carrier) :
      (Sum.elim (rvValues x) (rvValues y) ∘ finSumFinEquiv.symm) ∈
        (rawRVSpace (n + m)).preimage G.carrier ↔ Fin.append x y ∈ G.carrier := by
    have he : Sum.elim (rvValues x) (rvValues y) ∘ finSumFinEquiv.symm = rvValues (Fin.append x y) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [rvValues]
    rw [he]
    exact rawRV_preimage_mem G _
  change S.Definable LRV _
  convert hd.inter hg using 1
  ext z
  have hz (hx : z ∘ Sum.inl ∈ P.domain) (hy : z ∘ Sum.inr ∈ Q.domain) :
      (z ∘ finSumFinEquiv.symm) ∈ (rawRVSpace (n + m)).preimage G.carrier ↔
        Fin.append (P.decode ⟨z ∘ Sum.inl, hx⟩) (Q.decode ⟨z ∘ Sum.inr, hy⟩) ∈ G.carrier := by
    have h := hrow (P.decode ⟨z ∘ Sum.inl, hx⟩) (Q.decode ⟨z ∘ Sum.inr, hy⟩)
    rw [rvValues_decode, rvValues_decode] at h
    simpa only [Sum.elim_comp_inl_inr] using h
  constructor
  · rintro ⟨hx, hy, h⟩
    exact ⟨⟨hx, hy⟩, (hz hx hy).mpr h⟩
  · rintro ⟨⟨hx, hy⟩, h⟩
    exact ⟨hx, hy, (hz hx hy).mp h⟩

def originalDescendedBijection {n m : ℕ} (N : ℕ+) (a : Fin n → ℤ) (b : Fin m → ℤ)
    (X : Set (Fin n → ℂ)) (Y : Set (Fin m → ℂ))
    (hX : (Set.univ : Set ℂ).Definable Language.ring X)
    (hY : (Set.univ : Set ℂ).Definable Language.ring Y)
    (hiX : FiniteInvariant N a X) (hiY : FiniteInvariant N b Y) (e : X ≃ Y)
    (hG : (Set.univ : Set ℂ).Definable Language.ring (framedEquivGraph X Y e))
    (hiG : FiniteInvariant N (Fin.append a b) (framedEquivGraph X Y e)) :
    DefinableBijection (descendedOriginalSet N a X hX) (descendedOriginalSet N b Y hY) := by
  let A := descendedOriginalSet N a X hX
  let B := descendedOriginalSet N b Y hY
  let E := actualDescendedBijection N a b X Y hX hY hiX hiY e
  let G := descendedOriginalSet N (Fin.append a b) (framedEquivGraph X Y e) hG
  let P := rawRVSpace (M := Carrier) n
  let Q := rawRVSpace (M := Carrier) m
  have hrel := (A.definable.left_relation P Q).inter P Q
    ((B.definable.right_relation P Q).inter P Q (append_relation_definable G))
  refine ⟨⟨E, hrel.congr P Q ?_⟩, E.bijective⟩
  intro x y
  constructor
  · rintro ⟨hx, hy, hxy⟩
    let u : A := ⟨x, hx⟩
    let v : B := ⟨y, hy⟩
    have he : E u = v := (actual_descended_graph N a b X Y hX hY hiX hiY e hG hiG u v).mp hxy
    exact ⟨u, rfl, congrArg Subtype.val he⟩
  · rintro ⟨u, rfl, hy⟩
    have hv : y ∈ B.carrier := hy ▸ (E u).property
    refine ⟨u.property, hv, ?_⟩
    exact (actual_descended_graph N a b X Y hX hY hiX hiY e hG hiG u ⟨y, hv⟩).mpr
      (Subtype.ext hy)

end DiamondIntegral.Section5.PuiseuxOriginal
