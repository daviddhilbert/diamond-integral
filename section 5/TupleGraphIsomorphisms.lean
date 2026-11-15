import «section 5».FunctionalGraphEquivalences

/-! A complete constructible equivariant graph with checked two-sided
uniqueness gives an actual isomorphism of diagonal constructible objects. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language PuiseuxOriginal
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def diagonalIsoOfTupleGraph (X Y : DiagonalConstructible.Object)
    (G : Set (Fin (X.arity + Y.arity) → ℂ))
    (hG : (Set.univ : Set ℂ).Definable Language.ring G)
    (hiG : RationalInvariant (Fin.append X.weights Y.weights) G)
    (hContained : ∀ z ∈ G, (fun i => z (Fin.castAdd Y.arity i)) ∈ X.domain ∧
      (fun j => z (Fin.natAdd X.arity j)) ∈ Y.domain)
    (hX : ∀ x : X.domain, ∃! y : Y.domain, Fin.append x.val y.val ∈ G)
    (hY : ∀ y : Y.domain, ∃! x : X.domain, Fin.append x.val y.val ∈ G) :
    DiagonalConstructible.Iso X Y := by
  let R := fun x : X.domain => fun y : Y.domain => Fin.append x.val y.val ∈ G
  let e := equivalenceOfGraph R hX hY
  have he : framedEquivGraph X.domain Y.domain e = G := by
    ext z
    constructor
    · rintro ⟨x, hx, hy⟩
      have hR : Fin.append x.val (e x).val ∈ G := (equivalenceOfGraph_iff R hX hY x (e x)).mpr rfl
      have hz : Fin.append x.val (e x).val = z := by
        rw [← hx, ← hy]
        exact Fin.append_castAdd_natAdd (f := z)
      exact hz ▸ hR
    · intro hz
      obtain ⟨hx, hy⟩ := hContained z hz
      let x : X.domain := ⟨(fun i => z (Fin.castAdd Y.arity i)), hx⟩
      let y : Y.domain := ⟨(fun j => z (Fin.natAdd X.arity j)), hy⟩
      have hR : R x y := by
        change Fin.append (fun i => z (Fin.castAdd Y.arity i)) (fun j => z (Fin.natAdd X.arity j)) ∈ G
        simpa only [Fin.append_castAdd_natAdd] using hz
      have hxy : e x = y := (equivalenceOfGraph_iff R hX hY x y).mp hR
      exact ⟨x, rfl, (congrArg Subtype.val hxy).symm⟩
  exact {
    equiv := e
    graph_definable := he.symm ▸ hG
    graph_invariant := he.symm ▸ hiG }

end DiamondIntegral.Section5
