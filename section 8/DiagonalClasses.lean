import «section 8».TruncClasses
import FubiniTheorems.Comparison.GeometricLinearIdeals
import FubiniTheorems.Comparison.GeometricTheta
import FubiniTheorems.Fubini.InflatedFamilyFubiniVol

/-! Classes of diagonal constructible objects in `K^μ̂ Var_ℂ / (linear actions)`.

* `dcClass_product`, `dcClass_iso`, `dcClass_affineSpace`: `dcClass` is multiplicative, invariant
  under isomorphisms, and an affine space with any weights has class `[𝔸]^n`.
* `reindexIso`: a coordinate permutation preserving weights and domains is an isomorphism. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace DiamondIntegral.Section8.Truncation

open Classical FirstOrder FirstOrder.Language
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.RingDefinable

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem dcClass_eq_comparison (X : DiagonalConstructible.Object) :
    dcClass X = DiagonalConstructible.geometricLinearActionComparison
      (Ideal.Quotient.mk DiagonalConstructible.linearActionIdeal (DiagonalConstructible.objectClass X)) :=
  (DiagonalConstructible.geometricLinearActionComparison_mk _).symm

theorem dcClass_product (X Y : DiagonalConstructible.Object) :
    dcClass (DiagonalConstructible.product X Y) = dcClass X * dcClass Y := by
  rw [dcClass, DiagonalConstructible.objectClass_product, map_mul, map_mul]
  rfl

theorem dcClass_iso {X Y : DiagonalConstructible.Object} (f : DiagonalConstructible.Iso X Y) :
    dcClass X = dcClass Y := by
  rw [dcClass, dcClass, DiagonalConstructible.objectClass_iso f]

theorem dcClass_affineSpace {n : ℕ} (q : Fin n → ℚ) :
    dcClass (DiagonalConstructible.affineSpace q) = modifiedAffineLineClass ^ n := by
  have h0 : dcClass (DiagonalConstructible.affineSpace q) =
      dcClass (DiagonalConstructible.affineSpace (fun _ : Fin n => (0 : ℚ))) := by
    rw [dcClass_eq_comparison, dcClass_eq_comparison]
    congr 1
    exact Ideal.Quotient.eq.mpr (DiagonalConstructible.affine_difference_mem q)
  rw [h0, dcClass, DiagonalConstructible.affineSpace_class, map_prod, map_prod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [DiagonalConstructible.affineLine, DiagonalConstructible.toVarietyRing_affineSpace]
  rfl

/-! ### Isomorphisms given by coordinate permutations -/

theorem rdef_coord_eq {N : ℕ} (a b : Fin N) : RDef {z : Fin N → ℂ | z a = z b} := by
  convert rdef_zero (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin N) ℂ) using 1
  ext z
  simp [sub_eq_zero]

/-- The equivalence of domains of a coordinate permutation. -/
def reindexEquiv (X Y : DiagonalConstructible.Object) (π : Fin X.arity ≃ Fin Y.arity)
    (hd : ∀ x : Fin X.arity → ℂ, x ∈ X.domain ↔ x ∘ π.symm ∈ Y.domain) : X.domain ≃ Y.domain where
  toFun := fun x => ⟨x.val ∘ π.symm, (hd x.val).mp x.property⟩
  invFun := fun y => ⟨y.val ∘ π, (hd _).mpr (by
    have : (y.val ∘ π) ∘ π.symm = y.val := by funext j; simp
    rw [this]; exact y.property)⟩
  left_inv := fun x => Subtype.ext (by funext i; simp)
  right_inv := fun y => Subtype.ext (by funext j; simp)

theorem reindex_graph (X Y : DiagonalConstructible.Object) (π : Fin X.arity ≃ Fin Y.arity)
    (hd : ∀ x : Fin X.arity → ℂ, x ∈ X.domain ↔ x ∘ π.symm ∈ Y.domain) :
    framedEquivGraph X.domain Y.domain (reindexEquiv X Y π hd) =
      {z | (fun i => z (Fin.castAdd Y.arity i)) ∈ X.domain ∧
        ∀ j, z (Fin.natAdd X.arity j) = z (Fin.castAdd Y.arity (π.symm j))} := by
  ext z
  simp only [framedEquivGraph, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, hy⟩
    refine ⟨?_, fun j => ?_⟩
    · rw [hx]; exact x.property
    · have h1 := congrFun hy j
      have h2 := congrFun hx (π.symm j)
      change z (Fin.natAdd X.arity j) = x.val (π.symm j) at h1
      change z (Fin.castAdd Y.arity (π.symm j)) = x.val (π.symm j) at h2
      rw [h1, h2]
  · rintro ⟨hx, hy⟩
    refine ⟨⟨fun i => z (Fin.castAdd Y.arity i), hx⟩, rfl, ?_⟩
    funext j
    exact hy j

/-- A coordinate permutation `π` with `Y.weights ∘ π = X.weights` and `x ∈ X ↔ x ∘ π⁻¹ ∈ Y` is an
isomorphism `X ≅ Y`. -/
def reindexIso (X Y : DiagonalConstructible.Object) (π : Fin X.arity ≃ Fin Y.arity)
    (hw : ∀ i, Y.weights (π i) = X.weights i)
    (hd : ∀ x : Fin X.arity → ℂ, x ∈ X.domain ↔ x ∘ π.symm ∈ Y.domain) :
    DiagonalConstructible.Iso X Y where
  equiv := reindexEquiv X Y π hd
  graph_definable := by
    rw [reindex_graph]
    have h := (X.definable.preimage_comp (Fin.castAdd Y.arity)).inter
      (rdef_iInter fun j : Fin Y.arity => rdef_coord_eq (Fin.natAdd X.arity j) (Fin.castAdd Y.arity (π.symm j)))
    convert h using 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  graph_invariant := by
    rw [reindex_graph]
    intro η z
    have hw' : ∀ j, Y.weights j = X.weights (π.symm j) := by
      intro j
      have := hw (π.symm j)
      rwa [_root_.Equiv.apply_symm_apply] at this
    have hcast : (fun i => rationalAction (Fin.append X.weights Y.weights) η z (Fin.castAdd Y.arity i)) =
        rationalAction X.weights η (fun i => z (Fin.castAdd Y.arity i)) := by
      funext i; simp [rationalAction, Fin.append_left]
    simp only [Set.mem_ofPred_eq]
    rw [hcast, X.invariant η]
    refine and_congr Iff.rfl (forall_congr' fun j => ?_)
    simp only [rationalAction, Fin.append_left, Fin.append_right, hw']
    constructor
    · intro h
      exact mul_left_cancel₀ (Units.ne_zero _) h
    · intro h
      rw [h]

end DiamondIntegral.Section8.Truncation
