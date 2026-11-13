import «section 3».RVGenericCoordinateInvariance
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Coordinatewise value invariance implies invariance on the whole
nonzero RV preimage, including the empty tuple in degree zero. -/
theorem rvCoordinateInvariant_full_fibre {n : ℕ} (A : Set (Fin n → M))
    (hA : ∀ i, RVCoordinateInvariant A i) (p q : Fin n → M) (h : Same p q) :
    p ∈ A ↔ q ∈ A := by
  induction n with
  | zero =>
    have he : p = q := Subsingleton.elim _ _
    rw [he]
  | succ n ih =>
    let D : Set (Fin n → M) := {a | (Fin.snoc a (q (Fin.last n)) : Fin (n+1) → M) ∈ A}
    have hp : ∀ i, NonzeroRV (p i) := fun i => (h i).1
    have hq : ∀ i, NonzeroRV (q i) := fun i => (h i).2.1
    have hD : ∀ i, RVCoordinateInvariant D i := by
      intro i a ha x hx
      have hsnoc : ∀ j : Fin (n+1), NonzeroRV (((Fin.snoc a (q (Fin.last n)) : Fin (n+1) → M) : Fin (n+1) → M) j) := by
        intro j
        exact Fin.lastCases (by simpa only [Fin.snoc_last] using hq (Fin.last n))
          (fun k => by simpa only [Fin.snoc_castSucc] using ha k) j
      have hs : SameScalar x ((Fin.snoc a (q (Fin.last n)) : Fin (n+1) → M) i.castSucc) := by
        simpa only [Fin.snoc_castSucc] using hx
      have hh := hA i.castSucc ((Fin.snoc a (q (Fin.last n)) : Fin (n+1) → M)) hsnoc x hs
      have he : Function.update ((Fin.snoc a (q (Fin.last n)) : Fin (n+1) → M)) i.castSucc x =
          Fin.snoc (Function.update a i x) (q (Fin.last n)) := by
        funext j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simp [Ne.symm (Fin.castSucc_ne_last i)]
        · by_cases hk : k = i
          · subst k; simp
          · simp [hk]
      change ((Fin.snoc a (q (Fin.last n)) : Fin (n+1) → M) ∈ A ↔ Fin.snoc (Function.update a i x) (q (Fin.last n)) ∈ A)
      rw [← he]
      exact hh
    have hinit : Same (Fin.init p) (Fin.init q) := fun i => h i.castSucc
    have hind := ih D hD (Fin.init p) (Fin.init q) hinit
    have hlast := hA (Fin.last n) p hp (q (Fin.last n))
      ((same_scalar_symm _ _).mp (h (Fin.last n)))
    have he : Function.update p (Fin.last n) (q (Fin.last n)) =
        Fin.snoc (Fin.init p) (q (Fin.last n)) := by
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [Fin.init_def]
    rw [he] at hlast
    exact hlast.trans (hind.trans (by change Fin.snoc (Fin.init q) (q (Fin.last n)) ∈ A ↔ q ∈ A; rw [Fin.snoc_init_self]))

/-- Generic selection in every coordinate produces a full value-fibre
invariant set by an explicit finite iteration. -/
def rvFullFibreGeneric {n : ℕ} (A : Set (Fin n → M)) : Set (Fin n → M) :=
  (List.finRange n).foldl rvGenericCoordinate A

theorem rvFullFibreGeneric_invariant {n : ℕ} (A : Set (Fin n → M))
    (p q : Fin n → M) (h : Same p q) :
    p ∈ rvFullFibreGeneric A ↔ q ∈ rvFullFibreGeneric A :=
  rvCoordinateInvariant_full_fibre _
    (fun i => rvGenericCoordinate_fold_invariant A (List.finRange n) i (by simp)) p q h

theorem rvFullFibreGeneric_definableOverBase {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {n : ℕ} (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A) :
    DefinableOverBase B (fun _ => .rv) (rvFullFibreGeneric A) :=
  rvGenericCoordinate_fold_definableOverBase hc hs h00 B hsmall A hA _

end DiamondIntegral.Section3
