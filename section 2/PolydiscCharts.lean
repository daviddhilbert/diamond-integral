import «section 2».PolydiscNormalForm
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set

/-!
# Coordinate charts for actual polydisc names

A chart enumerates singleton names first and finite-radius names second.
Only singleton names supply VF points; finite centres remain inside the
invariant quotient-name relation. The entire actual DC tuple is retained.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

structure PolydiscNaming {d : ℕ} (D : Fin d → DC (M := M)) where
  pointArity : ℕ
  finiteArity : ℕ
  coordinates : Fin (pointArity + finiteArity) ≃ Fin d
  points : Fin pointArity → VF M
  closed : Fin finiteArity → Bool
  centres : Fin finiteArity → VF M
  radii : Fin finiteArity → Gamma M
  names_eq : normalFormDiscNames points closed centres radii = D ∘ coordinates

def discNameProduct {d : ℕ} (D : Fin d → DC (M := M)) : Set (Fin d → M) :=
  {x | ∀ i, x i ∈ BallImaginaries.underlying (D i)}

theorem PolydiscNaming.product_iff {d : ℕ} {D : Fin d → DC (M := M)}
    (C : PolydiscNaming D) (x : Fin d → M) :
    x ∈ discNameProduct D ↔ x ∘ C.coordinates ∈
      prefixedNamedPolydisc C.points C.closed C.centres C.radii := by
  have hn (i : Fin (C.pointArity+C.finiteArity)) :
      normalFormDiscNames C.points C.closed C.centres C.radii i = D (C.coordinates i) :=
    congrFun C.names_eq i
  constructor
  · intro hx
    constructor
    · funext i
      have h := hx (C.coordinates (Fin.castAdd C.finiteArity i))
      rw [← hn] at h
      simpa only [normalFormDiscNames, Fin.append_left, singletonDiscTupleNames,
        closedDiscCode_infinity_underlying, Set.mem_singleton_iff, Function.comp_apply,
        SpecialTransformations.Section4.vfValues] using h
    · intro i
      have h := hx (C.coordinates (Fin.natAdd C.pointArity i))
      rw [← hn] at h
      simpa only [normalFormDiscNames, Fin.append_right, Function.comp_apply] using h
  · rintro ⟨hp, hf⟩ i
    obtain ⟨j, rfl⟩ := C.coordinates.surjective i
    rw [← hn]
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [normalFormDiscNames, Fin.append_left, singletonDiscTupleNames,
        closedDiscCode_infinity_underlying, Set.mem_singleton_iff]
      exact congrFun hp k
    · simpa only [normalFormDiscNames, Fin.append_right, Function.comp_apply] using hf k

theorem discNameProduct_proper {d : ℕ} (D : Fin d → DC (M := M)) :
    discNameProduct D ⊆ GammaParameters.sortedUniverse (fun _ => .vf) := by
  intro x hx i
  exact disc_underlying_subset_vf _ (hx i)

noncomputable def finitePolydiscNaming {d : ℕ} (closed : Fin d → Bool)
    (a : Fin d → VF M) (δ : Fin d → Gamma M) :
    PolydiscNaming (finitePolydiscNames closed a δ) where
  pointArity := 0
  finiteArity := d
  coordinates := (finCongr (Nat.zero_add d))
  points := Fin.elim0
  closed := closed
  centres := a
  radii := δ
  names_eq := by
    funext j
    refine Fin.addCases (fun i => Fin.elim0 i) (fun i => ?_) j
    simp only [normalFormDiscNames, Fin.append_right, Function.comp_apply]
    congr 1
    apply Fin.ext
    simp

/-- Every closed polydisc, including arbitrary singleton coordinates, has
a chart. The partition is a finite reindexing of its actual DC names. -/
theorem closedPolydiscNaming_nonempty {d : ℕ} (a : Fin d → VF M)
    (γ : Fin d → GammaInfinity M) :
    Nonempty (PolydiscNaming (fun i => closedDiscCode (a i) (γ i))) := by
  classical
  let I : Set (Fin d) := {i | γ i = Values.infinity (M := M)}
  let p := Fintype.card I
  let n := Fintype.card (Iᶜ : Set (Fin d))
  let ep : Fin p ≃ I := (Fintype.equivFin I).symm
  let en : Fin n ≃ (Iᶜ : Set (Fin d)) := (Fintype.equivFin (Iᶜ : Set (Fin d))).symm
  let e : Fin (p+n) ≃ Fin d :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr ep en).trans (Equiv.Set.sumCompl I))
  let points : Fin p → VF M := fun i => a (ep i).val
  let centres : Fin n → VF M := fun i => a (en i).val
  let radii : Fin n → Gamma M := fun i => ⟨γ (en i).val, (en i).property⟩
  have hel (i : Fin p) : e (Fin.castAdd n i) = (ep i).val := by simp [e]
  have her (i : Fin n) : e (Fin.natAdd p i) = (en i).val := by simp [e]
  refine ⟨⟨p, n, e, points, fun _ => true, centres, radii, ?_⟩⟩
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have hi : γ (ep i).val = Values.infinity (M := M) := (ep i).property
    simp only [normalFormDiscNames, Fin.append_left, singletonDiscTupleNames, Function.comp_apply]
    rw [hel]
    change closedDiscCode (a (ep i).val) (Values.infinity (M := M)) =
      closedDiscCode (a (ep i).val) (γ (ep i).val)
    rw [hi]
  · simp only [normalFormDiscNames, Fin.append_right, finitePolydiscNames, ite_true,
      Function.comp_apply]
    rw [her]

end DiamondIntegral.Section2
