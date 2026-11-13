import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.ModelTheory.Definability
import Mathlib.FieldTheory.Galois.Infinite

/-! Definable bijections over a field preserve its rational points inside
a Galois extension. This applies to arbitrary first-order definable maps,
not only polynomial maps, and is the point-counting step needed after
finite-field specialization. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.DefinableGaloisPoints

theorem definable_invariant {K α : Type*} [Field K] [FirstOrder.Ring.CompatibleRing K]
    {A : Set K} {S : Set (α → K)} (hS : A.Definable Language.ring S)
    (τ : K ≃+* K) (hτ : ∀ a ∈ A, τ a = a) (x : α → K) :
    τ ∘ x ∈ S ↔ x ∈ S := by
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hS
  rw [hφ]
  let e : Language.ring.Equiv K K := FirstOrder.Ring.languageEquivEquivRingEquiv.symm τ
  have hv : e ∘ Sum.elim (fun a : A => a.val) x =
      Sum.elim (fun a : A => a.val) (τ ∘ x) := by
    funext z
    cases z with
    | inl a => exact hτ a.val a.property
    | inr i => rfl
  have he := StrongHomClass.realize_formula e φ (v := Sum.elim (fun a : A => a.val) x)
  rw [hv] at he
  exact he

variable {E K α β : Type*} [Field E] [Field K] [Algebra E K]
variable [FirstOrder.Ring.CompatibleRing K]

def graphOn (S : Set (α → K)) (f : (α → K) → (β → K)) : Set ((α ⊕ β) → K) :=
  {w | w ∘ Sum.inl ∈ S ∧ f (w ∘ Sum.inl) = w ∘ Sum.inr}

def rationalPoints (S : Set (α → K)) : Set (α → K) :=
  {x | x ∈ S ∧ ∀ i, x i ∈ Set.range (algebraMap E K)}

theorem graph_transport {S : Set (α → K)} {f : (α → K) → (β → K)}
    (hg : (Set.range (algebraMap E K)).Definable Language.ring (graphOn S f))
    (τ : K ≃ₐ[E] K) {x : α → K} (hx : x ∈ S) :
    τ ∘ x ∈ S ∧ f (τ ∘ x) = τ ∘ f x := by
  have hfix : ∀ a ∈ Set.range (algebraMap E K), τ.toRingEquiv a = a := by
    rintro a ⟨b, rfl⟩
    exact τ.commutes b
  have he := (definable_invariant hg τ.toRingEquiv hfix (Sum.elim x (f x))).mpr ⟨hx, rfl⟩
  exact he

theorem fixes_rational {x : α → K} (hx : ∀ i, x i ∈ Set.range (algebraMap E K))
    (τ : K ≃ₐ[E] K) : τ ∘ x = x := by
  funext i
  obtain ⟨a, ha⟩ := hx i
  rw [Function.comp_apply, ← ha, τ.commutes]

theorem mapsTo_rational [IsGalois E K] {S : Set (α → K)} {T : Set (β → K)}
    {f : (α → K) → (β → K)}
    (hg : (Set.range (algebraMap E K)).Definable Language.ring (graphOn S f))
    (hm : Set.MapsTo f S T) : Set.MapsTo f (rationalPoints (E := E) S) (rationalPoints (E := E) T) := by
  intro x hx
  refine ⟨hm hx.1, fun i => (InfiniteGalois.mem_range_algebraMap_iff_fixed (f x i)).mpr ?_⟩
  intro τ
  have he := (graph_transport hg τ hx.1).2
  rw [fixes_rational hx.2 τ] at he
  exact (congrFun he i).symm

theorem bijOn_rational [IsGalois E K] {S : Set (α → K)} {T : Set (β → K)}
    {f : (α → K) → (β → K)}
    (hg : (Set.range (algebraMap E K)).Definable Language.ring (graphOn S f))
    (hb : Set.BijOn f S T) : Set.BijOn f (rationalPoints (E := E) S) (rationalPoints (E := E) T) := by
  refine ⟨mapsTo_rational hg hb.mapsTo, hb.injOn.mono (fun _ hx => hx.1), ?_⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hb.surjOn hy.1
  refine ⟨x, ⟨hx, fun i => (InfiniteGalois.mem_range_algebraMap_iff_fixed (x i)).mpr ?_⟩, hxy⟩
  intro τ
  obtain ⟨hτx, he⟩ := graph_transport hg τ hx
  have hfix : τ ∘ y = y := fixes_rational hy.2 τ
  rw [hxy, hfix] at he
  have hxx : τ ∘ x = x := hb.injOn hτx hx (he.trans hxy.symm)
  exact congrFun hxx i

theorem rationalPoints_finite [Finite α] [Finite E] (S : Set (α → K)) :
    (rationalPoints (E := E) S).Finite := by
  apply (Set.finite_range (fun x : α → E => algebraMap E K ∘ x)).subset
  intro x hx
  choose a ha using hx.2
  exact ⟨a, funext ha⟩

theorem rational_count_eq [IsGalois E K] {S : Set (α → K)} {T : Set (β → K)}
    {f : (α → K) → (β → K)}
    (hg : (Set.range (algebraMap E K)).Definable Language.ring (graphOn S f))
    (hb : Set.BijOn f S T) :
    (rationalPoints (E := E) S).ncard = (rationalPoints (E := E) T).ncard :=
  Nat.card_congr (bijOn_rational hg hb).equiv

end DiamondIntegral.Section4.DefinableGaloisPoints
