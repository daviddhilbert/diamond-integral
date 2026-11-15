import «section 5».ComplexRationalGraphCover
import Mathlib.ModelTheory.Definability

/-! Finite rational descriptions for actual pure-field definable graphs,
with any finite number of output coordinates. All coefficients belong to
the original complex field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
local instance rationalGraphComplexRing : CompatibleRing ℂ := compatibleRingOfRing ℂ

theorem complex_definable_named_formula {α : Type} {D : Set (α → ℂ)}
    (hD : (Set.univ : Set ℂ).Definable Language.ring D) :
    ∃ φ : (Language.ring[[ℂ]]).Formula α, ∀ v, v ∈ D ↔ φ.Realize v := by
  obtain ⟨ψ, rfl⟩ := hD
  let f : ↥(Set.univ : Set ℂ) → ℂ := Subtype.val
  letI : (LHom.constantsOnMap f).IsExpansionOn ℂ :=
    constantsOnMap_isExpansionOn rfl
  letI : (Language.ring.lhomWithConstantsMap f).IsExpansionOn ℂ :=
    LHom.sumMap_isExpansionOn _ _ _
  refine ⟨(Language.ring.lhomWithConstantsMap f).onFormula ψ, ?_⟩
  intro v
  exact (LHom.realize_onFormula _ _).symm

theorem complex_definable_scalar_graph_finite_rational_cover {n : ℕ}
    (G : Set (Fin n ⊕ Fin 1 → ℂ))
    (hG : (Set.univ : Set ℂ).Definable Language.ring G)
    (hu : ∀ (x : Fin n → ℂ) (y z : ℂ), Sum.elim x (fun _ => y) ∈ G →
      Sum.elim x (fun _ => z) ∈ G → y = z) :
    ∃ s : Finset (MvPolynomial (Fin n) ℂ × MvPolynomial (Fin n) ℂ),
      ∀ (x : Fin n → ℂ) (y : ℂ), Sum.elim x (fun _ => y) ∈ G →
        ∃ pq ∈ s, pq.2.eval₂ (RingHom.id ℂ) x ≠ 0 ∧
          y * pq.2.eval₂ (RingHom.id ℂ) x = pq.1.eval₂ (RingHom.id ℂ) x := by
  obtain ⟨φ, hφ⟩ := complex_definable_named_formula hG
  obtain ⟨s, hs⟩ := complex_scalar_graph_finite_rational_cover φ
    (fun x y z hy hz => hu x y z ((hφ _).mpr hy) ((hφ _).mpr hz))
  exact ⟨s, fun x y hy => hs x y ((hφ _).mp hy)⟩

def scalarCoordinateGraph {n m : ℕ} (G : Set (Fin n ⊕ Fin m → ℂ)) (j : Fin m) :
    Set (Fin n ⊕ Fin 1 → ℂ) :=
  {v | ∃ y : Fin m → ℂ, Sum.elim (fun i => v (.inl i)) y ∈ G ∧ y j = v (.inr 0)}

theorem scalarCoordinateGraph_definable {n m : ℕ}
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hG : (Set.univ : Set ℂ).Definable Language.ring G) (j : Fin m) :
    (Set.univ : Set ℂ).Definable Language.ring (scalarCoordinateGraph G j) := by
  have he : scalarCoordinateGraph G j =
      (fun v : Fin n ⊕ Fin m → ℂ => v ∘ Sum.map id (fun _ : Fin 1 => j)) '' G := by
    ext v
    constructor
    · rintro ⟨y, hy, hj⟩
      refine ⟨Sum.elim (fun i => v (.inl i)) y, hy, ?_⟩
      funext i
      cases i with
      | inl i => rfl
      | inr k =>
        change y j = v (.inr k)
        exact hj.trans (congrArg (fun k => v (.inr k)) (Subsingleton.elim 0 k))
    · rintro ⟨w, hw, rfl⟩
      refine ⟨fun k => w (.inr k), ?_, rfl⟩
      convert hw using 1
      funext i
      cases i <;> rfl
  rw [he]
  exact hG.image_comp _

theorem complex_definable_graph_finite_rational_cover {n m : ℕ}
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hG : (Set.univ : Set ℂ).Definable Language.ring G)
    (hu : ∀ (x : Fin n → ℂ) (y z : Fin m → ℂ),
      Sum.elim x y ∈ G → Sum.elim x z ∈ G → y = z) :
    ∃ s : Finset (Fin m → MvPolynomial (Fin n) ℂ × MvPolynomial (Fin n) ℂ),
      ∀ (x : Fin n → ℂ) (y : Fin m → ℂ), Sum.elim x y ∈ G →
        ∃ r ∈ s, ∀ j, (r j).2.eval₂ (RingHom.id ℂ) x ≠ 0 ∧
          y j * (r j).2.eval₂ (RingHom.id ℂ) x = (r j).1.eval₂ (RingHom.id ℂ) x := by
  have hc (j : Fin m) := complex_definable_scalar_graph_finite_rational_cover
    (scalarCoordinateGraph G j) (scalarCoordinateGraph_definable G hG j)
    (by
      intro x a b ha hb
      obtain ⟨y, hy, hya⟩ := ha
      obtain ⟨z, hz, hzb⟩ := hb
      exact hya.symm.trans ((congrFun (hu x y z hy hz) j).trans hzb))
  choose s hs using hc
  let R := ∀ j, ↥(s j)
  let candidates : Finset (Fin m → MvPolynomial (Fin n) ℂ × MvPolynomial (Fin n) ℂ) :=
    Finset.univ.image (fun r : R => fun j => (r j).val)
  refine ⟨candidates, ?_⟩
  intro x y hxy
  have hw (j : Fin m) := hs j x (y j) (by exact ⟨y, hxy, rfl⟩)
  choose r hr hformula using hw
  let witness : R := fun j => ⟨r j, hr j⟩
  refine ⟨r, Finset.mem_image.mpr ⟨witness, Finset.mem_univ _, rfl⟩, hformula⟩

end DiamondIntegral.Section5
