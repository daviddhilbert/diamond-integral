import «section 5».ScalarGammaParameterControl
import «section 3».GammaGroundMapTuples
import «section 3».RVUnitGammaMaps
import Section4.MapProduct

/-! Actual scalar Gamma functions on arbitrary nonzero RV domains become
value functions after a finite partition over the original ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}


theorem finite_scalar_gamma_parameter_control {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    {ι : Type} [Fintype ι]
    (f : ι → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
    ∃ N : ℕ, ∃ A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n),
      ∃ D : Fin N → ι → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))),
      (∀ i, (A i).carrier ⊆ X.carrier) ∧
      (∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier) ∧
      (∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (A i).carrier) ∧
      (∀ i j α, α ∈ (D i j).carrier → ∀ β ∈ (D i j).carrier,
        Fin.init α = Fin.init β → α (Fin.last n) = β (Fin.last n)) ∧
      (∀ i j (x : X), x.val ∈ (A i).carrier → ∀ γ,
        (f j x).val = γ ↔ Fin.snoc (rvUnitTupleValues x.val) γ ∈ (D i j).carrier) := by
  choose N A D hsub hd hcov hfun hrow using
    (fun j => scalar_gamma_parameter_control hκ hs h00 hr hγ hΓ X (f j))
  let J := (j : ι) → Fin (N j)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let Q : Fin (Fintype.card J) → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) := fun i =>
    X.inter ⟨⋂ j, (A j (e i j)).carrier, GammaGroundDefinable.iInter (fun j => (A j (e i j)).definable)⟩
  refine ⟨Fintype.card J, Q, (fun i j => D j (e i j)), ?_, ?_, ?_, ?_, ?_⟩
  · intro i x hx
    exact hx.1
  · intro i k hik
    have hex : ∃ j, e i j ≠ e k j := by
      by_contra h
      push_neg at h
      exact hik (e.injective (funext h))
    obtain ⟨j, hj⟩ := hex
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (hd j _ _ hj) (Set.mem_iInter.mp hx.2 j) (Set.mem_iInter.mp hy.2 j)
  · intro x
    constructor
    · intro hx
      choose j hj using (fun j => (hcov j x).mp hx)
      obtain ⟨i, hi⟩ := e.surjective j
      exact ⟨i, hx, Set.mem_iInter.mpr (fun k => by simpa only [hi] using hj k)⟩
    · rintro ⟨i, hi⟩
      exact hi.1
  · intro i j α hα β hβ hi
    exact hfun j (e i j) α hα β hβ hi
  · intro i j x hx γ
    exact hrow j (e i j) x (Set.mem_iInter.mp hx.2 j) γ

end DiamondIntegral.Section5
