import «section 3».GammaGroundRVAngularProductBijections
import «section 3».RVGroundAngularPartition
import Mathlib.Data.Fintype.Sigma
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- An original-Gamma-ground product chart for a nonzero RV tuple piece. The
ambient arities here are independent of an RV[k] label degree. -/
structure GammaGroundRVProductPiece (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (n : ℕ) where
  source : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)
  residueArity : ℕ
  gammaArity : ℕ
  arity_eq : residueArity + gammaArity = n
  residue : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) residueArity)
  gamma : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin gammaArity))
  residue_finite : (rvUnitTupleValues '' residue.carrier).Finite
  bijection : GammaGroundBijection source (residue.prod (gammaGroundRVUnitGammaPreimage gamma))

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem gammaGroundRVAngularCell_product_pieces {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (E : RVAngularCell X.carrier) :
    ∃ N : ℕ, ∃ C : Fin N → GammaGroundRVProductPiece hc B n,
      (∀ i j, i ≠ j → Disjoint (C i).source.carrier (C j).source.carrier) ∧
      ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (C i).source.carrier := by
  let K := Section2.zeroFaceChart (Set.range E.active)
  obtain ⟨N,R,G,Y,hR,hbij,hdis,hcov⟩ := gammaGroundRVAngularCell_product_bijections hκ hs h00 hsmall hγsmall hΓ X E K
  have hdim : K.zeroArity + K.freeArity = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr K.coordinates
  let f := fun i => Classical.choice (hbij i)
  exact ⟨N,fun i => ⟨Y i,K.zeroArity,K.freeArity,hdim,R i,G i,hR i,f i⟩,hdis,hcov⟩

/-- Local geometric product normal form for any actual RV-definable set
on its nonzero tuple locus. All source pieces, residue sets, Gamma sets
and bijections use the original real/Gamma ground. RV[k] labels are separate. -/
theorem gammaGroundRV_nonzero_product_normal_form {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A) :
    ∃ N : ℕ, ∃ C : Fin N → GammaGroundRVProductPiece hc B n,
      (∀ i j, i ≠ j → Disjoint (C i).source.carrier (C j).source.carrier) ∧
      ∀ x : Fin n → (CanonicalRV.RVSort M)ˣ,
        rvUnitValues x ∈ A ↔ ∃ i, x ∈ (C i).source.carrier := by
  obtain ⟨N,W,hW,hE,hWd,hcov⟩ := gammaGround_finite_angular_partition hκ hs h00 hc B hsmall A hA
  let X : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) := fun i => gammaGroundRVUnitSetOfBase (W i) (hW i)
  have hdis : ∀ i j, i ≠ j → Disjoint (X i).carrier (X j).carrier := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun x hi hj => Set.disjoint_left.mp (hWd i j hij) hi hj)
  let E := fun i => Classical.choice (hE i)
  choose L C hCd hCc using fun i => gammaGroundRVAngularCell_product_pieces (hc := hc) hκ hs h00 hsmall hγsmall hΓ (X i) (E i)
  let J := (i : Fin N) × Fin (L i)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let D : J → GammaGroundRVProductPiece hc B n := fun j => C j.1 j.2
  have hsub : ∀ i j, (C i j).source.carrier ⊆ (X i).carrier :=
    fun i j x hx => (hCc i x).mpr ⟨j,hx⟩
  have hDd : ∀ i j : J, i ≠ j → Disjoint (D i).source.carrier (D j).source.carrier := by
    rintro ⟨i,a⟩ ⟨j,b⟩ hne
    by_cases hij : i = j
    · subst j
      exact hCd i a b (fun he => hne (by cases he; rfl))
    · exact (hdis i j hij).mono (hsub i a) (hsub j b)
  refine ⟨Fintype.card J,fun i => D (e i),fun i j hij => hDd (e i) (e j) (fun he => hij (e.injective he)),?_⟩
  intro x
  rw [hcov x]
  constructor
  · rintro ⟨i,hx⟩
    obtain ⟨j,hj⟩ := (hCc i x).mp hx
    obtain ⟨k,hk⟩ := e.surjective ⟨i,j⟩
    exact ⟨k,by simpa only [hk,D] using hj⟩
  · rintro ⟨k,hk⟩
    exact ⟨(e k).1,hsub (e k).1 (e k).2 hk⟩
end DiamondIntegral.Section3
