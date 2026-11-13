import «section 3».GammaPieceSums
import «section 3».GammaGroundGammaPartitions
import «section 3».GammaGroundRVFinitePartitions
import «section 3».TensorProductCuts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n r : ℕ}

/-- A single empty native Gamma piece has zero positive class even
though its finite-family tag is still present. -/
theorem gammaGroundGammaSemiringClass_single_empty :
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single
      (GammaGroundDefSet.empty hc B ((volumeGammaSpace hc).power (Fin n)))) = 0 := by
  let E := GammaGroundGammaObject.empty hc B n
  let G := GammaGroundGammaObject.single (GammaGroundDefSet.empty hc B ((volumeGammaSpace hc).power (Fin n)))
  have h := gammaGroundGammaSemiringClass_iso (asIso (show E.coprod G ⟶ E from
    gammaGroundGammaCoprodEmptyRightHom E G (fun _ => rfl)))
  simpa only [gammaGroundGammaSemiringClass_coprod,E,gammaGroundGammaSemiringClass_empty,zero_add] using h

theorem gammaGroundGammaSemiringClass_native_partition
    (G A D : GammaGroundGammaPiece hc B n)
    (hA : A.carrier ⊆ G.carrier) (hD : D.carrier ⊆ G.carrier)
    (hd : Disjoint A.carrier D.carrier) (hu : (A.union D).carrier = G.carrier) :
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single A) +
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single D) := by
  let E : ((GammaGroundGammaObject.single G).restrict (fun _ => A)).coprod
      ((GammaGroundGammaObject.single G).restrict (fun _ => D)) ≅ GammaGroundGammaObject.single G :=
    asIso (show _ ⟶ _ from gammaGroundGammaPartitionHom (GammaGroundGammaObject.single G)
      (fun _ => A) (fun _ => D) (fun _ => hA) (fun _ => hD) (fun _ => hd) (fun _ => hu))
  have h := gammaGroundGammaSemiringClass_iso E
  rw [gammaGroundGammaSemiringClass_coprod] at h
  exact h.symm

/-- Finite disjoint native Gamma unions are positive sums. Every
comparison uses the actual same-ground Gamma code lift. -/
theorem gammaGroundGammaSemiringClass_native_finiteUnion {ι : Type}
    (F : Finset ι) (A : ι → GammaGroundGammaPiece hc B n)
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier) :
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (gammaGroundDefSetFiniteUnion F A)) =
      ∑ i ∈ F, gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (A i)) := by
  induction F using Finset.induction_on with
  | empty =>
    have he : gammaGroundDefSetFiniteUnion ∅ A = GammaGroundDefSet.empty hc B ((volumeGammaSpace hc).power (Fin n)) := by
      apply gammaGroundDefSet_eq_of_carrier_eq
      ext x
      simp only [gammaGroundDefSetFiniteUnion,Finset.notMem_empty,false_and,exists_false]
      rfl
    rw [he,gammaGroundGammaSemiringClass_single_empty,Finset.sum_empty]
  | @insert i F hi ih =>
    let V := gammaGroundDefSetFiniteUnion F A
    let U := gammaGroundDefSetFiniteUnion (insert i F) A
    have hA : (A i).carrier ⊆ U.carrier := fun x hx => ⟨i,Finset.mem_insert_self i F,hx⟩
    have hV : V.carrier ⊆ U.carrier := by
      rintro x ⟨j,hj,hx⟩
      exact ⟨j,Finset.mem_insert_of_mem hj,hx⟩
    have hdis : Disjoint (A i).carrier V.carrier := by
      apply Set.disjoint_left.mpr
      rintro x hx ⟨j,hj,hy⟩
      exact Set.disjoint_left.mp (hd i j (fun he => hi (he.symm ▸ hj))) hx hy
    have hu : ((A i).union V).carrier = U.carrier := by
      ext x
      change (x ∈ (A i).carrier ∨ ∃ j ∈ F, x ∈ (A j).carrier) ↔ ∃ j ∈ insert i F, x ∈ (A j).carrier
      simp only [Finset.mem_insert,exists_eq_or_imp]
    have h := gammaGroundGammaSemiringClass_native_partition U (A i) V hA hV hdis hu
    rw [ih] at h
    simpa only [Finset.sum_insert hi] using h

theorem gammaGroundGammaSemiringClass_native_finite_partition {ι : Type} [Fintype ι]
    (G : GammaGroundGammaPiece hc B n) (A : ι → GammaGroundGammaPiece hc B n)
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ G.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
      ∑ i, gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (A i)) := by
  have he : G = gammaGroundDefSetFiniteUnion Finset.univ A := by
    apply gammaGroundDefSet_eq_of_carrier_eq
    ext x
    change x ∈ G.carrier ↔ ∃ i ∈ (Finset.univ : Finset ι), x ∈ (A i).carrier
    simpa only [Finset.mem_univ,true_and] using hcov x
  rw [he,gammaGroundGammaSemiringClass_native_finiteUnion _ A hd]

/-- Actual RES restrictions obey the same finite positive partition
identity with their original label degree. -/
theorem gammaGroundRESDirectSumClass_finite_partition {ι : Type} [Fintype ι]
    (X : GammaGroundRESObject hc B r)
    (A : ι → GammaGroundDefSet hc B (rawRVSpace X.obj.arity))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ X.obj.domain.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    gammaGroundRESDirectSumClass X = ∑ i,
      gammaGroundRESDirectSumClass (X.restrict (A i) (fun x hx => (hcov x).mpr ⟨i,hx⟩)) := by
  have hh : gammaGroundRESClass X = ∑ i,
      gammaGroundRESClass (X.restrict (A i) (fun x hx => (hcov x).mpr ⟨i,hx⟩)) := by
    apply gammaGroundRESToRVKPlus_injective
    simpa only [map_sum,gammaGroundRESToRVKPlus_class,GammaGroundRESObject.restrict] using
      gammaGroundRVClass_finite_partition X.obj A hd hcov
  have h := congrArg (DirectSum.of (GammaGroundRESKPlus hc B) r) hh
  simpa only [gammaGroundRESDirectSumClass,map_sum] using h
end DiamondIntegral.Section3
