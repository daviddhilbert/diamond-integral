import «section 3».MeasuredGammaPieceSums
import «section 3».MeasuredGammaWeightTranslations
import «section 3».GammaGroundMeasuredGammaPartitions
import «section 3».GammaGroundMeasuredGammaRepresentatives
import «section 3».GammaNativeFinitePartitions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

def gammaGroundMeasuredGammaSingleWeightRestrictHom
    (G A : GammaGroundGammaPiece hc B n) (hA : A.carrier ⊆ G.carrier)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) :
    GammaGroundMeasuredGammaHom ((gammaGroundMeasuredGammaSingleWeight G f hf).restrict (fun _ => A) (fun _ => hA))
      (gammaGroundMeasuredGammaSingleWeight A f hf) where
  underlying := GammaGroundGammaHom.id (GammaGroundGammaObject.single A)
  preserves a := by
    change (gammaGroundMeasuredGammaSingleWeight G f hf).combinedWeight
      ⟨a.1,GammaGroundMap.inclusion hA a.2⟩ = (gammaGroundMeasuredGammaSingleWeight A f hf).combinedWeight a
    rw [gammaGroundMeasuredGammaSingleWeight_combined,gammaGroundMeasuredGammaSingleWeight_combined]
    rfl

theorem gammaGroundMeasuredGammaSemiringClass_native_partition
    (G A D : GammaGroundGammaPiece hc B n)
    (hA : A.carrier ⊆ G.carrier) (hD : D.carrier ⊆ G.carrier)
    (hd : Disjoint A.carrier D.carrier) (hu : (A.union D).carrier = G.carrier)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) :
    gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight A f hf) +
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight D f hf) := by
  let U := gammaGroundMeasuredGammaSingleWeight G f hf
  let h := gammaGroundMeasuredGammaPartitionHom U (fun _ => A) (fun _ => D)
    (fun _ => hA) (fun _ => hD) (fun _ => hd) (fun _ => hu)
  have he := gammaGroundMeasuredGammaSemiringClass_iso (asIso (show _ ⟶ U from h))
  rw [gammaGroundMeasuredGammaSemiringClass_coprod] at he
  rw [gammaGroundMeasuredGammaSemiringClass_iso (asIso (show _ ⟶ _ from
    gammaGroundMeasuredGammaSingleWeightRestrictHom G A hA f hf)),
    gammaGroundMeasuredGammaSemiringClass_iso (asIso (show _ ⟶ _ from
      gammaGroundMeasuredGammaSingleWeightRestrictHom G D hD f hf))] at he
  exact he.symm

theorem gammaGroundMeasuredGammaSemiringClass_single_empty
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) :
    gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight
      (GammaGroundDefSet.empty hc B ((volumeGammaSpace hc).power (Fin n))) f hf) = 0 := by
  let E := GammaGroundMeasuredGammaObject.empty hc B n
  let A := gammaGroundMeasuredGammaSingleWeight
    (GammaGroundDefSet.empty hc B ((volumeGammaSpace hc).power (Fin n))) f hf
  let h : GammaGroundMeasuredGammaHom (E.coprod A) E :=
    { underlying := gammaGroundGammaCoprodEmptyRightHom E.underlying A.underlying (fun _ => rfl)
      preserves := by
        intro x
        rcases gammaGroundFamilyCoprod_cases E.underlying A.underlying x with ⟨a,rfl⟩ | ⟨a,rfl⟩
        · exact a.1.elim0
        · exact False.elim a.2.property }
  have he := gammaGroundMeasuredGammaSemiringClass_iso (asIso (show E.coprod A ⟶ E from h))
  simpa only [gammaGroundMeasuredGammaSemiringClass_coprod,E,gammaGroundMeasuredGammaSemiringClass_empty,zero_add] using he

theorem gammaGroundMeasuredGammaSemiringClass_native_finiteUnion {ι : Type}
    (F : Finset ι) (A : ι → GammaGroundGammaPiece hc B n)
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) :
    gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (gammaGroundDefSetFiniteUnion F A) f hf) =
      ∑ i ∈ F, gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (A i) f hf) := by
  induction F using Finset.induction_on with
  | empty =>
    have he : gammaGroundDefSetFiniteUnion ∅ A = GammaGroundDefSet.empty hc B ((volumeGammaSpace hc).power (Fin n)) := by
      apply gammaGroundDefSet_eq_of_carrier_eq
      ext x
      simp only [gammaGroundDefSetFiniteUnion,Finset.notMem_empty,false_and,exists_false]
      rfl
    rw [he,gammaGroundMeasuredGammaSemiringClass_single_empty,Finset.sum_empty]
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
    have he := gammaGroundMeasuredGammaSemiringClass_native_partition U (A i) V hA hV hdis hu f hf
    rw [ih] at he
    simpa only [Finset.sum_insert hi] using he

theorem gammaGroundMeasuredGammaSemiringClass_native_finite_partition {ι : Type} [Fintype ι]
    (G : GammaGroundGammaPiece hc B n) (A : ι → GammaGroundGammaPiece hc B n)
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ G.carrier ↔ ∃ i, x ∈ (A i).carrier)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) :
    gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      ∑ i, gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (A i) f hf) := by
  have he : G = gammaGroundDefSetFiniteUnion Finset.univ A := by
    apply gammaGroundDefSet_eq_of_carrier_eq
    ext x
    change x ∈ G.carrier ↔ ∃ i ∈ (Finset.univ : Finset ι), x ∈ (A i).carrier
    simpa only [Finset.mem_univ,true_and] using hcov x
  rw [he,gammaGroundMeasuredGammaSemiringClass_native_finiteUnion _ A hd]
end DiamondIntegral.Section3
