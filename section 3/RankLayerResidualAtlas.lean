import «section 3».NativeBoxResidualPartitions
import «section 3».TensorRankLayerAtlas
import «section 3».NativeTensorHyperplaneReduction
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k m : ℕ}
variable {ι : Type} [Fintype ι]

structure GammaGroundTensorRankLayerMatchedFamily (L : GammaGroundTensorRankLayer hc B k m) (ι : Type) [Fintype ι] where
  parent : ι → Fin L.topCount
  box : ∀ i, GammaGroundTensorBox (L.residue (parent i)) (L.gamma (parent i))
  disjoint : ∀ i j, i ≠ j → Disjoint
    ((L.topMap (parent i)).comp (box i).inclusion).image.carrier
    ((L.topMap (parent j)).comp (box j).inclusion).image.carrier

namespace GammaGroundTensorRankLayerMatchedFamily
variable {L : GammaGroundTensorRankLayer hc B k m}

def union (E : GammaGroundTensorRankLayerMatchedFamily L ι) :=
  gammaGroundDefSetFiniteUnion Finset.univ (fun i => ((L.topMap (E.parent i)).comp (E.box i).inclusion).image)

def residualObject (E : GammaGroundTensorRankLayerMatchedFamily L ι) :=
  L.object.restrict (L.object.domain.sdiff E.union) (fun _ h => h.1)

abbrev TopResidualIndex (E : GammaGroundTensorRankLayerMatchedFamily L ι) :=
  Σ j : Fin L.topCount, GammaGroundTensorParentRemainderIndex L.residue L.gamma E.parent E.box j

abbrev ResidualIndex (E : GammaGroundTensorRankLayerMatchedFamily L ι) :=
  Sum E.TopResidualIndex (Fin L.lower.length)

def remainderBox (E : GammaGroundTensorRankLayerMatchedFamily L ι) (c : E.TopResidualIndex) :=
  gammaGroundTensorParentRemainderBox L.residue L.gamma E.parent E.box c.1 c.2

def residualChart (E : GammaGroundTensorRankLayerMatchedFamily L ι) : E.ResidualIndex → GammaGroundNativeTensorChart hc B k :=
  Sum.elim (fun c => (E.remainderBox c).toNativeChart (Nat.sub_add_cancel L.within_degree)) (fun j => L.lower.get j)

def ambientMap (E : GammaGroundTensorRankLayerMatchedFamily L ι) (c : E.ResidualIndex) :
    GammaGroundMap (E.residualChart c).source L.object.domain := by
  rcases c with c | j
  · exact (L.topMap c.1).comp (E.remainderBox c).inclusion
  · exact L.lowerMap j

theorem ambientMap_injective (E : GammaGroundTensorRankLayerMatchedFamily L ι) (c : E.ResidualIndex) :
    Function.Injective (E.ambientMap c) := by
  rcases c with c | j
  · exact (L.topMap_injective c.1).comp (E.remainderBox c).inclusion_injective
  · exact L.lowerMap_injective j

theorem lower_outside_union (E : GammaGroundTensorRankLayerMatchedFamily L ι)
    (j : Fin L.lower.length) (u : (L.lower.get j).source) :
    (L.lowerMap j u).val ∉ E.union.carrier := by
  rintro ⟨i,_,v,hv⟩
  have h1 : (L.lowerMap j u).val ∈ (L.topMap (E.parent i)).image.carrier := ⟨(E.box i).inclusion v,hv⟩
  have h2 : (L.lowerMap j u).val ∈ (L.lowerMap j).image.carrier := ⟨u,rfl⟩
  exact Set.disjoint_left.mp (L.top_lower_disjoint (E.parent i) j) h1 h2

theorem ambientMap_outside_union (E : GammaGroundTensorRankLayerMatchedFamily L ι)
    (c : E.ResidualIndex) (u : (E.residualChart c).source) :
    (E.ambientMap c u).val ∉ E.union.carrier := by
  rcases c with ⟨j,c⟩ | j
  · let x := (E.remainderBox ⟨j,c⟩).inclusion u
    have hx : x.val ∈ (E.remainderBox ⟨j,c⟩).source.carrier := by
      change (u.val.1,u.val.2) ∈ _
      exact u.property
    exact (gammaGroundTensorParentRemainder_source_cover L.residue L.gamma L.topMap
      L.topMap_injective L.topMap_disjoint E.parent E.box j x).mpr ⟨c,hx⟩
  · exact E.lower_outside_union j u

def residualMap (E : GammaGroundTensorRankLayerMatchedFamily L ι) (c : E.ResidualIndex) :
    GammaGroundMap (E.residualChart c).source E.residualObject.domain :=
  (E.ambientMap c).corestrict (fun u => ⟨(E.ambientMap c u).property,E.ambientMap_outside_union c u⟩)

theorem residualMap_injective (E : GammaGroundTensorRankLayerMatchedFamily L ι) (c : E.ResidualIndex) :
    Function.Injective (E.residualMap c) :=
  (E.ambientMap c).corestrict_injective _ (E.ambientMap_injective c)

theorem residualMap_image (E : GammaGroundTensorRankLayerMatchedFamily L ι) (c : E.ResidualIndex) :
    (E.residualMap c).image.carrier = (E.ambientMap c).image.carrier := by
  ext z
  constructor <;> rintro ⟨u,hu⟩ <;> exact ⟨u,hu⟩

theorem ambientMap_disjoint (E : GammaGroundTensorRankLayerMatchedFamily L ι)
    (c d : E.ResidualIndex) (hcd : c ≠ d) :
    Disjoint (E.ambientMap c).image.carrier (E.ambientMap d).image.carrier := by
  rcases c with ⟨i,c⟩ | i <;> rcases d with ⟨j,d⟩ | j
  · by_cases hij : i = j
    · subst j
      apply Set.disjoint_left.mpr
      rintro z ⟨u,hu⟩ ⟨v,hv⟩
      have he := (L.topMap_injective i) (show L.topMap i ((E.remainderBox ⟨i,c⟩).inclusion u) =
        L.topMap i ((E.remainderBox ⟨i,d⟩).inclusion v) from Subtype.ext (hu.trans hv.symm))
      have hp : u.val = v.val := congrArg (fun x : gammaGroundNativeProductDomain (L.residue i) (L.gamma i) => x.val) he
      have hn : c.val ≠ d.val := fun he => hcd (congrArg Sum.inl (congrArg (Sigma.mk i) (Subtype.ext he)))
      have hd' := gammaGroundTensorGridBox_disjoint (L.residue i) (L.gamma i)
        (fun a => (gammaGroundTensorChildren L.residue L.gamma E.parent E.box i a).residue)
        (fun a => (gammaGroundTensorChildren L.residue L.gamma E.parent E.box i a).gamma) c.val d.val hn
      exact Set.disjoint_left.mp hd' u.property (hp.symm ▸ v.property)
    · apply (L.topMap_disjoint i j hij).mono
      · rintro z ⟨u,hu⟩; exact ⟨(E.remainderBox ⟨i,c⟩).inclusion u,hu⟩
      · rintro z ⟨v,hv⟩; exact ⟨(E.remainderBox ⟨j,d⟩).inclusion v,hv⟩
  · apply (L.top_lower_disjoint i j).mono
    · rintro z ⟨u,hu⟩; exact ⟨(E.remainderBox ⟨i,c⟩).inclusion u,hu⟩
    · exact fun _ h => h
  · apply (L.top_lower_disjoint j i).symm.mono
    · exact fun _ h => h
    · rintro z ⟨v,hv⟩; exact ⟨(E.remainderBox ⟨j,d⟩).inclusion v,hv⟩
  · exact L.lowerMap_disjoint i j (fun he => hcd (congrArg Sum.inr he))

theorem residualMap_disjoint (E : GammaGroundTensorRankLayerMatchedFamily L ι)
    (c d : E.ResidualIndex) (hcd : c ≠ d) :
    Disjoint (E.residualMap c).image.carrier (E.residualMap d).image.carrier := by
  rw [E.residualMap_image,E.residualMap_image]
  exact E.ambientMap_disjoint c d hcd

theorem residualMap_cover (E : GammaGroundTensorRankLayerMatchedFamily L ι)
    (v : E.residualObject.domain) : ∃ c : E.ResidualIndex, ∃ u, E.residualMap c u = v := by
  rcases L.cover ⟨v.val,v.property.1⟩ with ⟨j,x,hx⟩ | ⟨j,x,hx⟩
  · have hout : (L.topMap j x).val ∉ E.union.carrier := by
      rw [congrArg (fun z : L.object.domain => z.val) hx]
      exact v.property.2
    obtain ⟨c,hc'⟩ := (gammaGroundTensorParentRemainder_source_cover L.residue L.gamma L.topMap
      L.topMap_injective L.topMap_disjoint E.parent E.box j x).mp hout
    let u : (E.remainderBox ⟨j,c⟩).source := ⟨x.val,hc'⟩
    have hu : (E.remainderBox ⟨j,c⟩).inclusion u = x := Subtype.ext (Prod.eta x.val)
    refine ⟨.inl ⟨j,c⟩,u,?_⟩
    apply Subtype.ext
    exact (congrArg (fun w : gammaGroundNativeProductDomain (L.residue j) (L.gamma j) => (L.topMap j w).val) hu).trans
      (congrArg (fun z : L.object.domain => z.val) hx)
  · exact ⟨.inr j,x,Subtype.ext (congrArg (fun z : L.object.domain => z.val) hx)⟩

/-- The complete residual tensor sum presents the actual inherited RV
complement, including the original lower-rank charts. -/
theorem residual_value_image (E : GammaGroundTensorRankLayerMatchedFamily L ι) :
    gammaGroundUnmeasuredTensorMap (∑ c : E.ResidualIndex, (E.residualChart c).value) =
      gammaGroundRVSemiringClass E.residualObject := by
  symm
  apply gammaGroundNativeTensorCharts_RV_image_partition E.residualObject E.residualChart E.residualMap
    E.residualMap_injective E.residualMap_disjoint
  intro z
  constructor
  · intro hz
    obtain ⟨c,u,hu⟩ := E.residualMap_cover ⟨z,hz⟩
    exact ⟨c,u,congrArg (fun v : E.residualObject.domain => v.val) hu⟩
  · rintro ⟨c,u,hu⟩
    exact hu ▸ (E.residualMap c u).property

/-- All matched boxes and the complete residual tensor sum form the
original positive layer value. -/
theorem value_split (E : GammaGroundTensorRankLayerMatchedFamily L ι) :
    L.value = (∑ i : ι, (E.box i).value) +
      ∑ c : E.ResidualIndex, (E.residualChart c).value := by
  have hlower : (L.lower.map GammaGroundNativeTensorChart.value).sum =
      ∑ j : Fin L.lower.length, (L.lower.get j).value := by
    calc
      _ = ((List.ofFn L.lower.get).map GammaGroundNativeTensorChart.value).sum :=
        congrArg (fun l => (l.map GammaGroundNativeTensorChart.value).sum) (List.ofFn_get L.lower).symm
      _ = _ := by rw [List.map_ofFn,List.sum_ofFn]; rfl
  have hr : (∑ c : E.ResidualIndex, (E.residualChart c).value) =
      (∑ j : Fin L.topCount, ∑ c : GammaGroundTensorParentRemainderIndex L.residue L.gamma E.parent E.box j,
        (gammaGroundTensorParentRemainderBox L.residue L.gamma E.parent E.box j c).value) +
          (L.lower.map GammaGroundNativeTensorChart.value).sum := by
    rw [hlower]
    calc
      _ = (∑ c : E.TopResidualIndex, (E.remainderBox c).value) +
          ∑ j : Fin L.lower.length, (L.lower.get j).value := Fintype.sum_sum_type _
      _ = _ := congrArg (fun v => v + ∑ j : Fin L.lower.length, (L.lower.get j).value)
        (Fintype.sum_sigma' (fun j c => (gammaGroundTensorParentRemainderBox L.residue L.gamma E.parent E.box j c).value))
  rw [hr]
  dsimp only [GammaGroundTensorRankLayer.value]
  rw [gammaGroundTensorParents_residual_value_split L.residue L.gamma L.topMap E.parent E.box E.disjoint]
  exact add_assoc _ _ _

/-- Once the unmatched maximal-rank Gamma factors are covered by the
finite exceptional hyperplanes, the complete residual value has a
strictly smaller-rank homogeneous native normal form. -/
theorem residual_lower_normal_form {n : ℕ}
    {L : GammaGroundTensorRankLayer hc B k (1+n)}
    (E : GammaGroundTensorRankLayerMatchedFamily L ι) (h00 : M ⊨ Axioms.ACVF00)
    (Q : Fin L.topCount → Finset (GammaGroundCharacterHyperplane B (1+n)))
    (hcover : ∀ j (x : gammaGroundNativeProductDomain (L.residue j) (L.gamma j)),
      (L.topMap j x).val ∈ E.union.carrier ∨
        ∃ h ∈ Q j, rvUnitTupleValues x.val.1 ∈ h.carrier) :
    ∃ l : List (GammaGroundNativeTensorChart hc B k),
      (∑ c : E.ResidualIndex, (E.residualChart c).value) =
        (l.map GammaGroundNativeTensorChart.value).sum ∧
          ∀ Z ∈ l, Z.gammaDegree ≤ n := by
  have hnf (c : E.ResidualIndex) : ∃ l : List (GammaGroundNativeTensorChart hc B k),
      (E.residualChart c).value = (l.map GammaGroundNativeTensorChart.value).sum ∧
        ∀ Z ∈ l, Z.gammaDegree ≤ n := by
    rcases c with ⟨j,c⟩ | j
    · let A := E.remainderBox ⟨j,c⟩
      have hγ := gammaGroundTensorParentRemainder_gamma_cover L.residue L.gamma L.topMap
        L.topMap_injective L.topMap_disjoint E.parent E.box Q hcover j c
      exact gammaGroundNativeTensor_finite_hyperplane_normal_form h00
        ((L.residue j).restrict A.residue A.residue_subset) A.gamma
        (Nat.sub_add_cancel L.within_degree) (Q j) hγ
    · refine ⟨[L.lower.get j],by simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]; rfl,?_⟩
      intro Z hZ
      have he : Z = L.lower.get j := List.mem_singleton.mp hZ
      subst Z
      have hr := L.lower_rank_at j
      omega
  choose l hl hr using hnf
  let q := (Fintype.equivFin E.ResidualIndex).symm
  let parts := List.ofFn (fun a => l (q a))
  refine ⟨parts.flatten,?_,?_⟩
  · calc
      _ = ∑ c : E.ResidualIndex, ((l c).map GammaGroundNativeTensorChart.value).sum :=
        Finset.sum_congr rfl (fun c _ => hl c)
      _ = ∑ a, ((l (q a)).map GammaGroundNativeTensorChart.value).sum :=
        (Equiv.sum_comp q (fun c => ((l c).map GammaGroundNativeTensorChart.value).sum)).symm
      _ = _ := by simp only [parts,List.map_flatten,List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  · intro Z hZ
    obtain ⟨p,hp,hZ⟩ := List.mem_flatten.mp hZ
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
    exact hr (q a) Z hZ
end GammaGroundTensorRankLayerMatchedFamily
end DiamondIntegral.Section3
