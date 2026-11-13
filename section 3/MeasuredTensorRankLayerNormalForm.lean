import «section 3».MeasuredNativeTensorCharts
import «section 3».MeasuredNativeRESPartitions
import «section 3».TensorRankLayerNormalForm
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k m : ℕ}

structure GammaGroundMeasuredTensorRankLayer (hc : CanonicalStructure.IsCanonical (M := M))
    (B : GammaParameters.Base (M := M)) (k m : ℕ) where
  within_degree : m ≤ k
  topCount : ℕ
  residue : Fin topCount → GammaGroundRESUnitChart hc B (k-m)
  gamma : Fin topCount → GammaGroundGammaPiece hc B m
  weight : Fin topCount → (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M)
  weight_definable : ∀ i, FullGammaFunction (integrationGammaBase B) (weight i)
  lower : List (GammaGroundNativeTensorChart hc B k)
  lower_rank : ∀ Z ∈ lower, Z.gammaDegree < m
  lower_weight : ∀ j : Fin lower.length, (Fin (lower.get j).gammaDegree → Values.Gamma (M := M)) → Values.Gamma (M := M)
  lower_weight_definable : ∀ j, FullGammaFunction (integrationGammaBase B) (lower_weight j)

namespace GammaGroundMeasuredTensorRankLayer

def unmeasured (L : GammaGroundMeasuredTensorRankLayer hc B k m) : GammaGroundTensorRankLayer hc B k m :=
  ⟨L.within_degree,L.topCount,L.residue,L.gamma,L.lower,L.lower_rank⟩

def topChart (L : GammaGroundMeasuredTensorRankLayer hc B k m) (i : Fin L.topCount) : GammaGroundMeasuredNativeTensorChart hc B k :=
  ⟨L.unmeasured.topChart i,L.weight i,L.weight_definable i⟩

def lowerChart (L : GammaGroundMeasuredTensorRankLayer hc B k m) (j : Fin L.lower.length) : GammaGroundMeasuredNativeTensorChart hc B k :=
  ⟨L.lower.get j,L.lower_weight j,L.lower_weight_definable j⟩

def topValue (L : GammaGroundMeasuredTensorRankLayer hc B k m) (i : Fin L.topCount) : GammaGroundMeasuredPositiveTensor hc B :=
  gammaGroundMeasuredRESDirectSumClass (L.residue i).measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
    gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (L.gamma i) (L.weight i) (L.weight_definable i))

def value (L : GammaGroundMeasuredTensorRankLayer hc B k m) : GammaGroundMeasuredPositiveTensor hc B :=
  (∑ i, L.topValue i) + ∑ j, (L.lowerChart j).value

@[simp] theorem topChart_value (L : GammaGroundMeasuredTensorRankLayer hc B k m) (i : Fin L.topCount) :
    (L.topChart i).value = L.topValue i := rfl
end GammaGroundMeasuredTensorRankLayer

theorem gammaGroundMeasuredNativeTensorChart_top_normalize (Z : GammaGroundMeasuredNativeTensorChart hc B k)
    (h : Z.underlying.gammaDegree = m) :
    ∃ X : GammaGroundRESUnitChart hc B (k-m), ∃ G : GammaGroundGammaPiece hc B m,
      ∃ f : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M),
        ∃ hf : FullGammaFunction (integrationGammaBase B) f,
      Z.value = gammaGroundMeasuredRESDirectSumClass X.measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) := by
  rcases Z with ⟨⟨r,n,hdegree,X,G⟩,f,hf⟩
  change n = m at h
  subst n
  have hr : r = k-m := by omega
  subst r
  exact ⟨X,G,f,hf,rfl⟩

/-- A homogeneous measured native normal form splits positively into
its maximal-arity layer and lower charts, retaining every Gamma weight. -/
theorem gammaGroundMeasuredNativeTensor_rank_layer_normal_form
    (l : List (GammaGroundMeasuredNativeTensorChart hc B k)) (hbound : m ≤ k)
    (hl : ∀ Z ∈ l, Z.underlying.gammaDegree ≤ m) :
    ∃ L : GammaGroundMeasuredTensorRankLayer hc B k m,
      (l.map GammaGroundMeasuredNativeTensorChart.value).sum = L.value := by
  induction l with
  | nil =>
    let L : GammaGroundMeasuredTensorRankLayer hc B k m :=
      ⟨hbound,0,Fin.elim0,Fin.elim0,Fin.elim0,(fun i => i.elim0),[],
        (by intro Z hZ; exact False.elim (List.not_mem_nil hZ)),(fun i => i.elim0),(fun i => i.elim0)⟩
    refine ⟨L,?_⟩
    simp [L,GammaGroundMeasuredTensorRankLayer.value]
  | cons Z l ih =>
    obtain ⟨L,hL⟩ := ih (fun W hW => hl W (List.mem_cons_of_mem Z hW))
    by_cases hZ : Z.underlying.gammaDegree = m
    · obtain ⟨X,G,f,hf,hvalue⟩ := gammaGroundMeasuredNativeTensorChart_top_normalize Z hZ
      let R : GammaGroundMeasuredTensorRankLayer hc B k m :=
        ⟨hbound,L.topCount+1,Fin.cases X L.residue,Fin.cases G L.gamma,Fin.cases f L.weight,
          Fin.cases hf L.weight_definable,L.lower,L.lower_rank,L.lower_weight,L.lower_weight_definable⟩
      have h0 : R.topValue 0 = gammaGroundMeasuredRESDirectSumClass X.measured
          ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
            gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) := rfl
      have hs (i : Fin L.topCount) : R.topValue i.succ = L.topValue i := rfl
      refine ⟨R,?_⟩
      change Z.value+(l.map GammaGroundMeasuredNativeTensorChart.value).sum = _
      rw [hvalue,hL]
      change _ + ((∑ i, L.topValue i) + ∑ j, (L.lowerChart j).value) =
        (∑ i : Fin (L.topCount+1), R.topValue i) + ∑ j, (L.lowerChart j).value
      rw [Fin.sum_univ_succ]
      simp only [h0,hs]
      exact (add_assoc _ _ _).symm
    · have hlt : Z.underlying.gammaDegree < m := by
        have hle := hl Z (List.mem_cons_self ..)
        omega
      let W : ∀ j : Fin (Z.underlying::L.lower).length,
          (Fin ((Z.underlying::L.lower).get j).gammaDegree → Values.Gamma (M := M)) → Values.Gamma (M := M) := by
        intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · exact Z.weight
        · exact L.lower_weight i
      have hW : ∀ j, FullGammaFunction (integrationGammaBase B) (W j) := by
        intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · exact Z.weight_definable
        · exact L.lower_weight_definable i
      let R : GammaGroundMeasuredTensorRankLayer hc B k m :=
        ⟨hbound,L.topCount,L.residue,L.gamma,L.weight,L.weight_definable,Z.underlying::L.lower,
          (by intro U hU; rcases List.mem_cons.mp hU with rfl | hU; exact hlt; exact L.lower_rank U hU),W,hW⟩
      have h0 : R.lowerChart 0 = Z := rfl
      have hs (j : Fin L.lower.length) : R.lowerChart j.succ = L.lowerChart j := rfl
      refine ⟨R,?_⟩
      change Z.value+(l.map GammaGroundMeasuredNativeTensorChart.value).sum = _
      rw [hL]
      change Z.value + ((∑ i, L.topValue i) + ∑ j, (L.lowerChart j).value) =
        (∑ i, L.topValue i) + ∑ j : Fin (L.lower.length+1), (R.lowerChart j).value
      rw [Fin.sum_univ_succ]
      simp only [h0,hs]
      exact add_left_comm _ _ _
end DiamondIntegral.Section3
