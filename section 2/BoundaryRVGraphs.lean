import «section 2».RawRVBoundary
import «section 2».RVCylinders
import «section 2».ScalarCorrespondencePullback

/-! The graphs C_ij in the main boundary proof retain every source tag
and place the representative's output tag in the chosen coordinate. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def rawScalarCorrespondenceGraph (V : Set (Fin n → M)) (F : (Fin n → M) → Set M) :
    Set (Fin (n+1) → M) := {z | Fin.init z ∈ V ∧ z (Fin.last n) ∈ F (Fin.init z)}

def boundaryRVGraph (i : Fin (n+1)) (V : Set (Fin n → M)) (F : (Fin n → M) → Set M) :
    Set (Fin (n+1) → RVInfinity M) :=
  rvCoordinateCylinder i (rawRVInterior V) ∩
    rvReindexed (lastToCoordinate i).symm (rawRVImage (rawScalarCorrespondenceGraph V F))

theorem boundaryRVGraph_mem_iff (i : Fin (n+1)) (V : Set (Fin n → M))
    (F : (Fin n → M) → Set M) (t : Fin (n+1) → RVInfinity M) :
    t ∈ boundaryRVGraph i V F ↔ Fin.removeNth i t ∈ rawRVInterior V ∧
      ∃ a ∈ rawRVPolydisc (Fin.removeNth i t), a ∈ V ∧
        ∃ y ∈ F a, iVF y ∧ iRv y = (t i).val := by
  constructor
  · rintro ⟨hint,w,hw,hwV,hwy⟩
    change w ∈ rawRVPolydisc (t ∘ lastToCoordinate i) at hw
    refine ⟨hint,Fin.init w,?_,hwV,w (Fin.last n),hwy,?_,?_⟩
    · intro j
      have h := hw j.castSucc
      simpa only [Fin.init,Function.comp_apply,lastToCoordinate_castSucc,Fin.removeNth] using h
    · exact (hw (Fin.last n)).1
    · have h := (hw (Fin.last n)).2
      simpa only [Function.comp_apply,lastToCoordinate_last] using h
  · rintro ⟨hint,a,hat,ha,y,hy,hyVF,hyt⟩
    refine ⟨hint,Fin.snoc a y,?_,?_,?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun q => ?_) j
      · change iVF ((Fin.snoc a y : Fin (n+1) → M) (Fin.last n)) ∧
          iRv ((Fin.snoc a y : Fin (n+1) → M) (Fin.last n)) =
            ((t ∘ lastToCoordinate i) (Fin.last n)).val
        simpa only [Fin.snoc_last,Function.comp_apply,lastToCoordinate_last] using And.intro hyVF hyt
      · change iVF ((Fin.snoc a y : Fin (n+1) → M) q.castSucc) ∧
          iRv ((Fin.snoc a y : Fin (n+1) → M) q.castSucc) =
            ((t ∘ lastToCoordinate i) q.castSucc).val
        have hq : iVF (a q) ∧ iRv (a q) = (t (i.succAbove q)).val := hat q
        simpa only [Fin.snoc_castSucc,Function.comp_apply,lastToCoordinate_castSucc] using hq
    · simpa only [Fin.init_snoc] using ha
    · simpa only [Fin.init_snoc,Fin.snoc_last] using hy

theorem rawScalarCorrespondenceGraph_restrict_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M)
    (D V : Set (Fin n → M)) (hV : DefinableOver S (fun _ => .vf) V) (hVD : V ⊆ D)
    (F : (Fin n → M) → Set M)
    (hF : DefinableOver S (fun _ => .vf) (rawScalarCorrespondenceGraph D F)) :
    DefinableOver S (fun _ => .vf) (rawScalarCorrespondenceGraph V F) := by
  exact scalar_correspondence_pullback_definable hc S D V hV id
    (fun j => Set.DefinableFun.proj LRV) hVD F hF

theorem boundaryRVGraph_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (i : Fin (n+1)) (V : Set (Fin n → M))
    (hV : DefinableOver S (fun _ => .vf) V) (F : (Fin n → M) → Set M)
    (hF : DefinableOver S (fun _ => .vf) (rawScalarCorrespondenceGraph V F)) :
    DefinableOver S (fun _ => .rv) (rvInputValues '' boundaryRVGraph i V F) := by
  rw [boundaryRVGraph,Set.image_inter rvInputValues_injective]
  have hC := rvCoordinateCylinder_definable hc S i _ (rawRVInterior_definable hc S V hV)
  have hG := rvReindexed_definable hc S (lastToCoordinate i).symm _ (rawRVImage_definable hc S _ hF)
  exact (GammaParameters.base_empty_iff S _ _).mp
    (((GammaParameters.base_empty_iff S _ _).mpr hC).inter
      ((GammaParameters.base_empty_iff S _ _).mpr hG))

end DiamondIntegral.Section2
