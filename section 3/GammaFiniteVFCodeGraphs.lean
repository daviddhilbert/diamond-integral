import «section 3».GammaVFCoordinateRows
import Section3.FiniteCoding
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.RawClosure.Tuple
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section3.Barycentre
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {q n : ℕ}

def gammaVFCoordinateFibre (R : GammaParameters.Relation S q n (fun _ => .vf)) (N : ℕ)
    (i : Fin n) (t : Fin q → M) : Finset (VFType (M := M)) :=
  boundedVFFibre (gammaVFCoordinateRow R i) (gammaVFCoordinateRow_vf R i) N t

def gammaFiniteVFCode (R : GammaParameters.Relation S q n (fun _ => .vf)) (N : ℕ)
    (t : Fin q → M) (x : Fin n → M) (k : Fin (n*N)) : M :=
  rawCode N (gammaVFCoordinateFibre R N (finProdFinEquiv.symm k).1) t
      (x (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2

/-- The coding graph retains every Gamma representative, not a chosen
real-code expansion. Truncation makes its construction uniform. -/
def gammaFiniteVFCodeRelation (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (R : GammaParameters.Relation S q n (fun _ => .vf)) (N : ℕ) :
    GammaParameters.Relation S q (n+n*N) (FiniteCoding.graphSort (n := n) (m := n*N)) := by
  let e : Fin n ⊕ Fin (n*N) ≃ Fin (n+n*N) := finSumFinEquiv
  let input := fun z : Fin (n+n*N) → M => z ∘ e ∘ Sum.inl
  let output := fun z : Fin (n+n*N) → M => z ∘ e ∘ Sum.inr
  let T : Set ((Fin q → M) × (Fin (n+n*N) → M)) :=
    {p | (p.1,input p.2) ∈ R.carrier ∧ gammaFiniteVFCode R N p.1 (input p.2) = output p.2}
  refine ⟨T,?_,?_,?_⟩
  · rw [canonical_normalize_eq hc]
    have hR := R.definable
    rw [canonical_normalize_eq hc] at hR
    let C := Fin q ⊕ Fin (n+n*N)
    have hr : S.Definable LRV {z : C → M | (z ∘ Sum.inl,input (z ∘ Sum.inr)) ∈ R.carrier} :=
      hR.preimage_comp (Sum.map id (fun i => e (.inl i)))
    have hv (k : Fin (n*N)) : S.DefinableFun LRV (fun z : C → M =>
        gammaFiniteVFCode R N (z ∘ Sum.inl) (input (z ∘ Sum.inr)) k) := by
      have hcode := boundedVFFibre_code_definable h00 S
        (gammaVFCoordinateRow R (finProdFinEquiv.symm k).1)
        (gammaVFCoordinateRow_definable hc R (finProdFinEquiv.symm k).1)
        (gammaVFCoordinateRow_vf R (finProdFinEquiv.symm k).1) N (finProdFinEquiv.symm k).2
      exact hcode.comp (show S.DefinableMap LRV (fun z : C → M =>
        Sum.elim (z ∘ Sum.inl) (fun _ : Fin 1 => input (z ∘ Sum.inr) (finProdFinEquiv.symm k).1)) from by
          intro j
          rcases j with j | j
          · exact Set.DefinableFun.proj LRV
          · exact Set.DefinableFun.proj LRV)
    have heq (k : Fin (n*N)) : S.Definable LRV {z : C → M |
        gammaFiniteVFCode R N (z ∘ Sum.inl) (input (z ∘ Sum.inr)) k = output (z ∘ Sum.inr) k} :=
      (hv k).ofPred_eq (Set.DefinableFun.proj LRV)
    convert hr.inter (Set.definable_iInter_of_finite heq) using 1
    ext z
    change (_ ∧ _) ↔ (_ ∧ _)
    simp only [Set.mem_iInter,Set.mem_ofPred_eq]
    exact and_congr Iff.rfl funext_iff
  · rintro ⟨t,z⟩ ⟨hR,hc⟩
    refine ⟨(R.proper _ hR).1,?_⟩
    intro j
    obtain ⟨i,rfl⟩ := e.surjective j
    rcases i with i | k
    · change sortEval (Sum.elim (fun _ : Fin n => .vf) (fun _ : Fin (n*N) => .rv)
        (finSumFinEquiv.symm (finSumFinEquiv (.inl i)))) (input z i)
      rw [Equiv.symm_apply_apply]
      change iVF (input z i)
      exact (R.proper _ hR).2 i
    · have hvf : iVF (input z (finProdFinEquiv.symm k).1) := (R.proper _ hR).2 _
      have hcode := code_sorted N
        (boundedVFFibre (gammaVFCoordinateRow R (finProdFinEquiv.symm k).1)
          (gammaVFCoordinateRow_vf R (finProdFinEquiv.symm k).1) N t)
        (⟨input z (finProdFinEquiv.symm k).1,hvf⟩ : VFType (M := M)) (finProdFinEquiv.symm k).2
      change sortEval (Sum.elim (fun _ : Fin n => .vf) (fun _ : Fin (n*N) => .rv)
        (finSumFinEquiv.symm (finSumFinEquiv (.inr k)))) (output z k)
      rw [Equiv.symm_apply_apply]
      change iRV (output z k)
      rw [← congrFun hc k]
      change iRV (rawCode N
        (boundedVFFibre (gammaVFCoordinateRow R (finProdFinEquiv.symm k).1)
          (gammaVFCoordinateRow_vf R (finProdFinEquiv.symm k).1) N) t
        (⟨input z (finProdFinEquiv.symm k).1,hvf⟩ : VFType (M := M)).val
        (finProdFinEquiv.symm k).2)
      rw [rawCode_eq_code]
      exact hcode
  · intro t u htu z
    change ((GammaParameters.rawTuple t,input z) ∈ R.carrier ∧
      gammaFiniteVFCode R N (GammaParameters.rawTuple t) (input z) = output z) ↔
      ((GammaParameters.rawTuple u,input z) ∈ R.carrier ∧
        gammaFiniteVFCode R N (GammaParameters.rawTuple u) (input z) = output z)
    have hcode (hR : (GammaParameters.rawTuple t,input z) ∈ R.carrier) :
        gammaFiniteVFCode R N (GammaParameters.rawTuple t) (input z) =
          gammaFiniteVFCode R N (GammaParameters.rawTuple u) (input z) := by
      funext k
      exact gammaVFCoordinateFibre_code_invariant R (finProdFinEquiv.symm k).1 N t u htu
        ⟨input z (finProdFinEquiv.symm k).1,(R.proper _ hR).2 _⟩ (finProdFinEquiv.symm k).2
    constructor
    · rintro ⟨hr,he⟩
      exact ⟨(R.invariant t u htu _).mp hr,(hcode hr).symm.trans he⟩
    · rintro ⟨hr,he⟩
      have ht := (R.invariant t u htu _).mpr hr
      exact ⟨ht,(hcode ht).trans he⟩
end DiamondIntegral.Section3
