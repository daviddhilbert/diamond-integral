import «section 2».DiscToDisc
import «section 2».RVBoundCoordinates

/-! Full Gamma graphs on mixed VF/RV coordinates and their RV-indexed
value families. Existing RV tags are retained through every projection. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

theorem mixedTuple_rv (x : Mixed M n m) :
    mixedTuple x ∘ Fin.natAdd n = rvInputValues x.2 := by
  funext i
  exact Fin.append_right _ _ i

theorem mixedTuple_eq_append_iff (x : Mixed M n m) (t : Fin m → RVInfinity M) (z : Fin n → M) :
    mixedTuple x = Fin.append z (rvInputValues t) ↔ vfValues x.1 = z ∧ x.2 = t := by
  constructor
  · intro he
    constructor
    · funext i
      simpa only [mixedTuple,Fin.append_left] using congrFun he (Fin.castAdd m i)
    · apply rvInputValues_injective
      funext i
      simpa only [mixedTuple,Fin.append_right,rvValues,rvInputValues] using congrFun he (Fin.natAdd n i)
  · rintro ⟨he,ht⟩
    change Fin.append (vfValues x.1) (rvValues x.2) = _
    rw [he,ht]
    rfl

def mixedGammaGraph (A : Set (Mixed M n m)) (p : Mixed M n m → Gamma M) :
    Set (Fin (n+m) ⊕ Fin 1 → M) :=
  {z | GammaParameters.NonzeroRV (z (.inr 0)) ∧
    ∃ x ∈ A, mixedTuple x = z ∘ Sum.inl ∧ GammaParameters.codeValue (z (.inr 0)) = p x}

def mixedGammaFamily (A : Set (Mixed M n m)) (p : Mixed M n m → Gamma M)
    (y : Fin m → M) : Set (Gamma M) :=
  {γ | ∃ x ∈ A, rvInputValues x.2 = y ∧ γ = p x}

theorem mixed_rv_domain_definable (S : Set M) (A : Set (Mixed M n m))
    (hA : S.Definable LRV (mixedTuple '' A)) :
    S.Definable LRV (rvInputValues '' (Prod.snd '' A)) := by
  convert hA.image_comp (Fin.natAdd n) using 1
  ext y
  constructor
  · rintro ⟨t,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨mixedTuple x,⟨x,hx,rfl⟩,mixedTuple_rv x⟩
  · rintro ⟨_,⟨x,hx,rfl⟩,he⟩
    exact ⟨x.2,⟨x,hx,rfl⟩,(mixedTuple_rv x).symm.trans he⟩

theorem mixedGammaFamily_graph_definable (S : Set M) (A : Set (Mixed M n m))
    (p : Mixed M n m → Gamma M) (hp : S.Definable LRV (mixedGammaGraph A p)) :
    S.Definable LRV (rawGammaFamilyGraph (rvInputValues '' (Prod.snd '' A)) (mixedGammaFamily A p)) := by
  let π : Fin m ⊕ Fin 1 → Fin (n+m) ⊕ Fin 1 := Sum.map (Fin.natAdd n) id
  convert hp.image_comp π using 1
  ext z
  constructor
  · rintro ⟨_,hzNZ,x,hx,hxz,hγ⟩
    let w : Fin (n+m) ⊕ Fin 1 → M := Sum.elim (mixedTuple x) (fun _ => z (.inr 0))
    refine ⟨w,⟨hzNZ,x,hx,rfl,hγ⟩,?_⟩
    funext j
    cases j with
    | inl j => exact (congrFun (mixedTuple_rv x) j).trans (congrFun hxz j)
    | inr j => fin_cases j; rfl
  · rintro ⟨w,⟨hwNZ,x,hx,hxw,hγ⟩,hwz⟩
    have hout : w (.inr 0) = z (.inr 0) := congrFun hwz (.inr 0)
    have hsource : rvInputValues x.2 = z ∘ Sum.inl := by
      funext j
      exact (congrFun (mixedTuple_rv x) j).symm.trans
        ((congrFun hxw (Fin.natAdd n j)).trans (congrFun hwz (.inl j)))
    exact ⟨⟨x.2,⟨x,hx,rfl⟩,hsource⟩,hout ▸ hwNZ,x,hx,hsource,hout ▸ hγ⟩

theorem mixedGammaFamily_fibre_eq (A : Set (Mixed M n m)) (p : Mixed M n m → Gamma M)
    (t : Fin m → RVInfinity M) :
    mixedGammaFamily A p (rvInputValues t) = (fun a => p (a,t)) '' vfFibre A t := by
  ext γ
  constructor
  · rintro ⟨x,hx,hxt,rfl⟩
    have ht : x.2 = t := rvInputValues_injective hxt
    refine ⟨x.1,?_,?_⟩
    · change (x.1,t) ∈ A
      simpa only [← ht] using hx
    · simp only [← ht]
  · rintro ⟨a,ha,rfl⟩
    exact ⟨(a,t),ha,rfl,rfl⟩

end DiamondIntegral.Section2
