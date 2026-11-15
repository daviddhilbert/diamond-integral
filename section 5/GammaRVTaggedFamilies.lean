import «section 5».GammaGroundDisjointBijections

/-! Finite families of differently sized RV sets are encoded by literal
RV zero/one tagged domains. Component bijections give one actual definable
bijection of those domains over the unchanged mixed parameter base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : GammaParameters.Base (M := M))

abbrev GammaRVSet := Σ n, GammaGroundDefSet hc B (rawRVSpace (M := M) n)

def taggedRVFinFamily : (n : ℕ) → (Fin n → GammaRVSet hc B) → GammaRVSet hc B
  | 0, _ => ⟨0, GammaGroundDefSet.empty hc B (rawRVSpace 0)⟩
  | n + 1, A =>
    let R := taggedRVFinFamily n (fun i => A i.succ)
    ⟨1 + ((A 0).1 + R.1), gammaGroundRVTaggedUnion (A 0).2 R.2⟩

def taggedRVFinFamilyBijection : (n : ℕ) →
    (A C : Fin n → GammaRVSet hc B) →
    (∀ i, GammaGroundBijection (A i).2 (C i).2) →
    GammaGroundBijection (taggedRVFinFamily hc B n A).2 (taggedRVFinFamily hc B n C).2
  | 0, _, _, _ => GammaGroundBijection.id _
  | n + 1, A, C, f => gammaGroundRVTaggedUnionBijection (f 0)
      (taggedRVFinFamilyBijection n (fun i => A i.succ) (fun i => C i.succ) (fun i => f i.succ))

def GammaRVFiniteValues {n : ℕ} (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) : Prop :=
  ((fun t i => Values.vrv (t i)) '' A.carrier).Finite

theorem gammaGroundRVTaggedUnion_finite_values {n m : ℕ}
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (C : GammaGroundDefSet hc B (rawRVSpace (M := M) m))
    (hA : GammaRVFiniteValues hc B A) (hC : GammaRVFiniteValues hc B C) :
    GammaRVFiniteValues hc B (gammaGroundRVTaggedUnion A C) := by
  let z : Values.GammaTop (M := M) := Values.vrv
    (⟨iRVZero, rv_zero_mem (by infer_instance : M ⊨ Axioms.ACVF)⟩ : CanonicalRV.RVSort M)
  let o : Values.GammaTop (M := M) := Values.vrv
    (⟨iRVOne, rv_one_mem (by infer_instance : M ⊨ Axioms.ACVF)⟩ : CanonicalRV.RVSort M)
  let L (γ : Fin n → Values.GammaTop (M := M)) :=
    Fin.append (fun _ : Fin 1 => z) (Fin.append γ (fun _ : Fin m => z))
  let R (γ : Fin m → Values.GammaTop (M := M)) :=
    Fin.append (fun _ : Fin 1 => o) (Fin.append (fun _ : Fin n => z) γ)
  apply ((hA.image L).union (hC.image R)).subset
  rintro _ ⟨t, ht, rfl⟩
  rcases ht with ⟨u, hu⟩ | ⟨v, hv⟩
  · left
    refine ⟨fun i => Values.vrv (u.val i), ⟨u.val, u.property, rfl⟩, ?_⟩
    rw [← hu]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [L, z, gammaGroundRVLeftTag, GammaGroundMap.ofGlobal, rvLeftTagMap,
        rvMapOfCode, Map.ofCodes, rvLeftTag, Fin.append_left]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [L, gammaGroundRVLeftTag, GammaGroundMap.ofGlobal, rvLeftTagMap,
          rvMapOfCode, Map.ofCodes, rvLeftTag, rvAppend, Fin.append_right, Fin.append_left]
      · simp only [L, z, gammaGroundRVLeftTag, GammaGroundMap.ofGlobal, rvLeftTagMap,
          rvMapOfCode, Map.ofCodes, rvLeftTag, rvAppend, rvZeroTuple, Fin.append_right]
  · right
    refine ⟨fun i => Values.vrv (v.val i), ⟨v.val, v.property, rfl⟩, ?_⟩
    rw [← hv]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [R, o, gammaGroundRVRightTag, GammaGroundMap.ofGlobal, rvRightTagMap,
        rvMapOfCode, Map.ofCodes, rvRightTag, Fin.append_left]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [R, z, gammaGroundRVRightTag, GammaGroundMap.ofGlobal, rvRightTagMap,
          rvMapOfCode, Map.ofCodes, rvRightTag, rvAppend, rvZeroTuple, Fin.append_right, Fin.append_left]
      · simp only [R, gammaGroundRVRightTag, GammaGroundMap.ofGlobal, rvRightTagMap,
          rvMapOfCode, Map.ofCodes, rvRightTag, rvAppend, Fin.append_right]

theorem taggedRVFinFamily_finite_values (n : ℕ) (A : Fin n → GammaRVSet hc B)
    (hA : ∀ i, GammaRVFiniteValues hc B (A i).2) :
    GammaRVFiniteValues hc B (taggedRVFinFamily hc B n A).2 := by
  induction n with
  | zero => exact Set.finite_empty.image _
  | succ n ih =>
    exact gammaGroundRVTaggedUnion_finite_values hc B (A 0).2
      (taggedRVFinFamily hc B n (fun i => A i.succ)).2 (hA 0)
        (ih (fun i => A i.succ) (fun i => hA i.succ))

end DiamondIntegral.Section5
