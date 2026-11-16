import «section 6».FiniteRVCenters

/-! The RV image of a finite unary VF projection is finite and has its
complete defining graph over the original base. Finitary output images
of those exceptional labels are finite and definable as well. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}

def unaryLeadingTermMap (A : DefSet (rawMixedSpace (M := M) 1 r) S) :
    Map A (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let P := rawMixedSpace (M := M) 1 r
  let Q := rawRVSpace (M := M) 1
  let f (p : Mixed M 1 r) : Fin 1 → RVInfinity M := fun _ => rv M (p.1 0)
  let F (z : Fin 1 ⊕ Fin r → M) : Fin 1 → M := fun _ => iRv (z (.inl 0))
  have hF : S.DefinableMap LRV F := fun _ => hullRVCode_definable S (.inl (0 : Fin 1))
  have hcode (z : P.domain) : rvValues (f (P.decode z)) = F z.val := by
    funext i
    exact congrArg iRv (congrFun (mixedValues_decode z) (.inl 0))
  have hdom (z : P.domain) : F z.val ∈ Q.domain := ⟨f (P.decode z),hcode z⟩
  exact Map.ofCodes A f F hF hdom
    (fun z => rvValues_injective ((rvValues_decode ⟨F z.val,hdom z⟩).trans (hcode z).symm))

def unaryRVImage (A : DefSet (rawMixedSpace (M := M) 1 r) S) : Set M :=
  {u | ∃ p ∈ A.carrier, iRv (p.1 0).val = u}

theorem unaryRVImage_definable (A : DefSet (rawMixedSpace (M := M) 1 r) S) :
    S.Definable₁ LRV (unaryRVImage A) := by
  convert rvCoordinateSet_definable (unaryLeadingTermMap A).image (0 : Fin 1) using 1
  ext u
  constructor
  · rintro ⟨p,hp,he⟩
    exact ⟨⟨fun _ => rv M (p.1 0),⟨⟨p,hp⟩,rfl⟩⟩,he⟩
  · rintro ⟨b,hb⟩
    obtain ⟨p,hp⟩ := b.property
    exact ⟨p.val,p.property,(congrArg (fun q : Fin 1 → RVInfinity M => (q 0).val) hp).trans hb⟩

theorem unaryRVImage_finite (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : (Prod.fst '' A.carrier).Finite) : (unaryRVImage A).Finite := by
  apply (hA.image (fun a : Fin 1 → VF M => iRv (a 0).val)).subset
  rintro u ⟨p,hp,he⟩
  exact ⟨p.1,⟨p,hp,rfl⟩,he⟩

def finitaryExceptionalOutputs (B : Set M) (R : M → M → Prop) : Set M :=
  {v | ∃ u ∈ B, R u v}

theorem finitaryExceptionalOutputs_finite (B : Set M) (hB : B.Finite) (R : M → M → Prop)
    (hR : ∀ u, {v | R u v}.Finite) : (finitaryExceptionalOutputs B R).Finite := by
  apply (hB.biUnion (fun u _ => hR u)).subset
  rintro v ⟨u,hu,hr⟩
  exact Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,hr⟩⟩

theorem finitaryExceptionalOutputs_definable (B : Set M) (hB : S.Definable₁ LRV B)
    (R : M → M → Prop)
    (hR : S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M | R (z (.inl 0)) (z (.inr 0))}) :
    S.Definable₁ LRV (finitaryExceptionalOutputs B R) := by
  let swap : Fin 1 ⊕ Fin 1 → Fin 1 ⊕ Fin 1 := Sum.elim Sum.inr Sum.inl
  have h := ((hB.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)).inter
    (hR.preimage_comp swap)).exists_of_finite
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ finitaryExceptionalOutputs B R}
  convert h using 1
  ext z
  change (∃ u ∈ B, R u (z 0)) ↔ ∃ q : Fin 1 → M, q 0 ∈ B ∧ R (q 0) (z 0)
  exact ⟨fun ⟨u,hu,hr⟩ => ⟨(fun _ => u),hu,hr⟩,fun ⟨q,hq,hr⟩ => ⟨q 0,hq,hr⟩⟩

end DiamondIntegral.Section6
