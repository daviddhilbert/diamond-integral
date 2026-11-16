import «section 6».FibrePreparationBases
import «section 6».PreparedCentripetalProgramRealizations

/-! The lower-dimensional preparation witnesses on the actual
coordinate fibres admit finitely many complete original-base programs.
The selected formulas cover the actual VF parameter, including empty
fibres, without naming any RV representative. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_coordinate_fibre_programs
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
    (hLocal : ∀ a : VF M,Nonempty (PreparedSynchronizedFamily (G := G)
      ((headFibreTemplate A).fibre (fun _ => a.val))
      (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val))
      (fun i => headFibreTemplate_subset (hPA i) a))) :
    ∃ l : ℕ,∃ T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S 1 n r s,
      ∀ a : VF M,∃ i,(fun _ : Fin 1 => a.val) ∈
        (T i).2.preparedGood (headFibreTemplate A) (fun i => headFibreTemplate (P i)) := by
  let X := (rawVFSpace (M := M) 1).domain
  have hX : S.Definable LRV X := (rawVFSpace (M := M) 1).definable_domain S
  have hLocalRaw (z : Fin 1 → M) (hz : z ∈ X) :
      ∃ s,∃ B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range z),
      ∃ f : Map ((headFibreTemplate A).fibre z) B,
      ∃ h : SynchronizedCentripetalChain (G := G) (Fin k) ((headFibreTemplate A).fibre z) B f
          (fun i => (headFibreTemplate (P i)).fibre z),
        IsRVPullback ((headFibreTemplate A).fibre z).carrier ∧
          ∀ i,IsRVPullback (f.restrict (h.atPiece i).source_subset).image.carrier := by
    change ∃ v : Fin 1 → VF M,vfValues v=z at hz
    obtain ⟨v,rfl⟩ := hz
    have he : vfValues v=(fun _ : Fin 1 => (v 0).val) := by
      funext i
      fin_cases i
      rfl
    rw [he]
    obtain ⟨F⟩ := hLocal (v 0)
    exact ⟨F.arity,F.target,F.map,F.chain,headFibreTemplate_rvPullback A hARV (v 0),F.prepared⟩
  obtain ⟨l,T,hCover⟩ := exists_finite_prepared_centripetal_programs h00 hc linear hκ hs hv hsmall hΓ
    X hX (headFibreTemplate A) (fun i => headFibreTemplate (P i)) hLocalRaw
  exact ⟨l,T,fun a => hCover (fun _ => a.val) ⟨(fun _ => a),rfl⟩⟩

end DiamondIntegral.Section6
