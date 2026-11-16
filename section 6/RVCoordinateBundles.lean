import «section 6».CentripetalFocusProjection

/-! Carrying an already released VF coordinate as the full RV disc
specified by one retained label. The actual bundle has a complete
original-base graph and is proper invariant over a proper base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem mixedValues_preimage_definable (R : Set (Fin n ⊕ Fin r → M)) (hR : S.Definable LRV R) :
    (rawMixedSpace (M := M) n r).Definable S {p | mixedValues p ∈ R} := by
  let P := rawMixedSpace (M := M) n r
  change S.Definable LRV (P.preimage {p | mixedValues p ∈ R})
  convert (P.definable_domain S).inter hR using 1
  ext z
  constructor
  · rintro ⟨hz,hzR⟩
    change mixedValues (P.decode ⟨z,hz⟩) ∈ R at hzR
    have hcode : mixedValues (P.decode ⟨z,hz⟩) = z := mixedValues_decode ⟨z,hz⟩
    exact ⟨hz,hcode ▸ hzR⟩
  · rintro ⟨hz,hzR⟩
    refine ⟨hz,?_⟩
    change mixedValues (P.decode ⟨z,hz⟩) ∈ R
    have hcode : mixedValues (P.decode ⟨z,hz⟩) = z := mixedValues_decode ⟨z,hz⟩
    exact hcode.symm ▸ hzR

def rvCoordinateBundle (C : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r) :
    DefSet (rawMixedSpace (M := M) (n+1) r) S := by
  let P := rawMixedSpace (M := M) (n+1) r
  have hBase : P.Definable S {p | (Fin.init p.1,p.2) ∈ C.carrier} := by
    have h := Map.definable_preimage (vfDropLast (DefSet.univ P S)) C.definable
    have he : {p : Mixed M (n+1) r | (Fin.init p.1,p.2) ∈ C.carrier} =
        {p | ∃ q : DefSet.univ P S, q.val = p ∧ (vfDropLast (DefSet.univ P S) q).val ∈ C.carrier} := by
      ext p
      constructor
      · exact fun hp => ⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩
      · rintro ⟨q,rfl,hq⟩
        exact hq
    convert h using 1
    exact he
  let R : Set (Fin (n+1) ⊕ Fin r → M) := {z | iRv (z (.inl (Fin.last n))) = z (.inr k)}
  have hR : S.Definable LRV R :=
    (rv_scalarCode_definable (Set.DefinableFun.proj (L := LRV) (A := S)
      (i := (.inl (Fin.last n) : Fin (n+1) ⊕ Fin r)))).ofPred_eq (Set.DefinableFun.proj LRV)
  have hTag : P.Definable S {p : Mixed M (n+1) r | rv M (p.1 (Fin.last n)) = p.2 k} := by
    convert mixedValues_preimage_definable R hR using 1
    ext p
    exact Subtype.ext_iff
  exact ⟨{p | (Fin.init p.1,p.2) ∈ C.carrier ∧ rv M (p.1 (Fin.last n)) = p.2 k},hBase.inter P hTag⟩

theorem rvCoordinateBundle_rvBounded (C : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (hC : RVSupportDoublyBounded C.carrier) : RVSupportDoublyBounded (rvCoordinateBundle C k).carrier := by
  obtain ⟨γ,hγ⟩ := hC
  exact ⟨γ,fun p hp i => hγ (Fin.init p.1,p.2) hp.1 i⟩

theorem rvCoordinateBundle_vfBounded (C : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (hC : VFBounded C.carrier) (hRV : RVSupportDoublyBounded C.carrier) :
    VFBounded (rvCoordinateBundle C k).carrier := by
  obtain ⟨γ,hγ⟩ := hC
  obtain ⟨δ,hδ⟩ := hRV
  refine ⟨min γ δ⁻¹,fun p hp i => ?_⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have he : vfValue (p.1 (Fin.last n)) = Values.vrv (p.2 k) := congrArg Values.vrv hp.2
    rw [he]
    exact (show (min γ δ⁻¹).val ≤ (δ⁻¹).val from min_le_right _ _).trans
      (hδ (Fin.init p.1,p.2) hp.1 k).1
  · exact (show (min γ δ⁻¹).val ≤ γ.val from min_le_left _ _).trans
      (hγ (Fin.init p.1,p.2) hp.1 j)

theorem rvCoordinateBundle_fibre_invariant
    (C : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (hC : ProperInvariant S C.carrier) (u : Fin r → RVInfinity M) :
    ∃ α : Fin (n+1) → Gamma M, AlphaInvariant α (vfFibre (rvCoordinateBundle C k).carrier u) := by
  obtain ⟨α,_,hInv⟩ := hC.radii u
  obtain ⟨γ,hγ⟩ := hC.rvBounded
  have step (a b : Fin (n+1) → VF M) (hab : Congruent (Fin.snoc α γ) a b)
      (ha : a ∈ vfFibre (rvCoordinateBundle C k).carrier u) :
      b ∈ vfFibre (rvCoordinateBundle C k).carrier u := by
    have hinit : Congruent α (Fin.init a) (Fin.init b) := by
      intro i
      simpa only [Fin.snoc_castSucc,Fin.init] using hab i.castSucc
    refine ⟨(hInv _ _ hinit).mp ha.1,?_⟩
    have hbound : vfValue (a (Fin.last n)) ≤ γ.val := by
      rw [show vfValue (a (Fin.last n)) = Values.vrv (u k) from congrArg Values.vrv ha.2]
      exact (hγ (Fin.init a,u) ha.1 k).2
    have hclose : γ.val < vfValue (b (Fin.last n)-a (Fin.last n)) := by
      simpa only [Fin.snoc_last] using hab.symm (Fin.last n)
    exact (rv_eq_of_close_at_radius γ hbound hclose).trans ha.2
  exact ⟨Fin.snoc α γ,fun a b hab => ⟨step a b hab,step b a hab.symm⟩⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem rvCoordinateBundle_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r) (hC : ProperInvariant S C.carrier) :
    ProperInvariant S (rvCoordinateBundle C k).carrier := by
  apply (lemma_6_5 h00 hc hκ hs hv _ (rvCoordinateBundle C k).definable
    (rvCoordinateBundle_vfBounded C k hC.vfBounded hC.rvBounded)
    (rvCoordinateBundle_rvBounded C k hC.rvBounded)).mpr
  intro u
  obtain ⟨α,hα⟩ := rvCoordinateBundle_fibre_invariant C k hC u
  exact hα.isClopen hv

end DiamondIntegral.Section6
