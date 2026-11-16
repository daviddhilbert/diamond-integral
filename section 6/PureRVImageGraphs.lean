import «section 6».FiniteVolumeRVIsomorphisms

/-! Full original-base real-code images of pairs of RV-valued maps.
These graphs retain all source labels until existential projection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

theorem rvProduct_code_image_definable
    (D : DefSet ((rawRVSpace (M := M) n).prod (rawRVSpace m)) S) :
    S.Definable LRV {z : Fin n ⊕ Fin m → M | ∃ a : D,
      rvValues a.val.1 = z ∘ Sum.inl ∧ rvValues a.val.2 = z ∘ Sum.inr} := by
  have hD := D.definable
  change S.Definable LRV (((rawRVSpace (M := M) n).prod (rawRVSpace m)).preimage D.carrier) at hD
  change S.Definable LRV {z : Fin n ⊕ Fin m → M | ∃ a : D,
      rvValues a.val.1 = z ∘ Sum.inl ∧ rvValues a.val.2 = z ∘ Sum.inr}
  convert hD using 1 <;> try rfl
  apply Set.ext
  intro (z : Fin n ⊕ Fin m → M)
  constructor
  · rintro ⟨a,ha,hb⟩
    let ca : (rawRVSpace (M := M) n).domain := ⟨z ∘ Sum.inl,a.val.1,ha⟩
    let cb : (rawRVSpace (M := M) m).domain := ⟨z ∘ Sum.inr,a.val.2,hb⟩
    refine ⟨⟨ca.property,cb.property⟩,?_⟩
    have hea : (rawRVSpace (M := M) n).decode ca = a.val.1 :=
      rvValues_injective ((rvValues_decode ca).trans ha.symm)
    have heb : (rawRVSpace (M := M) m).decode cb = a.val.2 :=
      rvValues_injective ((rvValues_decode cb).trans hb.symm)
    change ((rawRVSpace n).decode ca,(rawRVSpace m).decode cb) ∈ D.carrier
    rw [hea,heb]
    exact a.property
  · rintro ⟨hz,ha⟩
    let a : D := ⟨((rawRVSpace n).decode ⟨z ∘ Sum.inl,hz.1⟩,
      (rawRVSpace m).decode ⟨z ∘ Sum.inr,hz.2⟩),ha⟩
    exact ⟨a,rvValues_decode _,rvValues_decode _⟩

theorem rvPairMap_code_image_definable
    {P : SpecialTransformations.DefinableGeometry.Space LRV M} {A : DefSet P S}
    (f : Map A (DefSet.univ (rawRVSpace (M := M) n) S))
    (g : Map A (DefSet.univ (rawRVSpace (M := M) m) S)) :
    S.Definable LRV {z : Fin n ⊕ Fin m → M | ∃ a : A,
      rvValues (f a).val = z ∘ Sum.inl ∧ rvValues (g a).val = z ∘ Sum.inr} := by
  have h := rvProduct_code_image_definable (f.pair g).image
  convert h using 1
  ext z
  constructor
  · rintro ⟨a,ha,hb⟩
    exact ⟨⟨(f.pair g a).val,⟨a,rfl⟩⟩,ha,hb⟩
  · rintro ⟨⟨p,⟨a,hap⟩⟩,ha,hb⟩
    exact ⟨a,(congrArg (fun p => rvValues p.1) hap).trans ha,
      (congrArg (fun p => rvValues p.2) hap).trans hb⟩

end DiamondIntegral.Section6
