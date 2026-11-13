import «section 3».RESScissors
import «section 3».RVPositiveComparison

/-! Finite source-value support survives genuine tagged disjoint unions.
The RES positive classes embed in RV before any groupification. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem RVObject.coprod_res {U V : RVObject (M := M) S k}
    (hU : resProperty S k U) (hV : resProperty S k V) : resProperty S k (U.coprod V) := by
  let z : Section2.GammaInfinity M := Values.vrv (⟨iRVZero, rv_zero_mem hM⟩ : CanonicalRV.RVSort M)
  let o : Section2.GammaInfinity M := Values.vrv (⟨iRVOne, rv_one_mem hM⟩ : CanonicalRV.RVSort M)
  let L (γ : Fin U.arity → Section2.GammaInfinity M) :=
    Fin.append (fun _ : Fin 1 => z) (Fin.append γ (fun _ : Fin V.arity => z))
  let R (γ : Fin V.arity → Section2.GammaInfinity M) :=
    Fin.append (fun _ : Fin 1 => o) (Fin.append (fun _ : Fin U.arity => z) γ)
  apply ((hU.image L).union (hV.image R)).subset
  rintro _ ⟨t, ht, rfl⟩
  rcases ht with ⟨u, hu⟩ | ⟨v, hv⟩
  · left
    refine ⟨fun i => Values.vrv (u.val i), ⟨u.val, u.property, rfl⟩, ?_⟩
    rw [← hu]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [RVObject.toCompanion, L, z, rvLeftTagMap, rvMapOfCode, Map.ofCodes, rvLeftTag, Fin.append_left]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [RVObject.toCompanion, L, rvLeftTagMap, rvMapOfCode, Map.ofCodes, rvLeftTag, rvAppend,
          Fin.append_right, Fin.append_left]
      · simp only [RVObject.toCompanion, L, z, rvLeftTagMap, rvMapOfCode, Map.ofCodes, rvLeftTag, rvAppend,
          rvZeroTuple, Fin.append_right]
  · right
    refine ⟨fun i => Values.vrv (v.val i), ⟨v.val, v.property, rfl⟩, ?_⟩
    rw [← hv]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [RVObject.toCompanion, R, o, rvRightTagMap, rvMapOfCode, Map.ofCodes, rvRightTag, Fin.append_left]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [RVObject.toCompanion, R, z, rvRightTagMap, rvMapOfCode, Map.ofCodes, rvRightTag, rvAppend,
          rvZeroTuple, Fin.append_right, Fin.append_left]
      · simp only [RVObject.toCompanion, R, rvRightTagMap, rvMapOfCode, Map.ofCodes, rvRightTag, rvAppend,
          Fin.append_right]

def RESObject.coprod (U V : RESObject (M := M) S k) : RESObject S k :=
  ⟨U.obj.coprod V.obj, RVObject.coprod_res U.property V.property⟩

theorem resClass_iso {U V : RESObject (M := M) S k} (e : U ≅ V) :
    resClass U = resClass V := positiveClass_iso (resPresentation S k) ⟨e⟩

@[simp] theorem resClass_empty : resClass (RESObject.empty (M := M) S k) = 0 :=
  positiveClass_empty (resPresentation S k)

theorem resClass_scissor (U : RESObject (M := M) S k)
    (X : DefSet (rawRVSpace (M := M) U.obj.arity) S) (hX : X.carrier ⊆ U.obj.domain.carrier) :
    resClass (U.restrict X hX) +
      resClass (U.restrict (U.obj.difference X) (fun _ h => h.1)) = resClass U := by
  have hs := positiveClass_scissor (resPresentation S k)
    (show (resPresentation S k).scissor (U.restrict X hX)
      (U.restrict (U.obj.difference X) (fun _ h => h.1)) U (RESObject.empty S k) from
      ⟨U.obj, X, hX, rfl, rfl, rfl, rfl⟩)
  change resClass _ + resClass _ = resClass _ + resClass _ at hs
  simpa only [resClass_empty, add_zero] using hs

theorem resClass_coprod (U V : RESObject (M := M) S k) :
    resClass (U.coprod V) = resClass U + resClass V := by
  let W := U.coprod V
  let X := (rvLeftTagMap U.obj.domain V.obj.arity).image
  let Y := (rvRightTagMap V.obj.domain U.obj.arity).image
  have hX : X.carrier ⊆ W.obj.domain.carrier := fun _ h => Or.inl h
  have hY : Y.carrier ⊆ W.obj.domain.carrier := fun _ h => Or.inr h
  have hdiff : (W.obj.difference X).carrier = Y.carrier := by
    ext t
    constructor
    · rintro ⟨ht, hn⟩
      exact ht.resolve_left hn
    · intro ht
      exact ⟨Or.inr ht, fun hx => Set.disjoint_left.mp (rvTaggedImages_disjoint U.obj.domain V.obj.domain) hx ht⟩
  let f : U ⟶ W.restrict X hX :=
    ObjectProperty.homMk ⟨(rvLeftTagMap U.obj.domain V.obj.arity).toImage,
      rvLeftTagMap_toImage_bijective U.obj.domain V.obj.arity⟩
  let G := (rvRightTagMap V.obj.domain U.obj.arity).toImage
  let gmap : Map V.obj.domain (W.obj.difference X) := G.corestrict (fun a => hdiff.ge (G a).property)
  have hg : Function.Bijective gmap := by
    constructor
    · intro a b he
      apply (rvRightTagMap_toImage_bijective V.obj.domain U.obj.arity).injective
      exact Subtype.ext (congrArg (fun x : W.obj.difference X => x.val) he)
    · intro b
      obtain ⟨v, hv⟩ := hdiff.le b.property
      exact ⟨v, Subtype.ext hv⟩
  let g : V ⟶ W.restrict (W.obj.difference X) (fun _ h => h.1) := ObjectProperty.homMk ⟨gmap, hg⟩
  have hs := resClass_scissor W X hX
  rw [← resClass_iso ((resProperty S k).isoMk (asIso f.hom)), ← resClass_iso ((resProperty S k).isoMk (asIso g.hom))] at hs
  exact hs.symm

theorem resClass_surjective : Function.Surjective (resClass (M := M) (S := S) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (resPresentation S k) RESObject.coprod resClass_coprod


theorem resClass_eq_iff_iso {U V : RESObject (M := M) S k} :
    resClass U = resClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    have he := congrArg resToRVKPlus h
    rw [resToRVKPlus_class, resToRVKPlus_class] at he
    obtain ⟨e⟩ := rvClass_eq_iff_iso.mp he
    exact ⟨(resProperty S k).isoMk e⟩
  · rintro ⟨e⟩
    exact resClass_iso e

theorem resToRVKPlus_injective :
    Function.Injective (resToRVKPlus (M := M) (S := S) (k := k)) := by
  intro a b he
  obtain ⟨U, rfl⟩ := resClass_surjective a
  obtain ⟨V, rfl⟩ := resClass_surjective b
  rw [resToRVKPlus_class, resToRVKPlus_class] at he
  obtain ⟨e⟩ := rvClass_eq_iff_iso.mp he
  exact resClass_iso ((resProperty S k).isoMk e)

end DiamondIntegral.Section3
