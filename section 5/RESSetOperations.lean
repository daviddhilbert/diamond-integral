import «section 5».NativeRESClasses

/-! Products and scissors for literal finite-value original RV domains,
deduced from the checked native RES category and its ring presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def resSetProduct (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n m : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) S) (B : DefSet (rawRVSpace (M := M) m) S)
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hB : (Set.range (fun u : B => fun i => Values.vrv (u.val i))).Finite) :
    DefSet (rawRVSpace (M := M) (n + m)) S :=
  originalDomain hc ((nativeRESObjectOfSet hc A hA).product (nativeRESObjectOfSet hc B hB))

theorem resSetProduct_mem (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n m : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) S) (B : DefSet (rawRVSpace (M := M) m) S)
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hB : (Set.range (fun u : B => fun i => Values.vrv (u.val i))).Finite)
    (z : Fin (n + m) → CanonicalRV.RVSort M) :
    z ∈ (resSetProduct hc A B hA hB).carrier ↔
      (fun i => z (Fin.castAdd m i)) ∈ A.carrier ∧
      (fun i => z (Fin.natAdd n i)) ∈ B.carrier := by
  change (∃ u : (GammaGroundDefSet.ofReal (hc := hc) (ground := EmptyGammaGround.base S) A).prod
    (GammaGroundDefSet.ofReal B), Fin.append u.val.1 u.val.2 = z) ↔ _
  constructor
  · rintro ⟨u, rfl⟩
    simp only [Fin.append_left, Fin.append_right]
    exact u.property
  · rintro ⟨hA, hB⟩
    refine ⟨⟨((fun i => z (Fin.castAdd m i)), (fun i => z (Fin.natAdd n i))), hA, hB⟩, ?_⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem resSetClass_product (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n m : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) S) (B : DefSet (rawRVSpace (M := M) m) S)
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hB : (Set.range (fun u : B => fun i => Values.vrv (u.val i))).Finite) :
    resSetClass hc (resSetProduct hc A B hA hB)
      (originalDomain_finite_values hc _) = resSetClass hc A hA * resSetClass hc B hB := by
  exact (resSetClass_originalDomain hc _).trans (nativeUngradedClass_product hc _ _)

theorem resSetClass_scissor (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ}
    (A D E : DefSet (rawRVSpace (M := M) n) S)
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (hD : (Set.range (fun u : D => fun i => Values.vrv (u.val i))).Finite)
    (hE : (Set.range (fun u : E => fun i => Values.vrv (u.val i))).Finite)
    (hd : D.carrier ⊆ A.carrier) (he : E.carrier = A.carrier \ D.carrier) :
    resSetClass hc A hA = resSetClass hc D hD + resSetClass hc E hE := by
  let U := nativeRESObjectOfSet hc A hA
  let X := EmptyGammaGround.fromReal hc D
  let UD := U.restrict X hd
  let UE := U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)
  have hdc : resSetClass hc D hD = nativeUngradedClass hc UD := by
    apply nativeUngradedClass_bijection
    exact GammaGroundBijection.id X
  have hec : resSetClass hc E hE = nativeUngradedClass hc UE := by
    rw [← resSetClass_originalDomain hc UE]
    exact resSetClass_congr hc E (originalDomain hc UE) hE _ he
  rw [hdc, hec]
  exact (nativeUngradedClass_cut hc U X hd).symm

theorem resSetClass_empty (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) S)
    (hA : (Set.range (fun u : A => fun i => Values.vrv (u.val i))).Finite)
    (he : A.carrier = ∅) : resSetClass hc A hA = 0 := by
  let V := GammaGroundRESObject.empty hc (EmptyGammaGround.base S) n
  have hbij : GammaGroundBijection (nativeRESObjectOfSet hc A hA).obj.domain V.obj.domain := by
    have hfalse (a : A) : False := by simpa only [he, Set.mem_empty_iff_false] using a.property
    have hd : GammaGroundDefinable hc (EmptyGammaGround.base S)
        ((rawRVSpace (M := M) n).prod (rawRVSpace 0)) ∅ :=
      GammaGroundDefinable.of_real (Space.definable_empty _ S)
    refine ⟨⟨fun a => (hfalse a).elim, hd.congr ?_⟩,
      ⟨(fun a => (hfalse a).elim), (fun b => b.property.elim)⟩⟩
    intro z
    constructor
    · exact False.elim
    · rintro ⟨a, _, _⟩
      exact (hfalse a).elim
  exact (nativeUngradedClass_bijection hc _ V hbij).trans (nativeUngradedClass_empty hc _ n)

end DiamondIntegral.Section5
