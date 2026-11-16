import «section 6».RVHeadStartGeometry

/-! Actual bijections retaining a tuple of RV labels lift to every
head-start domain, fixing the added VF block pointwise. This transports
the required finite-fibre condition in degree n+k. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

structure HeadStartCarriedBijection (f : Map A B) (k : ℕ) (π : Fin k → Fin r) (θ : Fin k → Fin s) where
  map : Map (rvHeadStartBundle A k π) (rvHeadStartBundle B k θ)
  bijective : Function.Bijective map
  base : ∀ p,headStartBaseProjection B k θ (map p)=f (headStartBaseProjection A k π p)
  fixed : ∀ p,headStartExtraVF n k (map p).val.1=headStartExtraVF n k p.val.1

theorem HeadStartCarriedBijection.labels
    {f : Map A B} {k : ℕ} {π : Fin k → Fin r} {θ : Fin k → Fin s}
    (H : HeadStartCarriedBijection f k π θ) (p : rvHeadStartBundle A k π) :
    (H.map p).val.2=(f (headStartBaseProjection A k π p)).val.2 := by
  have h := congrArg Subtype.val (H.base p)
  rw [headStartBaseProjection_value] at h
  exact congrArg Prod.snd h

def carryHeadStartBijection (f : Map A B) (hf : Function.Bijective f) :
    (k : ℕ) → (π : Fin k → Fin r) → (θ : Fin k → Fin s) →
      (∀ p : A,∀ i,(f p).val.2 (θ i)=p.val.2 (π i)) → HeadStartCarriedBijection f k π θ
  | 0,π,θ,_ => {
      map := f
      bijective := hf
      base := fun _ => rfl
      fixed := fun _ => Subsingleton.elim _ _ }
  | k+1,π,θ,hLabels => by
      let H := carryHeadStartBijection f hf k (π ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
        (fun p i => hLabels p i.castSucc)
      let π₀ := π ∘ Fin.castSucc
      let θ₀ := θ ∘ Fin.castSucc
      have hL (p : rvHeadStartBundle A k π₀) :
          (H.map p).val.2 (θ (Fin.last k))=p.val.2 (π (Fin.last k)) := by
        have h := (congrFun (H.labels p) (θ (Fin.last k))).trans
          (hLabels (headStartBaseProjection A k π₀ p) (Fin.last k))
        simpa only [headStartBaseProjection_value] using h
      let F := carryLastMap H.map (π (Fin.last k)) (θ (Fin.last k)) hL
      refine {
        map := F
        bijective := carryLastMap_bijective H.map _ _ hL H.bijective
        base := ?_
        fixed := ?_ }
      · intro p
        change headStartBaseProjection B k θ₀
          (bundleProjection (rvHeadStartBundle B k θ₀) (θ (Fin.last k)) (F p))=
          f (headStartBaseProjection A k π₀
            (bundleProjection (rvHeadStartBundle A k π₀) (π (Fin.last k)) p))
        rw [carryLastMap_base]
        exact H.base _
      · intro p
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [headStartExtraVF,Fin.lastCases_last]
          exact carryLastMap_fixed H.map _ _ hL p
        · simp only [headStartExtraVF,Fin.lastCases_castSucc]
          dsimp only [F]
          rw [carryLastMap_value,Fin.init_snoc]
          exact congrFun (H.fixed (bundleProjection (rvHeadStartBundle A k π₀) (π (Fin.last k)) p)) j

theorem head_start_finite_rv_fibres_of_bijective
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (f : Map A B) (hf : Function.Bijective f) (k : ℕ) (π : Fin k → Fin r) (θ : Fin k → Fin s)
    (hLabels : ∀ p : A,∀ i,(f p).val.2 (θ i)=p.val.2 (π i))
    (hFin : ∀ a : Fin n → VF M,∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier ∧ u ∘ π=t}.Finite) :
    ∀ b : Fin (n+k) → VF M,
      {v : Fin s → RVInfinity M | (b,v) ∈ (rvHeadStartBundle B k θ).carrier}.Finite := by
  let H := carryHeadStartBijection f hf k π θ hLabels
  exact finite_rv_fibers_of_bijective hc h00 hκ hs hsmall H.map H.bijective
    (rvHeadStartBundle_finite_rv_fibres A k π hFin)

theorem prepared_head_start_finite_volume_of_bijective
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (f : Map A B) (hf : Function.Bijective f) (k : ℕ) (π : Fin k → Fin r) (θ : Fin k → Fin s)
    (hLabels : ∀ p : A,∀ i,(f p).val.2 (θ i)=p.val.2 (π i))
    (hB : IsRVPullback B.carrier)
    (hTag : ∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hFin : ∀ a : Fin n → VF M,∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier ∧ u ∘ π=t}.Finite) :
    (preparedHeadStartRVObject B k θ hTag).volume.FiniteFibres :=
  preparedRVObject_finite_volume _ (rvHeadStartBundle_pullback B k θ hB) _
    (head_start_finite_rv_fibres_of_bijective hc h00 hκ hs hsmall f hf k π θ hLabels hFin)

end DiamondIntegral.Section6
