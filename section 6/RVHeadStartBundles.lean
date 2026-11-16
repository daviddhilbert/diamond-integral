import «section 6».CarriedDefinableMaps

/-! Lift any finite tuple of retained RV labels to additional VF
coordinates. These are the literal head-start domains, with exact
membership and finite RV fibres in the full VF degree. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def rvHeadStartBundle (A : DefSet (rawMixedSpace (M := M) n r) S) :
    (k : ℕ) → (Fin k → Fin r) → DefSet (rawMixedSpace (M := M) (n+k) r) S
  | 0,_ => A
  | k+1,π => rvCoordinateBundle (rvHeadStartBundle A k (π ∘ Fin.castSucc)) (π (Fin.last k))

def headStartBaseVF {X : Type*} (n : ℕ) : (k : ℕ) → (Fin (n+k) → X) → (Fin n → X)
  | 0,a => a
  | k+1,a => headStartBaseVF n k (Fin.init a)

def headStartExtraVF {X : Type*} (n : ℕ) : (k : ℕ) → (Fin (n+k) → X) → (Fin k → X)
  | 0,_ => Fin.elim0
  | k+1,a => Fin.lastCases (a (Fin.last (n+k))) (headStartExtraVF n k (Fin.init a))

theorem mem_rvHeadStartBundle
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (π : Fin k → Fin r)
    (a : Fin (n+k) → VF M) (u : Fin r → RVInfinity M) :
    (a,u) ∈ (rvHeadStartBundle A k π).carrier ↔
      (headStartBaseVF n k a,u) ∈ A.carrier ∧ tupleRV M (headStartExtraVF n k a)=u ∘ π := by
  induction k with
  | zero =>
    simp only [rvHeadStartBundle,headStartBaseVF]
    exact ⟨fun h => ⟨h,Subsingleton.elim _ _⟩,And.left⟩
  | succ k ih =>
    change ((Fin.init a,u) ∈ (rvHeadStartBundle A k (π ∘ Fin.castSucc)).carrier ∧
      rv M (a (Fin.last (n+k)))=u (π (Fin.last k))) ↔ _
    rw [ih]
    constructor
    · rintro ⟨⟨hA,hHead⟩,hLast⟩
      refine ⟨hA,funext (fun i => ?_)⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [DiamondIntegral.Section2.tupleRV,headStartExtraVF,Fin.lastCases_last,Function.comp_apply] using hLast
      · simpa only [DiamondIntegral.Section2.tupleRV,headStartExtraVF,Fin.lastCases_castSucc,Function.comp_apply] using congrFun hHead j
    · rintro ⟨hA,hHead⟩
      refine ⟨⟨hA,funext (fun j => ?_)⟩,?_⟩
      · simpa only [DiamondIntegral.Section2.tupleRV,headStartExtraVF,Fin.lastCases_castSucc,Function.comp_apply] using congrFun hHead j.castSucc
      · simpa only [DiamondIntegral.Section2.tupleRV,headStartExtraVF,Fin.lastCases_last,Function.comp_apply] using congrFun hHead (Fin.last k)

def headStartBaseProjection
    (A : DefSet (rawMixedSpace (M := M) n r) S) :
    (k : ℕ) → (π : Fin k → Fin r) → Map (rvHeadStartBundle A k π) A
  | 0,_ => Map.id A
  | k+1,π => (headStartBaseProjection A k (π ∘ Fin.castSucc)).comp
      (bundleProjection (rvHeadStartBundle A k (π ∘ Fin.castSucc)) (π (Fin.last k)))

theorem headStartBaseProjection_value
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (π : Fin k → Fin r)
    (p : rvHeadStartBundle A k π) :
    (headStartBaseProjection A k π p).val=(headStartBaseVF n k p.val.1,p.val.2) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih _ _

theorem rvHeadStartBundle_finite_rv_fibres
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin n → VF M,∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier ∧ u ∘ π=t}.Finite)
    (a : Fin (n+k) → VF M) :
    {u : Fin r → RVInfinity M | (a,u) ∈ (rvHeadStartBundle A k π).carrier}.Finite := by
  apply (hFin (headStartBaseVF n k a) (tupleRV M (headStartExtraVF n k a))).subset
  intro u hu
  obtain ⟨hA,hHead⟩ := (mem_rvHeadStartBundle A k π a u).mp hu
  exact ⟨hA,hHead.symm⟩

end DiamondIntegral.Section6
