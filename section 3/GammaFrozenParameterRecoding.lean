import «section 3».GammaMeasuredSchemaBaseChange
import «section 3».GammaMeasuredGeometricRecodingValidity
import IntegrationSection6.GammaFormulaTypedRows
import Section3.GammaRealMap

/-! Naming only the frozen VF tail gives a literal substitution from a
full VF parameter tuple to its unary head. Complete density graphs and
finite geometric proof validity pass through the existing recoder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a b k : ℕ}

def gammaFrozenFormulaBaseChange (B : Base (M := M)) (x : Fin n → VF (M := M)) :
    GammaFormulaBaseChange B ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ :=
  ⟨fun _ _ h => h.mono Set.subset_union_left (Set.Subset.refl _)⟩

def frozenHeadDomainMap (x : Fin n → VF (M := M)) (a : ℕ) (w : Fin (1+a) → M) : Fin ((n+1)+a) → M :=
  Fin.append (Fin.cons (w (Fin.castAdd a 0)) (vfValues x)) (w ∘ Fin.natAdd 1)

def frozenHeadRelationMap (x : Fin n → VF (M := M)) (a b : ℕ) (w : Fin ((1+a)+b) → M) : Fin (((n+1)+a)+b) → M :=
  Fin.append (frozenHeadDomainMap x a (w ∘ Fin.castAdd b)) (w ∘ Fin.natAdd (1+a))

theorem frozenHeadDomainMap_definable (x : Fin n → VF (M := M)) (a : ℕ) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _
      (B.real ∪ Set.range (vfValues x)) (frozenHeadDomainMap x a) := by
  let f := frozenHeadDomainMap x a
  let S := B.real ∪ Set.range (vfValues x)
  change @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _ S f
  letI := CanonicalStructure.normalize (M := M)
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [f,frozenHeadDomainMap,Fin.append_left,Fin.cons_zero]
      change S.DefinableFun LRV (fun w : Fin (1+a) → M => w (Fin.castAdd a 0))
      exact Set.DefinableFun.proj LRV
    · simp only [f,frozenHeadDomainMap,Fin.append_left,Fin.cons_succ,vfValues]
      change S.DefinableFun LRV (fun _ : Fin (1+a) → M => (x j).val)
      exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self j))
  · simp only [f,frozenHeadDomainMap,Fin.append_right,Function.comp_apply]
    change S.DefinableFun LRV (fun w : Fin (1+a) → M => w (Fin.natAdd 1 i))
    exact Set.DefinableFun.proj LRV

theorem frozenHeadRelationMap_definable (x : Fin n → VF (M := M)) (a b : ℕ) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _
      (B.real ∪ Set.range (vfValues x)) (frozenHeadRelationMap x a b) := by
  let f := frozenHeadRelationMap x a b
  let S := B.real ∪ Set.range (vfValues x)
  let D := frozenHeadDomainMap x a
  have hD := frozenHeadDomainMap_definable (B := B) x a
  change @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) _ _ S f
  letI := CanonicalStructure.normalize (M := M)
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [f,frozenHeadRelationMap,Fin.append_left]
    change S.DefinableFun LRV (fun w : Fin ((1+a)+b) → M => D (w ∘ Fin.castAdd b) i)
    exact (hD i).comp (fun _ => Set.DefinableFun.proj LRV)
  · simp only [f,frozenHeadRelationMap,Fin.append_right,Function.comp_apply]
    change S.DefinableFun LRV (fun w : Fin ((1+a)+b) → M => w (Fin.natAdd (1+a) i))
    exact Set.DefinableFun.proj LRV

theorem frozenHeadDomainMap_append (x : Fin n → VF (M := M)) (z : Fin 1 → M) (r : Fin a → M) :
    frozenHeadDomainMap x a (Fin.append z r) = Fin.append (Fin.cons (z 0) (vfValues x)) r := by
  simp only [frozenHeadDomainMap,Fin.append_left]
  congr 1
  funext j
  exact Fin.append_right _ _ j

theorem frozenHeadRelationMap_append (x : Fin n → VF (M := M)) (z : Fin 1 → M) (r : Fin a → M) (s : Fin b → M) :
    frozenHeadRelationMap x a b (Fin.append (Fin.append z r) s) = Fin.append (Fin.append (Fin.cons (z 0) (vfValues x)) r) s := by
  have h : Fin.append (Fin.append z r) s ∘ Fin.castAdd b = Fin.append z r := funext (Fin.append_left _ _)
  have ht : Fin.append (Fin.append z r) s ∘ Fin.natAdd (1+a) = s := funext (Fin.append_right _ _)
  simp only [frozenHeadRelationMap,h,ht,frozenHeadDomainMap_append]

def gammaFrozenParameterRecode (B : Base (M := M)) (x : Fin n → VF (M := M)) :
    GammaParameterRecode ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (n+1) 1 (fun _ => .vf) (fun _ => .vf) where
  domain {a} D := ⟨{w | frozenHeadDomainMap x a w ∈ D.val ∧ w ∈ sortedUniverse (Fin.append (fun _ : Fin 1 => .vf) (fun _ : Fin a => .rv))},
    D.property.preimage_real_map _ _ (frozenHeadDomainMap_definable (B := B) x a)⟩
  relation {a b} R := ⟨{w | frozenHeadRelationMap x a b w ∈ R.val ∧ w ∈ sortedUniverse
      (Fin.append (Fin.append (fun _ : Fin 1 => .vf) (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv))},
    R.property.preimage_real_map _ _ (frozenHeadRelationMap_definable (B := B) x a b)⟩

theorem gammaFrozenParameterRecode_domain_rows (x : Fin n → VF (M := M))
    (D : GammaDomainFormula ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (n+1) a (fun _ => .vf))
    (z : Fin 1 → VF (M := M)) :
    (gammaFrozenParameterRecode B x).DomainAgreement D (vfValues (Fin.cons (z 0) x)) (vfValues z) := by
  apply gammaDomainRows_agree_of_typed D ((gammaFrozenParameterRecode B x).domain D)
  intro r
  have hSort := sorted_append_RV (fun _ : Fin 1 => SortTag.vf) (vfValues z) (fun j => (z j).property) r
  change (Fin.append (vfValues (Fin.cons (z 0) x)) (rvValues r) ∈ D.val) ↔
    (frozenHeadDomainMap x a (Fin.append (vfValues z) (rvValues r)) ∈ D.val ∧ _)
  rw [frozenHeadDomainMap_append]
  have heq : vfValues (Fin.cons (z 0) x) = Fin.cons (vfValues z 0) (vfValues x) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [heq]
  exact (and_iff_left hSort).symm

theorem gammaFrozenParameterRecode_relation_rows (x : Fin n → VF (M := M))
    (R : GammaRelationFormula ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (n+1) a b (fun _ => .vf))
    (z : Fin 1 → VF (M := M)) :
    (gammaFrozenParameterRecode B x).RelationAgreement R (vfValues (Fin.cons (z 0) x)) (vfValues z) := by
  apply gammaRelationRows_agree_of_typed R ((gammaFrozenParameterRecode B x).relation R)
  intro r s
  have hSort := sorted_append_RV _ _ (sorted_append_RV (fun _ : Fin 1 => SortTag.vf) (vfValues z) (fun j => (z j).property) r) s
  change (Fin.append (Fin.append (vfValues (Fin.cons (z 0) x)) (rvValues r)) (rvValues s) ∈ R.val) ↔
    (frozenHeadRelationMap x a b (Fin.append (Fin.append (vfValues z) (rvValues r)) (rvValues s)) ∈ R.val ∧ _)
  rw [frozenHeadRelationMap_append]
  have heq : vfValues (Fin.cons (z 0) x) = Fin.cons (vfValues z 0) (vfValues x) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [heq]
  exact (and_iff_left hSort).symm

theorem gammaFrozenParameterRecode_volume_rows (x : Fin n → VF (M := M))
    (F : GammaRVVolumeSchema ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (n+1) a k (fun _ => .vf))
    (z : Fin 1 → VF (M := M)) :
    (GammaVolumeParameterRecode.mk (gammaFrozenParameterRecode B x)).VolumeObjectAgreement F
      (vfValues (Fin.cons (z 0) x)) (vfValues z) :=
  ⟨⟨gammaFrozenParameterRecode_domain_rows x ⟨F.object.domain,F.object.domain_definable⟩ z,
      gammaFrozenParameterRecode_relation_rows x ⟨F.object.volume,F.object.volume_definable⟩ z⟩,
    gammaFrozenParameterRecode_relation_rows x ⟨F.density,F.density_definable⟩ z⟩

theorem gammaFrozenParameterRecode_geometry_rows (x : Fin n → VF (M := M))
    {F : GammaMeasuredRVSchema hc ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (n+1) a (k+1) (fun _ => .vf)}
    {E : GammaMeasuredRVSchema hc ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (n+1) b (k+1) (fun _ => .vf)}
    (H : GammaMeasuredRelationSchema F E) (z : Fin 1 → VF (M := M)) :
    H.RecodeAgreement (gammaFrozenParameterRecode B x) (vfValues (Fin.cons (z 0) x)) (vfValues z) := by
  induction H with
  | iso I => exact ⟨gammaFrozenParameterRecode_volume_rows x I.source.toRVTemplate z,
      gammaFrozenParameterRecode_volume_rows x I.target.toRVTemplate z,
      gammaFrozenParameterRecode_relation_rows x ⟨I.chart,I.chart_definable⟩ z⟩
  | agreement F E => exact ⟨gammaFrozenParameterRecode_volume_rows x F.toRVTemplate z,
      gammaFrozenParameterRecode_volume_rows x E.toRVTemplate z,trivial⟩
  | elementary F N A => exact ⟨gammaFrozenParameterRecode_volume_rows x F.toRVTemplate z,
      gammaFrozenParameterRecode_volume_rows x (F.elementaryFormula.essential.withBound N).toRVTemplate z,trivial⟩
  | symm H ih => exact ⟨gammaFrozenParameterRecode_volume_rows x _ z,gammaFrozenParameterRecode_volume_rows x _ z,ih⟩
  | trans E H K ihH ihK => exact ⟨gammaFrozenParameterRecode_volume_rows x _ z,gammaFrozenParameterRecode_volume_rows x _ z,ihH,ihK⟩
  | coprod H K N L ihH ihK => exact ⟨gammaFrozenParameterRecode_volume_rows x _ z,gammaFrozenParameterRecode_volume_rows x _ z,ihH,ihK⟩

end DiamondIntegral.Section3
