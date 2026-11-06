import Calderon.ActualModelSMixedWeakForm

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "EndFC" => Module.End ℝ FC

/-- Locality on the original finite smooth core, expressed in topological support. -/
def FiniteCoreSupportPreserving (A : EndFC) : Prop :=
  ∀ F : FC, tsupport (A F).val ⊆ tsupport F.val

/-- A pointwise zero-preserving action cannot enlarge topological support. -/
theorem finiteCoreSupportPreserving_of_pointwise (A : EndFC)
    (hA : ∀ (F : FC) (x : R3), F.val x = 0 → (A F).val x = 0) :
    FiniteCoreSupportPreserving hO hD A := by
  intro F
  apply closure_mono
  intro x hx hz
  exact hx (hA F x hz)

theorem finiteCoreSupportPreserving_zero : FiniteCoreSupportPreserving hO hD (0 : EndFC) := by
  apply finiteCoreSupportPreserving_of_pointwise
  intro F x _h
  rfl

theorem finiteCoreSupportPreserving_one : FiniteCoreSupportPreserving hO hD (1 : EndFC) := by
  intro F
  exact Set.Subset.rfl

theorem finiteCoreSupportPreserving_add (A B : EndFC)
    (hA : FiniteCoreSupportPreserving hO hD A) (hB : FiniteCoreSupportPreserving hO hD B) :
    FiniteCoreSupportPreserving hO hD (A+B) := by
  intro F
  change tsupport (fun x => (A F).val x+(B F).val x) ⊆ tsupport F.val
  exact (tsupport_add _ _).trans (union_subset (hA F) (hB F))

theorem finiteCoreSupportPreserving_sub (A B : EndFC)
    (hA : FiniteCoreSupportPreserving hO hD A) (hB : FiniteCoreSupportPreserving hO hD B) :
    FiniteCoreSupportPreserving hO hD (A-B) := by
  intro F
  change tsupport (fun x => (A F).val x-(B F).val x) ⊆ tsupport F.val
  exact (tsupport_sub _ _).trans (union_subset (hA F) (hB F))

theorem finiteCoreSupportPreserving_smul (c : ℝ) (A : EndFC)
    (hA : FiniteCoreSupportPreserving hO hD A) :
    FiniteCoreSupportPreserving hO hD (c • A) := by
  intro F
  change tsupport (fun x => c • (A F).val x) ⊆ tsupport F.val
  exact (tsupport_smul_subset_right (fun _ : R3 => c) (A F).val).trans (hA F)

theorem finiteCoreSupportPreserving_mul (A B : EndFC)
    (hA : FiniteCoreSupportPreserving hO hD A) (hB : FiniteCoreSupportPreserving hO hD B) :
    FiniteCoreSupportPreserving hO hD (A*B) := by
  intro F
  exact (hA (B F)).trans (hB F)

theorem finiteCoreSupportPreserving_sum {ι : Type*} (s : Finset ι) (A : ι → EndFC)
    (hA : ∀ i ∈ s, FiniteCoreSupportPreserving hO hD (A i)) :
    FiniteCoreSupportPreserving hO hD (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using finiteCoreSupportPreserving_zero hO hD
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact finiteCoreSupportPreserving_add hO hD _ _ (hA i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)))

theorem finiteCoreSupportPreserving_coreScalar (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c) :
    FiniteCoreSupportPreserving hO hD (coreScalar hO hD c hc) := by
  apply finiteCoreSupportPreserving_of_pointwise
  intro F x hx
  change c x • F.val x = 0
  rw [hx,smul_zero]

theorem finiteCoreSupportPreserving_coreNormalizedDerivative (hF : SphereFischerInner) (i : Fin 3) :
    FiniteCoreSupportPreserving hO hD (coreNormalizedDerivative hO hD hF i) := by
  apply finiteCoreSupportPreserving_of_pointwise
  intro F x hx
  change BoundedAngularShift.normalizedDerivative hF hO hD i (F.val x) = 0
  rw [hx,map_zero]

theorem finiteCoreSupportPreserving_coreNormalizedRaising (hF : SphereFischerInner) (i : Fin 3) :
    FiniteCoreSupportPreserving hO hD (coreNormalizedRaising hO hD hF i) := by
  apply finiteCoreSupportPreserving_of_pointwise
  intro F x hx
  change BoundedAngularShift.normalizedRaising hF hO hD i (F.val x) = 0
  rw [hx,map_zero]

theorem finiteCoreSupportPreserving_coreDirectionalDerivative (v : R3) :
    FiniteCoreSupportPreserving hO hD (coreDirectionalDerivative hO hD v) :=
  tsupport_coreDirectionalDerivative_subset hO hD v


/-- The original finite spectral block action is pointwise, without a uniform norm premise. -/
theorem finiteCoreSupportPreserving_coreBlockOperator
    (K : (k : ℕ) → harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k) :
    FiniteCoreSupportPreserving hO hD (coreBlockOperator hO hD K) := by
  apply finiteCoreSupportPreserving_of_pointwise
  intro F x hx
  change coreBlockField hO hD K F x = 0
  simp [coreBlockField,hx]

theorem finiteCoreSupportPreserving_coreWeightOperator (w : ℕ → ℝ) :
    FiniteCoreSupportPreserving hO hD (coreWeightOperator hO hD w) := by
  unfold coreWeightOperator
  exact finiteCoreSupportPreserving_coreBlockOperator hO hD _

theorem finiteCoreSupportPreserving_coreDegree :
    FiniteCoreSupportPreserving hO hD (coreDegree hO hD) := by
  unfold coreDegree
  exact finiteCoreSupportPreserving_coreWeightOperator hO hD _

theorem finiteCoreSupportPreserving_coreRotation (i j : Fin 3) :
    FiniteCoreSupportPreserving hO hD (coreRotation hO hD i j) := by
  unfold coreRotation
  exact finiteCoreSupportPreserving_coreBlockOperator hO hD _

theorem finiteCoreSupportPreserving_coreRaising (hF : SphereFischerInner) (i : Fin 3) :
    FiniteCoreSupportPreserving hO hD (coreRaising hO hD hF i) := by
  unfold coreRaising
  exact finiteCoreSupportPreserving_mul hO hD _ _
    (finiteCoreSupportPreserving_coreNormalizedRaising hO hD hF i)
    (finiteCoreSupportPreserving_coreWeightOperator hO hD _)

theorem finiteCoreSupportPreserving_coreDerivative (hF : SphereFischerInner) (i : Fin 3) :
    FiniteCoreSupportPreserving hO hD (coreDerivative hO hD hF i) := by
  unfold coreDerivative
  exact finiteCoreSupportPreserving_mul hO hD _ _
    (finiteCoreSupportPreserving_coreNormalizedDerivative hO hD hF i)
    (finiteCoreSupportPreserving_coreWeightOperator hO hD _)

theorem finiteCoreSupportPreserving_modelFirstOrder (d H : Fin 3 → EndFC) (H0 : EndFC)
    (hd : ∀ i, FiniteCoreSupportPreserving hO hD (d i))
    (hH : ∀ i, FiniteCoreSupportPreserving hO hD (H i))
    (hH0 : FiniteCoreSupportPreserving hO hD H0) :
    FiniteCoreSupportPreserving hO hD (ActualModelCommutatorWords.modelFirstOrder d H H0) := by
  unfold ActualModelCommutatorWords.modelFirstOrder
  apply finiteCoreSupportPreserving_add
  · apply finiteCoreSupportPreserving_sum
    intro i _hi
    exact finiteCoreSupportPreserving_mul hO hD _ _ (hH i) (hd i)
  · exact hH0

theorem finiteCoreSupportPreserving_modelSecondOrder
    (d : Fin 3 → EndFC) (a : Fin 3 → Fin 3 → EndFC) (B : Fin 3 → EndFC) (C : EndFC)
    (hd : ∀ i, FiniteCoreSupportPreserving hO hD (d i))
    (ha : ∀ i j, FiniteCoreSupportPreserving hO hD (a i j))
    (hB : ∀ i, FiniteCoreSupportPreserving hO hD (B i))
    (hC : FiniteCoreSupportPreserving hO hD C) :
    FiniteCoreSupportPreserving hO hD (ActualModelCommutatorWords.modelSecondOrder d a B C) := by
  unfold ActualModelCommutatorWords.modelSecondOrder
  apply finiteCoreSupportPreserving_add
  · apply finiteCoreSupportPreserving_add
    · apply finiteCoreSupportPreserving_sum
      intro i _hi
      apply finiteCoreSupportPreserving_sum
      intro j _hj
      exact finiteCoreSupportPreserving_mul hO hD _ _
        (finiteCoreSupportPreserving_mul hO hD _ _ (ha i j) (hd i)) (hd j)
    · apply finiteCoreSupportPreserving_sum
      intro i _hi
      exact finiteCoreSupportPreserving_mul hO hD _ _ (hB i) (hd i)
  · exact hC

section ActualReference
variable (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
  (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)

/-- All actual reference connection coefficients act pointwise in the base variable. -/
theorem finiteCoreSupportPreserving_nativeReferenceConnectionAction (a : Fin 3) :
    FiniteCoreSupportPreserving hO hD (nativeReferenceConnectionAction hO hD g hg L q a) := by
  unfold nativeReferenceConnectionAction
  apply finiteCoreSupportPreserving_smul
  apply finiteCoreSupportPreserving_sum
  intro i _hi
  apply finiteCoreSupportPreserving_sum
  intro j _hj
  exact finiteCoreSupportPreserving_mul hO hD _ _
    (finiteCoreSupportPreserving_coreScalar hO hD _ _)
    (finiteCoreSupportPreserving_coreRotation hO hD i j)

theorem finiteCoreSupportPreserving_nativeReferenceFirstCoefficient (j : Fin 3) :
    FiniteCoreSupportPreserving hO hD
      (nativeReferenceFirstCoefficient hO hD hF g hg L q dr Ar p hdr hAr j) := by
  unfold nativeReferenceFirstCoefficient
  apply finiteCoreSupportPreserving_sum
  intro a _ha
  apply finiteCoreSupportPreserving_mul
  · exact finiteCoreSupportPreserving_coreRaising hO hD hF a
  · unfold nativeReferenceFrameScalar
    exact finiteCoreSupportPreserving_coreScalar hO hD _ _

theorem finiteCoreSupportPreserving_nativeReferenceZeroCoefficient :
    FiniteCoreSupportPreserving hO hD
      (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr) := by
  unfold nativeReferenceZeroCoefficient
  apply finiteCoreSupportPreserving_sum
  intro a _ha
  apply finiteCoreSupportPreserving_mul
  · exact finiteCoreSupportPreserving_coreRaising hO hD hF a
  · apply finiteCoreSupportPreserving_add
    · exact finiteCoreSupportPreserving_nativeReferenceConnectionAction hO hD g hg L q a
    · apply finiteCoreSupportPreserving_mul
      · unfold nativeReferenceProfileScalar
        exact finiteCoreSupportPreserving_coreScalar hO hD _ _
      · exact finiteCoreSupportPreserving_coreDegree hO hD

theorem finiteCoreSupportPreserving_nativeReferenceAdjointFirstCoefficient (j : Fin 3) :
    FiniteCoreSupportPreserving hO hD
      (nativeReferenceAdjointFirstCoefficient hO hD hF g hg L q dr Ar p hdr hAr j) := by
  unfold nativeReferenceAdjointFirstCoefficient
  apply finiteCoreSupportPreserving_sum
  intro a _ha
  apply finiteCoreSupportPreserving_mul
  · apply finiteCoreSupportPreserving_smul
    exact finiteCoreSupportPreserving_mul hO hD _ _
      (finiteCoreSupportPreserving_coreNormalizedDerivative hO hD hF a)
      (finiteCoreSupportPreserving_coreWeightOperator hO hD _)
  · unfold nativeReferenceFrameScalar
    exact finiteCoreSupportPreserving_coreScalar hO hD _ _

theorem finiteCoreSupportPreserving_nativeReferenceAdjointZeroCoefficient :
    FiniteCoreSupportPreserving hO hD
      (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr) := by
  unfold nativeReferenceAdjointZeroCoefficient
  apply finiteCoreSupportPreserving_sum
  intro a _ha
  apply finiteCoreSupportPreserving_mul
  · exact finiteCoreSupportPreserving_coreNormalizedDerivative hO hD hF a
  · apply finiteCoreSupportPreserving_add
    · apply finiteCoreSupportPreserving_smul
      exact finiteCoreSupportPreserving_mul hO hD _ _
        (finiteCoreSupportPreserving_coreWeightOperator hO hD _)
        (finiteCoreSupportPreserving_nativeReferenceConnectionAction hO hD g hg L q a)
    · apply finiteCoreSupportPreserving_mul
      · unfold nativeReferenceProfileScalar
        exact finiteCoreSupportPreserving_coreScalar hO hD _ _
      · apply finiteCoreSupportPreserving_sub
        · exact finiteCoreSupportPreserving_coreWeightOperator hO hD _
        · exact finiteCoreSupportPreserving_smul hO hD _ _
            (finiteCoreSupportPreserving_coreWeightOperator hO hD _)

/-- Original T preserves the same input support by its checked exact differential formula. -/
theorem finiteCoreSupportPreserving_nativeT :
    FiniteCoreSupportPreserving hO hD (nativeT hO hD hF g hg L q dr Ar p hdr hAr) := by
  rw [nativeT_eq_modelFirstOrder]
  exact finiteCoreSupportPreserving_modelFirstOrder hO hD _ _ _
    (fun i => finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _)
    (fun i => finiteCoreSupportPreserving_nativeReferenceFirstCoefficient hO hD hF g hg L q dr Ar p hdr hAr i)
    (finiteCoreSupportPreserving_nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr)

/-- Original T-adjoint has the same locality, including every connection and spectral term. -/
theorem finiteCoreSupportPreserving_nativeTdag :
    FiniteCoreSupportPreserving hO hD (nativeTdag hO hD hF g hg L q dr Ar p hdr hAr) := by
  rw [nativeTdag_eq_modelFirstOrder]
  exact finiteCoreSupportPreserving_modelFirstOrder hO hD _ _ _
    (fun i => finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _)
    (fun i => finiteCoreSupportPreserving_nativeReferenceAdjointFirstCoefficient hO hD hF g hg L q dr Ar p hdr hAr i)
    (finiteCoreSupportPreserving_nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr)

/-- The actual Z shift is the literal local core defect action. -/
theorem finiteCoreSupportPreserving_nativeZ :
    FiniteCoreSupportPreserving hO hD (nativeZ hO hD hF g hg L q dr Ar p hdr hAr) := by
  have he : nativeZ hO hD hF g hg L q dr Ar p hdr hAr =
      coreDefectAction hO hD hF g hg L q dr Ar p hdr hAr := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    exact nativeZField_eq_coreAction hO hD hF g hg L q dr Ar p hdr hAr F
  rw [he]
  unfold coreDefectAction
  apply finiteCoreSupportPreserving_sum
  intro a _ha
  exact finiteCoreSupportPreserving_mul hO hD _ _
    (finiteCoreSupportPreserving_coreScalar hO hD _ _)
    (finiteCoreSupportPreserving_coreDerivative hO hD hF a)

end ActualReference

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
