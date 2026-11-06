import Calderon.FirstOrderCoordinateJetCalculus
import Calderon.SupportedSpectralFiniteSumConvergence

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic ReferenceDensityBounds

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma firstOrderCoordinateAction_partialSum_sub
    (A : Fin 3 → R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (B : R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (u : R3 → SphereSobolev (5/2:ℝ)) (hu : ContDiff ℝ ∞ u) (n : ℕ) (y : R3) :
    firstOrderCoordinateAction A B (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z)) y -
      firstOrderCoordinateAction A B u y =
    B y (sphereSobolevPartialSumL (5/2:ℝ) n (u y) - u y) +
      ∑ k : Fin 3, A k y
        (sphereSobolevPartialSumL (5/2:ℝ) n (fderiv ℝ u y (EuclideanSpace.single k 1)) -
          fderiv ℝ u y (EuclideanSpace.single k 1)) := by
  simp only [firstOrderCoordinateAction,fderiv_sphereSobolevPartialSumL_fiveHalf u hu,map_sub]
  rw [Finset.sum_sub_distrib]
  abel

/-- Local smooth operator coefficients preserve weighted source truncation convergence.
No coefficient bound independent of the radius or source is asserted. -/
theorem tendsto_integral_firstOrderCoordinateAction_partialSum_sub_sq
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (A : Fin 3 → R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (B : R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (u : R3 → SphereSobolev (5/2:ℝ)) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hA : ∀ k, ∀ y ∈ tsupport u, ContinuousAt (A k) y)
    (hB : ∀ y ∈ tsupport u, ContinuousAt B y) :
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (lam,y) *
      ‖firstOrderCoordinateAction A B (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z)) y -
        firstOrderCoordinateAction A B u y‖^2) atTop (𝓝 0) := by
  classical
  let V : Option (Fin 3) → R3 → SphereSobolev (5/2:ℝ) := fun k =>
    match k with
    | none => u
    | some j => fun y => fderiv ℝ u y (EuclideanSpace.single j 1)
  let C : Option (Fin 3) → R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W := fun k =>
    match k with
    | none => B
    | some j => A j
  have hV : ∀ k, Continuous (V k) := by
    intro k
    cases k with
    | none => exact hu.continuous
    | some j => exact ((hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hSupp : ∀ k, tsupport (V k) ⊆ tsupport u := by
    intro k
    cases k with
    | none => exact subset_rfl
    | some j => exact tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1)
  have hC : ∀ k, ∀ y ∈ tsupport u, ContinuousAt (C k) y := by
    intro k
    cases k with
    | none => exact hB
    | some j => exact hA j
  have hLimit := tendsto_integral_supported_finite_clm_partialSum_error
    g hg L lam (tsupport u) hc V hV hSupp C hC
  have hEq (n : ℕ) (y : R3) :
      (∑ k, C k y (sphereSobolevPartialSumL (5/2:ℝ) n (V k y) - V k y)) =
      firstOrderCoordinateAction A B (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z)) y -
        firstOrderCoordinateAction A B u y := by
    rw [Fintype.sum_option]
    exact (firstOrderCoordinateAction_partialSum_sub A B u hu n y).symm
  simpa only [hEq] using hLimit

lemma tsupport_firstOrderCoordinateAction_subset
    (A : Fin 3 → R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (B : R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (u : R3 → SphereSobolev (5/2:ℝ)) :
    tsupport (firstOrderCoordinateAction A B u) ⊆ tsupport u := by
  classical
  apply closure_minimal ?_ (isClosed_tsupport u)
  intro y hy
  by_contra hOutside
  have hValue : u y = 0 := image_eq_zero_of_notMem_tsupport hOutside
  have hDerivative : fderiv ℝ u y = 0 := fderiv_of_notMem_tsupport ℝ hOutside
  exact hy (by simp only [firstOrderCoordinateAction,hValue,hDerivative,
    ContinuousLinearMap.zero_apply,map_zero,Finset.sum_const_zero,add_zero])

lemma fderiv_firstOrderCoordinateAction_partialSum_sub
    (A : Fin 3 → R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (B : R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (u : R3 → SphereSobolev (5/2:ℝ)) (hu : ContDiff ℝ ∞ u) (n : ℕ) (y Z : R3)
    (hA : ∀ k, DifferentiableAt ℝ (A k) y) (hB : DifferentiableAt ℝ B y) :
    fderiv ℝ (firstOrderCoordinateAction A B
        (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z))) y Z -
      fderiv ℝ (firstOrderCoordinateAction A B u) y Z =
    ((fderiv ℝ B y Z) (sphereSobolevPartialSumL (5/2:ℝ) n (u y) - u y) +
      B y (sphereSobolevPartialSumL (5/2:ℝ) n (fderiv ℝ u y Z) - fderiv ℝ u y Z)) +
      ∑ k : Fin 3, ((fderiv ℝ (A k) y Z)
        (sphereSobolevPartialSumL (5/2:ℝ) n (fderiv ℝ u y (EuclideanSpace.single k 1)) -
          fderiv ℝ u y (EuclideanSpace.single k 1)) +
        A k y (sphereSobolevPartialSumL (5/2:ℝ) n
          (fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single k 1)) y Z) -
          fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single k 1)) y Z)) := by
  classical
  have hN := fderiv_firstOrderCoordinateAction_apply A B
    (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z)) y Z
      (contDiff_sphereSobolevPartialSumL_fiveHalf u hu n).contDiffAt hA hB
  have h0 := fderiv_firstOrderCoordinateAction_apply A B u y Z hu.contDiffAt hA hB
  have hDiff := congrArg₂ (fun a b : W => a-b) hN h0
  simp_rw [secondFderiv_sphereSobolevPartialSumL_fiveHalf u hu] at hDiff
  simp only [fderiv_sphereSobolevPartialSumL_fiveHalf u hu] at hDiff
  refine hDiff.trans ?_
  simp only [map_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  abel

theorem tendsto_integral_fderiv_firstOrderCoordinateAction_partialSum_sub_sq
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (A : Fin 3 → R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (B : R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (u : R3 → SphereSobolev (5/2:ℝ)) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hA : ∀ k, ∀ y ∈ tsupport u, ContDiffAt ℝ ∞ (A k) y)
    (hB : ∀ y ∈ tsupport u, ContDiffAt ℝ ∞ B y) (Z : R3) :
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (lam,y) *
      ‖fderiv ℝ (firstOrderCoordinateAction A B
          (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z))) y Z -
        fderiv ℝ (firstOrderCoordinateAction A B u) y Z‖^2) atTop (𝓝 0) := by
  classical
  let V : Option (Fin 3) × Bool → R3 → SphereSobolev (5/2:ℝ) := fun k =>
    match k with
    | (none,false) => u
    | (none,true) => fun y => fderiv ℝ u y Z
    | (some j,false) => fun y => fderiv ℝ u y (EuclideanSpace.single j 1)
    | (some j,true) => fun y => fderiv ℝ
        (fun z => fderiv ℝ u z (EuclideanSpace.single j 1)) y Z
  let C : Option (Fin 3) × Bool → R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W := fun k =>
    match k with
    | (none,false) => fun y => fderiv ℝ B y Z
    | (none,true) => B
    | (some j,false) => fun y => fderiv ℝ (A j) y Z
    | (some j,true) => A j
  have hDu (X : R3) : ContDiff ℝ ∞ (fun y => fderiv ℝ u y X) :=
    (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hV : ∀ k, Continuous (V k) := by
    rintro ⟨k,b⟩
    cases k <;> cases b
    · exact hu.continuous
    · exact (hDu Z).continuous
    · exact (hDu _).continuous
    · exact (((hDu _).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hSupp : ∀ k, tsupport (V k) ⊆ tsupport u := by
    rintro ⟨k,b⟩
    cases k <;> cases b
    · exact subset_rfl
    · exact tsupport_fderiv_apply_subset ℝ Z
    · exact tsupport_fderiv_apply_subset ℝ _
    · exact (tsupport_fderiv_apply_subset ℝ Z).trans (tsupport_fderiv_apply_subset ℝ _)
  have hC : ∀ k, ∀ y ∈ tsupport u, ContinuousAt (C k) y := by
    rintro ⟨k,b⟩ y hy
    cases k <;> cases b
    · exact (((hB y hy).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).continuousAt
    · exact (hB y hy).continuousAt
    · exact (((hA _ y hy).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).continuousAt
    · exact (hA _ y hy).continuousAt
  have hLimit := tendsto_integral_supported_finite_clm_partialSum_error
    g hg L lam (tsupport u) hc V hV hSupp C hC
  have hEq (n : ℕ) (y : R3) :
      (∑ k, C k y (sphereSobolevPartialSumL (5/2:ℝ) n (V k y) - V k y)) =
      fderiv ℝ (firstOrderCoordinateAction A B
        (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z))) y Z -
        fderiv ℝ (firstOrderCoordinateAction A B u) y Z := by
    by_cases hy : y ∈ tsupport u
    · rw [Fintype.sum_prod_type,Fintype.sum_option]
      simp only [Fintype.sum_bool,V,C]
      have h := fderiv_firstOrderCoordinateAction_partialSum_sub A B u hu n y Z
        (fun j => (hA j y hy).differentiableAt (by simp))
        ((hB y hy).differentiableAt (by simp))
      refine Eq.trans ?_ h.symm
      exact congrArg₂ (fun a b : W => a+b) (add_comm _ _)
        (Finset.sum_congr rfl (fun k hk => add_comm _ _))
    · have hz (k : Option (Fin 3) × Bool) : V k y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hy (hSupp k h))
      have hnSupp : tsupport (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z)) ⊆ tsupport u :=
        tsupport_comp_subset (map_zero (sphereSobolevPartialSumL (5/2:ℝ) n)) u
      have h0Out : y ∉ tsupport (firstOrderCoordinateAction A B u) :=
        fun h => hy (tsupport_firstOrderCoordinateAction_subset A B u h)
      have hnOut : y ∉ tsupport (firstOrderCoordinateAction A B
          (fun z => sphereSobolevPartialSumL (5/2:ℝ) n (u z))) :=
        fun h => hy (hnSupp (tsupport_firstOrderCoordinateAction_subset A B _ h))
      simp only [hz,map_zero,sub_zero,Finset.sum_const_zero,
        fderiv_of_notMem_tsupport ℝ h0Out,fderiv_of_notMem_tsupport ℝ hnOut,
        ContinuousLinearMap.zero_apply,sub_self]
  simpa only [hEq] using hLimit

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
