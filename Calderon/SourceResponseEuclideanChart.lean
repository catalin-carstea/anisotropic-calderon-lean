import Calderon.RadiusTwoSourceCoordinates
import Calderon.OpenDomainLocalChart
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped ContDiff Distributions Matrix
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature

/-- Actual source coordinates transported by the native finite Euclidean equivalence. -/
def radiusTwoSourceEuclideanCoordinates
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ)) : R3 → R3 :=
  fun x => (EuclideanSpace.equiv (Fin 3) ℝ).symm
    (radiusTwoSourceCoordinates hreg hcalc g hg f x)

theorem exists_radiusTwoSourceEuclideanCoordinates_localChart_of_det_ne_zero
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3))
    (hdet : (Matrix.of (fun i j =>
      d (radiusTwoSmoothSourceResponse hreg hcalc g hg (f i)) p j)).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph R3 R3,
      (e : R3 → R3) = radiusTwoSourceEuclideanCoordinates hreg hcalc g hg f ∧
      p ∈ e.source ∧ radiusTwoSourceEuclideanCoordinates hreg hcalc g hg f p ∈ e.target ∧
      e.source ⊆ (radiusTwoOpens : Set R3) ∧
      ContDiffOn ℝ ∞ (radiusTwoSourceEuclideanCoordinates hreg hcalc g hg f) e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  let E := EuclideanSpace.equiv (Fin 3) ℝ
  let U : Fin 3 → R3 → ℝ := fun i => radiusTwoSmoothSourceResponse hreg hcalc g hg (f i)
  let J : R3 →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi fun i => fderiv ℝ (U i) p
  let A : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun i j => d (U i) p j)
  have hPi : HasFDerivAt (radiusTwoSourceCoordinates hreg hcalc g hg f) J p := by
    apply hasFDerivAt_pi'.mpr
    intro i
    exact (differentiableAt_radiusTwoSmoothSourceResponse hreg hcalc g hg (f i) p hp).hasFDerivAt
  have hF : HasFDerivAt (radiusTwoSourceEuclideanCoordinates hreg hcalc g hg f)
      (E.symm.toContinuousLinearMap.comp J) p := E.symm.hasFDerivAt.comp p hPi
  have hJValue (v : R3) : J v = A *ᵥ WithLp.ofLp v := by
    funext i
    have hv : v = ∑ j : Fin 3, v j • EuclideanSpace.single j (1 : ℝ) := by
      ext j
      fin_cases j <;> simp [Fin.sum_univ_three, Pi.single_apply]
    change fderiv ℝ (U i) p v = ∑ j : Fin 3, d (U i) p j * v j
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hInjective : Function.Injective (E.symm.toContinuousLinearMap.comp J) := by
    intro v w h
    have hJ : J v = J w := E.symm.injective h
    have hvw : WithLp.ofLp v = WithLp.ofLp w :=
      Matrix.mulVec_injective_of_det_ne_zero hdet (by rw [← hJValue v, ← hJValue w, hJ])
    exact WithLp.ofLp_injective (2 : ENNReal) hvw
  have hInv : (fderiv ℝ (radiusTwoSourceEuclideanCoordinates hreg hcalc g hg f) p).IsInvertible := by
    rw [hF.fderiv]
    exact ConnectionError.isInvertible_of_injective_endomorphism _ hInjective
  have hSmooth : ContDiffOn ℝ ∞
      (radiusTwoSourceEuclideanCoordinates hreg hcalc g hg f) (radiusTwoOpens : Set R3) :=
    E.symm.contDiff.comp_contDiffOn (contDiffOn_radiusTwoSourceCoordinates hreg hcalc g hg f)
  exact ConnectionError.exists_smooth_local_chart_of_isOpen_of_isInvertible_fderiv
    _ (radiusTwoOpens : Set R3) radiusTwoOpens.isOpen hSmooth p hp hInv

end OAI.AnisotropicCalderon.ExteriorSource
