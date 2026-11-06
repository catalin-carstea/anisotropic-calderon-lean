import Calderon.FrozenCartesianChainRule
import Calderon.SourceChartCovectorGramAlgebra
import Mathlib.Analysis.Calculus.FDeriv.Congr

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Distributions BigOperators Matrix
namespace OAI.AnisotropicCalderon.ConnectionError

lemma isUnit_det_of_posDef_pullback
    (G1 G2 J : Matrix (Fin 3) (Fin 3) ℝ)
    (hG2 : G2.PosDef) (hMetric : G2 = Jᵀ * G1 * J) : IsUnit J.det := by
  apply isUnit_iff_ne_zero.mpr
  intro hJ
  have hdet := congrArg Matrix.det hMetric
  simp only [Matrix.det_mul, Matrix.det_transpose, hJ, zero_mul, mul_zero] at hdet
  exact hG2.det_pos.ne' hdet

end OAI.AnisotropicCalderon.ConnectionError
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ConnectionError

theorem radiusTwoSourceCovectorMatrix_eq_mul_of_open_match
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
    (Phi : R3 → R3) (W : Set R3) (hW : IsOpen W)
    (x : R3) (hx : x ∈ W) (hPhiX : Phi x ∈ (radiusTwoOpens : Set R3))
    (hPhi : DifferentiableAt ℝ Phi x)
    (hMatch : ∀ y ∈ W, ∀ source : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse hreg hcalc g2 hg2 source y =
        radiusTwoSmoothSourceResponse hreg hcalc g1 hg1 source (Phi y)) :
    Matrix.of (fun i j => d (radiusTwoSmoothSourceResponse hreg hcalc g2 hg2 (f i)) x j) =
    Matrix.of (fun i j => d (radiusTwoSmoothSourceResponse hreg hcalc g1 hg1 (f i)) (Phi x) j) * D Phi x := by
  ext i j
  have hNear : radiusTwoSmoothSourceResponse hreg hcalc g2 hg2 (f i) =ᶠ[𝓝 x]
      (radiusTwoSmoothSourceResponse hreg hcalc g1 hg1 (f i)) ∘ Phi := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact hMatch y hy (f i)
  have hd : d (radiusTwoSmoothSourceResponse hreg hcalc g2 hg2 (f i)) x j =
      d ((radiusTwoSmoothSourceResponse hreg hcalc g1 hg1 (f i)) ∘ Phi) x j :=
    congrArg (fun L : R3 →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) hNear.fderiv_eq
  change d (radiusTwoSmoothSourceResponse hreg hcalc g2 hg2 (f i)) x j =
    ∑ k : Fin 3, d (radiusTwoSmoothSourceResponse hreg hcalc g1 hg1 (f i))
      (Phi x) k * D Phi x k j
  exact hd.trans (d_comp_apply _ Phi x
    (differentiableAt_radiusTwoSmoothSourceResponse hreg hcalc g1 hg1 (f i) (Phi x) hPhiX)
    hPhi j)

theorem radiusTwoSourceCovectorGram_eq_of_open_isometry
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
    (Phi : R3 → R3) (W : Set R3) (hW : IsOpen W)
    (x : R3) (hx : x ∈ W) (hPhiX : Phi x ∈ (radiusTwoOpens : Set R3))
    (hPhi : DifferentiableAt ℝ Phi x)
    (hMatch : ∀ y ∈ W, ∀ source : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse hreg hcalc g2 hg2 source y =
        radiusTwoSmoothSourceResponse hreg hcalc g1 hg1 source (Phi y))
    (hMetric : g2 x = (D Phi x)ᵀ * g1 (Phi x) * D Phi x) :
    let K1 : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
      d (radiusTwoSmoothSourceResponse hreg hcalc g1 hg1 (f i)) (Phi x) j
    let K2 : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
      d (radiusTwoSmoothSourceResponse hreg hcalc g2 hg2 (f i)) x j
    K2 * (g2 x)⁻¹ * K2ᵀ = K1 * (g1 (Phi x))⁻¹ * K1ᵀ := by
  intro K1 K2
  have hK : K2 = K1 * D Phi x :=
    radiusTwoSourceCovectorMatrix_eq_mul_of_open_match
      hreg hcalc g1 hg1 g2 hg2 f Phi W hW x hx hPhiX hPhi hMatch
  exact covectorGram_eq_of_pullback K1 K2 (g1 (Phi x)) (g2 x) (D Phi x) hMetric hK
    (isUnit_det_of_posDef_pullback _ _ _ (hg2.posDef x) hMetric)

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ConnectionError.isUnit_det_of_posDef_pullback
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceCovectorMatrix_eq_mul_of_open_match
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceCovectorGram_eq_of_open_isometry
