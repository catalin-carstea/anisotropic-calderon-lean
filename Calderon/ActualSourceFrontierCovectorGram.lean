import Calderon.ActualSourceOpenMatchCovectorGram
import Calderon.ActualSourceCovectorGramContinuity

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff Distributions Matrix
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ConnectionError

theorem radiusTwoSourceCovectorGram_eq_of_limit_match
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
    (Phi : R3 → R3) (W : Set R3) (hW : IsOpen W)
    (x q : R3) (hx : x ∈ (radiusTwoOpens : Set R3))
    (hq : q ∈ (radiusTwoOpens : Set R3)) (hClosure : x ∈ closure W)
    (hLimit : Tendsto Phi (𝓝[W] x) (𝓝 q))
    (hMaps : ∀ y ∈ W, Phi y ∈ (radiusTwoOpens : Set R3))
    (hDiff : ∀ y ∈ W, DifferentiableAt ℝ Phi y)
    (hMatch : ∀ y ∈ W, ∀ source : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse hreg hcalc g2 hg2 source y =
        radiusTwoSmoothSourceResponse hreg hcalc g1 hg1 source (Phi y))
    (hMetric : ∀ y ∈ W, g2 y = (D Phi y)ᵀ * g1 (Phi y) * D Phi y) :
    let K1 : R3 → Matrix (Fin 3) (Fin 3) ℝ := fun y i j =>
      d (radiusTwoSmoothSourceResponse hreg hcalc g1 hg1 (f i)) y j
    let K2 : R3 → Matrix (Fin 3) (Fin 3) ℝ := fun y i j =>
      d (radiusTwoSmoothSourceResponse hreg hcalc g2 hg2 (f i)) y j
    K2 x * (g2 x)⁻¹ * (K2 x)ᵀ = K1 q * (g1 q)⁻¹ * (K1 q)ᵀ := by
  intro K1 K2
  letI : NeBot (𝓝[W] x) := mem_closure_iff_nhdsWithin_neBot.mp hClosure
  have hLeft : Tendsto (fun y => K2 y * (g2 y)⁻¹ * (K2 y)ᵀ)
      (𝓝[W] x) (𝓝 (K2 x * (g2 x)⁻¹ * (K2 x)ᵀ)) :=
    (continuousAt_radiusTwoSourceCovectorGram hreg hcalc g2 hg2 f x hx).mono_left
      nhdsWithin_le_nhds
  have hRight : Tendsto (fun y => K1 (Phi y) * (g1 (Phi y))⁻¹ * (K1 (Phi y))ᵀ)
      (𝓝[W] x) (𝓝 (K1 q * (g1 q)⁻¹ * (K1 q)ᵀ)) :=
    Filter.Tendsto.comp
      (continuousAt_radiusTwoSourceCovectorGram hreg hcalc g1 hg1 f q hq) hLimit
  have hEqual : (fun y => K2 y * (g2 y)⁻¹ * (K2 y)ᵀ) =ᶠ[𝓝[W] x]
      (fun y => K1 (Phi y) * (g1 (Phi y))⁻¹ * (K1 (Phi y))ᵀ) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact radiusTwoSourceCovectorGram_eq_of_open_isometry
      hreg hcalc g1 hg1 g2 hg2 f Phi W hW y hy (hMaps y hy) (hDiff y hy)
      hMatch (hMetric y hy)
  exact tendsto_nhds_unique_of_eventuallyEq hLeft hRight hEqual

theorem radiusTwoSourceCovectorMatrix_det_ne_zero_of_limit_match
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
    (Phi : R3 → R3) (W : Set R3) (hW : IsOpen W)
    (x q : R3) (hx : x ∈ (radiusTwoOpens : Set R3))
    (hq : q ∈ (radiusTwoOpens : Set R3)) (hClosure : x ∈ closure W)
    (hLimit : Tendsto Phi (𝓝[W] x) (𝓝 q))
    (hMaps : ∀ y ∈ W, Phi y ∈ (radiusTwoOpens : Set R3))
    (hDiff : ∀ y ∈ W, DifferentiableAt ℝ Phi y)
    (hMatch : ∀ y ∈ W, ∀ source : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse hreg hcalc g2 hg2 source y =
        radiusTwoSmoothSourceResponse hreg hcalc g1 hg1 source (Phi y))
    (hMetric : ∀ y ∈ W, g2 y = (D Phi y)ᵀ * g1 (Phi y) * D Phi y)
    (hRank : (Matrix.of (fun i j =>
      d (radiusTwoSmoothSourceResponse hreg hcalc g1 hg1 (f i)) q j)).det ≠ 0) :
    (Matrix.of (fun i j =>
      d (radiusTwoSmoothSourceResponse hreg hcalc g2 hg2 (f i)) x j)).det ≠ 0 := by
  have hGram := radiusTwoSourceCovectorGram_eq_of_limit_match hreg hcalc g1 hg1 g2 hg2 f
    Phi W hW x q hx hq hClosure hLimit hMaps hDiff hMatch hMetric
  have hInv : ((g1 q)⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact inv_ne_zero (hg1.posDef q).det_pos.ne'
  exact det_ne_zero_of_covectorGram_eq _ _ _ _ hGram hRank hInv

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceCovectorGram_eq_of_limit_match
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceCovectorMatrix_det_ne_zero_of_limit_match
