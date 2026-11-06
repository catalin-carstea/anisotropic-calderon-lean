import Calderon.ActualFiniteHarmonicModelReferenceZeroBalancedBounds
import Calderon.ActualReferenceDDHigherSpectralGraphs

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherLogFrameJets ActualReferenceDDHigherCLMProducts
  ActualReferenceDDHigherSpectralGraphs ActualReferenceDDSpectralTransport
  ActualReferenceModelTrace ActualReferenceParallelRaising AmbientReferenceRaising
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ReferenceWeightedApproximation
  PrincipalCommutator ConformalDepth RadiusProfile MetricOperator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

theorem exists_referenceZeroDefect_input_factors_uniform_coordinate_word_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ x ∈ K, let beta := actualReferenceBeta g L lam δ R p x
      1 ≤ beta → ∀ a : Fin 3,
      let LF : R3 → SphereL2 →L[ℝ] SphereL2 := fun y =>
        -(normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) a)) +
          referenceFrameDerivative g L lam a (fun z => Real.log (referenceRadius δ R p L z)) y •
            (ContinuousLinearMap.id ℝ SphereL2 - (2 : ℝ) • inverseDegreeMultiplier hO hD)
      let RF : R3 → SphereL2 →L[ℝ] SphereL2 := fun y =>
        normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) a) +
          referenceFrameDerivative g L lam a (fun z => Real.log (referenceRadius δ R p L z)) y •
            (ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD)
      ∀ w : List (Fin 3), w.length ≤ 2 →
        ‖coordinateFieldWordPartial w LF x‖ ≤ C*beta^(1+w.length) ∧
        ‖coordinateFieldWordPartial w RF x‖ ≤ C*beta^(1+w.length) ∧
        PreservesSphereSpectralGraphs hO hD (coordinateFieldWordPartial w LF x) ∧
        PreservesSphereSpectralGraphs hO hD (coordinateFieldWordPartial w RF x) := by
  obtain ⟨M,hM,hgeom⟩ := exists_referenceDD_fixed_geometry_uniform_coordinate_word_bounds
    hO hD g hg L K hK 2
  obtain ⟨J,hJ,hlog⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds
    g hg L hL K hK 2
  let B2 : SphereL2 →L[ℝ] SphereL2 := ContinuousLinearMap.id ℝ SphereL2 -
    (2 : ℝ) • inverseDegreeMultiplier hO hD
  let B1 : SphereL2 →L[ℝ] SphereL2 := ContinuousLinearMap.id ℝ SphereL2 -
    inverseDegreeMultiplier hO hD
  let B : ℝ := 1+‖B2‖+‖B1‖
  let C : ℝ := 1+M+4*J*B
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hB2 : ‖B2‖ ≤ B := by dsimp only [B]; linarith [norm_nonneg B1]
  have hB1 : ‖B1‖ ≤ B := by dsimp only [B]; linarith [norm_nonneg B2]
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCbound : M+4*J*B ≤ C := by dsimp only [C]; linarith
  have hIg := preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD
  have hIdg := preservesSphereSpectralGraphs_id hO hD
  have hB2g : PreservesSphereSpectralGraphs hO hD B2 :=
    preservesSphereSpectralGraphs_sub hO hD _ _ hIdg
      (preservesSphereSpectralGraphs_smul hO hD 2 _ hIg)
  have hB1g : PreservesSphereSpectralGraphs hO hD B1 :=
    preservesSphereSpectralGraphs_sub hO hD _ _ hIdg hIg
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hb a LF RF w hw
  have hb0 : 0 ≤ beta := le_trans zero_le_one hb
  let A : R3 → SphereL2 →L[ℝ] SphereL2 := fun y =>
    normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) a)
  let f : R3 → ℝ := referenceFrameDerivative g L lam a
    (fun y => Real.log (referenceRadius δ R p L y))
  have hAS : ContDiff ℝ ∞ A := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam a
  have hfS : ContDiff ℝ ∞ f := contDiff_referenceFrameDerivative g hg L lam a _
    (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hLF : ContDiff ℝ ∞ LF := hAS.neg.add (hfS.smul contDiff_const)
  have hRF : ContDiff ℝ ∞ RF := hAS.add (hfS.smul contDiff_const)
  have hAJ0 : HasCoordinateWordJetBound 2 A x M beta 0 := by
    intro v hv
    have ht := (hgeom lam hlam x hx v hv).2.2.2.2.2.1 a
    exact ht.trans (by simpa only [Nat.zero_add,mul_one] using
      mul_le_mul_of_nonneg_left (one_le_pow₀ hb) hM0)
  have hAJ : HasCoordinateWordJetBound 2 A x M beta 1 :=
    hasCoordinateWordJetBound_raise_degree 2 A x M beta 0 1 hM0 hb (by norm_num) hAJ0
  have hfJ : HasCoordinateWordJetBound 2 f x J beta 1 := by
    intro v hv
    simpa only [Real.norm_eq_abs,f,beta,actualReferenceBeta] using
      (hlog lam hlam δ hδ hδ1 R hR p hp x hx hb v hv).1 a
  have hConst (B0 : SphereL2 →L[ℝ] SphereL2) (hBnorm : ‖B0‖ ≤ B) :
      HasCoordinateWordJetBound 2 (fun _ : R3 => B0) x B beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 B0 x B beta hBnorm hb0
  have hProf (B0 : SphereL2 →L[ℝ] SphereL2) (hBnorm : ‖B0‖ ≤ B) :
      HasCoordinateWordJetBound 2 (fun y => f y • B0) x (4*J*B) beta 1 := by
    have ht := hasCoordinateWordJetBound_smul 2 f (fun _ : R3 => B0)
      hfS contDiff_const x J B beta 1 0 hJ.le hB0 hb0 hfJ (hConst B0 hBnorm)
    convert ht using 1 <;> norm_num
  have hLJ : HasCoordinateWordJetBound 2 LF x (M+4*J*B) beta 1 :=
    hasCoordinateWordJetBound_add 2 (fun y => -(A y)) (fun y => f y • B2)
      hAS.neg (hfS.smul contDiff_const) x M (4*J*B) beta 1
      (hasCoordinateWordJetBound_neg 2 A hAS x M beta 1 hAJ) (hProf B2 hB2)
  have hRJ : HasCoordinateWordJetBound 2 RF x (M+4*J*B) beta 1 :=
    hasCoordinateWordJetBound_add 2 A (fun y => f y • B1)
      hAS (hfS.smul contDiff_const) x M (4*J*B) beta 1 hAJ (hProf B1 hB1)
  have hAg (y : R3) : PreservesSphereSpectralGraphs hO hD (A y) :=
    preservesSphereSpectralGraphs_normalizedReferenceAngularConnection hO hD g L lam y
      (referenceMetricGramFrame g L (lam,y) a)
  have hNegAg (y : R3) : PreservesSphereSpectralGraphs hO hD (-(A y)) := by
    intro weight u U hU k
    change SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k ((-(A y)) U) =
      weight k • SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k ((-(A y)) u)
    simp only [ContinuousLinearMap.neg_apply,map_neg]
    rw [hAg y weight u U hU k,smul_neg]
  have hLg (y : R3) : PreservesSphereSpectralGraphs hO hD (LF y) :=
    preservesSphereSpectralGraphs_add hO hD _ _ (hNegAg y)
      (preservesSphereSpectralGraphs_smul hO hD (f y) B2 hB2g)
  have hRg (y : R3) : PreservesSphereSpectralGraphs hO hD (RF y) :=
    preservesSphereSpectralGraphs_add hO hD _ _ (hAg y)
      (preservesSphereSpectralGraphs_smul hO hD (f y) B1 hB1g)
  refine ⟨(hLJ w hw).trans ?_,(hRJ w hw).trans ?_,
    preservesSphereSpectralGraphs_coordinateFieldWordPartial hO hD LF hLF hLg w x,
    preservesSphereSpectralGraphs_coordinateFieldWordPartial hO hD RF hRF hRg w x⟩
  all_goals exact mul_le_mul_of_nonneg_right hCbound (pow_nonneg hb0 _)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
