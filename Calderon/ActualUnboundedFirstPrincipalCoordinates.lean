import Calderon.ActualUnboundedFirstPrincipalNormalForm

set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.ActualUnboundedFirstPrincipalCoordinates
open SphereHarmonic SpectralCoreRegularity AngularShiftGraph
  ReferenceDensityBounds PrincipalCommutator ScalarBaseAdjoint NaturalAngularAdjoint
  ActualScalarPrincipalAdjoint ActualBalancedFirstPrincipalError ActualSupportLocalSecondForm
  ActualFirstPrincipalFrameDerivativeRemainder AmbientAngularShift SmoothSphereFields
  SmoothAngularApplication ActualUnboundedFirstPrincipalNormalForm

lemma harmonicCoordinate_second_directional (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (m : ℕ) (X Y : R3) (u : R3 → SphereL2)
    (hu : ContDiff ℝ ∞ u) (x : R3) :
    directionalFDeriv X (directionalFDeriv Y
      (fun y => sphereHarmonicCoordinate hO hD m (u y))) x =
      sphereHarmonicCoordinate hO hD m (directionalFDeriv X (directionalFDeriv Y u) x) := by
  have he : directionalFDeriv Y (fun y => sphereHarmonicCoordinate hO hD m (u y)) =
      fun y => sphereHarmonicCoordinate hO hD m (directionalFDeriv Y u y) :=
    funext (directional_const_clm_apply (sphereHarmonicCoordinate hO hD m) Y u hu)
  rw [he]
  exact directional_const_clm_apply (sphereHarmonicCoordinate hO hD m) X
    (directionalFDeriv Y u) (contDiff_directionalFDeriv Y u hu) x

/-- The same scalar principal coefficients act in every exact harmonic
codomain. Taking a coordinate here is not projecting inside an angular product. -/
lemma scalarSecondBase_harmonicCoordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (m : ℕ) (v : Fin 3 → R3) (a : MatrixField)
    (u : R3 → SphereL2) (hu : ContDiff ℝ ∞ u) (x : R3) :
    sphereHarmonicCoordinate hO hD m (scalarSecondBase v a u x) =
      scalarSecondBase v a (fun y => sphereHarmonicCoordinate hO hD m (u y)) x := by
  simp only [scalarSecondBase,map_sum,map_smul]
  simp_rw [harmonicCoordinate_second_directional hO hD m _ _ u hu x]

/-- Exact degree-changing realization of the full unbounded graph output.
The input lies in H_(m+1), and `harmonicFrameLoweringCoefficient` has codomain
H_m. Degree-zero output is included because m is arbitrary. -/
lemma contractionFirstBase_harmonicCoordinate (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (u : R3 → SphereL2) (d : Fin 3 → R3 → SphereL2)
    (hu : ContDiff ℝ ∞ u) (hd : ∀ b, ContDiff ℝ ∞ (d b))
    (hgraph : ∀ b x, (u x,d b x) ∈ sphereDerivativeGraph hF hO hD b) (m : ℕ) (x : R3) :
    sphereHarmonicCoordinate hO hD m
      (contractionFirstBase coordinateDirection (negativeFrameEntry g L lam) d x) =
      ∑ k, harmonicFrameLoweringCoefficient hF g L lam k m x
        (directionalFDeriv (coordinateDirection k)
          (fun y => sphereHarmonicCoordinate hO hD (m+1) (u y)) x) := by
  have hcoord (b k : Fin 3) :
      sphereHarmonicCoordinate hO hD m (directionalFDeriv (coordinateDirection k) (d b) x) =
      HarmonicDerivativeOperator.harmonicDerivative hF m b
        (directionalFDeriv (coordinateDirection k)
          (fun y => sphereHarmonicCoordinate hO hD (m+1) (u y)) x) := by
    have hg := directional_sphereDerivativeGraph hF hO hD b (coordinateDirection k)
      u (d b) hu (hd b) (hgraph b) x m
    simpa only [directional_const_clm_apply (sphereHarmonicCoordinate hO hD (m+1))
      (coordinateDirection k) u hu x] using hg
  unfold contractionFirstBase scalarFirstBase
  simp only [map_sum,map_smul,map_neg,negativeFrameEntry,neg_smul]
  simp_rw [hcoord]
  rw [Finset.sum_comm]
  simp only [harmonicFrameLoweringCoefficient,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,← Finset.sum_neg_distrib]

/-- The actual all-degree ambient construction has the native finite-degree
coefficient formula, with no graph witness or angular summability supplied. -/
theorem actualFrameFirstBase_harmonicCoordinate (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (m : ℕ) (x : R3) :
    sphereHarmonicCoordinate hO hD m (actualFrameFirstBase hF hO hD g L lam G hG x) =
      ∑ k, harmonicFrameLoweringCoefficient hF g L lam k m x
        (directionalFDeriv (coordinateDirection k)
          (fun y => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG y)) x) :=
  contractionFirstBase_harmonicCoordinate hF hO hD g L lam (ambientSphereL2 G hG)
    (fun b => ambientDerivativeField hF hO hD b G hG) (contDiff_ambientSphereL2 G hG)
    (fun b => contDiff_ambientDerivativeField hF hO hD b G hG)
    (fun b => ambientDerivativeField_graph hF hO hD b G hG) m x

/-- The scalar principal image is first constructed in the full angular
graph; its harmonic coordinate then uses precisely H_(m+1)→H_m. -/
theorem actualFrameFirstPrincipalComposition_harmonicCoordinate (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (m : ℕ) (x : R3) :
    sphereHarmonicCoordinate hO hD m
      (actualFrameFirstPrincipalComposition hF hO hD g L lam δ R p h G hG x) =
      ∑ k, harmonicFrameLoweringCoefficient hF g L lam k m x
        (directionalFDeriv (coordinateDirection k)
          (scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h)
            (fun y => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG y))) x) := by
  have ha := OAI.AnisotropicCalderon.ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh
  have hphi := contDiff_ambientSphereL2 G hG
  unfold actualFrameFirstPrincipalComposition
  rw [contractionFirstBase_harmonicCoordinate hF hO hD g L lam
    (scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h) (ambientSphereL2 G hG))
    (fun b => scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h)
      (ambientDerivativeField hF hO hD b G hG))
    (contDiff_scalarSecondBase coordinateDirection _ _ ha hphi)
    (fun b => contDiff_scalarSecondBase coordinateDirection _ _ ha
      (contDiff_ambientDerivativeField hF hO hD b G hG))
    (fun b => scalarSecondBase_sphereDerivativeGraph hF hO hD b coordinateDirection
      (actualPrincipalMatrix g L lam δ R p h) (ambientSphereL2 G hG)
      (ambientDerivativeField hF hO hD b G hG) hphi
      (contDiff_ambientDerivativeField hF hO hD b G hG)
      (ambientDerivativeField_graph hF hO hD b G hG)) m x]
  have he : (fun y => sphereHarmonicCoordinate hO hD (m+1)
      (scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h)
        (ambientSphereL2 G hG) y)) =
      scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h)
        (fun y => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG y)) :=
    funext (scalarSecondBase_harmonicCoordinate hO hD (m+1) coordinateDirection
      (actualPrincipalMatrix g L lam δ R p h) (ambientSphereL2 G hG) hphi)
  rw [he]

/-- Complete native coordinate identity for the actual raw commutator.
Both output terms lie in H_m. The raising/lowering degree boundary is exact
and no spectral truncation is performed in either composition. -/
theorem actualFrameFirstPrincipalCommutator_harmonicCoordinate (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (m : ℕ) (x : R3) :
    sphereHarmonicCoordinate hO hD m
      (actualFrameFirstPrincipalCommutator hF hO hD g L lam δ R p h G hG x) =
      (∑ k, harmonicFrameLoweringCoefficient hF g L lam k m x
        (directionalFDeriv (coordinateDirection k)
          (scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h)
            (fun y => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG y))) x)) -
      scalarSecondBase coordinateDirection (actualPrincipalMatrix g L lam δ R p h)
        (fun y => ∑ k, harmonicFrameLoweringCoefficient hF g L lam k m y
          (directionalFDeriv (coordinateDirection k)
            (fun z => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG z)) y)) x := by
  have hfirst : ContDiff ℝ ∞ (actualFrameFirstBase hF hO hD g L lam G hG) :=
    contDiff_contractionFirstBase coordinateDirection (negativeFrameEntry g L lam)
      (fun b => ambientDerivativeField hF hO hD b G hG)
      (contDiff_negativeFrameEntry g hg L lam)
      (fun b => contDiff_ambientDerivativeField hF hO hD b G hG)
  unfold actualFrameFirstPrincipalCommutator
  rw [map_sub,actualFrameFirstPrincipalComposition_harmonicCoordinate hF hO hD g hg
    L lam δ R p h hδ hR hh G hG m x,
    scalarSecondBase_harmonicCoordinate hO hD m coordinateDirection
      (actualPrincipalMatrix g L lam δ R p h) (actualFrameFirstBase hF hO hD g L lam G hG) hfirst x]
  have he : (fun y => sphereHarmonicCoordinate hO hD m
      (actualFrameFirstBase hF hO hD g L lam G hG y)) =
      (fun y => ∑ k, harmonicFrameLoweringCoefficient hF g L lam k m y
        (directionalFDeriv (coordinateDirection k)
          (fun z => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG z)) y)) :=
    funext (actualFrameFirstBase_harmonicCoordinate hF hO hD g L lam G hG m)
  rw [he]

end OAI.AnisotropicCalderon.ActualUnboundedFirstPrincipalCoordinates
